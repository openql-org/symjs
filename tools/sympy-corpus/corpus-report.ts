// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file A vitest reporter that measures SymPy compatibility from the generated corpus tests.
 *
 * Every case of SymPy's doctests and unit tests is generated into a `*.corpus.test.ts` file as one
 * of three kinds: `it` (symjs gives SymPy's result), `it.fails` (the case translates to the public
 * API but the result differs) and `it.todo` (the case does not translate yet). The compatibility
 * rate of a corpus is the share of its cases that are `it` and pass. A passing case is exact when
 * symjs prints SymPy's `str()` output, and equivalent when it passed only by the mathematical
 * equivalence of `packages/symjs/tests/sympy-equivalent.ts` (the test records that in its meta).
 * The describe group names the SymPy source: `doctests of sympy.<package>.<module>` or
 * `sympy/<package>/.../test_<name>.py`.
 *
 * Usage: `bun run corpus:report` writes `docs/compat-report.md` and lists the equivalent cases in
 * `docs/compat-equivalent-cases.md`.
 */

import { writeFileSync } from 'node:fs';
import type { Reporter, TestCase, TestModule } from 'vitest/node';

type Corpus = 'doctests' | 'unit tests';

interface Tally {
  /** Passing cases with SymPy's printed result. */
  exact: number;
  /** Passing cases with an equivalent result in another form. */
  equivalent: number;
  fails: number;
  todo: number;
  /** An `it` that failed or an `it.fails` that passed: the generated file is out of date. */
  stale: number;
}

const empty = (): Tally => ({ exact: 0, equivalent: 0, fails: 0, todo: 0, stale: 0 });
const total = (t: Tally): number => t.exact + t.equivalent + t.fails + t.todo + t.stale;
const percent = (n: number, t: Tally): string => (total(t) === 0 ? '-' : `${((100 * n) / total(t)).toFixed(2)}%`);

function origin(test: TestCase): { corpus: Corpus; category: string } | undefined {
  const group = test.parent.type === 'suite' ? test.parent.name : '';
  const doc = /^doctests of sympy\.(\w+)/.exec(group);
  if (doc) return { corpus: 'doctests', category: doc[1] ?? '' };
  const unit = /^sympy\/(\w+)\/.*\.py$/.exec(group);
  if (unit) return { corpus: 'unit tests', category: unit[1] ?? '' };
  return undefined;
}

/** A table cell: pipes escaped, long values shortened. */
const cell = (s: string): string => (s.length > 200 ? `${s.slice(0, 200)}…` : s).replace(/\|/g, '\\|').replace(/`/g, "'").replace(/\n/g, ' ');

function table(rows: Map<string, Tally>): string[] {
  const lines = ['| Category | Rate | Exact rate | Exact | Equivalent | Fails | Todo | Stale |', '| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |'];
  const all = empty();
  const row = (t: Tally): string => `${percent(t.exact + t.equivalent, t)} | ${percent(t.exact, t)} | ${t.exact} | ${t.equivalent} | ${t.fails} | ${t.todo} | ${t.stale}`;
  for (const [name, t] of [...rows].sort(([a], [b]) => a.localeCompare(b))) {
    lines.push(`| ${name} | ${row(t)} |`);
    all.exact += t.exact;
    all.equivalent += t.equivalent;
    all.fails += t.fails;
    all.todo += t.todo;
    all.stale += t.stale;
  }
  lines.push(`| **all** | **${percent(all.exact + all.equivalent, all)}** | **${percent(all.exact, all)}** | ${all.exact} | ${all.equivalent} | ${all.fails} | ${all.todo} | ${all.stale} |`);
  return lines;
}

export default class CorpusReport implements Reporter {
  onTestRunEnd(modules: ReadonlyArray<TestModule>): void {
    const tallies = new Map<Corpus, Map<string, Tally>>([['doctests', new Map()], ['unit tests', new Map()]]);
    const stale: string[] = [];
    const equivalents: string[] = [];
    for (const module of modules) {
      if (!module.moduleId.endsWith('.corpus.test.ts')) continue;
      for (const test of module.children.allTests()) {
        const o = origin(test);
        if (o === undefined) continue;
        const byCategory = tallies.get(o.corpus);
        if (byCategory === undefined) continue;
        const t = byCategory.get(o.category) ?? empty();
        byCategory.set(o.category, t);
        const state = test.result().state;
        if (test.options.mode === 'todo') t.todo++;
        else if (state !== 'passed') {
          t.stale++;
          stale.push(`${test.module.relativeModuleId} > ${test.fullName}`);
        } else if (test.options.fails === true) t.fails++;
        else {
          const seen = test.meta().sympyEquivalent;
          if (seen === undefined) t.exact++;
          else {
            t.equivalent++;
            equivalents.push(`| ${o.corpus} | ${test.module.relativeModuleId} > ${test.fullName} | \`${cell(seen.got)}\` | \`${cell(seen.expected)}\` |`);
          }
        }
      }
    }
    const lines = [
      '# SymPy agreement of generated corpus tests (`bun run corpus:report`)',
      '',
      'Generated from the `*.corpus.test.ts` files; do not edit.',
      'Rate = cases that give SymPy\'s result / all cases; Exact rate = cases printed as SymPy prints them / all cases.',
      'Exact: the same `str()` output. Equivalent: a mathematically equal result in another form (listed in [compat-equivalent-cases.md](compat-equivalent-cases.md)).',
      'Fails: translated, the result differs. Todo: not translated yet.',
    ];
    for (const [corpus, rows] of tallies) lines.push('', `## ${corpus[0]?.toUpperCase() ?? ''}${corpus.slice(1)}`, '', ...table(rows));
    if (stale.length > 0) lines.push('', '## Stale cases', '', ...stale.map((s) => `- ${s}`));
    writeFileSync(new URL('../../docs/compat-report.md', import.meta.url), lines.join('\n') + '\n');
    const listed = [
      '# Generated corpus cases that pass by equivalence only (`bun run corpus:report`)',
      '',
      'Generated from the `*.corpus.test.ts` files; do not edit.',
      'symjs gives a mathematically equal result printed differently from SymPy (`packages/symjs/tests/sympy-equivalent.ts`).',
      '',
      '| Corpus | Case | symjs | SymPy |',
      '| --- | --- | --- | --- |',
      ...equivalents.sort(),
    ];
    writeFileSync(new URL('../../docs/compat-equivalent-cases.md', import.meta.url), listed.join('\n') + '\n');
  }
}

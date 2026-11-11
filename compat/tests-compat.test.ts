// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { appendFileSync, readFileSync, writeFileSync } from 'node:fs';
import { performance } from 'node:perf_hooks';
import { expect, it } from 'vitest';
import { runTestCase, testCaseKey } from './tests-harness';
import type { TestCase, TestOutcome } from './tests-harness';

interface Audit { examined: number; cases: number; reasons: Record<string, number> }
interface TestCorpus {
  sympy: string;
  cases: TestCase[];
  extraction: Audit & {
    sourceSites: number;
    categories: Record<string, Audit>;
    testStatuses: Record<string, number>;
    tests: { module: string; test: string; status: string }[];
  };
}
interface Counts { cases: number; exact: number; equivalent: number; fail: number; unsupported: number; error: number }
const emptyCounts = (): Counts => ({ cases: 0, exact: 0, equivalent: 0, fail: 0, unsupported: 0, error: 0 });
const ratio = (a: number, b: number): string => b === 0 ? '-' : `${(100 * a / b).toFixed(2)}%`;

it('measures the independent SymPy unit-test corpus and enforces its ratchet', () => {
  const corpus: TestCorpus = JSON.parse(readFileSync(new URL('./tests-corpus.json', import.meta.url), 'utf8'));
  const start = performance.now();
  const results: { c: TestCase; o: TestOutcome; id: string }[] = [];
  const total = emptyCounts();
  const modules: Record<string, Counts> = {};
  const categories: Record<string, Counts> = {};
  const groups: Record<string, number> = {};
  for (const t of corpus.extraction.tests) modules[t.module] ??= emptyCounts();
  for (const c of corpus.cases) {
    const progress = process.env['COMPAT_TESTS_PROGRESS'];
    if (progress) appendFileSync(progress, `${results.length} ${c.module}:${c.test}:${c.line} ${c.fn}\n`);
    const o = runTestCase(c);
    const id = testCaseKey(c);
    results.push({ c, o, id });
    const status = o.status === 'pass' ? 'exact' : o.status;
    for (const counts of [total, modules[c.module] ??= emptyCounts(), categories[c.category] ??= emptyCounts()]) {
      counts.cases++;
      counts[status]++;
    }
    if (o.status !== 'pass' && o.status !== 'equivalent') {
      const group = `${c.category}: ${c.fn} (${o.status})`;
      groups[group] = (groups[group] ?? 0) + 1;
    }
  }
  const seconds = (performance.now() - start) / 1000;
  const failures = results.filter(({ o }) => o.status !== 'pass' && o.status !== 'equivalent');
  const failing = failures.map(({ id }) => id).sort();
  const mismatch = results.filter(({ o }) => o.exceptionMismatch !== undefined);
  const lines = [
    '# SymPy unit-test compatibility (core and polys pilot)', '',
    `Reference: SymPy ${corpus.sympy}. Independent of the doctest corpus and its ratchet.`, '',
    `Measured **${total.cases}** cases: **${total.exact} exact**, **${total.equivalent} equivalent**, **${failures.length} failing**. Agreement: **${ratio(total.exact + total.equivalent, total.cases)}**.`, '',
    `Replay runtime: **${seconds.toFixed(2)} s**. Known gaps: **${failing.length}**. Exception class mismatches accepted in the pilot: **${mismatch.length}**.`, '',
    'Exact includes successful inequality, identity, boolean and exception assertions. Equality uses the existing doctest matching and equivalence rules.', '',
    '## Agreement by category', '', '| Category | Cases | Exact | Equivalent | Fail | Unsupported | Error | Agreement |',
    '|---|---:|---:|---:|---:|---:|---:|---:|',
  ];
  const row = (name: string, n: Counts): string => `| ${name} | ${n.cases} | ${n.exact} | ${n.equivalent} | ${n.fail} | ${n.unsupported} | ${n.error} | ${ratio(n.exact + n.equivalent, n.cases)} |`;
  for (const [category, counts] of Object.entries(categories).sort()) lines.push(row(category, counts));
  lines.push('', '## Agreement by test module', '', '| Module | Cases | Exact | Equivalent | Fail | Unsupported | Error | Agreement |', '|---|---:|---:|---:|---:|---:|---:|---:|');
  for (const [module, counts] of Object.entries(modules).sort()) lines.push(row(module, counts));
  lines.push('', '## Extraction audit', '',
    `${corpus.extraction.sourceSites} static assertion/exception sites; ${corpus.extraction.examined} examined observations. Executed loop instances count individually. Duplicates count as omissions; never-reached sites count once. Partial observations from timed-out tests are discarded.`, '',
    '| Category | Examined | Cases | Omitted |', '|---|---:|---:|---:|');
  for (const [category, audit] of Object.entries(corpus.extraction.categories).sort()) {
    lines.push(`| ${category} | ${audit.examined} | ${audit.cases} | ${Object.values(audit.reasons).reduce((a, b) => a + b, 0)} |`);
    expect(audit.examined).toBe(audit.cases + Object.values(audit.reasons).reduce((a, b) => a + b, 0));
  }
  lines.push('', '| Omission reason | core | polys | Total |', '|---|---:|---:|---:|');
  for (const [reason, n] of Object.entries(corpus.extraction.reasons).sort()) {
    lines.push(`| ${reason} | ${corpus.extraction.categories['core']?.reasons[reason] ?? 0} | ${corpus.extraction.categories['polys']?.reasons[reason] ?? 0} | ${n} |`);
  }
  lines.push('', '| Test execution status | Count |', '|---|---:|');
  for (const [status, count] of Object.entries(corpus.extraction.testStatuses).sort()) lines.push(`| ${status} | ${count} |`);
  lines.push('', '## Main failure groups', '', '| API and result | Cases |', '|---|---:|');
  for (const [group, n] of Object.entries(groups).sort((a, b) => b[1] - a[1]).slice(0, 40)) lines.push(`| ${group} | ${n} |`);
  lines.push('', '## Exception class mismatches', '',
    'Any exception from an invoked adapter counts as agreement in this pilot. Missing adapters and deserialization failures do not. ValueError and ZeroDivisionError map to RangeError; TypeError, NotImplementedError and polynomial exception classes retain their names.', '',
    '| Case | Python class | JS class |', '|---|---|---|');
  for (const { id, o } of mismatch) lines.push(`| ${id} | ${o.exceptionMismatch?.expected} | ${o.exceptionMismatch?.actual} |`);
  lines.push('');
  writeFileSync(new URL('./TESTS-REPORT.md', import.meta.url), lines.join('\n'));
  writeFileSync(new URL('./tests-report.json', import.meta.url), JSON.stringify({
    sympy: corpus.sympy, seconds, total, categories, modules, extraction: corpus.extraction,
    failureGroups: groups, failures: failures.map(({ c, o, id }) => ({ id, fn: c.fn, expected: c.expected, ...o })),
    exceptionMismatches: mismatch.map(({ id, o }) => ({ id, ...o.exceptionMismatch })),
  }, null, 1) + '\n');
  const gapsFile = new URL('./tests-known-gaps.json', import.meta.url);
  if (process.env['UPDATE_KNOWN_GAPS']) writeFileSync(gapsFile, JSON.stringify({ cases: failing }, null, 1) + '\n');
  const gaps: { cases: string[] } = JSON.parse(readFileSync(gapsFile, 'utf8'));
  expect(corpus.cases.length).toBeGreaterThan(0);
  expect(new Set(results.map(({ id }) => id)).size).toBe(corpus.cases.length);
  expect(corpus.extraction.examined).toBe(corpus.cases.length + Object.values(corpus.extraction.reasons).reduce((a, b) => a + b, 0));
  const known = new Set(gaps.cases);
  const actual = new Set(failing);
  expect(failing.filter((id) => !known.has(id)), 'new unit-test compatibility regressions').toEqual([]);
  expect(gaps.cases.filter((id) => !actual.has(id)), 'fixed unit-test cases still listed as gaps').toEqual([]);
  console.log(`SymPy unit tests: ${total.cases} cases; ${total.exact} exact, ${total.equivalent} equivalent, ${failing.length} gaps; ${seconds.toFixed(2)} s`);
});

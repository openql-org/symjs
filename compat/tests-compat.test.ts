// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { appendFileSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { performance } from 'node:perf_hooks';
import { createContext, Script } from 'node:vm';
import { expect, inject, it } from 'vitest';
import { runTestCase, testCaseKey } from '../tools/sympy-corpus/tests-harness';
import { corpusIndex, emptyCounts, failureKind, ratchetDifferences, replayDeadlineMs } from './tests-report';
import type { TestCase, TestOutcome } from '../tools/sympy-corpus/tests-harness';
import type { CategoryResult, TestGaps } from './tests-report';

declare module 'vitest' {
  export interface ProvidedContext { testsCategory: string; testsResults: string }
}

const category = inject('testsCategory');
const directory = inject('testsResults');
const audit = corpusIndex().categories[category];

it(`measures SymPy ${category} unit tests and enforces their ratchet`, () => {
  if (audit === undefined) throw new TypeError(`Unknown unit-test category ${category}`);
  const start = performance.now();
  const result: CategoryResult = { category, seconds: 0, total: emptyCounts(), modules: {}, failureGroups: {}, apiGroups: {}, failures: [], exceptionMismatches: [] };
  for (const module of audit.modules) result.modules[module] = emptyCounts();
  const ids = new Set<string>();
  // vm interrupts synchronous library calls too; vitest's asynchronous test timeout cannot.
  const context = createContext({ runTestCase, current: undefined });
  const script = new Script('runTestCase(current)');
  const deadline = replayDeadlineMs(category);
  for (const shard of audit.shards) {
    const cases: TestCase[] = JSON.parse(readFileSync(new URL(`../tools/sympy-corpus/tests-corpus/${shard.file}`, import.meta.url), 'utf8'));
    expect(cases.length).toBe(shard.cases);
    for (const c of cases) {
      if (c.category !== category) throw new TypeError(`Wrong category in ${shard.file}`);
      const id = testCaseKey(c);
      if (ids.has(id)) throw new TypeError(`Duplicate case ${id}`);
      ids.add(id);
      const progress = process.env['COMPAT_TESTS_PROGRESS'];
      if (progress) appendFileSync(`${progress}.${category}`, `${ids.size} ${id} ${c.fn}\n`);
      let o: TestOutcome;
      try {
        context['current'] = c;
        o = script.runInContext(context, { timeout: deadline });
      } catch (error) {
        if (typeof error !== 'object' || error === null || !('code' in error) || error.code !== 'ERR_SCRIPT_EXECUTION_TIMEOUT') throw error;
        o = { status: 'error', reason: `Replay deadline exceeded (${deadline / 1000} s)` };
      }
      const status = o.status === 'pass' ? 'exact' : o.status;
      for (const counts of [result.total, result.modules[c.module] ??= emptyCounts()]) { counts.cases++; counts[status]++; }
      if (o.exceptionMismatch) result.exceptionMismatches.push({ id, ...o.exceptionMismatch });
      if (o.status !== 'pass' && o.status !== 'equivalent') {
        result.failures.push({ id, fn: c.fn, expected: c.expected, outcome: o });
        const kind = failureKind(o);
        result.failureGroups[kind] = (result.failureGroups[kind] ?? 0) + 1;
        const api = `${c.fn} (${o.status})`;
        result.apiGroups[api] = (result.apiGroups[api] ?? 0) + 1;
      }
    }
  }
  result.seconds = (performance.now() - start) / 1000;
  writeFileSync(join(directory, `${category}.json`), JSON.stringify(result));
  mkdirSync(new URL('./tests-results/', import.meta.url), { recursive: true });
  writeFileSync(new URL(`./tests-results/${category}.jsonl`, import.meta.url), result.failures.map((r) => JSON.stringify(r)).join('\n') + '\n');
  expect(ids.size).toBe(audit.cases);
  expect(audit.examined).toBe(ids.size + Object.values(audit.reasons).reduce((a, b) => a + b, 0));
  const gaps: TestGaps = JSON.parse(readFileSync(new URL('../tools/sympy-corpus/tests-known-gaps.json', import.meta.url), 'utf8'));
  const known = { ...gaps, cases: gaps.cases.filter((id) => id.startsWith(`sympy.${category}.`)) };
  const failing = result.failures.map((f) => f.id);
  const timeouts = result.failures.filter((f) => f.outcome.status === 'error' && f.outcome.reason.startsWith('Replay deadline')).map((f) => f.id);
  if (!process.env['UPDATE_KNOWN_GAPS']) {
    const changes = ratchetDifferences(known, failing, timeouts);
    expect(changes.regressions, `new ${category} unit-test regressions`).toEqual([]);
    expect(changes.fixed, `fixed ${category} cases still listed as gaps`).toEqual([]);
  }
  console.log(`SymPy ${category}: ${ids.size} cases; ${result.total.exact} exact, ${result.total.equivalent} equivalent, ${failing.length} gaps; ${result.seconds.toFixed(2)} s`);
});

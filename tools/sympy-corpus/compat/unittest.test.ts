// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { appendFileSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { performance } from 'node:perf_hooks';
import { expect, inject, it } from 'vitest';
import { runTestCase, testCaseKey } from '../unittest-harness';
import { corpusIndex, emptyCounts, failureKind } from './unittest-report';
import type { TestCase, TestOutcome } from '../unittest-harness';
import type { CategoryResult } from './unittest-report';
import { replayWithDeadline, ratchetDifferences, type TestGaps } from './replay';

const category = inject('corpusCategory');
const directory = inject('corpusResults');
const audit = corpusIndex().categories[category];

it(`measures SymPy ${category} unit tests and enforces their ratchet`, () => {
  if (audit === undefined) throw new TypeError(`Unknown unit-test category ${category}`);
  const start = performance.now();
  const result: CategoryResult = { category, seconds: 0, total: emptyCounts(), modules: {}, failureGroups: {}, apiGroups: {}, failures: [], exceptionMismatches: [] };
  for (const module of audit.modules) result.modules[module] = emptyCounts();
  const ids = new Set<string>();
  const excluded = new Map<string, string>();
  const replay = replayWithDeadline(runTestCase, category);
  for (const shard of audit.shards) {
    const cases: TestCase[] = JSON.parse(readFileSync(new URL(`../unittest/${shard.file}`, import.meta.url), 'utf8'));
    expect(cases.length).toBe(shard.cases);
    for (const c of cases) {
      if (c.category !== category) throw new TypeError(`Wrong category in ${shard.file}`);
      const id = testCaseKey(c);
      if (ids.has(id)) throw new TypeError(`Duplicate case ${id}`);
      ids.add(id);
      if (c.exclusion) { excluded.set(id, c.exclusion); continue; }
      const progress = process.env['COMPAT_TESTS_PROGRESS'];
      if (progress) appendFileSync(`${progress}.${category}`, `${ids.size} ${id} ${c.fn}\n`);
      const o: TestOutcome = replay(c);
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
  result.exclusions = [...excluded].map(([id, reason]) => ({ id, reason }));
  result.seconds = (performance.now() - start) / 1000;
  writeFileSync(join(directory, `${category}.json`), JSON.stringify(result));
  mkdirSync(new URL('./results/unittest/', import.meta.url), { recursive: true });
  writeFileSync(new URL(`./results/unittest/${category}.jsonl`, import.meta.url), result.failures.map(r => JSON.stringify(r) + '\n').join(''));
  expect(ids.size).toBe(audit.cases);
  expect(audit.examined).toBe(ids.size + Object.values(audit.reasons).reduce((a, b) => a + b, 0));
  const gaps: TestGaps = JSON.parse(readFileSync(new URL('../unittest-known-gaps.json', import.meta.url), 'utf8'));
  const known = { ...gaps, cases: gaps.cases.filter((id) => id.startsWith(`sympy.${category}.`) && !excluded.has(id)) };
  const failing = result.failures.map((f) => f.id);
  const timeouts = result.failures.filter((f) => f.outcome.status === 'error' && f.outcome.reason.startsWith('Replay deadline')).map((f) => f.id);
  if (process.env['UPDATE_KNOWN_GAPS'] !== '1') {
    const changes = ratchetDifferences(known, failing, timeouts);
    expect(changes.regressions, `new ${category} unit-test regressions`).toEqual([]);
    expect(changes.fixed, `fixed ${category} cases still listed as gaps`).toEqual([]);
  }
  console.log(`SymPy ${category}: ${ids.size} cases; ${result.total.exact} exact, ${result.total.equivalent} equivalent, ${failing.length} gaps; ${result.seconds.toFixed(2)} s`);
});

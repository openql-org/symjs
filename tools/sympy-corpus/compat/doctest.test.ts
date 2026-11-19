// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { expect, inject, it } from 'vitest';
import { readCases, readIndex, type DoctestIndex } from '../corpus';
import { runCase } from '../harness';
import { apiKey, caseKey, caseLabel, counterpartFor } from '../doctest-harness';
import { adapterInventory, evidenceFor } from '../adapter-audit';
import { PORTS } from '../ports';
import { runOdeChecks } from '../ode-checks';
import { runBaseChecks } from './base-scope';
import { OUT_OF_SCOPE, OUT_OF_SCOPE_API, type DoctestResult, type ScopeChecks } from './doctest-report';
import { ratchetDifferences, replayWithDeadline, type TestGaps } from './replay';

const category = inject('corpusCategory');
const directory = inject('corpusResults');
const index = readIndex<DoctestIndex>('doctest');

it(`measures SymPy ${category} doctests and enforces their ratchet`, () => {
  const cases = [...readCases('doctest', category)];
  expect(cases).toHaveLength(index.categories[category]!.cases);
  const replay = replayWithDeadline(runCase, category);
  const result: DoctestResult = { results: [], apiEvidence: [], failing: [], timeouts: [], missingApi: [], ported: 0 };
  const counts = new Map<string, number>();
  const modules = new Set(cases.map(c => c.module));
  const failures = [];
  for (const c of cases) {
    if (c.category !== category) throw new TypeError(`Wrong category for ${caseLabel(c)}`);
    if (OUT_OF_SCOPE[caseLabel(c)] !== undefined) continue;
    const { module, src, fn, expected } = c;
    const o = replay(c);
    const evidence = evidenceFor(c);
    result.results.push({ c: { module, src, fn, category, expected }, o, evidence });
    if (PORTS[`${module}:${src}`]) result.ported++;
    counts.set(fn, (counts.get(fn) ?? 0) + 1);
    if (o.status === 'pass' || o.status === 'equivalent') continue;
    const id = caseKey(c);
    result.failing.push(id);
    if (o.status === 'error' && o.reason.startsWith('Replay deadline')) result.timeouts.push(id);
    failures.push({ id, fn, expected, outcome: o });
  }
  for (const a of index.api.filter(a => a.category === category && OUT_OF_SCOPE_API[apiKey(a)] === undefined)) {
    const counterpart = counterpartFor(a) ?? null;
    result.apiEvidence.push({ ...a, counterpart, status: counterpart ? 'present' : 'unverified-or-absent', directCases: counts.get(a.name) ?? 0 });
    if (!counterpart) result.missingApi.push(apiKey(a));
  }
  writeFileSync(join(directory, `${category}.json`), JSON.stringify(result));
  const output = new URL('./results/doctest/', import.meta.url);
  mkdirSync(output, { recursive: true });
  writeFileSync(new URL(`${category}.jsonl`, output), failures.map(f => JSON.stringify(f) + '\n').join(''));
  if (process.env['UPDATE_KNOWN_GAPS'] !== '1') {
    const gaps: TestGaps & { api: string[] } = JSON.parse(readFileSync(new URL('../doctest-known-gaps.json', import.meta.url), 'utf8'));
    const known = { ...gaps, cases: gaps.cases.filter(k => modules.has(k.split(':', 1)[0]!)) };
    const changes = ratchetDifferences(known, result.failing, result.timeouts);
    expect(changes.regressions, `new ${category} doctest regressions`).toEqual([]);
    expect(changes.fixed, `fixed ${category} cases still listed as gaps`).toEqual([]);
    expect(result.missingApi.filter(k => !gaps.api.includes(k)), `new ${category} API regressions`).toEqual([]);
    expect(gaps.api.filter(k => k.startsWith(category + ': ') && !result.missingApi.includes(k)), `fixed ${category} APIs still listed as gaps`).toEqual([]);
  }
});

if (category === ('core' in index.categories ? 'core' : Object.keys(index.categories)[0])) it('checks base scope and ODE agreement', () => {
  const checks: ScopeChecks = { base: runBaseChecks(), ode: runOdeChecks(), adapters: adapterInventory() };
  writeFileSync(join(directory, 'scope.json'), JSON.stringify(checks));
  expect(checks.base.filter(b => !b.pass), 'base scope regressions').toEqual([]);
  expect(checks.ode.filter(o => !o.pass), 'ODE regressions').toEqual([]);
});

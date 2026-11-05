// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { readFileSync, existsSync, writeFileSync } from 'node:fs';
import { expect, it } from 'vitest';
import { counterpartFor, hasCounterpart, type Case } from './harness';
import { adapterInventory, evidenceFor, REVIEWED_ADAPTERS } from './adapter-audit';
const read = (file: string) => JSON.parse(readFileSync(new URL(file, import.meta.url), 'utf8'));
it('pins the entire module universe without converting missing evidence into exclusions', () => {
  const scope = read('./scope-inventory.json');
  expect(scope.reference.sympy).toBe('1.14.0');
  expect(scope.modules.length).toBe(825);
  expect(new Set(scope.modules.map((m: { module: string }) => m.module)).size).toBe(825);
  for (const m of scope.modules) {
    expect(m.sha256).toMatch(/^[0-9a-f]{64}$/);
    expect(['partial', 'unimplemented', 'unassessed', 'excluded']).toContain(m.status);
    if (m.status === 'excluded') expect(m.reason.length).toBeGreaterThan(0);
    for (const source of m.sources) expect(existsSync(new URL('../packages/symjs/src/' + source, import.meta.url))).toBe(true);
  }
  for (const module of ['sympy.categories.baseclasses', 'sympy.solvers.pde', 'sympy.tensor.tensor', 'sympy.combinatorics.perm_groups', 'sympy.polys.numberfields.subfield']) {
    expect(scope.modules.find((m: { module: string }) => m.module === module).status).toBe('partial');
  }
});
it('requires actual exported counterparts, including the concrete method owner', () => {
  expect(counterpartFor({ name: 'substitution' })).toBe('substitution');
  expect(counterpartFor({ name: 'Integer' })).toBe('Rational.of');
  expect(hasCounterpart({ name: 'solve_triangulated' })).toBe(false);
  expect(hasCounterpart({ name: '.det', owner: 'MutableDenseMatrix' })).toBe(true);
  expect(hasCounterpart({ name: '.det', owner: 'Expr' })).toBe(false);
  expect(hasCounterpart({ name: '.det', owner: 'UnknownClass' })).toBe(false);
  expect(hasCounterpart({ name: 'missing' })).toBe(false);
  for (const name of Object.keys(REVIEWED_ADAPTERS).filter((n) => n !== 'solve_linear_system_LU')) expect(hasCounterpart({ name })).toBe(true);
});
it('lists every adapter and counts unaudited computations separately', () => {
  const inventory = adapterInventory();
  const file = new URL('./adapter-inventory.json', import.meta.url);
  if (process.env['UPDATE_ADAPTER_INVENTORY']) writeFileSync(file, JSON.stringify(inventory, null, 1) + '\n');
  expect(read('./adapter-inventory.json')).toEqual(inventory);
  expect(evidenceFor({ module: '', src: '', fn: 'nonlinsolve' } as Case)).toBe('reviewed-conversion');
  expect(evidenceFor({ module: '', src: '', fn: 'solve' } as Case)).toBe('harness-computation');
  expect(evidenceFor({ module: '', src: '', fn: 'N' } as Case)).toBe('unreviewed-adapter');
  expect(evidenceFor({ module: '', src: '', fn: 'primitive_element' } as Case)).toBe('public-call');
});
it('accounts for every examined doctest and maintains condition-based test links', () => {
  const corpus = read('./corpus.json');
  const omitted = Object.values(corpus.extraction.reasons).reduce((a: number, b) => a + Number(b), 0);
  expect(corpus.extraction.examined).toBe(corpus.cases.length + omitted);
  // The detailed list contains output-bearing examples; reason counts also
  // include setup statements without expected output.
  expect(corpus.extraction.omitted.length).toBeLessThanOrEqual(omitted);
  const modules = new Set(read('./scope-inventory.json').modules.map((m: { module: string }) => m.module));
  for (const c of corpus.cases) expect(modules.has(c.module)).toBe(true);
  for (const area of read('./capabilities.json').areas) {
    expect(area.tested.length).toBeGreaterThan(0); expect(area.remaining.length).toBeGreaterThan(0);
    for (const test of area.tests) expect(existsSync(new URL('../' + test, import.meta.url))).toBe(true);
  }
});

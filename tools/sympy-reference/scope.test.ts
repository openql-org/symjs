// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { readFileSync, existsSync, writeFileSync } from 'node:fs';
import { execFileSync } from 'node:child_process';
import { expect, it } from 'vitest';
import { counterpartFor, hasCounterpart, type Case } from '../sympy-corpus/harness';
import { adapterInventory, evidenceFor, REVIEWED_ADAPTERS } from '../sympy-corpus/adapter-audit';
import { collectApiMembers, generateApiMembers, formatApiMembers } from './api-members';
import { scopeLines, scopeSummary } from './scope-report';
const read = (file: string) => JSON.parse(readFileSync(new URL(file, import.meta.url), 'utf8'));
it('pins the entire module universe without converting missing evidence into exclusions', () => {
  const scope = read('./scope-inventory.json');
  expect(scope.reference.sympy).toBe('1.14.0');
  expect(scope.modules.length).toBe(825);
  expect(new Set(scope.modules.map((m: { module: string }) => m.module)).size).toBe(825);
  for (const m of scope.modules) {
    expect(m.sha256).toMatch(/^[0-9a-f]{64}$/);
    expect(['complete', 'partial', 'unassessed', 'extend', 'excluded']).toContain(m.status);
    if (m.status === 'partial' || m.status === 'complete') {
      expect(Object.keys(m.completeness)).toEqual(['publicApi', 'doctests', 'unitTests', 'limitations']);
      expect(Object.values(m.completeness).every((c) => (c as { pass: boolean }).pass)).toBe(m.status === 'complete');
    }
    if (m.status === 'excluded') expect(m.reason.length).toBeGreaterThan(0);
    for (const source of m.sources) expect(existsSync(new URL('../../packages/symjs/src/' + source, import.meta.url))).toBe(true);
  }
  for (const module of ['sympy.categories.baseclasses', 'sympy.solvers.pde', 'sympy.tensor.tensor', 'sympy.combinatorics.perm_groups', 'sympy.polys.numberfields.subfield']) {
    expect(scope.modules.find((m: { module: string }) => m.module === module).status).toBe('partial');
  }
});
it('generates a deterministic export and class-member snapshot from every package entry', async () => {
  const api = await generateApiMembers();
  const file = new URL('./api-members.json', import.meta.url);
  if (process.env['UPDATE_API_MEMBERS'] || process.env['UPDATE_API_REPORT']) writeFileSync(file, formatApiMembers(api));
  expect(readFileSync(file, 'utf8')).toBe(formatApiMembers(api));
  expect(api.exports['parseLatex']?.entries).toContain('./parsing');
  expect(api.exports['Matrix']?.prototype).toContain('det');
});
it('inspects inherited, static and accessor members without invoking getters', () => {
  class Parent { inherited() {} static inheritedStatic() {} }
  class Child extends Parent {
    method() {}
    get length() { throw new TypeError('must not invoke an accessor'); }
    static get property() { throw new TypeError('must not invoke a static accessor'); }
    _private() {}
  }
  const entries = { './subpath': { Child }, '.': { Child, zero: 0, absent: undefined } };
  const api = collectApiMembers(entries);
  expect(api.exports['Child']).toEqual({ entries: ['.', './subpath'], kind: 'function', prototype: ['inherited', 'length', 'method'], static: ['inheritedStatic', 'property'] });
  expect(api.exports['zero']?.kind).toBe('number');
  expect(api.exports['absent']).toBeUndefined();
  expect(collectApiMembers(Object.fromEntries(Object.entries(entries).reverse()))).toEqual(api);
});
it('enforces all completeness criteria, including negative and missing-evidence cases', () => {
  execFileSync('python3', ['-B', '-m', 'unittest', 'discover', '-s', 'tools/sympy-reference', '-p', 'test_inventory.py'], { cwd: new URL('../..', import.meta.url), stdio: 'pipe' });
}, 300_000);
it('reports complete modules and all statuses in each package', () => {
  const inventory = { reference: { sympy: '1.14.0' }, modules: [
    { module: 'sympy.example.one', status: 'complete', selectedForExtraction: true, hasCorpusCases: true },
    { module: 'sympy.example.two', status: 'partial', selectedForExtraction: false, hasCorpusCases: false },
    { module: 'sympy.other.three', status: 'excluded', selectedForExtraction: false, hasCorpusCases: false },
  ] };
  expect(scopeSummary(inventory)).toEqual({ modules: 3, statuses: { complete: 1, partial: 1, unassessed: 0, extend: 0, excluded: 1 }, completeModules: ['sympy.example.one'] });
  expect(scopeLines(inventory)).toContain('| example | 1 | 1 | 0 | 0 | 0 |');
  expect(scopeLines(inventory)).toContain('- `sympy.example.one`');
  expect(scopeLines({ ...inventory, modules: [] })).toContain('None meet all four criteria.');
});
it('requires actual exported counterparts, including the concrete method owner', () => {
  expect(counterpartFor({ name: 'substitution' })).toBe('substitution');
  expect(counterpartFor({ name: 'Integer' })).toBe('Rational.of');
  expect(hasCounterpart({ name: 'solve_triangulated' })).toBe(true);
  expect(hasCounterpart({ name: 'xypic_draw_diagram' })).toBe(true);
  expect(hasCounterpart({ name: '.det', owner: 'MutableDenseMatrix' })).toBe(true);
  expect(hasCounterpart({ name: '.det', owner: 'Expr' })).toBe(false);
  expect(hasCounterpart({ name: '.det', owner: 'UnknownClass' })).toBe(false);
  expect(hasCounterpart({ name: 'missing' })).toBe(false);
  for (const name of Object.keys(REVIEWED_ADAPTERS)) expect(hasCounterpart({ name })).toBe(true);
});
it('lists every adapter and counts unaudited computations separately', () => {
  const inventory = adapterInventory();
  const file = new URL('../sympy-corpus/adapter-inventory.json', import.meta.url);
  if (process.env['UPDATE_ADAPTER_INVENTORY']) writeFileSync(file, JSON.stringify(inventory, null, 1) + '\n');
  expect(read('../sympy-corpus/adapter-inventory.json')).toEqual(inventory);
  expect(evidenceFor({ module: '', src: '', fn: 'nonlinsolve' } as Case)).toBe('reviewed-conversion');
  expect(evidenceFor({ module: '', src: '', fn: 'solve' } as Case)).toBe('harness-computation');
  expect(evidenceFor({ module: '', src: '', fn: 'N' } as Case)).toBe('unreviewed-adapter');
  expect(evidenceFor({ module: '', src: '', fn: 'primitive_element' } as Case)).toBe('public-call');
});
it('accounts for every examined doctest and maintains condition-based test links', () => {
  const corpus = read('../sympy-corpus/corpus.json');
  const omitted = Object.values(corpus.extraction.reasons).reduce((a: number, b) => a + Number(b), 0);
  expect(corpus.extraction.examined).toBe(corpus.cases.length + omitted);
  // The detailed list contains output-bearing examples; reason counts also
  // include setup statements without expected output.
  expect(corpus.extraction.omitted.length).toBeLessThanOrEqual(omitted);
  const modules = new Set(read('./scope-inventory.json').modules.map((m: { module: string }) => m.module));
  for (const c of corpus.cases) expect(modules.has(c.module)).toBe(true);
  for (const area of read('./capabilities.json').areas) {
    expect(area.tested.length).toBeGreaterThan(0);
    // an area is complete exactly when nothing within SymPy 1.14's scope remains
    expect(area.status === 'complete').toBe(area.remaining.length === 0);
    for (const test of area.tests) expect(existsSync(new URL('../../' + test, import.meta.url))).toBe(true);
  }
});

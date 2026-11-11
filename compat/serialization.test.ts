// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { expect, it, vi } from 'vitest';
import { readFileSync } from 'node:fs';
import { ADAPTERS, JsList, JsTuple, deserialize, matches, runCase, solvesDsolveCase } from './harness';
import type { Case } from './harness';
import * as sj from '../packages/symjs/src';

const corpus = JSON.parse(readFileSync(new URL('./corpus.json', import.meta.url), 'utf8')) as { cases: Case[] };

it('replays the supported receiver families through the public API', () => {
  const modules = [
    'sympy.combinatorics.subsets', 'sympy.combinatorics.graycode', 'sympy.combinatorics.prufer',
    'sympy.logic.algorithms.dpll2', 'sympy.core.rules', 'sympy.ntheory.ecm', 'sympy.assumptions.wrapper',
  ];
  const tags = new Set(['PublicObject', 'GrayCode', 'SATSolver', 'SATLevel', 'Transform', 'ECMPoint']);
  const cases = corpus.cases.filter((c) => modules.includes(c.module) && c.self !== undefined && tags.has(c.self.t));
  expect(cases.length).toBeGreaterThan(90);
  for (const c of cases) expect(runCase(c), `${c.module}: ${c.src}`).toEqual({ status: 'pass' });
});

it('preserves expression keys in factor dictionaries', () => {
  const one = { t: 'Rational', p: '1', q: '1' };
  const two = { t: 'Rational', p: '2', q: '1' };
  const result = deserialize({ t: 'PublicObject', cls: 'Factors', args: [{ t: 'Dict', items: [[two, one]] }] });
  expect(result).toBeInstanceOf(sj.Factors);
  if (!(result instanceof sj.Factors)) throw new TypeError('Factors expected');
  expect(String(result.asExpr())).toBe('2');
  expect([...result.factors.keys()][0]).toBeInstanceOf(sj.Rational);
});

it('keeps unsupported constructors explicit', () => {
  expect(() => deserialize({ t: 'PublicObject', cls: 'MissingClass', args: [] })).toThrow('class MissingClass');
});

it('selects assignment components before comparing values or text', () => {
  const c: Case = { module: 'sympy.polys.polytools', category: 'polys', src: 'part', fn: 'factor_list', expected: '[2, 3]', pick: 1 };
  const values = [
    new JsTuple([1, new JsList([2, 3])]), new JsList([1, [2, 3]]), [1, [2, 3]],
    (function* () { yield 1; yield [2, 3]; })(), new Set([1, [2, 3]]),
  ];
  const adapter = vi.spyOn(ADAPTERS, 'factor_list');
  try {
    for (const value of values) {
      adapter.mockReturnValueOnce(value);
      expect(runCase(c)).toEqual({ status: 'pass' });
    }
    adapter.mockReturnValueOnce(new JsTuple(['first', 'second']));
    expect(runCase({ ...c, pick: 0, text: true, expected: 'first' })).toEqual({ status: 'pass' });
    expect(adapter).toHaveBeenCalledTimes(values.length + 1);
  } finally {
    adapter.mockRestore();
  }
});

it('reports invalid or unavailable assignment components clearly', () => {
  const c: Case = { module: 'sympy.polys.polytools', category: 'polys', src: 'part', fn: 'factor_list', expected: '1', pick: 0 };
  const adapter = vi.spyOn(ADAPTERS, 'factor_list');
  try {
    for (const value of [sj.Rational.of(1), null, undefined, {}]) {
      adapter.mockReturnValueOnce(value);
      expect(runCase(c)).toEqual({ status: 'error', reason: 'pick 0: call result is not indexable (expected an array, tuple or iterable)' });
    }
    for (const value of [new JsTuple([1]), [1], new Set([1])]) {
      adapter.mockReturnValueOnce(value);
      expect(runCase({ ...c, pick: 1 })).toEqual({ status: 'error', reason: 'pick 1: result has only 1 items' });
    }
    for (const pick of [-1, 0.5, NaN, Infinity]) {
      adapter.mockReturnValueOnce([1]);
      expect(runCase({ ...c, pick })).toEqual({ status: 'error', reason: `pick ${pick}: expected a nonnegative integer index` });
    }
  } finally {
    adapter.mockRestore();
  }
});

it('converts matrix dimensions and rational coefficients for the public calls', () => {
  const r = (p: number) => ({ t: 'Rational', p: String(p), q: '1' });
  const list = (...items: unknown[]) => ({ t: 'Tuple', items, list: true });
  const base: Case = { module: 'sympy.polys.matrices.domainmatrix', category: 'polys', src: 'A', fn: '.from_list_sympy',
    self: { t: 'Type', name: 'DomainMatrix' }, args: [r(1), r(2), list(list(r(1), r(2)))],
    expected: 'DomainMatrix([[1, 2]], (1, 2), ZZ)' };
  expect(runCase(base)).toEqual({ status: 'pass' });
  expect(runCase({ module: 'sympy.matrices.expressions.slice', category: 'matrices', src: 'M', fn: 'ImmutableMatrix',
    args: [r(1), r(2), list(r(1), r(2))], expected: 'Matrix([[1, 2]])' })).toEqual({ status: 'pass' });
  const self = { t: 'DomainMatrix', cls: 'DomainMatrix', domain: { t: 'Domain', name: 'QQ' },
    shape: [1, 1], rows: [[r(3)]], fmt: 'dense' };
  expect(runCase({ ...base, fn: '.eval_poly', self, args: [list({ ...r(2), mpq: true }, { ...r(1), mpq: true })],
    expected: 'DomainMatrix([[7]], (1, 1), QQ)' })).toEqual({ status: 'pass' });
});

it('compares nested multiline matrices without erasing meaningful text', () => {
  const c: Case = { module: 'sympy.matrices.expressions.applyfunc', category: 'matrices', src: 'expr', fn: 'ElementwiseApplyFunction',
    args: [{ t: 'FnClass', name: 'exp' }, { t: 'Matrix', rows: [[{ t: 'Rational', p: '1', q: '1' }, { t: 'Rational', p: '0', q: '1' }]], shape: [1, 2] }],
    expected: 'Lambda(_d, exp(_d)).(Matrix([\n[1, 0]]))' };
  expect(runCase(c)).toEqual({ status: 'pass' });
  expect(runCase({ ...c, expected: 'Lambda(_d, exp(_d)).(Matrix([\n[0, 1]]))' }).status).toBe('fail');
  expect(matches('a, b', "'a,b'")).toBe(false);
  expect(matches(new sj.Sym('a b'), 'ab')).toBe(false);
});

it('replays sparse rational row reduction with the explicit coefficient field', () => {
  const r = (p: number) => ({ t: 'Rational', p: String(p), q: '1', mpq: true });
  // Indices are Python ints, while coefficients are MPQ ground elements.
  const index = (p: number) => ({ t: 'Rational', p: String(p), q: '1' });
  const rows = { t: 'Dict', items: [
    [index(0), { t: 'Dict', items: [[index(0), r(1)], [index(1), r(2)]] }],
    [index(1), { t: 'Dict', items: [[index(0), r(3)], [index(1), r(4)]] }],
  ] };
  const c: Case = { module: 'sympy.polys.matrices.sdm', category: 'polys', src: 'Arref', fn: 'sdm_irref',
    args: [rows], pick: 0, expected: '{0: {0: MPQ(1,1)}, 1: {1: MPQ(1,1)}}' };
  expect(runCase(c)).toEqual({ status: 'pass' });
  expect(runCase({ ...c, src: 'pivots', pick: 1, expected: '[0, 1]' })).toEqual({ status: 'pass' });
});

it('preserves solver collection shapes, finite-difference orders and sequence bases', () => {
  const names = new Set(['cornacchia', 'diop_univariate', 'diop_quadratic', 'diop_solve', 'diop_general_sum_of_squares', 'diop_general_sum_of_even_powers', 'prime_as_sum_of_two_squares', 'integer_powers', 'finite_diff_weights']);
  const cases = corpus.cases.filter((c) => names.has(c.fn) || (c.module === 'sympy.series.sequences' && (c.self?.t === 'SeqExpr' || c.self?.t === 'SeqExprOp')));
  expect(cases.length).toBeGreaterThanOrEqual(16);
  for (const c of cases) expect(['pass','equivalent'], c.src).toContain(runCase(c).status);
  const unevaluated = corpus.cases.find((c) => c.src.startsWith('domain_check(Mul'))!;
  expect(runCase(unevaluated)).toEqual({status:'pass'});
});

it('preserves tuples nested in finite sets and table cells', () => {
  const cases = corpus.cases.filter((c) => c.fn === 'TableForm' || c.src === 'pprint(nonlinsolve(system, [a, b, c, d]), use_unicode=False)');
  expect(cases.length).toBeGreaterThan(1);
  for (const c of cases) expect(['pass', 'equivalent'], c.src).toContain(runCase(c).status);
});

it('verifies system ODE families under the same arbitrary-constant convention as dsolve', () => {
  const cases = corpus.cases.filter((c) => c.fn === 'dsolve_system');
  expect(cases.length).toBeGreaterThan(0);
  for (const c of cases) expect(['pass', 'equivalent'], c.src).toContain(runCase(c).status);
});

it('checks every nested ODE family and rejects an invalid alternative', () => {
  const x = sj.symbol('x'), f = sj.SymFunction('f')(x), C1 = sj.symbol('C1');
  const equations = new JsTuple([sj.add(sj.pow(sj.diff(f, x), 2), -4)]);
  const positive = sj.Eq(f, sj.add(C1, sj.mul(2, x)));
  const negative = sj.Eq(f, sj.add(C1, sj.mul(-2, x)));
  expect(solvesDsolveCase(equations, new JsList([new JsList([positive]), new JsList([negative])]))).toBe(true);
  expect(solvesDsolveCase(equations, [[positive], [sj.Eq(f, sj.add(C1, sj.mul(3, x)))]] )).toBe(false);
  expect(solvesDsolveCase(equations, [])).toBe(false);
});

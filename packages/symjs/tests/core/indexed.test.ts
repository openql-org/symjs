// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/indexed.ts.
// Indexed objects. Expected values are SymPy 1.14's.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { type Expr, IndexedBase, add, diff, mul, parse, pow, sstr, str, symbols } from '../../src';

const [x, i, j] = symbols('x i j');

const s = (e: unknown): string => str(e as Expr);

describe('small core nodes', () => {
  it('includes indexed entries themselves in free_symbols', () => {
    const F = new IndexedBase('F'), entry = F.at(0);
    expect(entry.freeSymbols()).toEqual(new Set([entry, F.label]));
    const indexed = F.at(i);
    expect(sj.freeSymbols(sj.add(indexed, x))).toEqual(new Set([indexed, F.label, i, x]));
    expect(sj.freeSymbols(new sj.Integral([indexed, i, sj.S.Zero, sj.S.One]))).toEqual(new Set([indexed, F.label]));
    expect(entry.isNumber).toBe(false);
  });
  it('prints and differentiates indexed objects', () => {
    const A = new sj.IndexedBase('A');
    const i = sj.symbol('i');
    expect(String(A)).toBe('A');
    expect(String(new sj.IndexedBase(sj.symbol('B')))).toBe('B');
    expect(String(sj.diff(A.at(i), A.at(i)))).toBe('1');
  });
});

describe('Indexed derivatives', () => {
  const A = new IndexedBase('A');
  it('differentiates with respect to indexed objects', () => {
    expect(s(diff(A.at(i), A.at(i)))).toBe('1');
    expect(s(diff(A.at(i), A.at(j)))).toBe('KroneckerDelta(i, j)');
    expect(s(diff(pow(A.at(i), 2), A.at(i)))).toBe('2*A[i]');
    expect(s(diff(pow(A.at(i), 2), A.at(j)))).toBe('2*KroneckerDelta(i, j)*A[i]');
    expect(s(diff(mul(A.at(i), A.at(j)), A.at(j)))).toBe('KroneckerDelta(i, j)*A[j] + A[i]');
    expect(s(diff(pow(A.at(i), 3), A.at(i), 2))).toBe('6*A[i]');
    expect(s(diff(x, A.at(i)))).toBe('0');
    expect(() => diff(A.at(i, j), A.at(i))).toThrow(RangeError);
  });
  it('differentiates with respect to an index or the label', () => {
    expect(s(diff(A.at(i), i))).toBe('nan');
    expect(s(diff(A.at(add(i, 1)), i))).toBe('nan');
    expect(s(diff(A.at(i), A.label))).toBe('0');
  });
});

describe('Indexed and equations with several radicals', () => {
  it('match SymPy', async () => {
    const { IndexedBase, Sum, solve, summation } = await import('../../src');
    const f = new IndexedBase('f');
    const n = symbols('n')[0];
    expect(sstr(f.at(n))).toBe('f[n]');
    expect(sstr(summation(f.at(n).pow(2), [n, 0, 3]))).toBe('f[0]**2 + f[1]**2 + f[2]**2 + f[3]**2');
    void Sum;
    const x = symbols('x')[0];
    expect(solve(parse('-x**(1/5) + x**(1/3) + 1/7'), x).map((e) => sstr(e))).toEqual(['CRootOf(7*x**5 - 7*x**3 + 1, 1)**15', 'CRootOf(7*x**5 - 7*x**3 + 1, 2)**15']);
    expect(solve(parse('x**(1/2) - x**(1/4) - 2'), x).map((e) => sstr(e))).toEqual(['16']);
  });
});

it('compares base labels and retains rank and inherited real assumptions', () => {
  const a = new sj.IndexedBase('A');
  expect(a.equals(new sj.IndexedBase('A'))).toBe(true);
  expect(a.equals(new sj.IndexedBase('B'))).toBe(false);
  expect(a.equals(sj.symbol('A'))).toBe(false);
  expect(a.at(i,j).rank).toBe(2);
  expect(a.isReal).toBe('unknown');
  expect(new sj.IndexedBase(sj.symbol('A', {real:true})).isReal).toBe(true);
});

it('preserves explicit base shapes through indexing and substitution', () => {
  const A = new sj.IndexedBase('A', { shape: [x, 2] });
  expect(A.shape).toEqual([x, sj.Rational.of(2)]);
  expect(sj.shape(A.at(i, j))).toEqual([x, sj.Rational.of(2)]);
  expect(sj.shape(sj.xreplace(A.at(i, j), new Map([[x, sj.Rational.of(3)]])))).toEqual([sj.Rational.of(3), sj.Rational.of(2)]);
  expect(A.equals(new sj.IndexedBase('A', { shape: [x, 3] }))).toBe(false);
  expect(A.equals(new sj.IndexedBase('A', { shape: [x, 2] }))).toBe(true);
  expect(A.equals(new sj.IndexedBase('A'))).toBe(false);
  expect(String(A)).toBe('A');
  expect(sj.latex(A)).toBe('A');
  expect(sj.latex(A.at(i, j))).toBe('{A}_{i,j}');
  expect(() => A.at(i)).toThrow('Rank mismatch');
  const B = new sj.IndexedBase('B');
  expect(B.shape).toBe(sj.NoMatch);
  expect(B.withArgs(B.args).equals(B)).toBe(true);
});

it('inherits and preserves base assumptions without changing a symbolic label', () => {
  const label = sj.symbol('a');
  const a = new sj.IndexedBase(label, { positive: true, shape: [2] });
  expect(a.label).toBe(label);
  expect(a.equals(new sj.IndexedBase(label))).toBe(false);
  expect(a.equals(new sj.IndexedBase(label, { positive: true, real: true, shape: [2] }))).toBe(true);
  for (const e of [a, a.at(i)]) {
    expect([sj.isReal(e), sj.isComplex(e), sj.isImaginary(e), sj.isNonnegative(e), sj.isNonzero(e)]).toEqual([true, true, false, true, true]);
    expect(sj.log(sj.exp(e)).equals(e)).toBe(true);
    expect(e.isRealSelf()).toBe(true);
  }
  expect(sj.isReal(sj.xreplace(a.at(i), [[i, j]]))).toBe(true);
  const integer = new sj.IndexedBase('I', { integer: true });
  expect(sj.isIntegerValued(integer.label)).toBe(true);
  expect(sj.isIntegerValued(integer.at(0))).toBe(true);
  expect(a.func(...a.args).equals(new sj.IndexedBase(label, {shape: [2]}))).toBe(true);
  const b = new sj.IndexedBase('b');
  expect(b.func(...b.args).equals(b)).toBe(true);
  expect(new sj.IndexedBase('c', {commutative: false}).at(0).isCommutative).toBe(false);
});

it('validates indexed constructors and evaluates substituted sequence entries', () => {
  const a = new sj.IndexedBase('A');
  expect(() => new sj.Indexed([a])).toThrow(RangeError);
  expect(() => new sj.Indexed([a.at(i), j])).toThrow(TypeError);
  const tuple = sj.Tuple(10, 20);
  expect(String(a.at(1).subs(a, tuple))).toBe('20');
  expect(String(a.at(-1).subs(a.label, tuple))).toBe('20');
  expect(String(a.at(0).subs(a.label, sj.symbol('B')))).toBe('B[0]');
  expect(() => a.at(2).subs(a, tuple)).toThrow(RangeError);
  expect(new sj.Indexed([tuple, i]).assumptions0.size).toBe(0);
  expect(new sj.Indexed([tuple, i]).isRealSelf()).toBeUndefined();
  expect(new sj.Indexed([tuple, i]).subsSelf(i, j)).toBeUndefined();
  expect(String(new sj.Indexed([tuple, i]).withArgs([tuple, i]))).toBe('(10, 20)[i]');
  expect(String(new sj.Indexed([tuple, sj.S.Half]).withArgs([tuple, sj.S.Half]))).toBe('(10, 20)[1/2]');
  expect(String(new sj.Indexed([tuple, i, j]).withArgs([tuple, i, j]))).toBe('(10, 20)[i, j]');
});

it('gives the element when the base becomes an explicit array (SymPy Indexed on an NDimArray)', () => {
  const [x, y, z, w] = symbols('x y z w');
  const A = new IndexedBase('A', { shape: [2, 2] });
  const M = sj.ImmutableDenseNDimArray([[x, y], [z, w]]);
  expect(str(sj.subs(A.at(0, 0), [[A, M]]))).toBe('x');
  expect(str(sj.subs(A.at(1, 0), [[A, M]]))).toBe('z');
  // a symbolic index stays an indexed entry
  expect(str(sj.subs(A.at(x, 0), [[A, M]]))).toBe('[[x, y], [z, w]][x, 0]');
});

it('stores assumptions on a base with a quotient as its label', () => {
  const label = x.div(i);
  const base = new IndexedBase(label, { real: true });
  expect(base.label).toBe(label);
  expect(base.isReal).toBe(true);
  expect(new IndexedBase(label).isReal).toBe('unknown');
});

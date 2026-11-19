// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/accumbounds.ts.
// AccumBounds (SymPy AccumulationBounds). Expected values are SymPy 1.14's
// (sympy.calculus.tests.test_accumulationbounds).

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { Expr, Pow, Rational, S, impl } from '../../src/core/nodes';
import { add, mul, pow } from '../../src/core/ops';

const [x] = sj.symbols('x');

const A = sj.AccumBounds;

const s = (e: unknown) => sj.str(e as sj.Expr);
const R = (p: number, q: number) => sj.Rational.of(BigInt(p), BigInt(q));

const { I, oo } = sj;

const s2 = (e: Expr): string => e.toString();
const R2 = (p: number, q = 1) => Rational.of(p, q);

const negOo = mul(-1, oo);

describe('AccumBounds', () => {
  it('interval arithmetic', () => {
    expect(s(sj.add(A(1, 3), A(2, 5)))).toBe('AccumBounds(3, 8)');
    expect(s(sj.add(A(1, 3), 2))).toBe('AccumBounds(3, 5)');
    expect(s(sj.mul(A(1, 3), -2))).toBe('AccumBounds(-6, -2)');
    expect(s(sj.mul(A(-1, 2), A(-3, 1)))).toBe('AccumBounds(-6, 3)');
    expect(s(sj.pow(A(-1, 2), 2))).toBe('AccumBounds(0, 4)');
    expect(s(sj.pow(A(1, 2), -1))).toBe('AccumBounds(1/2, 1)');
    expect(s(sj.pow(A(-1, 2), -1))).toBe('AccumBounds(-oo, oo)');
    expect(s(sj.pow(A(1, 4), R(1, 2)))).toBe('AccumBounds(1, 2)');
    expect(s(sj.sub(A(1, 2), A(1, 2)))).toBe('AccumBounds(-1, 1)');
    expect(s(sj.add(x, A(1, 2)))).toBe('x + AccumBounds(1, 2)');
    expect(s(A(2, 2))).toBe('2');
    expect(() => A(3, 1)).toThrow(RangeError);
    expect(() => A(x, 1)).toThrow(TypeError);
  });
  it('properties and set operations', () => {
    const a = A(1, 3) as sj.AccumBoundsNode;
    expect([s(a.min), s(a.max), s(a.delta), s(a.mid), a.contains(2), a.contains(4)]).toEqual(['1', '3', '2', '2', true, false]);
    expect(s(a.intersection(A(2, 4)))).toBe('AccumBounds(2, 3)');
    expect(s(a.intersection(A(4, 6)))).toBe('EmptySet');
    expect(s((A(1, 4) as sj.AccumBoundsNode).intersection(sj.finiteSet(1, 2, 5)))).toBe('{1, 2}');
    expect(s(a.union(A(2, 5) as sj.AccumBoundsNode))).toBe('AccumBounds(1, 5)');
    expect(() => a.union(A(4, 5) as sj.AccumBoundsNode)).toThrow(RangeError);
  });
});

describe('AccumBounds (SymPy test_accumulationbounds)', () => {
  it('has delta, mid, LaTeX and membership', () => {
    const ab = A(1, 3);
    expect(s2((ab as sj.AccumBoundsNode).delta)).toBe('2');
    expect(s2((ab as sj.AccumBoundsNode).mid)).toBe('2');
    expect(sj.latex(ab)).toBe('\\left\\langle 1, 3\\right\\rangle');
    expect((ab as sj.AccumBoundsNode).contains(2)).toBe(true);
    expect((ab as sj.AccumBoundsNode).contains(4)).toBe(false);
  });
  it('rebuilds with new bounds by substitution', () => {
    // SymPy: AccumBounds(1, 2).subs(2, 3) = AccumBounds(1, 3)
    expect(s2(A(1, 2).subs(R2(2), 3))).toBe('AccumBounds(1, 3)');
  });
  it('intersects and unites intervals', () => {
    const ab = (lo: number, hi: number) => A(lo, hi) as sj.AccumBoundsNode;
    // SymPy: AccumBounds(1, 3).intersection(AccumBounds(2, 5)) = AccumBounds(2, 3), either way round
    expect(s2(ab(1, 3).intersection(ab(2, 5)))).toBe('AccumBounds(2, 3)');
    expect(s2(ab(2, 5).intersection(ab(1, 3)))).toBe('AccumBounds(2, 3)');
    expect(ab(1, 2).intersection(ab(3, 4))).toBe(sj.EmptySet);
    // SymPy: AccumBounds(1, 3).intersection(FiniteSet(2, 7)) = {2}
    expect(s2(ab(1, 3).intersection(new sj.FiniteSet([R2(2), R2(7)])))).toBe('{2}');
    expect(s2(ab(1, 3).union(ab(2, 5)))).toBe('AccumBounds(1, 5)');
    expect(() => ab(1, 2).union(ab(3, 4))).toThrow(RangeError);
  });
  it('multiplies intervals with an unbounded end (0*oo = 0 for the bounds)', () => {
    // SymPy: AccumBounds(0, oo)*AccumBounds(-1, 1) = AccumBounds(-oo, oo)
    expect(s2(mul(A(0, oo), A(-1, 1)))).toBe('AccumBounds(-oo, oo)');
    expect(String(mul(A(negOo, 1), 0))).toBe('AccumBounds(-oo, 0)');
  });
  it('keeps a non-real number beside the interval', () => {
    // SymPy: AccumBounds(1, 2) + I, I*AccumBounds(1, 2), (1 + I)*AccumBounds(1, 2)
    expect(s2(add(A(1, 2), I))).toBe('AccumBounds(1, 2) + I');
    expect(s2(mul(I, A(1, 2)))).toBe('I*AccumBounds(1, 2)');
    expect(s2(mul(A(1, 2), add(1, I)))).toBe('(1 + I)*AccumBounds(1, 2)');
  });
  it('is its own conjugate, adjoint and transpose', () => {
    // SymPy: conjugate(AccumBounds(1, 2)) = adjoint(...) = transpose(...) = AccumBounds(1, 2)
    expect(s2(sj.conjugate(A(1, 2)))).toBe('AccumBounds(1, 2)');
    expect(s2(sj.adjoint(A(1, 2)))).toBe('AccumBounds(1, 2)');
    expect(s2(sj.transpose(A(1, 2)))).toBe('AccumBounds(1, 2)');
  });
  it('raises intervals to integer powers', () => {
    // SymPy: AccumBounds(1, 3)**0 = 1, AccumBounds(-3, -1)**2 = AccumBounds(1, 9), AccumBounds(-3, 1)**2 = AccumBounds(0, 9)
    expect(pow(A(1, 3), 0)).toBe(S.One);
    expect(s2(pow(A(-3, -1), 2))).toBe('AccumBounds(1, 9)');
    expect(s2(pow(A(-3, 1), 2))).toBe('AccumBounds(0, 9)');
    expect(s2(pow(A(-3, -1), 3))).toBe('AccumBounds(-27, -1)');
    // SymPy: AccumBounds(2, 3)**-2 = AccumBounds(1/9, 1/4), AccumBounds(-1, 2)**-2 = AccumBounds(0, oo)
    expect(s2(pow(A(2, 3), -2))).toBe('AccumBounds(1/9, 1/4)');
    expect(s2(pow(A(-1, 2), -2))).toBe('AccumBounds(0, oo)');
    expect(s2(pow(A(-1, 2), -1))).toBe('AccumBounds(-oo, oo)');
  });
  it('raises nonnegative intervals to fractional powers', () => {
    // SymPy: AccumBounds(1, 4)**(1/2) = AccumBounds(1, 2), AccumBounds(1, 4)**(-1/2) = AccumBounds(1/2, 1)
    expect(s2(pow(A(1, 4), R2(1, 2)))).toBe('AccumBounds(1, 2)');
    expect(s2(pow(A(1, 4), R2(-1, 2)))).toBe('AccumBounds(1/2, 1)');
    // SymPy: AccumBounds(0, 4)**(1/2) = AccumBounds(0, 2), AccumBounds(0, 4)**(-1/2) = AccumBounds(1/2, oo)
    expect(s2(pow(A(0, 4), R2(1, 2)))).toBe('AccumBounds(0, 2)');
    expect(s2(pow(A(0, 4), R2(-1, 2)))).toBe('AccumBounds(1/2, oo)');
  });
  it('leaves a fractional power of an interval with negative numbers unevaluated', () => {
    // SymPy: AccumBounds(-1, 4)**(1/2) = sqrt(AccumBounds(-1, 4)); AccumBounds(-1, 4)**(1/3) likewise
    const e = pow(A(-1, 4), R2(1, 2));
    expect(e).toBeInstanceOf(Pow);
    expect(s2(e)).toBe('sqrt(AccumBounds(-1, 4))');
    expect(s2(pow(A(-1, 4), R2(1, 3)))).toBe('AccumBounds(-1, 4)**(1/3)');
  });
  it('rejects bounds that are not ordered real numbers', () => {
    expect(() => A(2, 1)).toThrow(RangeError);
    expect(() => A(x, 1)).toThrow(TypeError);
    expect(s2(A(1, 1))).toBe('1');
  });
});

describe('AccumBounds to an infinite power (SymPy AccumBounds.__pow__)', () => {
  const moo = mul(-1, oo);
  it.each([
    [1, 3, oo, 'AccumBounds(0, oo)'],
    [0, 3, oo, 'AccumBounds(0, oo)'],
    [R(1, 4), R(1, 2), oo, '0'],
    [2, 3, oo, 'oo'],
    [-1, 2, oo, 'AccumBounds(-oo, oo)'],
    [-2, -1, oo, 'nan'],
    [R(-1, 2), R(-1, 4), oo, '0'],
    [-3, -2, oo, 'zoo'],
    [R(-1, 2), R(1, 2), oo, '0'],
    [R(-1, 2), 2, oo, 'AccumBounds(0, oo)'],
    [1, 3, moo, 'AccumBounds(0, oo)'],
    [R(1, 4), R(1, 2), moo, 'oo'],
    [2, 3, moo, '0'],
    [0, R(1, 2), moo, 'oo'],
    [-2, -1, moo, 'nan'],
    [-1, 1, moo, 'AccumBounds(-oo, oo)'],
  ] as const)('AccumBounds(%s, %s)**%s = %s', (a, b, e, want) => expect(s(pow(A(a, b), e))).toBe(want));
  it('inverts an interval with 0 as an end point', () => {
    // SymPy: 1/AccumBounds(0, 2) = AccumBounds(1/2, oo), AccumBounds(-2, 0)**-3 = AccumBounds(-oo, -1/8)
    expect(s(pow(A(0, 2), -1))).toBe('AccumBounds(1/2, oo)');
    expect(s(pow(A(-2, 0), -1))).toBe('AccumBounds(-oo, -1/2)');
    expect(s(pow(A(0, 2), -2))).toBe('AccumBounds(1/4, oo)');
    expect(s(pow(A(-2, 0), -3))).toBe('AccumBounds(-oo, -1/8)');
    expect(s(pow(A(-1, 2), -1))).toBe('AccumBounds(-oo, oo)');
  });
});

it('raises positive intervals to interval powers and preserves unresolved negative bases', () => {
  expect(String(pow(A(2,3),A(-1,2)))).toBe('AccumBounds(1/3, 9)');
  expect(String(pow(A(0.5,2),A(-1,2)))).toBe('AccumBounds(0.25, 4)');
  expect(String(pow(A(-2,3),A(-1,2)))).toBe('AccumBounds(-2, 3)**AccumBounds(-1, 2)');
  expect((A(1,oo) as sj.AccumBoundsNode).contains(sj.S.NegativeInfinity)).toBe(true);
  expect((A(sj.S.NegativeInfinity,0) as sj.AccumBoundsNode).contains(oo)).toBe(true);
  expect((A(1,2) as sj.AccumBoundsNode).contains(oo)).toBe(false);
  expect((A(1,2) as sj.AccumBoundsNode).contains(1.5)).toBe(true);
});

it('validates real symbolic bounds and membership', () => {
  const r = sj.symbol('r', { real: true });
  expect(String(A(r, add(r, 1)))).toBe('AccumBounds(r, r + 1)');
  expect(() => A(I, 1)).toThrow(TypeError);
  expect(() => A(1, I)).toThrow(TypeError);
  const bounds = new sj.AccumBoundsNode(S.Zero, S.One);
  expect(() => bounds.contains(I)).toThrow(TypeError);
  expect(() => bounds.contains(r)).toThrow();
  expect(String(pow(A(0, 2), A(-1, 1)))).toBe('AccumBounds(0, 2)**AccumBounds(-1, 1)');
});

it('reports unloaded set operations', () => {
  const saved = { ...impl };
  try {
    impl.emptySet = undefined;
    const bounds = new sj.AccumBoundsNode(S.Zero, S.One);
    expect(() => bounds.intersection(A(2, 3))).toThrow(sj.NotLoadedError);
    impl.setIntersection = undefined;
    expect(() => bounds.intersection(sj.finiteSet(1))).toThrow(sj.NotLoadedError);
    Object.assign(impl, saved);
    impl.interval = undefined;
    expect(() => bounds.intersection(sj.finiteSet(1))).toThrow(sj.NotLoadedError);
  } finally {
    Object.assign(impl, saved);
  }
});

it('takes square roots of nonnegative symbolic bounds', () => {
  const n = sj.symbol('n', { nonnegative: true, integer: true });
  expect(String(pow(A(n, add(n, 1)), S.Half))).toBe('AccumBounds(sqrt(n), sqrt(n + 1))');
});

it('absorbs indeterminate products into the whole extended real line', async () => {
  const sj = await import('../../src');
  const bounds = sj.AccumBounds(sj.S.NegativeInfinity, sj.S.Infinity);
  expect(sj.mul(bounds, sj.S.NaN)).toBe(bounds);
  expect(sj.mul(bounds, 0)).toBe(bounds);
  expect(sj.mul(bounds, sj.AccumBounds(-1, 1))).toBe(bounds);
});

it('retains the unbounded directions of a product at zero and a quotient at infinity', () => {
  const r = sj.symbol('r', { real: true });
  expect(String(mul(0, A(r, oo)))).toBe('AccumBounds(0, oo)');
  const indeterminate = add(-1, pow(sj.sin(1), 2), pow(sj.cos(1), 2));
  expect(mul(indeterminate, A(1, 2))).toBeInstanceOf(sj.Mul);
  const right = A(1, oo);
  const left = A(negOo, -1);
  expect(String(S.Zero.div(A(0, 2)))).toBe('0');
  expect(String(mul(0, right))).toBe('AccumBounds(0, oo)');
  expect(String(right.div(negOo))).toBe('AccumBounds(-oo, 0)');
  expect(String(left.div(negOo))).toBe('AccumBounds(0, oo)');
  expect(String(mul(0, right, A(-1, 1)))).toBe('AccumBounds(-oo, oo)');
  expect(String(mul(A(-1, 1), 0, right))).toBe('AccumBounds(-oo, oo)');
});

it('keeps unresolved interval powers symbolic', () => {
  const n = sj.symbol('n', { integer: true });
  const r = sj.symbol('r', { nonnegative: true });
  expect(String(pow(A(-1, 2), n))).toBe('AccumBounds(-1, 2)**n');
  expect(String(pow(A(1, 2), A(r, add(r, 1))))).toBe('AccumBounds(1, 2)**AccumBounds(r, r + 1)');
  expect(String(pow(0, A(-2, 1)))).toBe('0**AccumBounds(-2, 1)');
});

it('requires real operands for ordered comparisons and decidable membership', () => {
  const bounds = new sj.AccumBoundsNode(S.NegOne, S.Zero);
  expect(() => sj.Ge(x, bounds)).toThrow(TypeError);
  expect(() => sj.Lt(bounds, x)).toThrow(TypeError);
  const boundary = add(-1, pow(sj.sin(1), 2), pow(sj.cos(1), 2));
  expect(() => bounds.contains(boundary)).toThrow(TypeError);
});

it('accepts an explicitly extended real operand in comparisons', () => {
  const r = sj.symbol('r', { extendedReal: true });
  expect(sj.Lt(A(0, 1), r)).toBeInstanceOf(sj.Rel);
  expect(String(A(0, r))).toBe('AccumBounds(0, r)');
  expect(String(add(A(1, 2), r))).toBe('AccumBounds(r + 1, r + 2)');
  expect(String(A(0, mul(2, r)))).toBe('AccumBounds(0, 2*r)');
  expect(String(mul(new sj.Float(0), A(1, oo)))).toBe('AccumBounds(0, oo)');
});

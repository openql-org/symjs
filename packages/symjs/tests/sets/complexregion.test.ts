// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/sets/complexregion.ts. Expected values are SymPy 1.14's str() and latex().

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';

const x = sj.symbol('x');
const p = (e: string) => sj.parse(e);
const I = (a: sj.ExprLike, b: sj.ExprLike, l = false, r = false) => sj.Interval.of(a, b, l, r);
const R = sj.ComplexRegion;
const C = (s: sj.SetExpr, v: sj.ExprLike) => String(sj.contains(s, sj.sympify(v)));
const a = I(2, 3);
const b = I(4, 6);
const c = I(1, 8);
const th = I(0, sj.mul(2, sj.pi));

describe('ComplexRegion (SymPy sympy.sets.fancysets)', () => {
  it('construction and attributes', () => {
    const r1 = R(sj.ProductSet(a, b)) as sj.ComplexRegionNode;
    const r2 = R(sj.Union(sj.ProductSet(a, b), sj.ProductSet(b, c))) as sj.ComplexRegionNode;
    expect([r1, r2].map(String)).toEqual([
      'CartesianComplexRegion(ProductSet(Interval(2, 3), Interval(4, 6)))',
      'CartesianComplexRegion(Union(ProductSet(Interval(2, 3), Interval(4, 6)), ProductSet(Interval(4, 6), Interval(1, 8))))',
    ]);
    expect(r1.psets.map(String)).toEqual(['ProductSet(Interval(2, 3), Interval(4, 6))']);
    expect([r2.aInterval, r2.bInterval, r1.sets].map(String)).toEqual(['Union(Interval(2, 3), Interval(4, 6))', 'Interval(1, 8)', 'ProductSet(Interval(2, 3), Interval(4, 6))']);
    expect([r1.polar, (R(sj.ProductSet(a, th), true) as sj.ComplexRegionNode).polar]).toEqual([false, true]);
    expect([R(sj.ProductSet(sj.FiniteSet.of(2, 4), sj.FiniteSet.of(3))), R(sj.ProductSet(sj.Reals, sj.Reals)), sj.ComplexRegion.fromReal(I(0, 1))].map(String)).toEqual([
      '{2 + 3*I, 4 + 3*I}',
      'Complexes',
      'CartesianComplexRegion(ProductSet(Interval(0, 1), {0}))',
    ]);
    expect(() => sj.ComplexRegion.fromReal(sj.ProductSet(I(0, 1), I(0, 1)))).toThrow(RangeError);
    // a region is made of products of two sets
    expect(() => R(I(0, 1), true)).toThrow('a product of two sets');
    expect(String(R(sj.ProductSet(a, th), true))).toBe('PolarComplexRegion(ProductSet(Interval(2, 3), Interval.Ropen(0, 2*pi)))');
    expect(String(R(sj.ProductSet(I(0, 1), I(p('3*pi/2'), p('5*pi/2'))), true))).toBe('PolarComplexRegion(ProductSet(Interval(0, 1), Union(Interval(0, pi/2), Interval.Ropen(3*pi/2, 2*pi))))');
    expect(String(sj.subs(R(sj.ProductSet(I(1, x), I(1, 2))), [[x, 3]]))).toBe('CartesianComplexRegion(ProductSet(Interval(1, 3), Interval(1, 2)))');
    expect(sj.latex(R(sj.ProductSet(b, b)))).toBe('\\left\\{x + y i\\; \\middle|\\; x, y \\in \\left[4, 6\\right]^{2} \\right\\}');
    expect(sj.latex(R(sj.ProductSet(b, I(0, sj.pi)), true))).toBe(
      '\\left\\{r \\left(i \\sin{\\left(\\theta \\right)} + \\cos{\\left(\\theta \\right)}\\right)\\; \\middle|\\; r, \\theta \\in \\left[4, 6\\right] \\times \\left[0, \\pi\\right] \\right\\}',
    );
  });
  it('membership (SymPy ComplexRegion._contains)', () => {
    const r1 = R(sj.ProductSet(a, b));
    expect([C(r1, p('2 + 5*I')), C(r1, p('1 + 5*I')), C(r1, x), C(r1, sj.Tuple(2, 5)), C(r1, a)]).toEqual([
      'True',
      'False',
      'Contains(x, CartesianComplexRegion(ProductSet(Interval(2, 3), Interval(4, 6))))',
      'True',
      'False',
    ]);
    expect(() => sj.contains(r1, sj.Tuple(1, 2, 3))).toThrow(RangeError);
    const pol = R(sj.ProductSet(a, th), true);
    expect([C(pol, p('2*I')), C(pol, 0), C(R(sj.ProductSet(I(0, 1), th), true), 0), C(pol, sj.Tuple(2, p('7*pi'))), C(R(sj.ProductSet(a, I(0, sj.pi)), true), -2), C(pol, x)]).toEqual([
      'True',
      'False',
      'True',
      'True',
      'True',
      'Contains(x, PolarComplexRegion(ProductSet(Interval(2, 3), Interval.Ropen(0, 2*pi))))',
    ]);
  });
  it('normalizeThetaSet (SymPy normalize_theta_set)', () => {
    const n = sj.normalizeThetaSet;
    expect(
      [
        I(0, p('4*pi')),
        I(sj.pi, p('3*pi'), true, true),
        I(p('pi/2'), p('3*pi/2')),
        I(p('3*pi/2'), p('5*pi/2')),
        sj.FiniteSet.of(0, p('3*pi'), p('-pi/2')),
        sj.Union(I(0, p('pi/2')), I(sj.pi, p('3*pi/2'))),
        I(0, p('2*pi'), true, true),
        sj.EmptySet,
      ].map((t) => String(n(t))),
    ).toEqual([
      'Interval.Ropen(0, 2*pi)',
      'Union(Interval.Ropen(0, pi), Interval.open(pi, 2*pi))',
      'Interval(pi/2, 3*pi/2)',
      'Union(Interval(0, pi/2), Interval.Ropen(3*pi/2, 2*pi))',
      '{0, pi, 3*pi/2}',
      'Union(Interval(0, pi/2), Interval(pi, 3*pi/2))',
      'Interval.open(0, 2*pi)',
      'EmptySet',
    ]);
    expect(() => n(I(0, 1))).toThrow(sj.NotImplementedError);
    expect(() => n(I(1, sj.add(1, sj.mul(2, sj.pi)), true, true))).toThrow(sj.NotImplementedError);
    expect(() => n(sj.FiniteSet.of(1))).toThrow(sj.NotImplementedError);
    expect(() => n(sj.Integers)).toThrow(sj.NotImplementedError);
    expect(() => n(sj.Complexes)).toThrow(RangeError);
    // the length of an interval with a symbolic end is not compared
    expect(() => n(I(0, x))).toThrow(sj.NotImplementedError);
  });
});

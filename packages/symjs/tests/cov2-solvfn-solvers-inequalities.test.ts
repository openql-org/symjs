// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { describe, expect, it } from 'vitest';
import { Abs, Eq, Gt, Poly, S as SS, parse, symbols } from '../src';
import { Piecewise as PW, Sym } from '../src/core/nodes';
import { add, mul, pow } from '../src/core/ops';
import { BoolOp } from '../src/core/boolalg';
import * as Q from '../src/solvers/inequalities';
import { Reals, finiteSet, interval, union } from '../src/sets/sets';

const [x, y] = symbols('x y');
const xr = new Sym('x', { real: true });
const p = (s: string) => parse(s);
const P = (s: string) => Poly.from(p(s), [x]);

// expected values from SymPy 1.14; comments mark where symjs differs
describe('solveset over intervals', () => {
  it('periods that are rational numbers, and candidates at poles', () => {
    expect(String(Q.solveset(p('sin(pi*x)'), x, interval(0, 3)))).toBe('{0, 1, 2, 3}');
    expect(String(Q.solveset(p('tan(x)-1'), x, interval(0, 4)))).toBe('{pi/4, 5*pi/4}');
  });
  it('zeros or bounds that are not known numbers give a ConditionSet', () => {
    // SymPy: Union(Intersection(ImageSet(Lambda(_n, 2*_n*pi), Integers), Interval(0, y)), ...)
    expect(String(Q.solveset(p('sin(x)'), x, interval(0, y)))).toBe('ConditionSet(x, Eq(sin(x), 0), Interval(0, y))');
    // SymPy: Union(Intersection(ImageSet(Lambda(_n, 2*_n*pi), Integers), Interval(0, oo)), ...)
    expect(String(Q.solveset(p('sin(x)'), x, interval(0, SS.Infinity)))).toBe('ConditionSet(x, Eq(sin(x), 0), Interval(0, oo))');
    // SymPy: ConditionSet(x, (-1 <= y) & (y <= 1), Union(Intersection({0}, ImageSet(...asin(y)...))))
    expect(String(Q.solveset(p('sin(x)-y'), x, interval(0, 1)))).toBe('ConditionSet(x, Eq(-y + sin(x), 0), Interval(0, 1))');
    // SymPy: ConditionSet(x, Ne(y, 0), {0})
    expect(String(Q.solveset(p('sin(x*y)'), x, interval(0, 1)))).toBe('ConditionSet(x, Eq(sin(x*y), 0), Interval(0, 1))');
    // SymPy: Intersection({y}, Interval(0, 1))
    expect(String(Q.solveset(p('x - y'), x, interval(0, 1)))).toBe('ConditionSet(x, Eq(x - y, 0), Interval(0, 1))');
    // SymPy: Intersection({2}, Interval(0, y))
    expect(String(Q.solveset(p('x - 2'), x, interval(0, y)))).toBe('ConditionSet(x, Eq(x - 2, 0), Interval(0, y))');
    expect(String(Q.solveset(p('x**2 - 2'), x, interval(0, 3)))).toBe('{sqrt(2)}');
  });
  it('an inequality with parameters is a ConditionSet', () => {
    expect(String(Q.solveset(p('x > y'), x, Reals))).toBe('ConditionSet(x, x > y, Reals)');
  });
  it('a periodic equation with a parameter factor', () => {
    expect(String(Q.solveset(p('y*sin(x)'), x, Reals))).toBe('Union(ImageSet(Lambda(_n, 2*_n*pi), Integers), ImageSet(Lambda(_n, 2*_n*pi + pi), Integers))');
  });
});

describe('inequalities', () => {
  it('an expression that cannot be evaluated raises', () => {
    // SymPy: NotImplementedError, relationship did not evaluate: -g(1) > 0
    expect(() => Q.solveUnivariateInequality(p('x*g(1) > 0'), x)).toThrow(TypeError);
  });
  it('solve_poly_inequality rejects an unknown relation', () => {
    // SymPy: ValueError, 'foo' is not a valid relation
    expect(() => Q.solvePolyInequality(P('x**2-1'), 'foo')).toThrow(TypeError);
  });
  it('solve_rational_inequalities with empty intersections', () => {
    expect(String(Q.solveRationalInequalities([[[[P('x'), P('1')], '>'], [[P('x'), P('1')], '<']]]))).toBe('EmptySet');
    expect(String(Q.solveRationalInequalities([[[[P('x'), P('x')], '==']]]))).toBe('EmptySet');
    expect(String(Q.solveRationalInequalities([[[[P('x-1'), P('x')], '>=']], [[[P('x+1'), P('1')], '<']]]))).toBe('Union(Interval.open(-oo, 0), Interval(1, oo))');
  });
  it('cases of an Abs split that are constant', () => {
    // SymPy raises NotImplementedError for these
    const sgn = add(mul(xr, pow(Abs(xr), -1)), 1);
    expect(String(Q.solveUnivariateInequality(Eq(sgn, 0), xr, { relational: false }))).toBe('Interval.open(-oo, 0)');
    expect(String(Q.solveUnivariateInequality(Gt(add(mul(xr, pow(Abs(xr), -1)), SS.I), 0), xr, { relational: false }))).toBe('EmptySet');
  });
  it('a periodic inequality with a rational period', () => {
    expect(String(Q.solveset(p('sin(pi*x) > 0'), x, Reals))).toBe('Interval.open(0, 1)');
  });
  it('piecewise_exclusive with a piece unbounded below', () => {
    expect(String(Q.piecewiseExclusive(new PW([x, p('x > 0'), SS.One, p('x < -1')])))).toBe('Piecewise((x, x > 0), (1, x < -1), (nan, (x >= -1) & (x <= 0)))');
  });
  it('as_set of an unevaluated Or with False', () => {
    expect(String(Q.asSet(new BoolOp('Or', [SS.false, p('x>0')])))).toBe('Interval.open(0, oo)');
  });
});

describe('monotonicity', () => {
  it('on a union of intervals', () => {
    expect(Q.isIncreasing(p('-x**3'), union(interval(1, 2), interval(3, 4)))).toBe(false);
    expect(Q.isIncreasing(p('-x**3'), finiteSet(1, 2))).toBe(false);
    expect(Q.isStrictlyIncreasing(p('x**3'), union(interval(1, 2), interval(3, 4)))).toBe(true);
    // a finite set with a symbol: SymPy None
    expect(Q.isIncreasing(p('-x**3'), finiteSet(y))).toBe(undefined);
    // SymPy True: x*y is linear in x, increasing or decreasing depending on the sign of y
    expect(Q.isMonotonic(p('x*y'), Reals, x)).toBe(true);
    // SymPy False (x**3 - x turns at x = +-sqrt(3)/3); not decided here as isDecreasing is undecided
    expect(Q.isMonotonic(p('x**3 - x'))).toBe(undefined);
  });
  it('a derivative that vanishes on an interval (x + Abs(x) for real x)', () => {
    const e = add(xr, Abs(xr));
    // SymPy False (is_strictly_increasing(x + Abs(x)) for real x)
    expect(Q.isStrictlyIncreasing(e, Reals, xr)).toBe(false);
    expect(Q.isStrictlyIncreasing(e, interval(-2, 1), xr)).toBe(false);
    expect(Q.isStrictlyIncreasing(e, interval(0, 1), xr)).toBe(true);
    expect(Q.isIncreasing(e, Reals, xr)).toBe(true);
  });
});

describe('maximum and minimum', () => {
  it('a rational period', () => {
    expect(String(Q.maximum(p('sin(pi*x)'), x))).toBe('1');
    expect(String(Q.minimum(p('sin(pi*x)'), x))).toBe('-1');
  });
  it('values with parameters', () => {
    expect(String(Q.maximum(p('x*y'), x, interval(0, 1)))).toBe('Max(0, y)');
    expect(String(Q.minimum(p('x*y'), x, interval(0, 1)))).toBe('Min(0, y)');
    expect(String(Q.maximum(p('x**2+y'), x, interval(-1, 2)))).toBe('y + 4');
    expect(String(Q.minimum(p('x**2+y'), x, interval(-1, 2)))).toBe('y');
  });
});

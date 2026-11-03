// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/solvers/inequalities.ts: inequality solving, solveset helpers, singularities, monotonicity and extrema; expected values from SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Abs, Eq, Gt, Ne, NotImplementedError, parse, Poly, Reals, S as SS, sin, solveset, symbols } from '../../src';
import { BoolOp, xor } from '../../src/core/boolalg';
import { Piecewise as PW, Sym } from '../../src/core/nodes';
import { add, mul, pow } from '../../src/core/ops';
import { finiteSet, Integers, intersection, interval, union } from '../../src/sets/sets';
import * as Q from '../../src/solvers/inequalities';

const [x, y] = symbols('x y');
const xr = new Sym('x', { real: true });
const p = (s: string) => parse(s);
const P = (s: string) => Poly.from(p(s), [x]);
const pw = (...args: string[]) => new PW(args.map((t) => (t === 'True' ? SS.true : t === 'False' ? SS.false : p(t))));
const show = (v: unknown): string =>
  Array.isArray(v) ? `[${v.map((e) => (Array.isArray(e) ? `(${e.map(String).join(', ')})` : String(e))).join(', ')}]` : String(v);

// expected values from SymPy 1.14 (periodicity None is undefined here); comments mark where symjs differs

describe('periodicity', () => {
  it('follows SymPy', () => {
    expect(show(Q.periodicity(p('tan(2*x)'), x))).toBe('pi/2');
    expect(show(Q.periodicity(p('cot(x/3)'), x))).toBe('3*pi');
    expect(show(Q.periodicity(p('Abs(sin(x))'), x))).toBe('pi');
    expect(Q.periodicity(p('Abs(x)'), x)).toBeUndefined();
    expect(show(Q.periodicity(p('exp(sin(x))'), x))).toBe('2*pi');
    expect(show(Q.periodicity(p('exp(I*x)'), x))).toBe('2*pi');
    expect(show(Q.periodicity(p('sin(x)**2'), x))).toBe('2*pi');
    expect(show(Q.periodicity(p('2**sin(x)'), x))).toBe('2*pi');
    expect(show(Q.periodicity(p('sin(x)**cos(x)'), x))).toBe('2*pi');
    expect(Q.periodicity(p('x**x'), x)).toBeUndefined();
    expect(show(Q.periodicity(p('Eq(sin(x), cos(2*x))'), x))).toBe('2*pi');
    expect(show(Q.periodicity(y, x))).toBe('0');
    expect(Q.periodicity(p('sin(x)+sin(sqrt(2)*x)'), x)).toBeUndefined();
    expect(Q.periodicity(p('sin(pi*x)+sin(x)'), x)).toBeUndefined();
    expect(Q.periodicity(x, x)).toBeUndefined();
    expect(Q.periodicity(p('sin(x**2)'), x)).toBeUndefined();
    expect(show(Q.periodicity(p('log(sin(x))'), x))).toBe('2*pi');
    // SymPy returns 2*pi through decompogen, but atan2(sin(x), x) is not periodic
    expect(Q.periodicity(p('atan2(sin(x), x)'), x)).toBeUndefined();
    expect(show(Q.periodicity(p('sin(2*x)+cos(3*x)'), x))).toBe('2*pi');
    expect(show(Q.periodicity(p('sin(pi*x)+cos(2*pi*x)'), x))).toBe('2');
    expect(show(Q.periodicity(p('sin(sin(x))'), x))).toBe('2*pi');
    expect(show(Q.periodicity(p('Abs(sin(sin(x)))'), x))).toBe('pi');
    expect(show(Q.periodicity(p('Abs(cos(2*x))'), x))).toBe('pi/2');
    expect(show(Q.periodicity(p('Abs(tan(x))'), x))).toBe('pi');
    expect(Q.periodicity(p('exp(x+I*x)'), x)).toBeUndefined();
    expect(show(Q.periodicity(p('exp(I*sin(x))'), x))).toBe('2*pi');
    expect(Q.periodicity(p('exp(sqrt(I)*x)'), x)).toBeUndefined();
    expect(show(Q.periodicity(p('Abs(sin(exp(sin(x))))'), x))).toBe('2*pi');
  });
});

describe('solveUnivariateInequality', () => {
  it('follows SymPy', () => {
    expect(show(Q.solveUnivariateInequality(Ne(p('x**2'), 1), x))).toBe('((-oo < x) & (x < -1)) | ((-1 < x) & (x < 1)) | ((1 < x) & (x < oo))');
    expect(show(Q.solveUnivariateInequality(p('Eq(x**2, 1)'), x))).toBe('Eq(x, -1) | Eq(x, 1)');
    expect(show(Q.solveUnivariateInequality(p('x**2 <= 4'), x, { relational: false }))).toBe('Interval(-2, 2)');
    expect(show(Q.solveUnivariateInequality(p('x**2 > 1'), x, { domain: interval(0, 5) }))).toBe('(x <= 5) & (1 < x)');
    expect(show(Q.solveUnivariateInequality(p('(x-1)/(x+2) >= 0'), x))).toBe('((1 <= x) & (x < oo)) | ((-oo < x) & (x < -2))');
    expect(show(Q.solveUnivariateInequality(p('Abs(x-1) < 2'), x))).toBe('(-1 < x) & (x < 3)');
    expect(show(Q.solveUnivariateInequality(p('sin(x) > 0'), x))).toBe('(0 < x) & (x < pi)');
    expect(show(Q.solveUnivariateInequality(p('sqrt(x) > 1'), x))).toBe('(1 < x) & (x < oo)');
    // SymPy raises AttributeError
    expect(() => Q.solveUnivariateInequality(x, x)).toThrow(TypeError);
    expect(show(Q.solveUnivariateInequality(p('(x-1)**2*(x-3) >= 0'), x))).toBe('Eq(x, 1) | ((3 <= x) & (x < oo))');
    expect(show(Q.solveUnivariateInequality(p('log(x) > 0'), x))).toBe('(1 < x) & (x < oo)');
    expect(show(Q.solveUnivariateInequality(p('x - sqrt(2) > 0'), x))).toBe('(x < oo) & (sqrt(2) < x)');
    // SymPy raises NotImplementedError too (infinitely many zeros)
    expect(() => Q.solveUnivariateInequality(Eq(p('sin(x)/x'), 0), x)).toThrow(NotImplementedError);
    expect(() => Q.solveUnivariateInequality(p('x**2 - a > 0'), x)).toThrow(NotImplementedError);
    expect(show(Q.solveUnivariateInequality(Eq(p('sin(x)/(1-cos(x))'), 0), x))).toBe('Eq(x, pi)');
    expect(show(Q.solveUnivariateInequality(p('sin(x)/(1-cos(x)) > 0'), x))).toBe('(0 < x) & (x < pi)');
    expect(show(Q.solveUnivariateInequality(p('x**2+1 > 0'), x))).toBe('(-oo < x) & (x < oo)');
  });
});

describe('solvePolyInequality', () => {
  it('follows SymPy', () => {
    expect(show(Q.solvePolyInequality(P('x**2-1'), '=='))).toBe('[{-1}, {1}]');
    expect(show(Q.solvePolyInequality(P('x**2-1'), '!='))).toBe('[Interval.open(-oo, -1), Interval.open(-1, 1), Interval.open(1, oo)]');
    expect(show(Q.solvePolyInequality(P('x**2-1'), '>'))).toBe('[Interval.open(-oo, -1), Interval.open(1, oo)]');
    expect(show(Q.solvePolyInequality(P('x**2-1'), '<'))).toBe('[Interval.open(-1, 1)]');
    expect(show(Q.solvePolyInequality(P('-x**2+1'), '>='))).toBe('[Interval(-1, 1)]');
    expect(show(Q.solvePolyInequality(P('x**2-1'), '<='))).toBe('[Interval(-1, 1)]');
    expect(show(Q.solvePolyInequality(P('(x-1)**2*(x+2)'), '>'))).toBe('[Interval.open(-2, 1), Interval.open(1, oo)]');
    expect(show(Q.solvePolyInequality(P('(x-1)**2*(x+2)'), '<='))).toBe('[Interval(-oo, -2), {1}]');
    // SymPy prints Interval(-oo, oo), which equals Reals
    expect(show(Q.solvePolyInequality(P('(x-1)**2'), '>='))).toBe('[Reals]');
    expect(show(Q.solvePolyInequality(P('(x-1)**2'), '<'))).toBe('[]');
    expect(show(Q.solvePolyInequality(P('(x-1)**2'), '<='))).toBe('[{1}]');
    expect(show(Q.solvePolyInequality(P('-(x-1)**3*(x+2)'), '<='))).toBe('[Interval(-oo, -2), Interval(1, oo)]');
    expect(show(Q.solvePolyInequality(P('(x-1)**2*(x+2)'), '<'))).toBe('[Interval.open(-oo, -2)]');
  });
});

describe('solveRationalInequalities', () => {
  it('follows SymPy', () => {
    expect(show(Q.solveRationalInequalities([[[[P('x-1'), P('x+1')], '>']]]))).toBe('Union(Interval.open(-oo, -1), Interval.open(1, oo))');
    expect(show(Q.solveRationalInequalities([[[[P('x-1'), P('x+1')], '>'], [[P('x-3'), P('1')], '<']], [[[P('x'), P('1')], '>']], []]))).toBe('Union(Interval.open(-oo, -1), Interval.open(0, oo))');
    expect(show(Q.solveRationalInequalities([[[[P('x**2+1'), P('1')], '<'], [[P('x'), P('1')], '>']]]))).toBe('EmptySet');
    expect(show(Q.solveRationalInequalities([[[[P('x'), P('x**2-1')], '>=']]]))).toBe('Union(Interval.Lopen(-1, 0), Interval.open(1, oo))');
  });
});

describe('reduceInequalities', () => {
  it('follows SymPy', () => {
    expect(show(Q.reduceInequalities(p('x**2 < 4')))).toBe('(-2 < x) & (x < 2)');
    expect(show(Q.reduceInequalities([p('x > 0'), p('x < 3')]))).toBe('(0 < x) & (x < 3)');
    expect(show(Q.reduceInequalities([p('x > 0').subs(x, xr)]))).toBe('0 < x');
    expect(show(Q.reduceInequalities([p('x**2 < 4').subs(x, xr)]))).toBe('(-2 < x) & (x < 2)');
    expect(show(Q.reduceInequalities([p('x**2 > 4').subs(x, xr)]))).toBe('(2 < x) | (x < -2)');
    expect(show(Q.reduceInequalities([p('x**2-4')]))).toBe('Eq(x, -2) | Eq(x, 2)');
    expect(show(Q.reduceInequalities([SS.true, p('x > 1')]))).toBe('(1 < x) & (x < oo)');
    expect(show(Q.reduceInequalities([p('x > 1'), p('y < 2')]))).toBe('(-oo < y) & (1 < x) & (x < oo) & (y < 2)');
    expect(show(Q.reduceInequalities(p('x + a > 1'), [x]))).toBe('x > 1 - a');
    expect(show(Q.reduceInequalities(p('-2*x + a > 1'), [x]))).toBe('x < a/2 - 1/2');
    expect(show(Q.reduceInequalities(p('2*x + a <= 1'), [x]))).toBe('(-oo < x) & (x <= 1/2 - a/2)');
    expect(show(Q.reduceInequalities(p('-x + a >= 1'), [x]))).toBe('(-oo < x) & (x <= a - 1)');
    expect(show(Q.reduceInequalities(p('Eq(2*x + a, 1)'), [x]))).toBe('Eq(x, 1/2 - a/2)');
    expect(() => Q.reduceInequalities(p('x**2 + a > 1'), [x])).toThrow(NotImplementedError);
    expect(show(Q.reduceInequalities(p('a*x > 1'), [x]))).toBe('a*x > 1');
    expect(() => Q.reduceInequalities(p('x + y > 1'), [x, y])).toThrow(NotImplementedError);
    expect(show(Q.reduceInequalities(p('x + a >= 1'), [x]))).toBe('(x < oo) & (x >= 1 - a)');
    expect(show(Q.reduceInequalities(p('x + a < 1'), [x]))).toBe('x < 1 - a');
    expect(show(Q.reduceInequalities(Ne(p('2*x+a'), 1), [x]))).toBe('Ne(x, 1/2 - a/2)');
  });
});

describe('solveset', () => {
  it('follows SymPy', () => {
    expect(show(Q.solveset(Ne(x, 1), x, Reals))).toBe('Union(Interval.open(-oo, 1), Interval.open(1, oo))');
    expect(show(Q.solveset(p('0'), x))).toBe('Complexes');
    expect(show(Q.solveset(p('1'), x))).toBe('EmptySet');
    expect(show(Q.solveset(p('x**2-1'), x, interval(0, 5)))).toBe('{1}');
    expect(show(Q.solveset(p('x**2+1'), x))).toBe('{-I, I}');
    expect(show(Q.solveset(p('(x**2+1)/(x-I)'), x))).toBe('{-I}');
    expect(show(Q.solveset(p('sin(x)'), x))).toBe('Union(ImageSet(Lambda(_n, 2*_n*pi), Integers), ImageSet(Lambda(_n, 2*_n*pi + pi), Integers))');
    expect(show(Q.solveset(p('exp(x)-1'), x))).toBe('ImageSet(Lambda(_n, 2*_n*I*pi), Integers)');
    expect(show(Q.solveset(p('2*exp(3*x+1)-6'), x))).toBe('ImageSet(Lambda(_n, 2*_n*I*pi/3 - 1/3 + log(3)/3), Integers)');
    expect(show(Q.solveset(p('exp(x)'), x))).toBe('EmptySet');
    expect(show(Q.solveset(p('x**2 < 1'), x, interval(0, 5)))).toBe('Interval.Ropen(0, 1)');
    expect(show(Q.solveset(p('tan(x)-1'), x, Reals))).toBe('ImageSet(Lambda(_n, _n*pi + pi/4), Integers)');
    expect(show(Q.solveset(p('cos(x)'), x, Reals))).toBe('Union(ImageSet(Lambda(_n, 2*_n*pi + pi/2), Integers), ImageSet(Lambda(_n, 2*_n*pi + 3*pi/2), Integers))');
    expect(show(Q.solveset(p('sin(x)-2'), x, Reals))).toBe('EmptySet');
    expect(show(Q.solveset(Ne(x, 1), x))).toBe('ConditionSet(x, Ne(x, 1), Complexes)');
    expect(show(Q.solveset(Ne(p('x**2'), 1), x, interval(0, 5)))).toBe('Union(Interval.Ropen(0, 1), Interval.Lopen(1, 5))');
    expect(show(Q.solveset(p('x/(x-1)'), x, Reals))).toBe('{0}');
    expect(show(Q.solveset(p('x/(x-1)'), x))).toBe('{0}');
    expect(show(Q.solveset(p('log(x)-1'), x))).toBe('{E}');
    expect(show(Q.solveset(p('x**2-4'), x, Integers))).toBe('{-2, 2}');
    expect(show(Q.solveset(p('sin(x)+x'), x, Reals))).toBe('ConditionSet(x, Eq(x + sin(x), 0), Reals)');
    // SymPy: ConditionSet(x, Ne(a, 0), Union(...)); symjs keeps the equation (it used to give {0, pi/a})
    expect(show(Q.solveset(p('sin(a*x)'), x, Reals))).toBe('ConditionSet(x, Eq(sin(a*x), 0), Reals)');
    // SymPy: ConditionSet(x, (-1 <= a) & (a <= 1), Union(ImageSet(...asin(a)), ImageSet(...))); symjs keeps the equation
    expect(show(Q.solveset(p('sin(x)-a'), x, Reals))).toBe('ConditionSet(x, Eq(-a + sin(x), 0), Reals)');
    // SymPy finds Union(ImageSet(Lambda(_n, 2*_n*I*pi), Integers), ImageSet(Lambda(_n, I*(2*_n*pi + pi) + log(2)), Integers)); symjs leaves the equation unsolved
    expect(show(Q.solveset(p('exp(x)+exp(2*x)-2'), x))).toBe('ConditionSet(x, Eq(exp(2*x) + exp(x) - 2, 0), Complexes)');
    expect(show(Q.solveset(p('exp(x**2)-1'), x))).toBe('ConditionSet(x, Eq(exp(x**2) - 1, 0), Complexes)');
    expect(show(Q.solveset(p('exp(-x)-3'), x))).toBe('ImageSet(Lambda(_n, 2*_n*I*pi - log(3)), Integers)');
    expect(show(Q.solveset(p('x**2+x*sin(x)-1'), x, Reals))).toBe('ConditionSet(x, Eq(x**2 + x*sin(x) - 1, 0), Reals)');
    // SymPy gives Range(2, oo, 1); integer domains are not supported for inequalities
    expect(() => Q.solveset(p('x > 1'), x, Integers)).toThrow(NotImplementedError);
    expect(show(Q.solveset(p('x > 1'), x))).toBe('ConditionSet(x, x > 1, Complexes)');
  });
});

describe('singularities', () => {
  it('follows SymPy', () => {
    expect(show(Q.singularities(p('log(x)'), x))).toBe('{0}');
    expect(show(Q.singularities(p('atanh(x)'), x))).toBe('{-1, 1}');
    expect(show(Q.singularities(p('tan(x)'), x, Reals))).toBe('Union(ImageSet(Lambda(_n, 2*_n*pi + pi/2), Integers), ImageSet(Lambda(_n, 2*_n*pi + 3*pi/2), Integers))');
    expect(show(Q.singularities(p('cot(x)'), x, Reals))).toBe('Union(ImageSet(Lambda(_n, 2*_n*pi), Integers), ImageSet(Lambda(_n, 2*_n*pi + pi), Integers))');
    expect(show(Q.singularities(p('1/x').subs(x, xr), xr))).toBe('{0}');
    expect(show(Q.singularities(p('1/(x**2-1)'), x, interval(0, 5)))).toBe('{1}');
  });
});

describe('stationaryPoints', () => {
  it('follows SymPy', () => {
    expect(show(Q.stationaryPoints(p('x**3-3*x'), x))).toBe('{-1, 1}');
    expect(show(Q.stationaryPoints(p('x**3-3*x'), x, interval(0, 5)))).toBe('{1}');
  });
});

describe('monotonicity', () => {
  it('follows SymPy', () => {
    expect(Q.isIncreasing(p('x**2'), interval(0, p('oo')))).toBe(true);
    expect(Q.isIncreasing(p('x**2'), Reals)).toBe(false);
    expect(Q.isStrictlyIncreasing(p('x**3'), interval(1, 2))).toBe(true);
    expect(Q.isDecreasing(p('1/x'), interval(1, 2))).toBe(true);
    expect(Q.isStrictlyDecreasing(p('-x'), Reals)).toBe(true);
    // SymPy is_monotonic returns False because the derivative vanishes at 0, but x**3 is monotonic
    expect(Q.isMonotonic(p('x**3'))).toBe(true);
    // SymPy returns False; -x**3 is monotonic (decreasing)
    expect(Q.isMonotonic(p('-x**3'))).toBe(true);
    expect(Q.isMonotonic(p('x**2'))).toBe(false);
    // SymPy returns False; the sign of the derivative y depends on y, so the answer is unknown
    expect(Q.isIncreasing(p('x*y'), Reals, x)).toBeUndefined();
    // SymPy raises NotImplementedError
    expect(() => Q.isIncreasing(p('x*y'), Reals)).toThrow(TypeError);
    expect(Q.isDecreasing(p('x**3'))).toBe(false);
    // SymPy returns False, but x**2 is strictly increasing on [0, oo) (the derivative vanishes only at 0)
    expect(Q.isStrictlyIncreasing(p('x**2'), interval(0, p('oo')))).toBe(true);
    expect(Q.isStrictlyIncreasing(p('1'), interval(0, 1), x)).toBe(false);
    // SymPy returns None; -x**3 is strictly decreasing
    expect(Q.isStrictlyDecreasing(p('-x**3'))).toBe(true);
    expect(Q.isIncreasing(p('x+sin(x)'))).toBe(true);
    // SymPy returns False, but x + sin(x) is strictly increasing (1 + cos(x) vanishes only at isolated points)
    expect(Q.isStrictlyIncreasing(p('x+sin(x)'))).toBe(true);
  });
});

describe('isConvex', () => {
  it('follows SymPy', () => {
    expect(Q.isConvex(p('x**2'), x)).toBe(true);
    expect(Q.isConvex(p('1/x'), x)).toBe(false);
    expect(Q.isConvex(p('1/x'), x, interval(1, 2))).toBe(true);
    expect(Q.isConvex(p('1/x'), x, interval(-1, 2))).toBe(false);
    expect(Q.isConvex(p('-x**2'), x)).toBe(false);
  });
});

describe('maximum and minimum', () => {
  it('follows SymPy', () => {
    expect(show(Q.maximum(p('sin(x)'), x))).toBe('1');
    expect(show(Q.minimum(p('x**2-2*x'), x))).toBe('-1');
    expect(show(Q.maximum(p('x**2'), x, interval(-1, 2)))).toBe('4');
    expect(show(Q.minimum(p('x**3-3*x'), x, interval(-3, 3)))).toBe('-18');
    expect(show(Q.maximum(p('cos(x)**2-sin(x)**2'), x))).toBe('1');
    expect(show(Q.minimum(p('exp(-x**2)'), x))).toBe('0');
    expect(show(Q.maximum(p('exp(x)*sin(x)'), x, interval(0, 4)))).toBe('sqrt(2)*exp(3*pi/4)/2');
    expect(show(Q.maximum(p('x*log(x)'), x))).toBe('oo');
    // SymPy returns a large closed form; symjs cannot solve cos(x) + 3*cos(3*x) = 0
    expect(() => Q.maximum(p('sin(2*x)*cos(x)'), x, interval(0, 4))).toThrow(NotImplementedError);
    // SymPy raises NotImplementedError; x**x is increasing on [1, 4]
    expect(show(Q.maximum(p('x**x'), x, interval(1, 4)))).toBe('256');
    // SymPy raises NotImplementedError; the minimum of x**x is at x = 1/e
    expect(show(Q.minimum(p('x**x'), x, interval(p('1/10'), 4)))).toBe('exp(-exp(-1))');
    expect(() => Q.maximum(p('gamma(x)'), x, interval(1, 4))).toThrow(NotImplementedError);
  });
});

describe('asExprSetPairs', () => {
  it('follows SymPy', () => {
    expect(show(Q.asExprSetPairs(pw('x', 'x<0', 'x**2', 'x<1', '1', 'True')))).toBe('[(x, Interval.open(-oo, 0)), (x**2, Interval.Ropen(0, 1)), (1, Interval(1, oo))]');
    expect(show(Q.asExprSetPairs(pw('x', '(x<0)|(x>5)', 'x**2', '(x>1)&(x<2)', '1', '~(x>3)')))).toBe('[(x, Union(Interval.open(-oo, 0), Interval.open(5, oo))), (x**2, Interval.open(1, 2)), (1, Union(Interval(0, 1), Interval(2, 3)))]');
    expect(show(Q.asExprSetPairs(pw('x', 'x<0', '2', 'False', '3', 'True'), interval(-1, 1)))).toBe('[(x, Interval.Ropen(-1, 0)), (3, Interval(0, 1))]');
    expect(() => Q.asExprSetPairs(pw('x', 'y<0', '1', 'x<0'))).toThrow(NotImplementedError);
    expect(show(Q.asExprSetPairs(pw('x', 'x<-5', '1', '~((x>1)&(x<2))')))).toBe('[(x, Interval.open(-oo, -5)), (1, Union(Interval(-5, 1), Interval(2, oo)))]');
    expect(show(Q.asExprSetPairs(new PW([x, p('x<-5'), SS.One, new BoolOp('Not', [p('(x>1)&(x<2)')])])))).toBe('[(x, Interval.open(-oo, -5)), (1, Union(Interval(-5, 1), Interval(2, oo)))]');
  });
});

describe('piecewiseExclusive', () => {
  it('follows SymPy', () => {
    expect(show(Q.piecewiseExclusive(pw('x', 'x<0', 'x**2', 'x<1')))).toBe('Piecewise((x, x < 0), (x**2, (x >= 0) & (x < 1)), (nan, x >= 1))');
    expect(show(Q.piecewiseExclusive(pw('x', 'x<0', 'x**2', 'x<1'), { skipNan: true }))).toBe('Piecewise((x, x < 0), (x**2, (x >= 0) & (x < 1)))');
    // SymPy leaves the conditions unsimplified and gives no piece at x = 0 and x = 1, where the original Piecewise gives 6
    expect(show(Q.piecewiseExclusive(pw('x', 'x<0', 'x**2', '(x>1)&(x<3)', '5', '(x>5)|(x<-3)', '6', '~(x>10)', '7', 'False', '8', 'True')))).toBe('Piecewise((x, x < 0), (x**2, (x > 1) & (x < 3)), (5, x > 5), (6, ((x >= 0) & (x <= 1)) | ((x >= 3) & (x <= 5))))');
    expect(show(Q.piecewiseExclusive(pw('x', 'x<0', '1', 'Eq(x, 0)', '2', 'x>0')))).toBe('Piecewise((x, x < 0), (1, Eq(x, 0)), (2, x > 0))');
    // equivalent to SymPy (1, (x >= 0) & ((x > 2) | (x < -1)))
    expect(show(Q.piecewiseExclusive(pw('x', 'x<0', '1', '(x<-1)|(x>2)', '2', 'x>1')))).toBe('Piecewise((x, x < 0), (1, x > 2), (2, (x <= 2) & (x > 1)), (nan, (x >= 0) & (x <= 1)))');
    // SymPy also handles several symbols; symjs supports univariate conditions only
    expect(() => Q.piecewiseExclusive(pw('x', 'y<0', '1', 'x<0'))).toThrow(NotImplementedError);
    expect(show(Q.piecewiseExclusive(pw('x', '(x<0)&(x>1)', '1', 'True')))).toBe('1');
    // equivalent to SymPy (1, (x >= -5) & Eq(x**2, 1)), (nan, (x >= -5) & Ne(x**2, 1))
    expect(show(Q.piecewiseExclusive(pw('x', 'x<-5', '1', 'Eq(x**2, 1)')))).toBe('Piecewise((x, x < -5), (1, Eq(x, -1) | Eq(x, 1)), (nan, (x > 1) | ((x >= -5) & (x < -1)) | ((x > -1) & (x < 1))))');
    expect(show(Q.piecewiseExclusive(pw('x', 'x<0', '1', 'x>=0')))).toBe('Piecewise((x, x < 0), (1, x >= 0))');
    // SymPy gives (1, (x >= 2) | ((x > -5) & (x < 1))) and nan on [1, 2), but the condition Not(1 < x < 2) holds at x = -5 and x = 1
    expect(show(Q.piecewiseExclusive(new PW([x, p('x<-5'), SS.One, new BoolOp('Not', [p('(x>1)&(x<2)')])])))).toBe('Piecewise((x, x < -5), (1, (x >= 2) | ((x >= -5) & (x <= 1))), (nan, (x > 1) & (x < 2)))');
  });
});

describe('notEmptyIn', () => {
  it('follows SymPy', () => {
    expect(show(Q.notEmptyIn(intersection(finiteSet(p('x/2')), interval(0, 1)), x))).toBe('Interval(0, 2)');
    expect(show(Q.notEmptyIn(intersection(finiteSet(x, p('x**2')), interval(1, p('oo'))), x))).toBe('Union(Interval(-oo, -1), Interval(1, oo))');
    expect(show(Q.notEmptyIn(intersection(finiteSet(x), interval(p('-oo'), 2, true, true)), x))).toBe('Interval.open(-oo, 2)');
    expect(show(Q.notEmptyIn(intersection(finiteSet(x), interval(0, 2, true, false)), x))).toBe('Interval.Lopen(0, 2)');
    // SymPy raises ValueError
    expect(() => Q.notEmptyIn(interval(0, 1), x)).toThrow(NotImplementedError);
  });
});

describe('asSet', () => {
  it('follows SymPy', () => {
    expect(show(Q.asSet(p('x > 0')))).toBe('Interval.open(0, oo)');
    expect(show(Q.asSet(p('(x > 0) & (x < 3)')))).toBe('Interval.open(0, 3)');
    expect(show(Q.asSet(p('(x < 0) | (x > 3)')))).toBe('Union(Interval.open(-oo, 0), Interval.open(3, oo))');
    expect(show(Q.asSet(p('~(x > 0)')))).toBe('Interval(-oo, 0)');
    expect(show(Q.asSet(true))).toBe('UniversalSet');
    expect(show(Q.asSet(false))).toBe('EmptySet');
    expect(() => Q.asSet(p('x + y > 0'))).toThrow(NotImplementedError);
    expect(show(Q.asSet(p('Eq(x**2, 1)')))).toBe('{-1, 1}');
    // SymPy raises AttributeError
    expect(() => Q.asSet(xor(p('x>0'), p('x<1')))).toThrow(NotImplementedError);
    // SymPy And(True, x > 0, evaluate=False).as_set()
    expect(show(Q.asSet(new BoolOp('And', [SS.true, p('x>0')])))).toBe('Interval.open(0, oo)');
    // SymPy Not(And(x > 0, x < 1)).as_set()
    expect(show(Q.asSet(new BoolOp('Not', [p('(x>0)&(x<1)')])))).toBe('Union(Interval(-oo, 0), Interval(1, oo))');
    // SymPy x.as_set() gives UniversalSet; symjs accepts relations and boolean combinations only
    expect(() => Q.asSet(x)).toThrow(NotImplementedError);
  });
});

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

describe('solveset with ImageSet and ConditionSet', () => {
  it('periodic, complex exponential and unsolvable equations', () => {
    expect(String(solveset(sin(x), x, Reals))).toBe('Union(ImageSet(Lambda(_n, 2*_n*pi), Integers), ImageSet(Lambda(_n, 2*_n*pi + pi), Integers))');
    expect(String(solveset(parse('sin(x) + cos(x)'), x, Reals))).toBe('Union(ImageSet(Lambda(_n, 2*_n*pi + 3*pi/4), Integers), ImageSet(Lambda(_n, 2*_n*pi + 7*pi/4), Integers))');
    expect(String(solveset(parse('exp(x) + 1'), x))).toBe('ImageSet(Lambda(_n, I*(2*_n*pi + pi)), Integers)');
    expect(String(solveset(parse('cos(x) - 2'), x, Reals))).toBe('EmptySet');
    expect(String(solveset(parse('x**2 + x*sin(x) - 1'), x, Reals))).toBe('ConditionSet(x, Eq(x**2 + x*sin(x) - 1, 0), Reals)');
  });
});

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/solvers/inequalities.ts: inequality solving, solveset helpers, singularities, monotonicity and extrema; expected values from SymPy 1.14.

import { describe, expect, it, vi } from 'vitest';
import * as sj from '../../src';
import { Abs, And, Eq, Ge, Gt, Lt, Ne, Or, exp, NotImplementedError, Rational, erf, erfc, erfcinv, erfinv, parse, Poly, Reals, S as SS, sin, solveset, symbols } from '../../src';
import type { Expr } from '../../src';
import { BoolOp, xor } from '../../src/core/boolalg';
import { Piecewise as PW, Sym } from '../../src/core/nodes';
import { add, mul, pow } from '../../src/core/ops';
import { Complexes, ConditionSet, finiteSet, Integers, intersection, interval, union } from '../../src/sets/sets';
import * as Q from '../../src/solvers/inequalities';
import * as AlgebraicSolver from '../../src/solvers/solve';

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
    // x/Abs(x) is undefined at 0 (SymPy (0 <= x) & (x < oo) wrongly includes 0, where x/Abs(x) + 1 is nan)
    expect(show(Q.reduceInequalities(p('x/Abs(x) + 1 > 0'), [x]))).toBe('(0 < x) & (x < oo)');
    expect(show(Q.reduceInequalities([p('x > 0'), p('x < 3')]))).toBe('(0 < x) & (x < 3)');
    expect(show(Q.reduceInequalities([p('x > 0').subs(x, xr)]))).toBe('0 < x');
    expect(show(Q.reduceInequalities([p('x**2 < 4').subs(x, xr)]))).toBe('(-2 < x) & (x < 2)');
    expect(show(Q.reduceInequalities([p('x**2 > 4').subs(x, xr)]))).toBe('(2 < x) | (x < -2)');
    expect(show(Q.reduceInequalities([p('x**2-4')]))).toBe('Eq(x, -2) | Eq(x, 2)');
    expect(show(Q.reduceInequalities([SS.true, p('x > 1')]))).toBe('(1 < x) & (x < oo)');
    expect(show(Q.reduceInequalities([p('x > 1'), p('y < 2')]))).toBe('(-oo < y) & (1 < x) & (x < oo) & (y < 2)');
    expect(show(Q.reduceInequalities([p('x + y - 3'), p('x > 3')], [x]))).toBe('(3 < x) & (x < oo) & Eq(x, 3 - y)');
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

describe('solveset with parameters and inverse functions (sympy.stats needs both)', () => {
  const z = new Sym('z', { real: true });
  const w = new Sym('w');
  const zp = new Sym('zp', { positive: true });
  const div = (a: Expr, b: Expr): Expr => mul(a, pow(b, -1));
  it('solves for x when the zeros have parameters', () => {
    // SymPy prints z/2 + 1/2
    expect(String(Q.solveset(add(mul(2, xr), mul(-1, z), -1), xr, Reals))).toBe('{(z + 1)/2}');
    expect(String(Q.solveset(add(mul(2, xr), mul(-1, w)), xr, Reals))).toBe('Intersection({w/2}, Reals)');
    expect(String(Q.solveset(add(pow(xr, 2), mul(-1, zp)), xr, Reals))).toBe('{-sqrt(zp), sqrt(zp)}');
    expect(String(Q.solveset(add(pow(xr, 2), zp), xr, Reals))).toBe('EmptySet');
    expect(String(Q.solveset(div(add(xr, mul(-1, z)), add(xr, mul(-1, w))), xr, Reals))).toBe('Complement({z}, Intersection({w}, Reals))');
    expect(String(Q.solveset(add(mul(2, xr), mul(-1, z)), xr, interval(0, 1)))).toBe('Intersection({z/2}, Interval(0, 1))');
  });
  it('decided conditions and comparisons with oo', () => {
    const x0 = new Sym('x');
    expect(String(Q.solveset(SS.true, xr, Reals))).toBe('Reals');
    expect(String(Q.solveset(SS.false, xr, Reals))).toBe('EmptySet');
    expect(String(Q.solveset(Lt(xr, SS.Infinity), xr, Reals))).toBe('Reals');
    // x is not known to be real (SymPy decides x < oo only for a real x): the inequality over the reals
    expect(String(Q.solveset(Lt(x0, SS.Infinity), x0, Reals))).toBe('Reals');
    expect(String(Q.solveset(Gt(x0, SS.Infinity), x0, Reals))).toBe('EmptySet');
    expect(String(Q.solveset(Ge(add(x0, 1), SS.NegativeInfinity), x0, Reals))).toBe('Reals');
    expect(String(Q.solveset(Eq(add(x0, SS.Infinity), 0), x0, Reals))).toBe('EmptySet');
  });
  it('solves each piece of a Piecewise where its condition holds first (SymPy _solveset)', () => {
    const half = Rational.of(1, 2);
    expect(String(Q.solveset(new PW([add(half, mul(-1, exp(mul(-2, xr)))), Ge(xr, 0), mul(-1, half), SS.true]), xr, interval(0, SS.Infinity)))).toBe('{log(2)/2}');
    expect(String(Q.solveset(new PW([add(xr, -1), Gt(xr, 0), add(xr, 1), SS.true]), xr, Reals))).toBe('{-1, 1}');
    expect(String(Q.solveset(new PW([add(xr, -1), And(Gt(xr, 0), Lt(xr, 5)), add(xr, 1), Or(Lt(xr, -3), Gt(xr, 7)), SS.Zero, SS.true]), xr, Reals))).toBe(
      'Union({1}, Interval(-3, 0), Interval(5, 7))',
    );
    expect(String(Q.solveset(new PW([add(xr, -1), Gt(xr, 0)]), xr, Reals))).toBe('{1}');
    const positive = new Sym('y', { positive: true });
    const absolute = new PW([add(x, -3), Ge(x, 3), add(3, mul(-1, x)), SS.true]);
    expect(String(Q.solveset(add(absolute, mul(-1, positive)), x, Reals))).toBe('{3 - y, y + 3}');
    expect(String(Q.solveset(p('Piecewise((0, Eq(x, pi)), ((x - pi)/sin(x), True))'), x, Complexes))).toBe('{pi}');
    // SymPy raises a ValueError over the complex numbers
    expect(String(Q.solveset(new PW([add(xr, -1), Gt(xr, 0), add(xr, 1), SS.true]), xr))).toBe('ConditionSet(x, Eq(Piecewise((x - 1, x > 0), (x + 1, True)), 0), Complexes)');
  });
  it('inverts erf, erfc, erfinv and erfcinv (SymPy _invert_real)', () => {
    expect(String(Q.solveset(add(mul(Rational.of(1, 3), erf(add(xr, -2))), Rational.of(1, 6)), xr, Reals))).toBe('{erfinv(-1/2) + 2}');
    expect(String(Q.solveset(erfc(xr), xr, Reals))).toBe('EmptySet');
    expect(String(Q.solveset(add(erfinv(xr), -1), xr, Reals))).toBe('{erf(1)}');
    expect(String(Q.solveset(erf(xr), xr, interval(0, 1)))).toBe('{0}');
    expect(String(Q.solveset(add(erfcinv(xr), -1), xr, Reals))).toBe('{erfc(1)}');
    // two terms with x, or x outside the function: not inverted (SymPy solves x*erf(x) = 0 to {0})
    expect(String(Q.solveset(add(erf(xr), erf(mul(2, xr))), xr, Reals))).toBe('ConditionSet(x, Eq(erf(x) + erf(2*x), 0), Reals)');
    expect(String(Q.solveset(mul(xr, erf(xr)), xr, Reals))).toBe('{0}');
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
    expect(show(Q.solveset(p('exp(2*x) - 2*exp(x) + 1'), x))).toBe('ImageSet(Lambda(_n, 2*_n*I*pi), Integers)');
    expect(show(Q.solveset(p('exp(x)+exp(2*x)-2'), x))).toBe('Union(ImageSet(Lambda(_n, 2*_n*I*pi), Integers), ImageSet(Lambda(_n, I*(2*_n*pi + pi) + log(2)), Integers))');
    expect(show(Q.solveset(p('exp(x**2)-1'), x))).toBe('ConditionSet(x, Eq(exp(x**2) - 1, 0), Complexes)');
    expect(show(Q.solveset(p('exp(-x)-3'), x))).toBe('ImageSet(Lambda(_n, 2*_n*I*pi - log(3)), Integers)');
    expect(show(Q.solveset(p('x**2+x*sin(x)-1'), x, Reals))).toBe('ConditionSet(x, Eq(x**2 + x*sin(x) - 1, 0), Reals)');
    expect(show(Q.solveset(p('x > 1'), x, Integers))).toBe('Range(2, oo, 1)');
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
    expect(() => Q.isIncreasing(p('x*y'), Reals)).toThrow('The function has not yet been implemented for all multivariate expressions.');
    // a constant (SymPy True)
    expect(Q.isIncreasing(p('2*pi'), Reals)).toBe(true);
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
    // several symbols: the conditions And-ed with the negations of the earlier ones (SymPy)
    expect(show(Q.piecewiseExclusive(pw('x', 'y<0', '1', 'x<0')))).toBe('Piecewise((x, y < 0), (1, (y >= 0) & (x < 0)), (nan, (x >= 0) & (y >= 0)))');
    expect(show(Q.piecewiseExclusive(pw('x', 'x<y', 'y', 'True')))).toBe('Piecewise((x, x < y), (y, x >= y))');
    expect(show(Q.piecewiseExclusive(pw('1', 'x<y', '2', 'x>2', '3', 'True')))).toBe('Piecewise((1, x < y), (2, (x >= y) & (x > 2)), (3, (x >= y) & (x <= 2)))');
    expect(show(Q.piecewiseExclusive(pw('1', '(x<y)&(y>0)', '2', 'True')))).toBe('Piecewise((1, (y > 0) & (x < y)), (2, (x >= y) | (y <= 0)))');
    expect(show(Q.piecewiseExclusive(pw('x', 'y<0', '1', 'x<0'), { skipNan: true }))).toBe('Piecewise((x, y < 0), (1, (y >= 0) & (x < 0)))');
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
    expect(String(Q.solveset(p('x - y'), x, interval(0, 1)))).toBe('Intersection({y}, Interval(0, 1))');
    expect(String(Q.solveset(p('x - 2'), x, interval(0, y)))).toBe('Intersection({2}, Interval(0, y))');
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
    // Constant pieces retain denominator exclusions and reject nonreal ordering.
    const sgn = add(mul(xr, pow(Abs(xr), -1)), 1);
    expect(String(Q.solveUnivariateInequality(Eq(sgn, 0), xr, { relational: false }))).toBe('Interval.open(-oo, 0)');
    expect(() => Q.solveUnivariateInequality(Gt(add(mul(xr, pow(Abs(xr), -1)), SS.I), 0), xr, { relational: false })).toThrow(TypeError);
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
    // SymPy False (x**3 - x turns at x = +-sqrt(3)/3)
    expect(Q.isMonotonic(p('x**3 - x'))).toBe(false);
    expect(Q.isDecreasing(p('x**3 - x'))).toBe(false);
    // SymPy False; neither increasing nor decreasing is decided on a symbolic point here
    expect(Q.isMonotonic(p('x**3 - x'), finiteSet(y))).toBe(undefined);
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

describe('solveset over the reals with a parameter (SymPy _invert_real)', () => {
  const R = (s: string, locals: Record<string, Expr> = {}) => show(Q.solveset(parse(s, { locals }), x, Reals));
  it('even roots: an ImageSet over the nonnegative values of the parameter', () => {
    expect(R('x**2 - p')).toBe('Intersection({-sqrt(p), sqrt(p)}, Reals)');
    expect(R('sqrt(x) - y')).toBe('ImageSet(Lambda(x, x**2), Intersection({y}, Interval(0, oo)))');
    expect(R('sqrt(x) + y')).toBe('ImageSet(Lambda(x, x**2), Intersection({-y}, Interval(0, oo)))');
    expect(R('2*sqrt(x) + y - 1')).toBe('ImageSet(Lambda(x, x**2), Intersection({1/2 - y/2}, Interval(0, oo)))');
    expect(R('x**(3/2) - y')).toBe('ImageSet(Lambda(x, x**(2/3)), Intersection({y}, Interval(0, oo)))');
    expect(R('x**(1/4) - y')).toBe('ImageSet(Lambda(x, x**4), Intersection({y}, Interval(0, oo)))');
    expect(R('sqrt(x + 1) - y')).toBe('ImageSet(Lambda(x, x**2 - 1), Intersection({y}, Interval(0, oo)))');
    expect(R('sqrt(x**2 + 1) - y')).toBe(
      'Union(ImageSet(Lambda(x, -sqrt(x**2 - 1)), Intersection({y}, Interval(0, oo))), ImageSet(Lambda(x, sqrt(x**2 - 1)), Intersection({y}, Interval(0, oo))))',
    );
    const yp = new Sym('yp', { positive: true });
    expect(R('sqrt(x) - yp', { yp })).toBe('{yp**2}');
    expect(R('sqrt(x) + yp', { yp })).toBe('EmptySet');
    expect(R('sqrt(x) - 2')).toBe('{4}');
    expect(R('sqrt(2*x + 1) - y')).toBe('ImageSet(Lambda(x, x**2/2 - 1/2), Intersection({y}, Interval(0, oo)))');
    expect(R('sqrt(x**3 + 1) - y')).toBe('ImageSet(Lambda(x, Abs(x**2 - 1)**(1/3)*sign(x**2 - 1)), Intersection({y}, Interval(0, oo)))');
    expect(R('sqrt(x**2 + x) - y')).toBe('ConditionSet(x, Eq(-y + sqrt(x**2 + x), 0), Reals)');
    // SymPy: ConditionSet(x, Contains(y, Interval(0, oo)), {-y, y})
    expect(R('sqrt(x**2) - y')).toBe('Intersection({-y, y}, Reals)');
  });
  it('odd roots: real_root', () => {
    expect(R('x**3 - p')).toBe('Intersection({Abs(p)**(1/3)*sign(p)}, Reals)');
    expect(R('x**3 + p')).toBe('Intersection({-Abs(p)**(1/3)*sign(p)}, Reals)');
    expect(R('x**5 - p')).toBe('Intersection({Abs(p)**(1/5)*sign(p)}, Reals)');
    expect(R('2*x**3 - p')).toBe('Intersection({2**(2/3)*Abs(p)**(1/3)*sign(p)/2}, Reals)');
    expect(R('(x - 1)**3 - p')).toBe('Intersection({Abs(p)**(1/3)*sign(p) + 1}, Reals)');
    expect(R('x**3 - yr', { yr: new Sym('yr', { real: true }) })).toBe('{Abs(yr)**(1/3)*sign(yr)}');
    expect(R('x**4 - p')).toBe('Intersection({-p**(1/4), p**(1/4)}, Reals)');
    expect(R('x**(1/3) - y')).toBe('Intersection({y**3}, Reals)');
    expect(R('x**3 - 8')).toBe('{2}');
  });
});

describe('reduceAbsInequality and reduceAbsInequalities (SymPy)', () => {
  const E = parse;
  it('reduceAbsInequality', () => {
    expect(String(Q.reduceAbsInequality(E('Abs(x - 5) - 3'), '<', x))).toBe('(2 < x) & (x < 8)');
    expect(String(Q.reduceAbsInequality(E('Abs(x - 5) - 3'), '>=', x))).toBe('((8 <= x) & (x < oo)) | ((-oo < x) & (x <= 2))');
    expect(String(Q.reduceAbsInequality(E('Abs(Abs(x - 1) - 2) - 1'), '<', x))).toBe('((-2 < x) & (x < 0)) | ((2 < x) & (x < 4))');
    expect(String(Q.reduceAbsInequality(E('Abs(x)**2 - 4'), '<=', x))).toBe('(-2 <= x) & (x <= 2)');
    expect(String(Q.reduceAbsInequality(E('Abs(x)*Abs(x - 2) - 1'), '==', x))).toBe('Eq(x, 1) | Eq(x, 1 + sqrt(2)) | Eq(x, 1 - sqrt(2))');
  });
  it('reduceAbsInequalities', () => {
    expect(String(Q.reduceAbsInequalities([[E('Abs(3*x - 5) - 7'), '<'], [E('Abs(x + 25) - 13'), '>']], x))).toBe('(-2/3 < x) & (x < 4) & (((-oo < x) & (x < -38)) | ((-12 < x) & (x < oo)))');
    expect(String(Q.reduceAbsInequalities([[E('Abs(x - 4) + Abs(3*x - 5) - 7'), '<']], x))).toBe('(1/2 < x) & (x < 4)');
  });
  it('rejects other relations and non-integer powers', () => {
    expect(() => Q.reduceAbsInequality(E('Abs(x)'), '<>', x)).toThrow("Invalid relational operator symbol: '<>'");
    expect(() => Q.reduceAbsInequality(E('sqrt(Abs(x)) - 1'), '<', x)).toThrow('Only Integer Powers are allowed on Abs.');
  });
});

it('reduces OR groups of rational inequalities in all input forms', () => {
  expect(String(Q.reduceRationalInequalities([[p('x**2 <= 0')]], x))).toBe('Eq(x, 0)');
  expect(String(Q.reduceRationalInequalities([[[add(xr, 2), '>']]], xr))).toBe('-2 < x');
  expect(String(Q.reduceRationalInequalities([[add(x, 2)]], x))).toBe('Eq(x, -2)');
  expect(String(Q.reduceRationalInequalities([[p('x + 2 > 0')]], x, false))).toBe('Interval.open(-2, oo)');
  expect(() => Q.reduceRationalInequalities([[[x, 'bad']]], x)).toThrow(TypeError);
  expect(String(Q.reduceRationalInequalities([], x))).toBe('False');
  expect(String(Q.solvePolyInequalities([[P('x**2 - 3'), '>'], [P('1 - x**2'), '>']]))).toBe('Union(Interval.open(-oo, -sqrt(3)), Interval.open(-1, 1), Interval.open(sqrt(3), oo))');
});

describe('real roots with parameters of unknown realness (SymPy _invert_real)', () => {
  it('intersects a root with an unknown imaginary part with the reals', async () => {
    const sj = await import('../../src');
    const x = sj.symbol('x', { real: true });
    const y = sj.symbol('y');
    const a = sj.symbol('a', { real: true });
    expect(sj.sstr(solveset(sj.sub(sj.pow(sj.add(x, y), 3), a), x, Reals))).toBe('Intersection({-y + Abs(a)**(1/3)*sign(a)}, Reals)');
  });
});

it('rejects increasing behavior on a translated interval of positive width', () => {
  const a = new Sym('a', { real: true });
  expect(Q.isIncreasing(mul(-1, xr), interval(a, add(a, 1)), xr)).toBe(false);
});


it('solves constant polynomial signs, including the zero polynomial', () => {
  for (const [poly, rel, expected] of [
    ['0', '==', '[Reals]'], ['1', '==', '[EmptySet]'], ['0', '!=', '[EmptySet]'],
    ['2', '>', '[Reals]'], ['-2', '>=', '[EmptySet]'], ['0', '<=', '[Reals]'],
  ] as const) expect(show(Q.solvePolyInequality(P(poly), rel))).toBe(expected);
  expect(() => Q.solvePolyInequality(P('1'), '?')).toThrow(TypeError);
  expect(() => Q.solvePolyInequality(P('a'), '>')).toThrow(NotImplementedError);
});

it('restricts inequalities to finite, empty and disconnected real domains', () => {
  expect(show(Q.solveUnivariateInequality(p('x**2 > 1'), x, { relational: false, domain: union(interval(-3, -2), interval(0, 3)) }))).toBe('Union(Interval(-3, -2), Interval.Lopen(1, 3))');
  expect(show(Q.solveUnivariateInequality(p('1/x > 0'), x, { relational: false, domain: finiteSet(-1, 0, 1, 2) }))).toBe('{1, 2}');
  expect(show(Q.solveUnivariateInequality(Eq(x, 0), x, { relational: false, domain: finiteSet(0, 1) }))).toBe('{0}');
  expect(show(Q.solveUnivariateInequality(p('x < 1'), x, { relational: false, domain: finiteSet() }))).toBe('EmptySet');
});

it('solves real exponential equations by logarithms and common generators', () => {
  for (const [expression, expected] of [
    ['2**x-4', '{2}'], ['2**x+4**x', 'EmptySet'], ['2**x-4**x+12', '{2}'],
    ['2**x+4**x+8**x-84', '{2}'], ['(-2)**x-4', '{2}'], ['(-3)**x-27', 'EmptySet'],
    ['(-5)**(x+1)-625', '{3}'], ['(-2)**x', 'EmptySet'],
    ['2**x*x-1', '{LambertW(log(2))/log(2)}'],
  ] as const) expect(show(Q.solveset(p(expression), x, Reals))).toBe(expected);
  expect(show(Q.solveset(p('Abs(x)-2'), x, Reals))).toBe('{-2, 2}');
  expect(show(Q.solveset(p('Abs(x+3)-2*Abs(x-3)'), x, Reals))).toBe('{1, 9}');
});

it('keeps unresolved real exponential equations explicit and checks domain types', () => {
  expect(() => Q.solveUnivariateInequality(p('x > 0'), x, { domain: Complexes })).toThrow(NotImplementedError);
  expect(show(Q.solveset(p('2**x'), x, Reals))).toBe('EmptySet');
  expect(show(Q.solveset(p('3*(-2)**x'), x, Reals))).toBe('EmptySet');
  expect(show(Q.solveset(p('(-2)**x+(-2)**(x+1)'), x, Reals))).toBe('EmptySet');
  for (const expression of ['(-2)**x-y', '(-2)**x-1/2', '2**(I*x)-1', '2**x+3**x+1']) {
    expect(Q.solveset(p(expression), x, Reals)).toBeInstanceOf(ConditionSet);
  }
});

it('preserves decided inequalities in relational and set forms', () => {
  expect(Q.solveUnivariateInequality(SS.true, x)).toBe(SS.true);
  expect(Q.solveUnivariateInequality(SS.false, x)).toBe(SS.false);
  expect(Q.solveUnivariateInequality(SS.true, x, { relational: false })).toBe(Reals);
  const domain = interval(0, 1);
  expect(Q.solveUnivariateInequality(SS.true, x, { relational: false, domain })).toBe(domain);
  expect(Q.solveUnivariateInequality(SS.false, x, { relational: false })).toBe(finiteSet());
});

it('handles modulo periods, unsupported variables and singular powers', () => {
  expect(String(Q.periodicity(sj.Mod(x, 4), x))).toBe('4');
  expect(String(Q.periodicity(sj.Mod(sj.sin(x), 4), x))).toBe('2*pi');
  expect(Q.periodicity(new sj.DefinedFunctionCall('Mod', [p('x**2+1'), x], { nargs: 2 }), x)).toBeUndefined();
  expect(Q.periodicity(new sj.DefinedFunctionCall('Mod', [p('x**2'), sj.Rational.of(4)], { nargs: 2 }), x)).toBeUndefined();
  // @ts-expect-error Invalid scalar variable.
  expect(() => Q.periodicity(x, sj.S.One)).toThrow(NotImplementedError);
  expect(() => Q.singularities(sj.pow(x, sj.S.NegativeInfinity), x)).toThrow(NotImplementedError);
  // @ts-expect-error Invalid scalar variable.
  expect(() => Q.maximum(x, sj.S.One)).toThrow(RangeError);
  expect(() => Q.maximum(x, x, sj.EmptySet)).toThrow(RangeError);
});

it('finds extrema of absolute values including a zero crossing', () => {
  expect(String(Q.minimum(p('Abs(x)'), x, interval(-1, 2)))).toBe('0');
  expect(String(Q.minimum(p('Abs(x)'), x, interval(1, 2)))).toBe('1');
  expect(String(Q.minimum(p('Abs(x)'), x, interval(-2, -1)))).toBe('1');
});

it('finds nonempty domains for finite sets, empty sets and unions', () => {
  expect(Q.notEmptyIn(sj.EmptySet, x)).toBe(sj.EmptySet);
  expect(Q.notEmptyIn(sj.finiteSet(x), x)).toBe(sj.Reals);
  expect(Q.notEmptyIn(sj.union(sj.finiteSet(x), sj.finiteSet(2)), x)).toBe(sj.Reals);
  expect(() => Q.notEmptyIn(sj.finiteSet(x), x, x)).toThrow(NotImplementedError);
  // @ts-expect-error Invalid scalar variable.
  expect(() => Q.notEmptyIn(sj.finiteSet(x), sj.S.One)).toThrow(RangeError);
  expect(() => Q.notEmptyIn(new sj.SetOp('Intersection', [sj.finiteSet(x), sj.Integers]), x)).toThrow(NotImplementedError);
  expect(Q.notEmptyIn(new sj.SetOp('Intersection', [sj.finiteSet(0), interval(1, 2)]), x)).toBe(sj.EmptySet);
  expect(Q.notEmptyIn(new sj.SetOp('Union', [sj.finiteSet(x), sj.finiteSet(2)]), x)).toBe(sj.Reals);
});

it('leaves absolute-value extrema with undecidable zero crossings unsupported', () => {
  expect(() => Q.minimum(p('Abs(x*y)'), x, interval(1, 2))).toThrow(NotImplementedError);
});

it('inverts real hyperbolic functions within their ranges', () => {
  for (const source of ['cosh(x)', 'cosh(x)+2', 'tanh(x)-1', 'tanh(x)+1', 'coth(x)', 'sech(x)-2', 'sech(x)', 'csch(x)']) {
    expect(solveset(p(source), x, Reals), source).toBe(sj.EmptySet);
  }
  for (const [source, expected] of [
    ['sinh(x)-2', '{asinh(2)}'], ['cosh(x)-2', '{-acosh(2), acosh(2)}'],
    ['tanh(x)-1/2', '{atanh(1/2)}'], ['coth(x)-2', '{acoth(2)}'],
    ['sech(x)-1/2', '{-asech(1/2), asech(1/2)}'], ['csch(x)-3', '{acsch(3)}'],
    ['coth(log(x))+2', '{exp(-acoth(2))}'], ['coth(exp(x))+2', 'EmptySet'],
  ] as const) expect(String(solveset(p(source), x, Reals)), source).toBe(expected);
  expect(String(solveset(p('tanh(x)-y'), x, Reals))).toBe('Intersection({log(y/(1 - y) + 1/(1 - y))/2}, Reals)');
});

it('tracks periods of real parts and nonempty images over disconnected targets', () => {
  expect(Q.periodicity(new sj.Fn('re', [x]), x)).toBeUndefined();
  expect(Q.periodicity(new sj.Fn('re', [y]), x)).toBe(SS.Zero);
  const targets = new sj.SetOp('Union', [interval(-2, -1), interval(1, 2)]);
  const input = new sj.SetOp('Intersection', [finiteSet(x), targets]);
  expect(String(Q.notEmptyIn(input, x))).toBe('Union(Interval(-2, -1), Interval(1, 2))');
});

it('restricts complex-coefficient inequalities to real-valued points', () => {
  for (const [expression, expected] of [
    ['(x+I)*(x+2*I) < 0', 'Eq(x, 0)'],
    ['((x-1)*(x-2)+I)*((x-1)*(x-2)+2*I) < 0', 'Eq(x, 1) | Eq(x, 2)'],
    ['(((x-1)*(x-2)+I)*((x-1)*(x-2)+2*I))/(x-2) > 0', 'Eq(x, 1)'],
  ] as const) expect(String(Q.solveUnivariateInequality(p(expression), x))).toBe(expected);
  expect(() => Q.solveUnivariateInequality(p('x-I < 0'), x)).toThrow(TypeError);
  const lhs = new sj.Mul([add(x, -2), add(x, -1), new sj.Pow(add(x, -1), SS.NegOne)]);
  expect(String(Q.solveUnivariateInequality(sj.Relational(lhs, 0, '<', { evaluate: false }), x, { relational: false }))).toBe('Union(Interval.open(-oo, 1), Interval.open(1, 2))');
});

it('splits reciprocal trigonometric inequalities at their poles', () => {
  expect(String(Q.solveUnivariateInequality(p('tan(x) < 1'), x, { relational: false }))).toBe('Union(Interval.Ropen(0, pi/4), Interval.open(pi/2, pi))');
  for (const source of ['cot(x)>0', 'sec(x)>0', 'csc(x)>0']) {
    expect(String(Q.solveUnivariateInequality(p(source), x, { relational: false }))).not.toContain('ConditionSet');
  }
  const realProduct = new sj.Mul([SS.I, SS.I, x]);
  expect(String(Q.solveUnivariateInequality(sj.Relational(realProduct, 0, '>', { evaluate: false }), x))).toBe('(-oo < x) & (x < 0)');
});

it('preserves both sides of integer relationals and restricts finite integer domains', () => {
  const inverse = pow(x, -1);
  expect(String(solveset(sj.Relational(add(x, inverse), add(-2, inverse), '>', { evaluate: false }), x, Integers))).toBe('Union(Range(-1, 0, 1), Range(1, oo, 1))');
  expect(String(solveset(p('x/(x-3)<3'), x, sj.Range.of(0, 5)))).toBe('Range(0, 3, 1)');
  for (const source of ['Abs(x)-1', 'Min(x,15)-1', 'Max(x,15)-1']) {
    expect(() => solveset(p(source), x, Complexes)).toThrow(RangeError);
  }
});

describe('solveset input and domain handling', () => {
  it('infers a single unknown and supports expression targets', () => {
    expect(solveset(p('x - 2')).toString()).toBe('{2}');
    expect(solveset(0, undefined, Reals)).toBe(Reals);
    expect(() => solveset(p('x + y'))).toThrow(RangeError);
    expect(solveset(p('sin(x) - cos(x)'), p('sin(x)')).toString()).toBe('{cos(x)}');
  });

  it('solves products and clears coupled real radicals', () => {
    expect(solveset(p('(x + 2)*(exp(x) - 3)'), x, Reals).toString()).toBe('{-2, log(3)}');
    expect(solveset(p('sqrt(2*x - 1) - sqrt(x - 4) - 2'), x, Reals).toString()).toBe('{5, 13}');
    expect(solveset(p('sqrt(x - 3) - sqrt(x) - 3'), x, Reals)).toBe(sj.EmptySet);
  });

  it('preserves the first matching piece and tests its finite boundary', () => {
    const piecewise = p('Piecewise((0, Eq(x, pi)), ((x - pi)/sin(x), True))');
    expect(solveset(piecewise, x, Reals).toString()).toBe('{pi}');
  });

  it('orders indexed roots and keeps large logarithmic bounds exact', () => {
    expect(Q.solveUnivariateInequality(Gt(p('x**7 - x - 2'), 0), x, { relational: false }).toString())
      .toBe('Interval.open(CRootOf(x**7 - x - 2, 0), oo)');
    expect(Q.reduceInequalities(p('log(x) < 1000'), [x]).toString()).toBe('(0 < x) & (x < exp(1000))');
  });
});

it('solves affine congruences over the integers', () => {
  expect(solveset(sj.Mod(add(mul(5, x), -8), 7).sub(3), x, Integers).toString()).toMatch(/7\*.* \+ 5/);
  expect(solveset(sj.Mod(mul(2, x), 4).sub(1), x, Integers)).toBe(sj.EmptySet);
  expect(solveset(sj.Mod(x, 3).sub(SS.I), x, Integers)).toBe(sj.EmptySet);
});

it('folds minimum and maximum over their real branches', () => {
  for (const [source, expected] of [
    ['x*Max(x,15)-10', '{2/3}'],
    ['x*Min(x,15)-10', '{-sqrt(10), sqrt(10)}'],
    ['Max(x+2,Abs(x-3)-1)-3', '{-1, 1}'],
  ] as const) expect(String(solveset(p(source), x, Reals)), source).toBe(expected);
});

it('restricts logarithmic comparisons to the input domain', () => {
  const domain = interval(1, 4);
  for (const [source, expected] of [
    ['log(x)>1', 'Interval.Lopen(E, 4)'],
    ['log(x)>=1', 'Interval(E, 4)'],
    ['log(x)<1', 'Interval.Ropen(1, E)'],
    ['log(x)<=1', 'Interval(1, E)'],
    ['Eq(log(x),1)', '{E}'],
    ['Ne(log(x),1)', 'Union(Interval.Ropen(1, E), Interval.Lopen(E, 4))'],
  ] as const) expect(String(Q.solveUnivariateInequality(p(source), x, { domain, relational: false })), source).toBe(expected);
  expect(String(Q.solveUnivariateInequality(p('x>0'), x, { domain: Integers, relational: false }))).toBe('Range(1, oo, 1)');
  expect(String(Q.solveUnivariateInequality(p('Ne(x**2,0)'), x))).toBe('(x > -oo) & (x < oo) & Ne(x, 0)');
});

it('uses signs outside the range of a shifted sine', () => {
  expect(Q.solveUnivariateInequality(p('2*sin(x)>3'), x)).toBe(SS.false);
  expect(Q.solveUnivariateInequality(p('2*sin(x)<3'), x, { relational: false })).toBe(Reals);
  expect(Q.reduceInequalities(p('sin(x)<2'), [x])).toBe(SS.true);
  expect(solveset(p('Abs(sin(x))+1'), x, Reals)).toBe(sj.EmptySet);
});

it('solves real equations by their outer function', () => {
  for (const [source, expected] of [
    ['arg(x)', 'Interval.open(0, oo)'],
    ['sinh(x)+sech(x)', '{log(sqrt(-2 + sqrt(5)))}'],
    ['2**x-3**x', '{0}'],
    ['2**x+3**x', 'EmptySet'],
    ['0**x-1', '{0}'],
    ['0**x-5', 'EmptySet'],
    ['Abs(x)', '{0}'],
    ['2*Abs(x)-4', '{-2, 2}'],
    ['exp(x**2)-2', '{-sqrt(log(2)), sqrt(log(2))}'],
    ['exp(1/x)-2', '{1/log(2)}'],
  ] as const) expect(String(solveset(p(source), x, Reals)), source).toBe(expected);
  expect(solveset(p('cos(x)+sinh(x)'), x, Complexes)).toBeInstanceOf(ConditionSet);
  expect(solveset(p('sin(exp(x))'), x, Complexes)).toBeInstanceOf(ConditionSet);
  expect(String(solveset(p('sin(Abs(x))'), x, Reals))).toBe(String(solveset(p('sin(x)'), x, Reals)));
});

it('validates the domain and tests candidate points in a finite set', () => {
  // @ts-expect-error A scalar is an invalid domain.
  expect(() => solveset(x, x, SS.One)).toThrow(TypeError);
  expect(() => solveset(x, Reals)).toThrow(TypeError);
  expect(solveset(1)).toBe(sj.EmptySet);
  expect(String(solveset(p('Eq(x,1)'), x, finiteSet(1, 2)))).toBe('{1}');
  expect(solveset(p('x-y'), x, finiteSet(1))).toBeInstanceOf(ConditionSet);
  expect(String(solveset(p('Piecewise((0,Ne(x,1)),(1,True))'), x, Reals))).toBe('Union(Interval.open(-oo, 1), Interval.open(1, oo))');
});

it('isolates a variable alongside a bound integral or sum', () => {
  expect(String(Q.reduceInequalities(p('x + Integral(y**2,(y,1,3)) - 1 >= 0'), [x])))
    .toBe('x >= 1 - Integral(y**2, (y, 1, 3))');
  expect(String(Q.reduceInequalities(p('x + y**2 + Sum(f(x),(x,1,3)) >= 0'), [x])))
    .toBe('x >= -y**2 - Sum(f(x), (x, 1, 3))');
  expect(String(Q.reduceInequalities(p('x*y<0'), [x]))).toBe('x*y < 0');
});

it('preserves real boundaries in transformed inequalities', () => {
  expect(String(solveset(p('log(x-6)/x <= 0'), x, Reals))).toBe('Interval.Lopen(6, 7)');
  expect(String(Q.reduceInequalities(p('1-x-sqrt((1-x)**2)<0'), [x]))).toBe('(1 < x) & (x < oo)');
  expect(String(Q.solveUnivariateInequality(p('x**2>0'), x, { domain: interval(-2, 2) })))
    .toBe('(x >= -2) & (x <= 2) & Ne(x, 0)');
});

it('handles affine congruence domain and residue restrictions', () => {
  const mod = sj.Mod;
  for (const equation of [mod(x, 3).sub(3), mod(x, -3).sub(1), mod(x, -3).add(3), mod(x, 3).sub(SS.Half)]) {
    expect(solveset(equation, x, Integers)).toBe(sj.EmptySet);
  }
  expect(String(solveset(mod(x, -3).add(2), x, Integers))).toMatch(/3\*.* \+ 1/);
  for (const equation of [mod(x, y).sub(1), mod(x.pow(2), 3).sub(1), mod(x, 3).sub(y), mod(x, 3).sub(x)]) {
    expect(solveset(equation, x, Integers)).toBeInstanceOf(ConditionSet);
  }
});

it('retains unresolved outer functions and filters radical candidates by interval', () => {
  for (const source of ['Abs(x)-y', '0**x-y']) {
    expect(solveset(p(source), x, Reals), source).toBeInstanceOf(ConditionSet);
  }
  expect(String(solveset(p('sqrt(2*x-1)-sqrt(x-4)-2'), x, interval(4, 8)))).toBe('{5}');
  expect(String(solveset(p('2*x+(x-10)**(-2)'), x, Reals)))
    .toBe('{-(3*sqrt(24081)/4 + 4027/4)**(1/3)/3 - 100/(3*(3*sqrt(24081)/4 + 4027/4)**(1/3)) + 20/3}');
});

it('rejects inconsistent integer congruences before dividing by the gcd', () => {
  const residue = new sj.DefinedFunctionCall('Mod', [mul(2, x), Rational.of(4)], { nargs: 2 });
  expect(solveset(add(residue, -1), x, Integers)).toBe(sj.EmptySet);
});

it('keeps unsupported equations after a failed radical elimination', () => {
  expect(solveset(p('sin(sqrt(x))+sqrt(x-1)'), x, Reals)).toBeInstanceOf(ConditionSet);
  expect(solveset(p('sqrt(x**2)-x+sqrt((x+1)**2)-(x+1)'), x, Reals)).toBeInstanceOf(ConditionSet);
});

it('handles real and imaginary components of phase and modulus', () => {
  expect(solveset(p('arg(x+I)'), x, Reals)).toBe(sj.EmptySet);
  expect(String(solveset(p('Abs(x+I)-2'), x, Reals))).toBe('{-sqrt(3), sqrt(3)}');
  expect(String(solveset(p('atan2(x,2)-pi/3'), x, Reals))).toBe('{2*sqrt(3)}');
  expect(solveset(p('atan2(x,2)-pi'), x, Reals)).toBe(sj.EmptySet);
  expect(solveset(p('atan2(2,x)-y'), x, Reals)).toBeInstanceOf(ConditionSet);
  expect(solveset(p('atan2(x,2)-y'), x, Reals)).toBeInstanceOf(ConditionSet);
});

it('includes finite domain endpoints of real radicals', () => {
  expect(String(solveset(p('x+sqrt(x**2-5)>0'), x, Reals))).toBe('Interval(sqrt(5), oo)');
  expect(String(solveset(p('x+sqrt(x**2-5)<0'), x, Reals))).toBe('Interval(-oo, -sqrt(5))');
  expect(String(solveset(p('sqrt(x-2)+2>0'), x, Reals))).toBe('Interval(2, oo)');
  expect(solveset(p('-x**2-2*x+(x+1)**2-1'), x, Reals)).toBe(Reals);
});

it('leaves real equations with symbolic powers conditional', () => {
  const r = new Sym('r', { rational: true });
  expect(solveset(add(pow(x, r), mul(-1, y)), x, Reals)).toBeInstanceOf(ConditionSet);
});

it('solves a Piecewise inequality on the regions selected by its conditions', () => {
  expect(String(solveset(p('Piecewise((1,x>10),(0,True))>0'), x, Reals))).toBe('Interval.open(10, oo)');
});

it('preserves exact indexed-root endpoints when reducing a single inequality', () => {
  expect(String(Q.reduceInequalities(p('x**8+x-9>=0'), [x])))
    .toBe('((-oo < x) & (x <= CRootOf(x**8 + x - 9, 0))) | ((x < oo) & (CRootOf(x**8 + x - 9, 1) <= x))');
});

describe('solveset on intervals with parameters (SymPy 1.14)', () => {
  const x = new Sym('x'), y = new Sym('y'), l = new Sym('l', { positive: true });
  const P = (s: string) => parse(s, { symbols: { x, y, l } });
  it('treats Interval(-oo, oo) as the real line', () => {
    const line = new sj.Interval(SS.NegativeInfinity, SS.Infinity, true, true);
    // SymPy prints the domain it was given: Intersection({y}, Interval(-oo, oo))
    expect(String(solveset(P('x - y'), x, line))).toBe('Intersection({y}, Reals)');
    expect(String(solveset(P('sin(x)'), x, line))).toBe('Union(ImageSet(Lambda(_n, 2*_n*pi), Integers), ImageSet(Lambda(_n, 2*_n*pi + pi), Integers))');
  });
  it('keeps the roots that the interval contains', () => {
    expect(String(solveset(P('x**2 - l'), x, sj.Interval.of(0, SS.Infinity)))).toBe('{sqrt(l)}');
    expect(String(solveset(P('(x - l)/(x + l)'), x, sj.Interval.of(0, SS.Infinity)))).toBe('{l}');
    expect(String(solveset(P('x**2 - y'), x, sj.Interval.of(0, 1)))).toBe('Intersection({-sqrt(y), sqrt(y)}, Interval(0, 1))');
    expect(String(solveset(P('(x - l)*(x - y)'), x, sj.Interval.of(0, SS.Infinity)))).toBe('Union({l}, Intersection({y}, Interval(0, oo)))');
  });
});

it('expresses several disjoint rational-inequality intervals as a union of conditions', () => {
  const t = sj.symbol('t');
  expect(String(sj.reduceRationalInequalities([[sj.Ne(t.pow(2), 1)]], t))).toBe('((-oo < t) & (t < -1)) | ((-1 < t) & (t < 1)) | ((1 < t) & (t < oo))');
});

it('solves homogeneous congruences and tests real parameterized roots on a bounded interval', () => {
  expect(String(solveset(sj.Mod(x, 3), x, Integers))).toMatch(/3\*/);
  const a = new Sym('a');
  const polynomial = add(pow(x, 2), mul(-1, add(a, 1), x), a);
  expect(String(solveset(polynomial, x, interval(-10, 10)))).toBe('Union({1}, Intersection({a}, Interval(-10, 10)))');
});

it('checks original equations and domain membership after clearing coupled radicals', () => {
  const solve = AlgebraicSolver.solve;
  const cases = [
    { source: 'sqrt(x)+sqrt(x-1)-1', domain: Reals, expected: '{1}' },
    { source: 'sqrt(x)+sqrt(x-1)-2', domain: interval(100, 101), expected: 'EmptySet' },
    { source: 'sqrt(x)+sqrt(x-1)+2', domain: Reals, expected: 'EmptySet' },
    { source: 'sqrt(x**2)-sqrt((x+1)**2)+1', domain: Reals, expected: undefined },
    { source: 'sinh(x)+cosh(x)-2', domain: Reals, expected: '{log(2)}' },
  ];
  for (const { source, domain, expected } of cases) {
    const equation = p(source);
    const fail = vi.spyOn(AlgebraicSolver, 'solve').mockImplementation((candidate, ...args) => {
      if (candidate instanceof sj.Expr && (candidate.equals(equation) || candidate.equals(sj.cancel(equation)))) return [];
      return solve(candidate, ...args);
    });
    try {
      const solution = solveset(equation, x, domain);
      if (expected === undefined) expect(solution).toBeInstanceOf(ConditionSet);
      else expect(String(solution)).toBe(expected);
    } finally {
      fail.mockRestore();
    }
  }
});

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/integrals/integrate.ts.
// Indefinite and definite integration. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { Sym, parse, integrate, symbols, diff, doit, latex, sstr } from '../../src';
import { Expr, impl } from '../../src/core/nodes';
import { NoMatchResult } from '../../src/core/truth';
import { heavisideAtInfinity, realIntegrand } from '../../src/integrals/integrate';
import * as sjReal from '../../src';
import { rischHooks } from '../../src/integrals/risch';

// Integrals (integrals/integrate.ts). Expected values are the str() forms printed by SymPy 1.14
// (p is a positive, q a negative and r a real symbol).

const syms = [new Sym('p', { positive: true }), new Sym('q', { negative: true }), new Sym('r', { real: true })];
const P = (s: string) => parse(s, { symbols: syms });

it('integrates affine Piecewise conditions that exclude a point or simplify to a truth value', () => {
  const x = sj.symbol('x');
  const a = sj.symbol('a');
  expect(integrate(sj.Piecewise([1, sj.Ne(x, a)], [0, true]), x).equals(x)).toBe(true);
  const condition = (lhs: Expr, rhs: Expr) => new sj.Rel('Gt', lhs, rhs);
  const raw = (test: Expr) => new sj.Piecewise([sj.S.One, test, sj.S.Two, sj.S.true]);
  expect(integrate(raw(sj.S.false), x).equals(sj.mul(2, x))).toBe(true);
  expect(integrate(raw(condition(sj.add(x, 1), x)), x).equals(x)).toBe(true);
  expect(integrate(raw(condition(x, x)), x).equals(sj.mul(2, x))).toBe(true);
});

it('evaluates symbolic interval holes and retains a singular branch constant', () => {
  const x = sj.symbol('x');
  const bound = sj.symbol('b', { positive: true });
  expect(sstr(integrate(P('Piecewise((x,x<2))'), x, [0, bound])))
    .toBe('Piecewise((Min(2, b)**2/2, b <= Min(2, b)), (nan, True))');
  expect(sstr(integrate(P('Piecewise((1,x>0),(1/x,True))'), x)))
    .toBe('Piecewise((log(x), x <= 0), (x, True))');
});

it('keeps the integral when a branch primitive or an affine clipping bound cannot be computed', () => {
  const x = sj.symbol('x');
  const a = sj.symbol('a');
  const f = sj.SymFunction('f')(x);
  expect(integrate(sj.Piecewise([f, sj.Gt(x, 0)], [0, true]), x)).toBeInstanceOf(sj.Integral);
  expect(integrate(sj.Piecewise([1, sj.And(sj.Gt(x, a), sj.Gt(f, 0))], [0, true]), x)).toBeInstanceOf(sj.Integral);
});
const V = (s: string): Sym => {
  const v = P(s);
  if (!(v instanceof Sym)) throw new TypeError(s);
  return v;
};
const [x, y, z, n, k, a, b, c, m, t] = [V('x'), V('y'), V('z'), V('n'), V('k'), V('a'), V('b'), V('c'), V('m'), V('t')];
const [pp, qq, rr] = [V('p'), V('q'), V('r')];
it('validates integration variables and integrates equalities on both sides', () => {
  expect(() => Reflect.apply(integrate, undefined, [x, sj.add(x, 1)])).toThrow(RangeError);
  expect(sstr(integrate(sj.Eq(x, y), x))).toBe('Eq(x**2/2, x*y)');
  expect(sstr(integrate(sj.Eq(x, y), x, [0, 1]))).toBe('Eq(1/2, y)');
});
it('integrates sums containing fully integrable piecewise terms', () => {
  const f = sj.add(x, sj.piecewise([x, sj.Lt(x, 0)], [sj.pow(x, 2), true]));
  expect(sstr(integrate(f, x))).toBe('x**2/2 + Piecewise((x**2/2, x < 0), (x**3/3, True))');
});
it('retains an unresolved inexact Gaussian instead of switching coefficient domains', () => {
  const f = P('exp(1.2*n*s*z*(-t + z)/t)');
  expect(integrate(f, z, [0, x])).toBeInstanceOf(sj.Integral);
});
it('differentiates primitives from the hyperbolic, trigonometric and special-function tables', () => {
  for (const source of ['sinh(x)', 'cosh(x)', 'cos(x)**4', 'x*cos(x)', 'x**2*cos(x)', 'x**2*sin(x)', 'acos(x)', 'erf(x)']) {
    const integrand = P(source);
    const primitive = integrate(integrand, x);
    expect(primitive).not.toBeInstanceOf(sj.Integral);
    for (const point of [sj.rational(1, 4), sj.rational(1, 2)]) {
      const actual = diff(primitive, x).subs(x, point).toNumber();
      expect(actual).toBeCloseTo(integrand.subs(x, point).toNumber(), 12);
    }
  }
});
const show = (v: unknown): string =>
  Array.isArray(v) ? `[${v.map(show).join(', ')}]` : v === undefined ? 'None' : v instanceof Expr || v instanceof NoMatchResult ? v.toString() : typeof v === 'string' ? v : JSON.stringify(v);
const pw = (e: unknown): sj.Piecewise => {
  if (!(e instanceof sj.Piecewise)) throw new TypeError('a Piecewise expected');
  return e;
};
/** The result, or the class name and message of what it throws. */
const run = (f: () => unknown): string => {
  try {
    return show(f());
  } catch (e) {
    return e instanceof Error ? `ERR ${e.constructor.name}: ${e.message}` : 'ERR';
  }
};
const conc = (e: unknown): sj.Concrete => {
  if (!(e instanceof sj.Concrete)) throw new TypeError('a Sum or Product expected');
  return e;
};
const conv = (e: unknown) => sj.isConvergent(conc(e));
const aconv = (e: unknown) => sj.isAbsolutelyConvergent(conc(e));
const moo = P('-oo');
void [x, y, z, n, k, a, b, c, m, t, pp, qq, rr, conv, aconv, moo, pw];

describe('results equal SymPy 1.14', () => {
  it('keeps an integral unresolved when the rational integrator cannot provide a primitive', () => {
    const original = rischHooks.integrate;
    if (original === undefined) throw new TypeError('integrator expected');
    expect(String(original(P('gamma(x)'), x))).toBe('Integral(gamma(x), x)');
    try {
      rischHooks.integrate = (f, v) => new sj.Integral([f, v]);
      expect(String(integrate(P('log(x)+1/(x**5-x+1)'), x))).toBe('Integral(log(x) + 1/(x**5 - x + 1), x)');
    } finally {
      rischHooks.integrate = original;
    }
  });
  it('integrates overlapping and disconnected Piecewise intervals in branch order', () => {
    expect(String(integrate(P('Piecewise((x, x < 1), (x**2, True))'), x, [0, 0]))).toBe('0');
    expect(String(integrate(P('Piecewise((x, x < 1), (x**2, x >= -1))'), x, [-2, 4]))).toBe('39/2');
    const f = P('Piecewise((1, x < 2), (2, x > 3), (3, True))');
    expect(String(integrate(f, x, [-2, 4]))).toBe('9');
    expect(String(integrate(f, x, [4, -2]))).toBe('-9');
    expect(String(integrate(P('Piecewise((1, x > 0), (-1, x < 0))'), x, [-2, 4]))).toBe('2');
    expect(String(integrate(P('Piecewise((1, (x > 1) & (x < 2)))'), x, [-2, 4]))).toBe('nan');
    expect(String(integrate(P('Piecewise((1, (x < 1) | (x > 2)), (2, True))'), x, [0, 3]))).toBe('4');
    expect(String(integrate(P('Piecewise((1, 2*x < x + 1), (2, True))'), x, [0, 3]))).toBe('5');
    expect(String(integrate(P('Piecewise((1, x > 0), (0, True))'), x, [sj.oo.neg(), 1]))).toBe('1');
    expect(String(integrate(P('Piecewise((1, x < 0), (0, True))'), x, [-1, sj.oo]))).toBe('1');
    expect(String(integrate(P('Piecewise((1, Eq(x, 0)), (0, True))'), x, [sj.oo.neg(), sj.oo]))).toBe('0');
    expect(String(integrate(P('Piecewise((0, x < oo), (1, True))'), x, [sj.oo.neg(), sj.oo]))).toBe('0');
    expect(String(integrate(P('Piecewise((gamma(x), x < 1), (0, True))'), x, [2, 0]))).toContain('Integral(');
    expect(String(integrate(P('Piecewise((gamma(x), x < 1), (0, True))'), x, [0, 2]))).toContain('Integral(');
    const condition = sj.ITE(sj.Lt(x, 1), sj.S.true, sj.S.false, { evaluate: false });
    expect(String(integrate(new sj.Piecewise([sj.S.One, condition, sj.S.Zero, sj.S.true]), x, [0, 2]))).toContain('Integral(');
    expect(String(integrate(P('Piecewise((1, x < 4), (2, x**2 < 1), (0, True))'), x, [0, 2]))).toBe('2');
    expect(String(integrate(P('Piecewise((1, x > 4), (2, x**2 < 1), (0, True))'), x, [0, 2]))).toContain('Integral(');
  });
  const cases: [string, () => unknown, string][] = [
    ["sj.integrate(P('sin(a*x)'), x)", () => sj.integrate(P('sin(a*x)'), x), "Piecewise((-cos(a*x)/a, Ne(a, 0)), (0, True))"],
    ["sj.integrate(P('exp(-a*x**2)'), x)", () => sj.integrate(P('exp(-a*x**2)'), x), "Piecewise((sqrt(pi)*erf(sqrt(a)*x)/(2*sqrt(a)), Ne(a, 0)), (x, True))"],
    ["sj.integrate(P('exp(-2*a*x**2)'), x)", () => sj.integrate(P('exp(-2*a*x**2)'), x), "Piecewise((sqrt(2)*sqrt(pi)*erf(sqrt(2)*sqrt(a)*x)/(4*sqrt(a)), Ne(a, 0)), (x, True))"],
    ["sj.integrate(P('exp(x**2*y)'), x)", () => sj.integrate(P('exp(x**2*y)'), x), "Piecewise((sqrt(pi)*erf(x*sqrt(-y))/(2*sqrt(-y)), Ne(y, 0)), (x, True))"],
    ["sj.integrate(P('exp(qq*x**2)'.replace('qq','q')), x)", () => sj.integrate(P('exp(qq*x**2)'.replace('qq','q')), x), "sqrt(pi)*erf(x*sqrt(-q))/(2*sqrt(-q))"],
    ["sj.integrate(P('sin(-2*x**2)'), x)", () => sj.integrate(P('sin(-2*x**2)'), x), "-3*sqrt(pi)*fresnels(2*x/sqrt(pi))*gamma(3/4)/(8*gamma(7/4))"],
    ["sj.integrate(P('cos(-2*x**2)'), x)", () => sj.integrate(P('cos(-2*x**2)'), x), "sqrt(pi)*fresnelc(2*x/sqrt(pi))*gamma(1/4)/(8*gamma(5/4))"],
    ["sj.integrate(P('x**2.5'), x)", () => sj.integrate(P('x**2.5'), x), "0.285714285714286*x**3.5"],
    ["sj.integrate(P('x**n'), x)", () => sj.integrate(P('x**n'), x), "Piecewise((x**(n + 1)/(n + 1), Ne(n, -1)), (log(x), True))"],
    ["sj.integrate(P('x**pi'), x)", () => sj.integrate(P('x**pi'), x), "x**(1 + pi)/(1 + pi)"],
    ["sj.integrate(P('1/sqrt(4 - x**2)'), x)", () => sj.integrate(P('1/sqrt(4 - x**2)'), x), "asin(x/2)"],
    ["sj.integrate(P('Ei(2*x)'), x)", () => sj.integrate(P('Ei(2*x)'), x), "x*Ei(2*x) - exp(2*x)/2"],
    ["sj.integrate(P('atan(2*x)'), x)", () => sj.integrate(P('atan(2*x)'), x), "x*atan(2*x) - log(4*x**2 + 1)/4"],
    ["sj.integrate(P('acot(x)'), x)", () => sj.integrate(P('acot(x)'), x), "x*acot(x) + log(x**2 + 1)/2"],
    ["sj.integrate(P('gamma(x)'), x)", () => sj.integrate(P('gamma(x)'), x), "Integral(gamma(x), x)"],
    ["sj.integrate(P('x*exp(x**2)'), x)", () => sj.integrate(P('x*exp(x**2)'), x), "exp(x**2)/2"],
    ["sj.integrate(P('x*exp(x**2)*sin(x)'), x)", () => sj.integrate(P('x*exp(x**2)*sin(x)'), x), "Integral(x*exp(x**2)*sin(x), x)"],
    ["sj.integrate(P('x**2*exp(sin(x))'), x)", () => sj.integrate(P('x**2*exp(sin(x))'), x), "Integral(x**2*exp(sin(x)), x)"],
    ["sj.integrate(P('log(x)**2*x'), x)", () => sj.integrate(P('log(x)**2*x'), x), "x**2*log(x)**2/2 - x**2*log(x)/2 + x**2/4"],
    ["sj.integrate(P('exp(x)*log(x)**2'), x)", () => sj.integrate(P('exp(x)*log(x)**2'), x), "Integral(exp(x)*log(x)**2, x)"],
    ["sj.integrate(P('exp(2*x)*cos(3*x)'), x)", () => sj.integrate(P('exp(2*x)*cos(3*x)'), x), "3*exp(2*x)*sin(3*x)/13 + 2*exp(2*x)*cos(3*x)/13"],
    ["sj.integrate(P('exp(x**2)*cos(3*x)'), x)", () => sj.integrate(P('exp(x**2)*cos(3*x)'), x), "Integral(exp(x**2)*cos(3*x), x)"],
    ["sj.integrate(P('exp(I*x)*sin(x)'), x)", () => sj.integrate(P('exp(I*x)*sin(x)'), x), "I*x/2 - exp(2*I*x)/4"],
    ["sj.integrate(P('exp(I*x)*sin(x**2)'), x)", () => sj.integrate(P('exp(I*x)*sin(x**2)'), x), "Integral(exp(I*x)*sin(x**2), x)"],
    ["sj.integrate(P('x**2/(x - 1)'), x)", () => sj.integrate(P('x**2/(x - 1)'), x), "x**2/2 + x + log(x - 1)"],
    ["sj.integrate(P('x**2/(x**2 + 1)'), x)", () => sj.integrate(P('x**2/(x**2 + 1)'), x), "x - atan(x)"],
    ["sj.integrate(P('x/(x**2 + 2*x + 2)'), x)", () => sj.integrate(P('x/(x**2 + 2*x + 2)'), x), "log(x**2 + 2*x + 2)/2 - atan(x + 1)"],
    ["sj.integrate(P('(2*x + 2)/(x**2 + 2*x + 2)'), x)", () => sj.integrate(P('(2*x + 2)/(x**2 + 2*x + 2)'), x), "log(x**2 + 2*x + 2)"],
    ["sj.integrate(P('1/(x*(x - 1)**2)'), x)", () => sj.integrate(P('1/(x*(x - 1)**2)'), x), "log(x) - log(x - 1) - 1/(x - 1)"],
    ["sj.integrate(P('(x + 1)**2/(x + 1)'), x)", () => sj.integrate(P('(x + 1)**2/(x + 1)'), x), "x**2/2 + x"],
    ["sj.integrate(sj.Piecewise([P('x'), P('x < 1')], [P('x**2'), true]), x)", () => sj.integrate(sj.Piecewise([P('x'), P('x < 1')], [P('x**2'), true]), x), "Piecewise((x**2/2, x < 1), (x**3/3 + 1/6, True))"],
    ["sj.integrate(sj.Piecewise([P('1'), P('y*x <= 0')], [P('2'), true]), x, [-2, 1])", () => sj.integrate(sj.Piecewise([P('1'), P('y*x <= 0')], [P('2'), true]), x, [-2, 1]), "Integral(Piecewise((1, x*y <= 0), (2, True)), (x, -2, 1))"],
    ["sj.integrate(P('x**y*exp(-x)'), x, [0, sj.oo])", () => sj.integrate(P('x**y*exp(-x)'), x, [0, sj.oo]), "Piecewise((gamma(y + 1), re(y) > -1), (Integral(x**y*exp(-x), (x, 0, oo)), True))"],
    ["sj.integrate(P('x**2*exp(-2*x)'), x, [0, sj.oo])", () => sj.integrate(P('x**2*exp(-2*x)'), x, [0, sj.oo]), "1/4"],
    ["sj.integrate(P('exp(-x)*gamma(x)'), x, [0, sj.oo])", () => sj.integrate(P('exp(-x)*gamma(x)'), x, [0, sj.oo]), "Integral(exp(-x)*gamma(x), (x, 0, oo))"],
    ["sj.integrate(P('exp(-x**2)*x'), x, [0, sj.oo])", () => sj.integrate(P('exp(-x**2)*x'), x, [0, sj.oo]), "1/2"],
    ["sj.integrate(P('gamma(x)'), x, [0, sj.oo])", () => sj.integrate(P('gamma(x)'), x, [0, sj.oo]), "Integral(gamma(x), (x, 0, oo))"],
    ["sj.integrate(P('x*exp(-x)*exp(-2*x)'), x, [0, sj.oo])", () => sj.integrate(P('x*exp(-x)*exp(-2*x)'), x, [0, sj.oo]), "1/9"],
    ["sj.integrate(P('x**p*exp(-x)'), x, [0, sj.oo])", () => sj.integrate(P('x**p*exp(-x)'), x, [0, sj.oo]), "gamma(p + 1)"],
    ["sj.integrate(P('x**y*exp(-x)'), x, [0, sj.oo], { conds: 'none' })", () => sj.integrate(P('x**y*exp(-x)'), x, [0, sj.oo], { conds: 'none' }), "gamma(y + 1)"],
    ["sj.integrate(P('gamma(x)*x'), x, [0, 1])", () => sj.integrate(P('gamma(x)*x'), x, [0, 1]), "Integral(x*gamma(x), (x, 0, 1))"],
    ["sj.integrate(P('1/x'), x, [1, sj.oo])", () => sj.integrate(P('1/x'), x, [1, sj.oo]), "oo"],
    ["sj.integrate(P('sin(x)**4'), x)", () => sj.integrate(P('sin(x)**4'), x), "3*x/8 - sin(x)**3*cos(x)/4 - 3*sin(x)*cos(x)/8"],
    ["sj.integrate(P('(y*x + 1)**3'), x)", () => sj.integrate(P('(y*x + 1)**3'), x), "x**4*y**3/4 + x**3*y**2 + 3*x**2*y/2 + x"],
    ["sj.integrate(P('x**2*sin(y*x)'), x)", () => sj.integrate(P('x**2*sin(y*x)'), x), "Piecewise((-x**2*cos(x*y)/y + 2*x*sin(x*y)/y**2 + 2*cos(x*y)/y**3, Ne(y, 0)), (0, True))"],
    ["sj.integrate(P('asin(x)'), x)", () => sj.integrate(P('asin(x)'), x), "x*asin(x) + sqrt(1 - x**2)"],
    ["sj.integrate(P('acos(x)'), x)", () => sj.integrate(P('acos(x)'), x), "x*acos(x) - sqrt(1 - x**2)"],
    ["sj.integrate(P('atan(x)'), x)", () => sj.integrate(P('atan(x)'), x), "x*atan(x) - log(x**2 + 1)/2"],
    ["sj.integrate(P('asinh(x)'), x)", () => sj.integrate(P('asinh(x)'), x), "x*asinh(x) - sqrt(x**2 + 1)"],
    ["sj.integrate(P('acot(x)'), x)", () => sj.integrate(P('acot(x)'), x), "x*acot(x) + log(x**2 + 1)/2"],
    ["sj.integrate(P('Shi(x)'), x)", () => sj.integrate(P('Shi(x)'), x), "x*Shi(x) - cosh(x)"],
    ["sj.integrate(P('erfc(x)'), x)", () => sj.integrate(P('erfc(x)'), x), "x*erfc(x) - exp(-x**2)/sqrt(pi)"],
    ["sj.integrate(P('erfi(x)'), x)", () => sj.integrate(P('erfi(x)'), x), "x*erfi(x) - exp(x**2)/sqrt(pi)"],
    ["sj.integrate(P('gamma(sin(x))*cos(x)'), x)", () => sj.integrate(P('gamma(sin(x))*cos(x)'), x), "Integral(cos(x)*gamma(sin(x)), x)"],
    ["sj.integrate(P('sin(x)**(1/2)*cos(x)'), x)", () => sj.integrate(P('sin(x)**(1/2)*cos(x)'), x), "2*sin(x)**(3/2)/3"],
    ["sj.integrate(P('exp(I*x)*gamma(x)*sin(x)'), x)", () => sj.integrate(P('exp(I*x)*gamma(x)*sin(x)'), x), "Integral(exp(I*x)*sin(x)*gamma(x), x)"],
    ["sj.integrate(P('(x**2 + 2*x + 1)/(x + 1)'), x)", () => sj.integrate(P('(x**2 + 2*x + 1)/(x + 1)'), x), "x**2/2 + x"],
    ["sj.integrate(P('1/(x**2*(x**2 + 1))'), x)", () => sj.integrate(P('1/(x**2*(x**2 + 1))'), x), "-atan(x) - 1/x"],
    ["sj.piecewiseIntegrate(pw(sj.Piecewise([P('x'), P('x < 1')], [P('x**2'), true])), x)", () => sj.piecewiseIntegrate(pw(sj.Piecewise([P('x'), P('x < 1')], [P('x**2'), true])), x), "Piecewise((x**2/2, x < 1), (x**3/3, True))"],
    ["sj.integrate(P('y*x**z*exp(-x)'), x, [0, sj.oo])", () => sj.integrate(P('y*x**z*exp(-x)'), x, [0, sj.oo]), "Piecewise((y*gamma(z + 1), re(z) > -1), (Integral(x**z*y*exp(-x), (x, 0, oo)), True))"],
    ["sj.integrate(P('x*(x**2 + 1)**(-1/2)'), x)", () => sj.integrate(P('x*(x**2 + 1)**(-1/2)'), x), "sqrt(x**2 + 1)"],
    ["sj.integrate(P('x*(x**2 + 1)**(1/3)'), x)", () => sj.integrate(P('x*(x**2 + 1)**(1/3)'), x), "3*x**2*(x**2 + 1)**(1/3)/8 + 3*(x**2 + 1)**(1/3)/8"],
    ["sj.integrate(P('1/(x**3 + 1)'), x)", () => sj.integrate(P('1/(x**3 + 1)'), x), "log(x + 1)/3 - log(x**2 - x + 1)/6 + sqrt(3)*atan(2*sqrt(3)*x/3 - sqrt(3)/3)/3"],
    ["sj.integrate(P('1/(x**2 + 1)**2'), x)", () => sj.integrate(P('1/(x**2 + 1)**2'), x), "x/(2*x**2 + 2) + atan(x)/2"],
    ["sj.integrate(P('1/(x**2 - y)'), x)", () => sj.integrate(P('1/(x**2 - y)'), x), "sqrt(1/y)*log(x - y*sqrt(1/y))/2 - sqrt(1/y)*log(x + y*sqrt(1/y))/2"],
    ["sj.integrate(P('x*(x**2 + 1)**(-3)'), x)", () => sj.integrate(P('x*(x**2 + 1)**(-3)'), x), "-1/(4*x**4 + 8*x**2 + 4)"],
    ["sj.integrate(P('sin(x)**2*cos(x)**2'), x)", () => sj.integrate(P('sin(x)**2*cos(x)**2'), x), "x/8 - sin(2*x)*cos(2*x)/16"],
    ["sj.integrate(sj.Piecewise([P('x'), P('y < 1')], [P('1'), true]), x)", () => sj.integrate(sj.Piecewise([P('x'), P('y < 1')], [P('1'), true]), x), "Piecewise((x**2/2, (y > -oo) & (y < 1)), (x, True))"],
    ["sj.integrate(P('tanh(x)'), x)", () => sj.integrate(P('tanh(x)'), x), "x - log(tanh(x) + 1)"],
    ["sj.integrate(P('exp(x)*log(x)'), x)", () => sj.integrate(P('exp(x)*log(x)'), x), "exp(x)*log(x) - Ei(x)"],
    ["sj.integrate(P('sin(log(x))'), x)", () => sj.integrate(P('sin(log(x))'), x), "x*sin(log(x))/2 - x*cos(log(x))/2"],
  ];
  it.each(cases)('%s', (_label, f, expected) => {
    expect(run(f)).toBe(expected);
  });
});

describe('results that differ from SymPy 1.14', () => {
  // [call, symjs result, SymPy 1.14 result]
  const cases: [string, () => unknown, string, string][] = [
    // the formula assumes a != 0 (SymPy adds the case a = 0)
    ["sj.integrate(P('exp(a*x)*sin(a*x)'), x)", () => sj.integrate(P('exp(a*x)*sin(a*x)'), x), "exp(a*x)*sin(a*x)/(2*a) - exp(a*x)*cos(a*x)/(2*a)", "Piecewise((exp(a*x)*sin(a*x)/(2*a) - exp(a*x)*cos(a*x)/(2*a), Ne(a, 0)), (0, True))"],
    ["sj.integrate(P('exp(-a*x**2 + x)'), x)", () => sj.integrate(P('exp(-a*x**2 + x)'), x), "sqrt(pi)*exp(1/(4*a))*erfi((-2*a*x + 1)/(2*sqrt(-a)))/(2*sqrt(-a))", "sqrt(pi)*exp(1/(4*a))*erfi((-2*a*x + 1)/(2*sqrt(-a)))/(2*sqrt(-a))"],
    // the same cases, with the condition written as Ne(y*z, 0)
    ["sj.integrate(P('exp(-x**2*y*z)'), x)", () => sj.integrate(P('exp(-x**2*y*z)'), x), "Piecewise((sqrt(pi)*erf(x*sqrt(y*z))/(2*sqrt(y*z)), Ne(y*z, 0)), (x, True))", "Piecewise((x, Eq(y, 0) | Eq(z, 0)), (sqrt(pi)*erf(x*sqrt(y*z))/(2*sqrt(y*z)), True))"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(P('exp(x**3)'), x)", () => sj.integrate(P('exp(x**3)'), x), "Integral(exp(x**3), x)", "exp(-I*pi/3)*gamma(1/3)*lowergamma(1/3, x**3*exp_polar(I*pi))/(9*gamma(4/3))"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(P('sin(x**3)'), x)", () => sj.integrate(P('sin(x**3)'), x), "Integral(sin(x**3), x)", "x**4*gamma(2/3)*hyper((2/3,), (3/2, 5/3), -x**6/4)/(6*gamma(5/3))"],
    ["sj.integrate(P('cos(x**2 + 1)'), x)", () => sj.integrate(P('cos(x**2 + 1)'), x), "sqrt(2)*sqrt(pi)*(cos(1)*fresnelc(sqrt(2)*x/sqrt(pi)) - sin(1)*fresnels(sqrt(2)*x/sqrt(pi)))/2", "sqrt(2)*sqrt(pi)*(cos(1)*fresnelc(sqrt(2)*x/sqrt(pi)) - sin(1)*fresnels(sqrt(2)*x/sqrt(pi)))/2"],
    // the same value for q < 0, written with sqrt(-q)
    ["sj.integrate(P('sin(q*x**2)'), x)", () => sj.integrate(P('sin(q*x**2)'), x), "-3*sqrt(2)*sqrt(pi)*fresnels(sqrt(2)*x*sqrt(-q)/sqrt(pi))*gamma(3/4)/(8*sqrt(-q)*gamma(7/4))", "3*sqrt(2)*sqrt(pi)*fresnels(sqrt(2)*sqrt(q)*x/sqrt(pi))*gamma(3/4)/(8*sqrt(q)*gamma(7/4))"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(P('1/sqrt(4 + x**2)'), x)", () => sj.integrate(P('1/sqrt(4 + x**2)'), x), "asinh(x/2)", "asinh(x/2)"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(P('1/sqrt(a - x**2)'), x)", () => sj.integrate(P('1/sqrt(a - x**2)'), x), "Integral(1/sqrt(a - x**2), x)", "Piecewise((-I*acosh(x/sqrt(a)), Abs(x**2/a) > 1), (asin(x/sqrt(a)), True))"],
    // completing the square is not implemented
    ["sj.integrate(P('1/sqrt(4 - x**2 + x)'), x)", () => sj.integrate(P('1/sqrt(4 - x**2 + x)'), x), "asin(2*sqrt(17)*(x - 1/2)/17)", "asin(2*sqrt(17)*(x - 1/2)/17)"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(P('asec(x)'), x)", () => sj.integrate(P('asec(x)'), x), "Integral(asec(x), x)", "x*asec(x) - Piecewise((acosh(x), Abs(x**2) > 1), (-I*asin(x), True))"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(P('sin(x)*cos(2*x)'), x)", () => sj.integrate(P('sin(x)*cos(2*x)'), x), "Integral(sin(x)*cos(2*x), x)", "2*sin(x)*sin(2*x)/3 + cos(x)*cos(2*x)/3"],
    // not implemented in symjs (SymPy's result shown)
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(P('sin(x**2)**2'), x)", () => sj.integrate(P('sin(x**2)**2'), x), "x/2 - sqrt(pi)*fresnelc(2*x/sqrt(pi))*gamma(1/4)/(16*gamma(5/4))", "-5*x*gamma(-5/4)/(8*gamma(-1/4)) + 5*sqrt(pi)*fresnelc(2*x/sqrt(pi))*gamma(-5/4)/(16*gamma(-1/4))"],
    ["sj.integrate(P('sin(x)*exp(x)*x'), x)", () => sj.integrate(P('sin(x)*exp(x)*x'), x), "x*(exp(x)*sin(x)/2 - exp(x)*cos(x)/2) + exp(x)*cos(x)/2", "x*exp(x)*sin(x)/2 - x*exp(x)*cos(x)/2 + exp(x)*cos(x)/2"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(P('log(x)**(1/2)*x'), x)", () => sj.integrate(P('log(x)**(1/2)*x'), x), "Integral(x*sqrt(log(x)), x)", "sqrt(2)*(sqrt(2)*x**2*sqrt(-log(x)) + sqrt(pi)*erfc(sqrt(2)*sqrt(-log(x)))/2)*sqrt(log(x))/(4*sqrt(-log(x)))"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(P('exp(a*x)*cos(3*x)'), x)", () => sj.integrate(P('exp(a*x)*cos(3*x)'), x), "Integral(exp(a*x)*cos(3*x), x)", "Piecewise((I*x*exp(-3*I*x)*sin(3*x)/2 + x*exp(-3*I*x)*cos(3*x)/2 + exp(-3*I*x)*sin(3*x)/6, Eq(a, -3*I)), (-I*x*exp(3*I*x)*sin(3*x)/2 + x*exp(3*I*x)*cos(3*x)/2 + exp(3*I*x)*sin(3*x)/6, Eq(a, 3*I)), (a*exp(a*x)*cos(3*x)/(a**2 + 9) + 3*exp(a*x)*sin(3*x)/(a**2 + 9), True))"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(P('exp(x)*sinh(x)'), x)", () => sj.integrate(P('exp(x)*sinh(x)'), x), "Integral(exp(x)*sinh(x), x)", "x*exp(x)*sinh(x)/2 - x*exp(x)*cosh(x)/2 + exp(x)*sinh(x)/2"],
    // the same value with the atan argument factored
    // not implemented in symjs (SymPy's result shown)
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(P('1/(x**4 + 1)'), x)", () => sj.integrate(P('1/(x**4 + 1)'), x), "-sqrt(2)*log(x**2 - sqrt(2)*x + 1)/8 + sqrt(2)*log(x**2 + sqrt(2)*x + 1)/8 + sqrt(2)*atan(sqrt(2)*x - 1)/4 + sqrt(2)*atan(sqrt(2)*x + 1)/4", "-sqrt(2)*log(x**2 - sqrt(2)*x + 1)/8 + sqrt(2)*log(x**2 + sqrt(2)*x + 1)/8 + sqrt(2)*atan(sqrt(2)*x - 1)/4 + sqrt(2)*atan(sqrt(2)*x + 1)/4"],
    // not implemented in symjs (SymPy's result shown)
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(P('Heaviside(x)'), x)", () => sj.integrate(P('Heaviside(x)'), x), "Integral(Heaviside(x), x)", "x*Heaviside(x)"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(sj.Piecewise([P('x'), P('x < 1')], [P('gamma(x)'), true]), x)", () => sj.integrate(sj.Piecewise([P('x'), P('x < 1')], [P('gamma(x)'), true]), x), "Integral(Piecewise((x, x < 1), (gamma(x), True)), x)", "Piecewise((x**2/2, x < 1), (Integral(gamma(x), (x, 1, x)) + 1/2, True))"],
    // not implemented in symjs (SymPy's result shown)
    // not implemented in symjs (SymPy's result shown)
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(sj.mul(P('2'), sj.Piecewise([P('x'), P('x < 1')], [P('gamma(x)'), true])), x)", () => sj.integrate(sj.mul(P('2'), sj.Piecewise([P('x'), P('x < 1')], [P('gamma(x)'), true])), x), "Integral(Piecewise((2*x, x < 1), (2*gamma(x), True)), x)", "Piecewise((x**2, x < 1), (2*Integral(gamma(x), x) - 2*Integral(gamma(x), (x, 1)) + 1, True))"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(sj.add(sj.Piecewise([P('x'), P('x < 1')], [P('gamma(x)'), true]), P('x')), x)", () => sj.integrate(sj.add(sj.Piecewise([P('x'), P('x < 1')], [P('gamma(x)'), true]), P('x')), x), "Integral(x + Piecewise((x, x < 1), (gamma(x), True)), x)", "Piecewise((x**2, x < 1), (Integral(x + gamma(x), (x, 1, x)) + 1, True))"],
    // the condition is rewritten for x < 0, the piecewise integral is not done
    ["sj.integrate(sj.Piecewise([P('1'), P('y/x < 0')], [P('2'), true]), x, [-2, -1])", () => sj.integrate(sj.Piecewise([P('1'), P('y/x < 0')], [P('2'), true]), x, [-2, -1]), "Integral(Piecewise((1, y/x < 0), (2, True)), (x, -2, -1))", "Integral(Piecewise((1, y/x < 0), (2, True)), (x, -2, -1))"],
    // the condition is rewritten for x < 0, the piecewise integral is not done
    ["sj.integrate(sj.Piecewise([P('1'), P('y*x**2 < 0')], [P('2'), true]), x, [-2, -1])", () => sj.integrate(sj.Piecewise([P('1'), P('y*x**2 < 0')], [P('2'), true]), x, [-2, -1]), "Integral(Piecewise((1, x**2*y < 0), (2, True)), (x, -2, -1))", "Integral(Piecewise((1, x**2*y < 0), (2, True)), (x, -2, -1))"],
    // SymPy raises TypeError
    ["sj.integrate(sj.Piecewise([P('1'), P('y*sin(x) < 0')], [P('2'), true]), x, [-2, -1])", () => sj.integrate(sj.Piecewise([P('1'), P('y*sin(x) < 0')], [P('2'), true]), x, [-2, -1]), "Integral(Piecewise((1, y*sin(x) < 0), (2, True)), (x, -2, -1))", "ERR TypeError"],
    // the condition is rewritten for x < 0, the piecewise integral is not done
    ["sj.integrate(sj.Piecewise([P('1'), P('y*x <= 0')], [P('2'), true]), x, [-2, -1])", () => sj.integrate(sj.Piecewise([P('1'), P('y*x <= 0')], [P('2'), true]), x, [-2, -1]), "Integral(Piecewise((1, x*y <= 0), (2, True)), (x, -2, -1))", "Integral(Piecewise((1, x*y <= 0), (2, True)), (x, -2, -1))"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(sj.Piecewise([P('1'), P('y*x < 0')], [P('2'), true]), x, [a, 1])", () => sj.integrate(sj.Piecewise([P('1'), P('y*x < 0')], [P('2'), true]), x, [a, 1]), "Integral(Piecewise((1, x*y < 0), (2, True)), (x, a, 1))", "Piecewise((Integral(Piecewise((1, x*y < 0), (2, True)), (x, a, 1)), a < 1), (-Integral(Piecewise((1, x*y < 0), (2, True)), (x, 1, a)), True))"],
    // the limit at oo is left for a symbolic y (SymPy uses the Mellin transform)
    ["sj.integrate(P('x*exp(-y*x)'), x, [0, sj.oo])", () => sj.integrate(P('x*exp(-y*x)'), x, [0, sj.oo]), "Piecewise((y**(-2), Abs(arg(y)) < pi/2), (Integral(x*exp(-x*y), (x, 0, oo)), True))", "Piecewise((y**(-2), Abs(arg(y)) < pi/2), (Integral(x*exp(-x*y), (x, 0, oo)), True))"],
    // the integral diverges: the antiderivative -x**2*cos(x) + 2*x*sin(x) + 2*cos(x) oscillates with unbounded
    // amplitude, so its values at oo fill AccumBounds(-oo, oo) (SymPy's oo*sign(AccumBounds(-1, 1)) - 2 is the
    // same set written unevaluated)
    ["sj.integrate(P('x**2*sin(x)'), x, [0, sj.oo])", () => sj.integrate(P('x**2*sin(x)'), x, [0, sj.oo]), "AccumBounds(-oo, oo)", "oo*sign(AccumBounds(-1, 1)) - 2"],
    // the same value with the fraction expanded
    ["sj.integrate(P('sin(y*x)**2'), x)", () => sj.integrate(P('sin(y*x)**2'), x), "Piecewise((x/2 - sin(x*y)*cos(x*y)/(2*y), Ne(y, 0)), (0, True))", "Piecewise(((x*y/2 - sin(x*y)*cos(x*y)/2)/y, Ne(y, 0)), (0, True))"],
    ["sj.integrate(P('x**(y)*log(x)'), x)", () => sj.integrate(P('x**(y)*log(x)'), x), "Piecewise((x*x**y*((y + 1)*log(x) - 1)/(y + 1)**2, Ne(y, -1)), (log(x)**2/2, True))", "Piecewise((x*x**y*y*log(x)/(y**2 + 2*y + 1) + x*x**y*log(x)/(y**2 + 2*y + 1) - x*x**y/(y**2 + 2*y + 1), Ne(y, -1)), (log(x)**2/2, True))"],
    // the case y = 0 is kept (SymPy's form divides by y)
    ["sj.integrate(P('1/(y*x + 1)'), x)", () => sj.integrate(P('1/(y*x + 1)'), x), "Piecewise((log(x*y + 1)/y, Ne(y, 0)), (x, True))", "log(x*y + 1)/y"],
    // the same cases, with the condition written as Ne(y, 0)
    ["sj.integrate(P('2**(y*x)'), x)", () => sj.integrate(P('2**(y*x)'), x), "Piecewise((2**(x*y)/(y*log(2)), Ne(y, 0)), (x, True))", "Piecewise((2**(x*y)/(y*log(2)), Ne(y*log(2), 0)), (x, True))"],
    ["sj.integrate(P('sin(x)/x'), x)", () => sj.integrate(P('sin(x)/x'), x), "Si(x)", "Si(x)"],
    // the same value, with the condition written as Ne(y, 0)
    ["sj.integrate(P('x*exp(y*x)'), x)", () => sj.integrate(P('x*exp(y*x)'), x), "Piecewise(((x/y - 1/y**2)*exp(x*y), Ne(y, 0)), (x**2/2, True))", "Piecewise(((x*y - 1)*exp(x*y)/y**2, Ne(y**2, 0)), (x**2/2, True))"],
    // differs from SymPy's log(cos(x)) + 1/(2*cos(x)**2) by a constant
    ["sj.integrate(P('tan(x)**3'), x)", () => sj.integrate(P('tan(x)**3'), x), "-log(tan(x)**2 + 1)/2 + tan(x)**2/2", "log(cos(x)) + 1/(2*cos(x)**2)"],
    // the same value for q < 0, written with sqrt(-q)
    ["sj.integrate(P('cos(q*x**2)'), x)", () => sj.integrate(P('cos(q*x**2)'), x), "sqrt(2)*sqrt(pi)*fresnelc(sqrt(2)*x*sqrt(-q)/sqrt(pi))*gamma(1/4)/(8*sqrt(-q)*gamma(5/4))", "sqrt(2)*sqrt(pi)*fresnelc(sqrt(2)*sqrt(q)*x/sqrt(pi))*gamma(1/4)/(8*sqrt(q)*gamma(5/4))"],
    // a factor whose derivative is 0 is not recognized as a constant
    ["sj.integrate(P('x*exp(sin(x)**2 + cos(x)**2)'), x)", () => sj.integrate(P('x*exp(sin(x)**2 + cos(x)**2)'), x), "Integral(x*exp(sin(x)**2 + cos(x)**2), x)", "x**2*exp(sin(x)**2)*exp(cos(x)**2)/2"],
    // a factor whose derivative is 0 is not recognized as a constant
    ["sj.integrate(P('x*(sin(x)**2 + cos(x)**2)**(1/2)'), x)", () => sj.integrate(P('x*(sin(x)**2 + cos(x)**2)**(1/2)'), x), "Integral(x*sqrt(sin(x)**2 + cos(x)**2), x)", "x**2*sqrt(sin(x)**2 + cos(x)**2)/2"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(P('x*sin(x**3)'), x)", () => sj.integrate(P('x*sin(x**3)'), x), "Integral(x*sin(x**3), x)", "x**5*gamma(5/6)*hyper((5/6,), (3/2, 11/6), -x**6/4)/(6*gamma(11/6))"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(sj.Piecewise([P('1'), P('y*x < 0')], [P('2'), true]), x, [-2, a])", () => sj.integrate(sj.Piecewise([P('1'), P('y*x < 0')], [P('2'), true]), x, [-2, a]), "Integral(Piecewise((1, x*y < 0), (2, True)), (x, -2, a))", "Piecewise((-Integral(Piecewise((1, x*y < 0), (2, True)), (x, a, -2)), a < -2), (Integral(Piecewise((1, x*y < 0), (2, True)), (x, -2, a)), True))"],
    // the same value with the power of the denominator not expanded
  ];
  it.each(cases)('%s', (_label, f, expected) => {
    expect(run(f)).toBe(expected);
  });
});


describe('definite integrals by Meijer G-functions (SymPy meijerint_definite)', () => {
  const cases: [string, string][] = [
    ['x*x**y*exp(-x)', 'Piecewise((gamma(y + 2), re(y) > -2), (Integral(x*x**y*exp(-x), (x, 0, oo)), True))'],
    ['exp(-x*x**2)', 'gamma(1/3)/3'],
    ['x**z*exp(-y*x)', 'Piecewise((gamma(z + 1)/(y*y**z), ((re(z) > -1) & (Abs(arg(y)) < pi/2)) | ((re(z) > -1) & (re(z) < 0) & Eq(Abs(arg(y)), pi/2))), (Integral(x**z*exp(-x*y), (x, 0, oo)), True))'],
    ['sin(x)/x', 'pi/2'],
    ['besselj(0, x)*exp(-x)', 'sqrt(2)/2'],
    ['x**2*exp(-x**2)', 'sqrt(pi)/4'],
    ['exp(-x**2)*cos(x)', 'sqrt(pi)*exp(-1/4)/2'],
  ];
  it.each(cases)('%s', (f, expected) => expect(String(sj.integrate(P(f), x, [0, sj.oo]))).toBe(expected));
  it('without the conditions (SymPy conds="none")', () => {
    expect(String(sj.integrate(P('x**z*exp(-y*x)'), x, [0, sj.oo], { conds: 'none' }))).toBe('gamma(z + 1)/(y*y**z)');
  });
});

// expected values from SymPy 1.14 dsolve
describe('dsolve hints (SymPy solver_map order and odesimp)', () => {
  it('integration by substitution', () => {
    expect(String(integrate(parse('x*cos(x**2)'), x))).toBe('sin(x**2)/2');
    expect(String(integrate(parse('exp(x)*cos(exp(x))'), x))).toBe('sin(exp(x))');
  });
});


describe('multiple integrals', () => {
  it('print, differentiate and evaluate like SymPy', async () => {
    const { Integral, Rational, add, mul, pow, subs } = await import('../../src');
    const [x, y] = symbols('x y');
    const i = new Integral([new Integral([add(x, y), y]), y, Rational.of(1), x]);
    expect(sstr(i)).toBe('Integral(x + y, y, (y, 1, x))');
    expect(latex(i)).toBe('\\int\\limits_{1}^{x}\\int \\left(x + y\\right)\\, dy\\, dy');
    expect(sstr(diff(i, x))).toBe('Integral(x + y, (y, x)) + Integral(1, y, (y, 1, x))');
    expect(sstr(diff(i, y))).toBe('0');
    expect(sstr(doit(i))).toBe('2*x**3/3 - x/2 - 1/6');
    expect(sstr(new Integral([new Integral([mul(x, y), x]), y]))).toBe('Integral(x*y, x, y)');
    expect(sstr(subs(new Integral([pow(x, 2), x]), [[x, Rational.of(1)]]))).toBe('Integral(x**2, (x, 1))');
  });
});

// SymPy 1.14: integrate(f, (x, a, b)); interior poles must not be crossed by F(b)-F(a).
describe('improper definite integrals', () => {
  it.each([
    ['1/x**2', '-1', '1', 'oo'],
    ['1/(x-1)**2', '0', '2', 'oo'],
    ['-1/x**2', '-1', '1', '-oo'],
    ['1/x', '-1', '1', 'nan'],
    ['1/x**3', '-1', '1', 'nan'],
    ['1/(x**2-1)', '-2', '2', 'nan'],
    ['1/x**2', '1', '-1', '-oo'],
    ['1/x**2', '-oo', 'oo', 'oo'],
    ['1/x**2', '1', '2', '1/2'],
    ['1/x**2', '0', '1', 'oo'],
    ['1/sqrt(x)', '0', '1', '2'],
    ['1/(x**2+1)', '-1', '1', 'pi/2'],
    ['log(x)', '-1', '1', '-2 + I*pi'],
    ['x', '2', '2', '0'],
  ])('%s on [%s, %s]', (f, lo, hi, expected) => {
    expect(String(integrate(P(f), x, [P(lo), P(hi)]))).toBe(expected);
  });
});

describe('unresolved singularities stay unevaluated', () => {
  // SymPy 1.14 computes these with stronger domain/root analysis. Until that
  // analysis is available, do not cross a possible pole with an endpoint subtraction.
  it.each([
    ['tan(x)', '0', 'pi'], // nan (the interior pole cannot be crossed)
    ['(5*x**4-1)/(x**5-x-1)', '0', '1'], // SymPy: 0; quintic root isolation is not used here
  ])('%s on [%s, %s]', (f, lo, hi) => {
    expect(integrate(P(f), x, [P(lo), P(hi)])).toBeInstanceOf(sj.Integral);
  });
  it('integrates a logarithmic derivative between consecutive sine zeros', () => {
    expect(String(integrate(P('cos(x)/sin(x)'), x, [1, 2]))).toBe('log(sin(2)) - log(sin(1))');
  });
  it('uses quartic roots to exclude interior singularities', () => {
    expect(String(integrate(P('(4*x**3+1)/(x**4+x+1)'), x, [0, 1]))).toBe('log(3)');
    // Degree alone is not a reason to leave an integral unevaluated: this
    // quintic factors into a quadratic and a cubic, both supported.
    expect(String(integrate(P('(5*x**4+1)/(x**5+x+1)'), x, [0, 1]))).toBe('log(3)');
  });
  it('retains the polynomial quotient when trying a real partial-fraction primitive', () => {
    const f = P('x**6/(x**4+x+1)');
    const result = integrate(f, x);
    expect(result).not.toBeInstanceOf(sj.Integral);
    const derivative = diff(result, x);
    for (const value of [1, 2, 3]) {
      const actual = derivative.subs([[x, value]]).evalf(25).toComplex();
      const expected = f.subs([[x, value]]).toNumber();
      expect(actual.re).toBeCloseTo(expected, 12);
      expect(actual.im).toBeCloseTo(0, 12);
    }
    // At zero the derivative cancels exactly. Evaluate its residual directly,
    // since arbitrary-precision relative accuracy cannot certify an exact zero.
    const zero = derivative.subs([[x, 0]]).toComplex();
    expect(Math.hypot(zero.re, zero.im)).toBeLessThan(1e-12);
  });
  it('evaluates the generic endpoint difference for symbolic bounds and poles', () => {
    expect(integrate(P('1/x**2'), x, [1, a]).equals(P('1 - 1/a'))).toBe(true);
    expect(integrate(P('1/x**2'), x, [a, 1]).equals(P('1/a - 1'))).toBe(true);
    expect(integrate(P('1/(x-y)**2'), x, [0, 1]).equals(P('-1/(1-y) - 1/y'))).toBe(true);
    // SymPy: integrate(log(x), (x, 1, a))
    expect(String(integrate(P('log(x)'), x, [1, a]))).toBe('a*log(a) - a + 1');
  });
});

describe('DiracDelta, SingularityFunction and the Risch algorithm (SymPy Integral._eval_integral)', () => {
  const D = sj.DiracDelta;
  const SF = sj.SingularityFunction;
  const f = sj.Function('f');
  const oo = sj.S.Infinity;
  it('integrates DiracDelta by deltaintegrate', () => {
    expect(String(integrate(D(x), x))).toBe('Heaviside(x)');
    expect(String(integrate(sj.mul(D(sj.sub(x, 1)), sj.pow(x, 2)), x))).toBe('Heaviside(x - 1)');
    expect(String(integrate(D(x, 1), x))).toBe('DiracDelta(x)');
    expect(String(integrate(sj.add(D(x), x), x))).toBe('x**2/2 + Heaviside(x)');
    expect(String(integrate(sj.mul(D(sj.sub(x, 1)), f(x)), x, [sj.mul(-1, oo), oo]))).toBe('f(1)');
    expect(String(integrate(sj.mul(D(sj.sub(x, 1)), sj.exp(x)), x, [sj.mul(-1, oo), oo]))).toBe('E');
    expect(String(integrate(sj.mul(D(sj.sub(sj.pow(x, 2), 1)), f(x), f(sj.pow(x, 2))), x))).toBe('f(-1)*f(1)*Heaviside(x + 1)/2 + f(1)**2*Heaviside(x - 1)/2');
    // deltaintegrate does not apply
    expect(String(integrate(D(sj.sin(x)), x))).toBe('Integral(DiracDelta(sin(x)), x)');
  });
  it('integrates SingularityFunction by singularityintegrate', () => {
    expect(String(integrate(SF(x, a, 3), x))).toBe('SingularityFunction(x, a, 4)/4');
    expect(String(integrate(sj.mul(5, SF(x, 5, -2)), x))).toBe('5*SingularityFunction(x, 5, -1)');
    expect(String(integrate(sj.mul(6, SF(x, 5, -1)), x))).toBe('6*SingularityFunction(x, 5, 0)');
    expect(String(integrate(sj.mul(SF(x, 1, -1), f(x)), x))).toBe('f(1)*SingularityFunction(x, 1, 0)');
    expect(String(integrate(sj.mul(x, SF(x, 0, -1)), x))).toBe('0');
    // term by term (SymPy prints SingularityFunction(x, 1, 3)/3 + sqrt(pi)*erfi(x)/2: the same sum)
    expect(String(integrate(sj.add(SF(x, 1, 2), sj.exp(sj.pow(x, 2))), x))).toBe('sqrt(pi)*erfi(x)/2 + SingularityFunction(x, 1, 3)/3');
    // singularityintegrate does not apply. SymPy returns SingularityFunction(sin(x), 1, 3)/3, which is
    // wrong: its derivative has the factor cos(x)
    expect(String(integrate(SF(sj.sin(x), 1, 2), x))).toBe('Integral(SingularityFunction(sin(x), 1, 2), x)');
  });
  it('integrates elementary transcendental functions by the Risch algorithm', () => {
    expect(String(integrate(P('exp(x)/(1 + exp(2*x))'), x))).toBe('RootSum(4*_z**2 + 1, Lambda(_i, _i*log(2*_i + exp(x))))');
    expect(String(integrate(P('log(x)/x**3'), x))).toBe('-log(x)/(2*x**2) - 1/(4*x**2)');
    expect(String(integrate(P('log(2*x)'), x))).toBe('x*log(2*x) - x');
    expect(integrate(P('log(x)**30'), x).toString().slice(0, 40)).toBe('x*log(x)**30 - 30*x*log(x)**29 + 870*x*l');
    // proven nonelementary: left unevaluated (SymPy then finds Ei(exp(x)) for exp(exp(x)) with other methods)
    expect(String(integrate(P('x**x'), x))).toBe('Integral(x**x, x)');
    // trigonometric (SymPy trigintegrate) and algebraic integrands are not for the Risch algorithm
    expect(String(integrate(P('1/sin(y)'), y))).toBe('log(cos(y) - 1)/2 - log(cos(y) + 1)/2');
    expect(String(integrate(P('sqrt(exp(x) + 1)/x'), x))).toBe('Integral(sqrt(exp(x) + 1)/x, x)');
  });
  it('keeps the nonelementary part of a Risch result', () => {
    // SymPy: x*log(x*exp(-x) + 1) + Integral((x**2 - x)/(x + exp(x)), x)
    expect(String(integrate(P('log(x/exp(x) + 1)'), x))).toBe('x*log(x*exp(-x) + 1) + Integral((x**2 - x)/(x + exp(x)), x)');
  });
});

describe('square roots of quadratics (SymPy manualintegrate)', () => {
  it('match SymPy', () => {
    const x = new Sym('x');
    const I = (t: string): string => sstr(integrate(parse(t), x));
    expect(I('sqrt(x**2 + 1)')).toBe('x*sqrt(x**2 + 1)/2 + asinh(x)/2');
    expect(I('sqrt(4*x**2 + 1)')).toBe('x*sqrt(4*x**2 + 1)/2 + asinh(2*x)/4');
    expect(I('sqrt(x**2 + 4)')).toBe('x*sqrt(x**2 + 4)/2 + 2*asinh(x/2)');
    expect(I('sqrt(1 - x**2)')).toBe('x*sqrt(1 - x**2)/2 + asin(x)/2');
    // SymPy: (x/2 + 1/4)*sqrt(x**2 + x) - log(2*x + 2*sqrt(x**2 + x) + 1)/8
    // (the logarithm differs from SymPy's by the constant log(2)/8)
    expect(I('sqrt(x**2 + x)')).toBe('(2*x + 1)*sqrt(x**2 + x)/4 - log(x + sqrt(x**2 + x) + 1/2)/8');
    expect(I('sqrt(x**2 - 1)')).toBe('x*sqrt(x**2 - 1)/2 - log(x + sqrt(x**2 - 1))/2');
    // SymPy: (x/2 + 1/4)*sqrt(x**2 + x + 1) + 3*asinh(2*sqrt(3)*(x + 1/2)/3)/8
    expect(I('sqrt(x**2 + x + 1)')).toBe('(2*x + 1)*sqrt(x**2 + x + 1)/4 + 3*asinh(sqrt(3)*(2*x + 1)/3)/8');
    const t = new Sym('t', { real: true });
    expect(sstr(integrate(parse('sqrt(4*t**2 + 1)').subs(new Sym('t'), t), t, [2, 5]))).toBe('-sqrt(17) - asinh(4)/4 + asinh(10)/4 + 5*sqrt(101)/2');
    // a perfect square (SymPy SqrtQuadraticDenomRule)
    expect(I('sqrt(x**2 + 2*x + 1)')).toBe('(x/2 + 1/2)*sqrt(x**2 + 2*x + 1)');
    expect(I('sqrt(x**2)')).toBe('x*sqrt(x**2)/2');
    expect(I('sqrt(4*x**2 - 4*x + 1)')).toBe('(x/2 - 1/4)*sqrt(4*x**2 - 4*x + 1)');
    expect(I('x**2*sqrt(x**2)')).toBe('x**3*sqrt(x**2)/4');
    // SymPy (heurisch): sqrt(x**2)*exp(x) - sqrt(x**2)*exp(x)/x
    expect(I('sqrt(x**2)*exp(x)')).toBe('Integral(sqrt(x**2)*exp(x), x)');
    expect(I('sqrt(x**2 + 1)*x**2')).toBe(I('x**2*sqrt(x**2 + 1)'));
    // SymPy: x**3*sqrt(a + x**2)/4 + a*x*sqrt(a + x**2)/8 - a**2*asinh(x/sqrt(a))/8 (with symbolic a)
    expect(I('x**2*sqrt(x**2 + a)')).toBe('-a**2*Piecewise((log(2*x + 2*sqrt(a + x**2)), Ne(a, 0)), (x*log(x)/sqrt(x**2), True))/8 + sqrt(a + x**2)*(a*x/8 + x**3/4)');
    // (SymPy: sqrt(a)*x*sqrt(1 + x**2/a)/2 + a*asinh(x/sqrt(a))/2)
    expect(I('sqrt(x**2 + a)')).toBe('a*Piecewise((log(2*x + 2*sqrt(a + x**2)), Ne(a, 0)), (x*log(x)/sqrt(x**2), True))/2 + x*sqrt(a + x**2)/2');
    expect(I('sqrt(x**3 + 1)')).toBe('Integral(sqrt(x**3 + 1), x)');
  });
});

describe('definite integrals of Piecewise conditions and delta functions (sympy.stats needs them)', () => {
  const w = new Sym('w', { positive: true });
  const oo = sj.S.Infinity;
  const noo = sj.S.NegativeInfinity;
  const PW = (...p: [Expr, Expr | boolean][]): Expr => sj.piecewise(...p);
  it('joins the antiderivatives continuously across a lower branch bound', () => {
    const value = integrate(PW([x, sj.Gt(x, 1)], [sj.S.One, true]), x);
    expect(sstr(value)).toBe('Piecewise((x, x <= 1), (x**2/2 + 1/2, True))');
    expect(value.subs(x, 1).equals(sj.S.One)).toBe(true);
  });
  it('conditions decided on the interval', () => {
    expect(sstr(integrate(PW([sj.S.One, sj.Gt(x, 0)], [sj.S.Zero, true]), x, [2, 1]))).toBe('-1');
    expect(sstr(integrate(PW([x, sj.Gt(x, -1)], [sj.S.Zero, true]), x, [0, 1]))).toBe('1/2');
    expect(sstr(integrate(PW([x, sj.Lt(x, 2)], [sj.S.Zero, true]), x, [0, 1]))).toBe('1/2');
    expect(sstr(integrate(PW([x, sj.Lt(x, 1)], [sj.S.Zero, true]), x, [0, 2]))).toBe('1/2');
    // x = 1/2 is a single point
    expect(sstr(integrate(PW([x, sj.Eq(x, sj.S.Half)], [sj.S.One, true]), x, [0, 1]))).toBe('1');
    const real = new Sym('x', { real: true });
    expect(sstr(integrate(PW([sj.mul(real, sj.exp(sj.mul(-1, sj.pow(real, 2)))), sj.and(sj.Gt(real, noo), sj.Lt(real, oo))], [sj.S.Zero, true]), real, [noo, oo]))).toBe('0');
    expect(sstr(integrate(PW([sj.S.One, sj.Lt(a, x)], [sj.S.Zero, true]), x, [0, 1]))).toBe('1 - Min(1, Max(0, a))');
  });
  it('a product with a Piecewise factor', () => {
    expect(sstr(integrate(sj.mul(x, PW([sj.S.One, sj.Lt(x, sj.S.Half)], [sj.Rational.of(2), true])), x, [0, 1]))).toBe('7/8');
  });
  it('a singularity left or right of an interval with a symbolic end', () => {
    expect(sstr(integrate(sj.pow(x, -1), x, [1, sj.add(1, w)]))).toBe('log(w + 1)');
    expect(sstr(integrate(sj.pow(x, -1), x, [sj.sub(-1, w), -1]))).toBe('-log(-w - 1) + I*pi');
  });
  it('DiracDelta over the real line (Heaviside at the infinite ends)', () => {
    const e = sj.exp(sj.mul(-1, sj.pow(x, 2)));
    expect(sstr(integrate(sj.mul(sj.DiracDelta(sj.sub(x, y)), e), x, [noo, oo]))).toBe('exp(-y**2)');
    expect(sstr(integrate(sj.mul(sj.DiracDelta(sj.sub(y, x)), e), x, [noo, oo]))).toBe('exp(-y**2)');
    expect(sstr(integrate(sj.mul(sj.DiracDelta(sj.sub(sj.mul(c, x), 1)), e), x, [noo, oo]))).toBe('exp(-1/c**2)/Abs(c)');
    expect(sstr(integrate(sj.mul(sj.DiracDelta(x), e), x, [noo, oo]))).toBe('1');
    expect(sstr(integrate(sj.mul(sj.DiracDelta(sj.mul(c, x)), e), x, [noo, oo]))).toBe('1/Abs(c)');
    expect(sstr(integrate(sj.mul(sj.Heaviside(sj.sin(y)), sj.DiracDelta(x), e), x, [noo, oo]))).toBe('Heaviside(sin(y))');
    expect(sstr(integrate(sj.mul(sj.DiracDelta(x), sj.Heaviside(sj.sub(sj.pow(x, 2), 1)), e), x, [noo, oo]))).toBe('0');
    expect(sstr(integrate(sj.mul(sj.Heaviside(sj.sin(x)), sj.DiracDelta(sj.sub(x, 1))), x, [noo, oo]))).toBe('1');
  });
});

describe('Heaviside at the infinite ends of an integral (internal)', () => {
  const H = sj.Heaviside;
  const at = (e: Expr, p: Expr): string => sstr(heavisideAtInfinity(e, x, p));
  it('a linear argument with a known sign of the coefficient', () => {
    expect(at(H(sj.add(x, y)), sj.S.Infinity)).toBe('1');
    expect(at(H(sj.add(x, y)), sj.S.NegativeInfinity)).toBe('0');
    expect(at(H(sj.sub(y, x)), sj.S.Infinity)).toBe('0');
    expect(at(H(sj.sub(y, x)), sj.S.NegativeInfinity)).toBe('1');
  });
  it('other arguments are kept', () => {
    expect(at(H(sj.mul(c, x)), sj.S.Infinity)).toBe('Heaviside(c*x)');
    expect(at(H(y), sj.S.Infinity)).toBe('Heaviside(y)');
    expect(at(H(sj.pow(x, 2)), sj.S.Infinity)).toBe('Heaviside(x**2)');
    expect(at(H(sj.sin(x)), sj.S.Infinity)).toBe('Heaviside(sin(x))');
    expect(at(H(x), sj.S.One)).toBe('Heaviside(x)');
  });
});

describe('rational, trigonometric and Piecewise integrands as SymPy integrates them', () => {
  const lam = new Sym('lambda', { positive: true });
  const Q = (s: string) => parse(s, { symbols: [rr, lam] });
  it.each([
    // ratint on the whole fraction (risch_integrate's base case)
    ['1/(x**2+2*a*x+a**2)', 'x', '-1/(a + x)'],
    ['x/(x**2+2*a*x+a**2)', 'x', 'a/(a + x) + log(a + x)'],
    ['1/(x+a)**3', 'x', '-1/(2*a**2 + 4*a*x + 2*x**2)'],
    ['1/x+1/(x+1)', 'x', 'log(x**2 + x)'],
    // the Risch algorithm before the heuristics for exponentials
    ['-exp(r)/(2*exp(r)-4)', 'r', '-log(exp(r) - 2)/2'],
    ['exp(r)/(3*exp(r)+1)', 'r', 'log(exp(r) + 1/3)/3'],
    // trigintegrate and heurisch in tan(u/2), with the floor term of a continuous arctangent
    ['1/(sin(x)*cos(x))', 'x', '-log(sin(x)**2 - 1)/2 + log(sin(x))'],
    ['sin(x)**2*cos(x)**2', 'x', 'x/8 - sin(2*x)*cos(2*x)/16'],
    ['(sin(r)+1)/(2*(sin(r)-1))', 'r', 'r*tan(r/2)/(2*tan(r/2) - 2) - r/(2*tan(r/2) - 2) + 4/(2*tan(r/2) - 2)'],
    ['1/(1+sin(y))', 'y', '-2/(tan(y/2) + 1)'],
    ['1/(2+cos(x))', 'x', '2*sqrt(3)*(atan(sqrt(3)*tan(x/2)/3) + pi*floor((x/2 - pi/2)/pi))/3'],
    ['cos(y)/(2+cos(y))', 'y', 'y - 4*sqrt(3)*(atan(sqrt(3)*tan(y/2)/3) + pi*floor((y/2 - pi/2)/pi))/3'],
    // sqrt_quadratic_rule
    ['x*sqrt(x**2+a*x+b)', 'x', '(-a*b/12 - a*(-a**2/8 + b/3)/2)*Piecewise((log(a + 2*x + 2*sqrt(a*x + b + x**2)), Ne(a**2/4 - b, 0)), ((a/2 + x)*log(a/2 + x)/sqrt((a/2 + x)**2), True)) + sqrt(a*x + b + x**2)*(-a**2/8 + a*x/12 + b/3 + x**2/3)'],
    ['(x**2+1)*sqrt(a*x**2+b*x+c)', 'x', 'Piecewise(((c - b*(b - b*c/(12*a) - 3*b*(a + c/4 - 5*b**2/(48*a))/(4*a))/(2*a) - c*(a + c/4 - 5*b**2/(48*a))/(2*a))*Piecewise((log(2*sqrt(a)*sqrt(a*x**2 + b*x + c) + 2*a*x + b)/sqrt(a), Ne(c - b**2/(4*a), 0)), ((x + b/(2*a))*log(x + b/(2*a))/sqrt(a*(x + b/(2*a))**2), True)) + sqrt(a*x**2 + b*x + c)*(x**3/4 + b*x**2/(24*a) + x*(a + c/4 - 5*b**2/(48*a))/(2*a) + (b - b*c/(12*a) - 3*b*(a + c/4 - 5*b**2/(48*a))/(4*a))/a), Ne(a, 0)), (2*(-2*c*(b*x + c)**(5/2)/(5*b**2) + (b**2 + c**2)*(b*x + c)**(3/2)/(3*b**2) + (b*x + c)**(7/2)/(7*b**2))/b, Ne(b, 0)), (sqrt(c)*(x**3/3 + x), True))'],
    ['log(x)/x**3', 'x', '-log(x)/(2*x**2) - 1/(4*x**2)'],
    // the condition Ne(1 - 1/(4*a), 0) is made canonical as Ne(1/a, 4)
    ['sqrt(a*x**2 + x + 1)', 'x', 'Piecewise(((1/2 - 1/(8*a))*Piecewise((log(2*sqrt(a)*sqrt(a*x**2 + x + 1) + 2*a*x + 1)/sqrt(a), Ne(1/a, 4)), ((x + 1/(2*a))*log(x + 1/(2*a))/sqrt(a*(x + 1/(2*a))**2), True)) + (x/2 + 1/(4*a))*sqrt(a*x**2 + x + 1), Ne(a, 0)), (2*(x + 1)**(3/2)/3, True))'],
    // a constant times a Piecewise is folded into one Piecewise (SymPy piecewise_fold)
    ['2*Piecewise((x, x < 1), (0, True))', 'x', 'Piecewise((x**2, x < 1), (1, True))'],
    ['a*Piecewise((x, x < 1), (0, True))', 'x', 'Piecewise((a*x**2/2, x < 1), (a/2, True))'],
    // conditions free of the integration variable (SymPy Piecewise._handle_irel)
    ['Piecewise((x,(y>0)&(z>0)),(1,True))', 'x', 'Piecewise((x**2/2, (y > 0) & (z > 0)), (x, True))'],
    ['Piecewise((x,y>0),(x**2,y<-1),(1,True))', 'x', 'Piecewise((x**2/2, (y > 0) & (y < oo)), (x**3/3, (y > -oo) & (y < -1)), (x, True))'],
    ['Piecewise((x,(y>0)&(y<-1)),(1,True))', 'x', 'x'],
    ['Piecewise((x,y>z),(1,True))', 'x', 'Piecewise((x**2/2, y > z), (x, True))'],
    ['Piecewise((exp(-x), y > 0), (0, True))', 'x', 'Piecewise((-exp(-x), (y > 0) & (y < oo)), (0, True))'],
    ['Piecewise((x, y > 0))', 'x', 'Piecewise((x**2/2, (y > 0) & (y < oo)), (nan, True))'],
    // a linear power by the table, a logarithmic part of degree 5 or more by partial fractions
    ['(2*x+1)**(3/2)', 'x', '(2*x + 1)**(5/2)/5'],
    ['(a*x+1)**(-2)', 'x', '-1/(a**2*x + a)'],
    ['(x**6 + x)/((x-1)**2*(x+1)*(x+2)*(x**2+2))', 'x', 'x + 2*log(x - 1)/9 - 31*log(x + 2)/27 - log(x**2 + 2)/27 - 17*sqrt(2)*atan(sqrt(2)*x/2)/54 - 1/(9*x - 9)'],
    ['x**6/((x+1)*(x+2)*(x+3)*(x+4)*(x+5))', 'x', 'x**2/2 - 15*x + log(x + 1)/24 - 32*log(x + 2)/3 + 729*log(x + 3)/4 - 2048*log(x + 4)/3 + 15625*log(x + 5)/24'],
  ])('%s d%s', (f, v, want) => expect(sstr(integrate(Q(f), V(v)))).toBe(want));

  it('differs from SymPy', () => {
    // SymPy: Piecewise((2*(a*x + 1)**(5/2)/(5*a), ...)) without the case a = 0: 2*(a*x + 1)**(5/2)/(5*a) and log(a*x + 1)/a
    expect(sstr(integrate(Q('(a*x+1)**(3/2)'), x))).toBe('Piecewise((2*(a*x + 1)**(5/2)/(5*a), Ne(a, 0)), (x, True))');
    expect(sstr(integrate(Q('1/(a*x+1)'), x))).toBe('Piecewise((log(a*x + 1)/a, Ne(a, 0)), (x, True))');
    // SymPy (ratint, whose Lazard-Rioboo-Trager logarithms combine the factors with the same residue):
    // -log(x + 3) + log(x**4 + 6*x**3 + 10*x**2 + 12*x + 16)/2 - 1/(x - 1); here a logarithmic part of degree 5 or
    // more goes to partial fractions
    expect(sstr(integrate(sj.together(Q('1/(x-1)**2 + x/(x**2+2) + 1/((x+2)*(x+3)*(x+4))')), x))).toBe('log(x + 2)/2 - log(x + 3) + log(x + 4)/2 + log(x**2 + 2)/2 - 1/(x - 1)');
    // SymPy: sqrt(2)*log(x - sqrt(2))/16 - sqrt(2)*log(x + sqrt(2))/16 - sqrt(2)*atan(sqrt(2)*x/2)/8 (the roots of the
    // quartic resultant are not found here; partial fractions give the same function)
    // SymPy (heurisch over the complex roots of 1 + t**4): atan(sqrt(2)*tan(x/2) - 1) - atan(sqrt(2)*tan(x/2) + 1),
    // which differs by a constant on each interval of continuity; no floor term for an argument not linear in tan
    expect(sstr(integrate(Q('sin(x)/(2 - sin(x)**2)'), x))).toBe('atan(tan(x/2)**2)');
    // an antiderivative with symbolic logarithms over an infinite interval: the Meijer G-function integrator
    // (SymPy 1.14)
    expect(sstr(integrate(Q('1/(x**2/2 + y**2/2 + 1)**2'), x, [sj.S.NegativeInfinity, sj.S.Infinity]))).toBe('Piecewise((sqrt(2)*pi*(y**2/2 + 1)/(2*polar_lift(y**2/2 + 1)**(5/2)), (Abs(arg(y**2/2 + 1)) < pi) | ((Abs(arg(y**2/2 + 1)) < pi) & Ne(1/(y**2/2 + 1), 0) & Ne(Abs(arg(y**2/2 + 1)), pi) & Ne(Abs(arg(y**2/2 + 1)), -pi))), (Integral((x**2/2 + y**2/2 + 1)**(-2), (x, -oo, oo)), True))');
    expect(sstr(integrate(Q('1/(x**4-4)'), x))).toBe('sqrt(2)*log(x - sqrt(2))/16 - sqrt(2)*log(x + sqrt(2))/16 - sqrt(2)*atan(sqrt(2)*x/2)/8');
  });

  it('definite', () => {
    const oo = sj.S.Infinity;
    expect(sstr(integrate(Q('Piecewise((exp(-x), y > 0), (0, True))'), x, [0, oo]))).toBe('Piecewise((1, (y > 0) & (y < oo)), (0, True))');
    expect(sstr(integrate(Q('Piecewise((x, y > 0), (x**2, True))'), x, [0, oo]))).toBe('oo');
    expect(sstr(integrate(Q('Piecewise((x, (y >= 0) & (y <= 1)), (0, True))'), x, [0, 1]))).toBe('Piecewise((1/2, (y >= 0) & (y <= 1)), (0, True))');
    // the entropy of an exponential distribution: exponential factors of a logarithm do not vanish
    expect(sstr(integrate(Q('-lambda*exp(-lambda*x)*log(lambda*exp(-lambda*x))'), x, [0, oo]))).toBe('1 - log(lambda)');
    // SymPy: 2*sqrt(3)*pi/3. The denominator is bounded below by 1.
    expect(sstr(integrate(Q('1/(2+cos(x))'), x, [0, Q('2*pi')]))).toBe('2*sqrt(3)*pi/3');
  });
});

it('integrates special functions, odd cosine powers and extension components', () => {
  const I = (s: string) => String(integrate(parse(s), x));
  expect(I('li(x)')).toBe('x*li(x) - Ei(2*log(x))');
  expect(I('Si(x)')).toBe('x*Si(x) + cos(x)');
  expect(I('tanh(2*x)')).toBe('x - log(tanh(2*x) + 1)/2');
  expect(I('sin(x)**2*cos(x)**3')).toBe('-sin(x)**5/5 + sin(x)**3/3');
  expect(I('sin(x)**3*cos(x)**2')).toBe('cos(x)**5/5 - cos(x)**3/3');
  expect(I('exp(pi*x**3)')).toBe('Integral(exp(pi*x**3), x)');
  expect(String(integrate(new sj.Quaternion(x, 0, 0, 0), x, [0, 1]))).toBe('1/2 + 0*i + 0*j + 0*k');
});

it('retains symbolic slopes multiplied by nonzero numeric constants', () => {
  expect(String(integrate(parse('exp(pi*y*x)'), x))).toBe('Piecewise((exp(pi*x*y)/(pi*y), Ne(y, 0)), (x, True))');
});

it('compares reversed Piecewise conditions and infinite breakpoints on a real interval', () => {
  for (const condition of [
    new sj.Rel('Lt', sj.S.NegativeInfinity, x),
    new sj.Rel('Lt', sj.S.Zero, x),
    new sj.Rel('Lt', sj.add(x, -1), x),
  ]) {
    const f = new sj.Mul([x, new sj.Piecewise([sj.S.One, condition, sj.S.Zero, sj.S.true])]);
    expect(String(integrate(f, x, [0, 1]))).toBe('1/2');
  }
  const c = new sj.Rel('Gt', x, sj.S.Zero);
  const f = new sj.Mul([x, new sj.Piecewise([sj.S.One, c, sj.S.Zero, sj.S.true])]);
  const a = new sj.Sym('a', { positive: true });
  expect(integrate(f, x, [a, sj.add(a, 1)]).subs(a, 2).equals(sj.Rational.of(5, 2))).toBe(true);
});

it('integrates absolute trigonometric waves across half-periods', () => {
  expect(String(integrate(parse('Abs(sin(x))'), x, [0, parse('2*pi')]))).toBe('4');
  expect(String(integrate(parse('Abs(cos(2*x))'), x, [parse('pi/4'), 0]))).toBe('-1/2');
  expect(String(integrate(parse('Abs(sin(x-pi/4))'), x, [0, parse('pi/2')]))).toBe('2 - sqrt(2)');
  for (const f of ['Abs(sin(x**2))', 'Abs(sin(exp(x)))', 'Abs(sin(a*x))', 'Abs(sin(x+I/2))']) {
    expect(integrate(parse(f), x, [1, 2])).toBeInstanceOf(sj.Integral);
  }
  expect(integrate(parse('Abs(sin(x))'), x, [0, sj.S.Infinity])).toBeInstanceOf(sj.Integral);
  for (const f of ['Abs(y)', 'Abs(log(y))']) {
    expect(integrate(parse(f), x, [1, 2]).equals(parse(f))).toBe(true);
  }
  const imaginarySlope = sj.fn('abs', [sj.fn('sin', [sj.mul(sj.S.I, x)], { evaluate: false })], { evaluate: false });
  expect(integrate(imaginarySlope, x, [0, 1])).toBeInstanceOf(sj.Integral);
});

it('matches the branch limits of a Piecewise Dirac delta antiderivative', () => {
  const f = sj.piecewise([sj.DiracDelta(sj.add(x, -1)), sj.Lt(x, 2)], [0, true]);
  expect(String(integrate(f, x))).toBe('Piecewise((Heaviside(x - 1), x < 2), (1, True))');
});

it('ignores isolated residue classes when measuring Piecewise intervals', () => {
  const residue = sj.Mod(x, 2);
  expect(String(integrate(sj.piecewise([1, sj.Eq(residue, 1)], [2, true]), x, [0, 5]))).toBe('10');
  expect(String(integrate(sj.piecewise([1, sj.Ne(residue, 1)], [2, true]), x, [0, 5]))).toBe('5');
  const y = new sj.Sym('y');
  const unsupported = [
    sj.Eq(sj.Mod(sj.pow(x, 2), 2), 1),
    sj.Eq(sj.Mod(x, y), 1),
    new sj.Rel('Eq', residue, x),
  ];
  for (const condition of unsupported) {
    expect(integrate(new sj.Piecewise([sj.S.One, condition, sj.S.Two, sj.S.true]), x, [0, 5]))
      .toBeInstanceOf(sj.Integral);
  }
});

it('combines infinite limits with proven finite symbolic endpoints', () => {
  const y = new sj.Sym('y');
  const f = sj.piecewise([1, sj.Lt(sj.sub(x, y), 0)], [0, true]);
  expect(integrate(f, y, [0, sj.S.Infinity])).toBe(sj.S.Infinity);
  expect(integrate(1, y, [sj.S.NegativeInfinity, sj.Max(0, x)])).toBe(sj.S.Infinity);
  expect(String(integrate(1, y, [sj.S.NegativeInfinity, x]))).toBe('x + oo');
  expect(String(integrate(1, y, [x, sj.S.Infinity]))).toBe('-x + oo');
});

describe('absolute values and signs of real polynomials', () => {
  const x = new sjReal.Sym('x', { real: true });
  const p = (s: string) => sjReal.parse(s, { symbols: [x] });
  it.each([
    ['Abs(x)', [-2, 1], '5/2'],
    ['Abs(x**2 - 1)', [-2, 2], '4'],
    ['Abs(x**2 - 3*x)', [-15, 15], '2259'],
    ['sign(x)', [-1, 2], '1'],
    ['sin(x)*sign(x)', ['-pi', 'pi'], '4'],
    ['x**2*sign(x - 2)', [0, 3], '11/3'],
    ['Min(2, x)', [0, 3], '4'],
    ['Max(x**2, x**3)', [0, 2], '49/12'],
  ])('integrates %s over real root intervals', (f, limits, expected) => {
    expect(String(sjReal.integrate(p(f), x, [p(String(limits[0])), p(String(limits[1]))]))).toBe(expected);
  });
  it.each([
    ['Abs(x)', 'Piecewise((-x**2/2, x <= 0), (x**2/2, True))'],
    ['Abs(2*x - 6)', 'Piecewise((-x**2 + 6*x, x <= 3), (x**2 - 6*x + 18, True))'],
    ['exp(-Abs(x))', 'Piecewise((exp(x), x <= 0), (2 - exp(-x), True))'],
    ['sign(2*x - 6)', 'Piecewise((-x, x < 3), (x - 6, True))'],
    ['2*x*sign(x**2 - 1)', 'Piecewise((x**2, x < -1), (2 - x**2, x < 1), (x**2, True))'],
  ])('finds a continuous primitive of %s', (f, expected) => {
    expect(String(sjReal.integrate(p(f), x))).toBe(expected);
  });
  it('leaves nonpolynomial and unresolved signs for other methods', () => {
    for (const f of ['sin(x)', 'Abs(sin(x))', 'Abs(x**4 + x + 1)', 'Min(x, x**2, x**3)', 'Abs(x - a) + Abs(x - b)', 'Abs(a*x)', 'Abs(x**2 + a)']) {
      const r = realIntegrand(p(f), x);
      expect(r).toBeUndefined();
    }
  });

  it('handles a polynomial with no real roots', () => {
    expect(String(realIntegrand(new sjReal.Fn('abs', [p('x**2 + 2*x + 2')]), x))).toBe('x**2 + 2*x + 2');
  });

  it('does not order unrelated real parameters or guess a parameter sign', () => {
    const a = new sjReal.Sym('a', { real: true }), b = new sjReal.Sym('b', { real: true });
    for (const f of ['Abs(x - a) + Abs(x - b)', 'Abs(a*x)']) {
      expect(realIntegrand(sjReal.parse(f, { symbols: [x, a, b] }), x)).toBeUndefined();
    }
  });
});

it('constructs unevaluated integrals with inferred, repeated, or explicit limits', () => {
  expect(String(sj.integral(x))).toBe('Integral(x, x)');
  expect(String(sj.integral(x, [x, 1], [y, 0, 2]))).toBe('Integral(x, (x, 1), (y, 0, 2))');
  expect(String(sj.integral(sj.Eq(x, y), x))).toBe('Eq(Integral(x, x), Integral(y, x))');
  const f = sj.SymFunction('f')(x), dx = diff(f, x);
  for (const variable of [f, dx, new sj.IndexedBase('v').at(x)]) expect(sj.integral(x, variable)).toBeInstanceOf(sj.Integral);
  for (const build of [() => sj.integral(x, sj.add(1, x)), () => sj.integral(1), () => sj.integral(sj.add(x, y)), () => sj.integral(x, []), () => sj.integral(x, 2), () => sj.integral(x, [x, 1, 2, 3])]) expect(build).toThrow(RangeError);
});

it('respects finite summation limits when interchanging sum and integral', () => {
  expect(String(integrate(sj.Sum(sj.mul(x, n), [n, 1, 3]), x))).toBe('3*x**2');
  expect(() => integrate(sj.Sum(n, [n, 1, x]), x)).toThrow(RangeError);
  expect(integrate(sj.Sum(sj.pow(x, n), [n, 1, sj.oo]), x)).toBeInstanceOf(sj.Integral);
  expect(integrate(sj.Sum(sj.pow(x, n), [n, 1, sj.oo]), x, [1, 2])).toBeInstanceOf(sj.Integral);
});

it('computes Fourier coefficients of the Poisson kernel', () => {
  for (const [order, denominator] of [[2, 6], [3, 12], [4, 24]]) {
    const f = P('cos(' + order + '*x)/(5 - 4*cos(x))');
    expect(integrate(f, x, [0, sj.mul(2, sj.pi)]).equals(sj.mul(sj.pi, sj.rational(1, denominator)))).toBe(true);
  }
});

it('uses the positive rate for improper logistic and hyperbolic integrals', () => {
  expect(String(integrate(P('1/(1+2**x)'), x, [0, sj.oo]))).toBe('1');
  expect(String(integrate(P('1/cosh(2*x)'), x, [0, sj.oo]))).toBe('pi/4');
});

it('leaves out exceptional parameter branches only when requested', () => {
  for (const source of ['x**n', '(2*x+1)**n', 'x**n*log(x)']) {
    expect(integrate(P(source), x)).toBeInstanceOf(sj.Piecewise);
    expect(integrate(P(source), x, undefined, { conds: 'none' })).not.toBeInstanceOf(sj.Piecewise);
  }
});

it('evaluates oscillatory improper integrals with the sign of the frequency', () => {
  const value = integrate(P('exp(-2*I*x**2)'), x, [sj.S.NegativeInfinity, sj.oo]);
  expect(value.equals(P('-I*sqrt(pi/2)*exp(I*pi/4)'))).toBe(true);
  expect(String(integrate(P('(cos(3*x)-cos(x))/x'), x, [0, sj.oo]))).toBe('-log(3)');
});

it('uses adjacent Bessel orders for polynomial and reciprocal moments', () => {
  for (const [input, output] of [
    ['besselj(1,x)**2/x', '-(besselj(0,x)**2+besselj(1,x)**2)/2'],
    ['x**2*besselj(0,x)*besselj(1,x)', 'x**2*besselj(1,x)**2/2'],
  ] as const) expect(sj.expand(integrate(P(input), x).sub(P(output))).equals(sj.S.Zero)).toBe(true);
});

it('differentiates logarithmic and hyperbolic primitives at ordinary real points', () => {
  for (const input of ['cos(log(x))', 'x*cosh(2*x)', '1/sinh(x)**2', '(x**2+x)**(-3/2)']) {
    const f = P(input), primitive = integrate(f, x);
    expect(primitive).not.toBeInstanceOf(sj.Integral);
    expect(diff(primitive, x).subs(x, 2).toNumber()).toBeCloseTo(f.subs(x, 2).toNumber(), 12);
  }
});

it('classifies constant integrals with indefinite and symbolic widths', () => {
  expect(sj.isZero(sj.integral(1, pp))).toBe(false);
  expect(sj.isZero(sj.integral(1, [x, y]))).toBe('unknown');
});

it('propagates unexpected failures from endpoint evaluation', () => {
  const original = { ...impl };
  try {
    impl.limit = () => { throw new TypeError('invalid endpoint'); };
    expect(() => integrate(P('1/x**2'), x, [0, 1])).toThrow(TypeError);
  } finally {
    Object.assign(impl, original);
  }
});

it('distinguishes constant Lambert W branches and variable substitution rates', () => {
  const w = P('LambertW(x,-1)');
  expect(integrate(w, x).equals(sj.add(sj.mul(x,w), sj.mul(-1,x), sj.mul(x,sj.pow(w,-1))))).toBe(true);
  for (const input of ['1/sqrt(1+tan(x**2)**2)', 'exp(x**2)*log(x)', '1/sinh(x**2)**2']) {
    expect(integrate(P(input), x)).toBeInstanceOf(sj.Integral);
  }
  const f = P('cos(log(x+1))');
  expect(diff(integrate(f, x), x).subs(x, 2).toNumber()).toBeCloseTo(f.subs(x, 2).toNumber(), 12);
});

it('keeps unsupported algebraic and Bessel primitives unevaluated', () => {
  for (const source of ['LambertW(x,x)', '(x**3+1)**(-3/2)', '(x**2+2*x+1)**(-3/2)', 'besselj(0,x)**3', '1/besselj(0,x)']) {
    const f = P(source);
    expect(integrate(f, x).equals(sj.integral(f, x))).toBe(true);
  }
});

it('checks signs, poles and convergence before using a definite integration rule', () => {
  const radical = 'sqrt(144*sin(x)**4*cos(x)**2+144*cos(x)**4*sin(x)**2)';
  expect(String(integrate(P(radical), x, [P('-pi/4'), 0]))).toBe('3');
  expect(String(integrate(P('(cos(x)+cos(2*x))/x'), x, [0, sj.oo]))).toBe('oo');
  // The radical changes sign inside the square, the Poisson kernel has a
  // pole, or the integrand falls outside the linear-frequency rules.
  for (const [source, lower, upper] of [
    [radical, '-pi/4', 'pi/4'], ['sqrt(sin(x)+2)', '1', '0'], ['sqrt(sin(x)+2)', '0', '1'],
    ['cos(2*x)/(1-cos(x))', '0', '2*pi'], ['cos(x**2)/(3+cos(x))', '0', '2*pi'],
    ['log(log(x))/x**a', '1', 'oo'], ['sin(x)*log(log(x))', '1', 'oo'], ['1/cosh(x**3)', '0', 'oo'],
  ] as const) {
    const f = P(source), a = P(lower), b = P(upper);
    expect(integrate(f, x, [a, b]).equals(sj.integral(f, [x, a, b]))).toBe(true);
  }
});

it('preserves finite sums when concrete evaluation is unavailable', () => {
  const saved = { ...impl };
  delete impl.doit;
  try {
    expect(String(integrate(sj.Sum(sj.mul(x,n), [n,1,3]), x))).toBe('Sum(n*x**2/2, (n, 1, 3))');
  } finally {
    Object.assign(impl, saved);
  }
});

it('integrates order terms only with respect to their expansion variable', () => {
  const f = sj.SymFunction('f')(x);
  expect(String(integrate(new sj.Order([x, x, sj.S.Zero]), x))).toBe('O(x**2)');
  for (const term of [new sj.Order([x, y, sj.S.Zero]), new sj.Order([f, x, sj.S.Zero])]) {
    expect(integrate(term, x).equals(sj.integral(term, x))).toBe(true);
  }
});

it('retains whole definite integrals when no term or applicable kernel can be evaluated', () => {
  const f = sj.SymFunction('f')(x), g = sj.SymFunction('g')(x);
  for (const [body, lo, hi] of [
    [f, sj.S.Zero, sj.mul(2,sj.pi)],
    [sj.add(f,g), sj.S.Zero, sj.S.One],
    [sj.pow(sj.add(1,f),-1), sj.S.Zero, sj.oo],
    [P('cos(x)/sin(x)'), sj.S.NegativeInfinity, sj.S.Two],
  ] as const) expect(integrate(body, x, [lo, hi]).equals(sj.integral(body, [x,lo,hi]))).toBe(true);
});

describe('definite integrals with parametric poles and Gaussian factors (SymPy 1.14 values)', () => {
  const x = new Sym('x'), t = new Sym('t'), y = new Sym('y');
  const l = new Sym('l', { positive: true }), r = new Sym('r', { real: true });
  const P = (src: string) => parse(src, { symbols: { x, t, y, l, r } });
  it('places a pole whose sign is known by assumptions', () => {
    expect(sstr(integrate(P('3*(x - l/2)**2/(l*(x/l + 1)**4)'), x, [0, sj.oo]))).toBe('3*l**2/4');
    expect(sstr(integrate(P('1/(x + l)**2'), x, [0, sj.oo]))).toBe('1/l');
  });
  it('ignores poles off the real axis', () => {
    expect(sstr(integrate(P('1/(x**2 + l**2)'), x, [0, sj.oo]))).toBe('pi/(2*l)');
  });
  it('returns the generic finite-interval value and checks convergence at infinity', () => {
    expect(sstr(integrate(P('1/(x + r)**2'), x, [0, 1]))).toBe('-1/(r + 1) + 1/r');
    expect(sstr(integrate(P('1/(x + r)**2'), x, [0, sj.oo]))).toMatch(/^Piecewise\(\(1\/r, /);
  });
});

it('keeps the given Piecewise integrand in an integral that stays unevaluated (SymPy 1.14)', () => {
  const x = new Sym('x');
  const f = sj.SymFunction('f');
  const p = sj.piecewise([1, sj.Eq(f(x), 1)], [2, sj.Lt(x, 10)], [0, true]);
  expect(sstr(integrate(p, x, [0, 5]))).toBe('Integral(Piecewise((1, Eq(f(x), 1)), (2, x < 10), (0, True)), (x, 0, 5))');
});

it('integrates through the Meijer G-functions when an endpoint limit of the antiderivative is not found', () => {
  expect(sstr(integrate(parse('(besselj(1, x)/x)**2'), new Sym('x'), [0, sj.oo]))).toBe('4/(3*pi)');
});

it('constructs the Integral of a self-integrating integrand through that integrand (SymPy Integral.__new__)', () => {
  const C = sj.CoordSys3D('C');
  const [a, b] = sj.symbols('a b');
  const [i, j] = C.baseVectors();
  const v = sj.add(sj.mul(a, i), sj.mul(b, j));
  expect(String(sj.integral(v, a, b))).toBe('(Integral(a, a, b))*C.i + (Integral(b, a, b))*C.j');
  expect(String(sj.integral(v, [a, 0, 1], [b, 0, 2]))).toBe('(Integral(a, (a, 0, 1), (b, 0, 2)))*C.i + (Integral(b, (a, 0, 1), (b, 0, 2)))*C.j');
  expect(String(sj.integral(sj.mul(a, sj.BaseDyadic(i, j)), a))).toBe('(Integral(a, a))*(C.i|C.j)');
  expect(String(sj.integral(new sj.Quaternion(a, 1, 2, 3), a))).toBe('a**2/2 + a*i + 2*a*j + 3*a*k');
  expect(sj.integral(sj.Vector.zero, a)).toBe(sj.Vector.zero);
  // an unevaluated product integrates as any other expression (SymPy raises an AttributeError)
  expect(sj.integral(sj.Cross(i, j), a).kind).toBe('Integral');
  expect(sj.integral(i, [a, 0]).kind).toBe('Integral');
});

it('keeps singularities and zero slopes separate in elementary integration rules', () => {
  const rate = sj.add(a, b);
  const f = sj.exp(sj.add(sj.mul(rate, x), 1));
  expect(integrate(f, x).subs(a, sj.mul(-1, b)).equals(sj.mul(x, sj.E))).toBe(true);
  const radical = P('sqrt(3*x**2-5)'), point = sj.rational(3, 2);
  expect(diff(integrate(radical, x), x).subs(x, point).toNumber()).toBeCloseTo(radical.subs(x, point).toNumber(), 10);
  for (const source of ['sin(x**2)*sin(x)', 'sin(x**3)**2', 'cos(x**2)**4', 'x*acos(a*x)', 'sqrt(log(x))*x**2', 'li(1/x)']) {
    const body = P(source);
    expect(integrate(body, x).equals(sj.integral(body, x))).toBe(true);
  }
});

it('computes the mean on either side of the unit circle and keeps poles on it', () => {
  const period = [0, sj.mul(2, sj.pi)] as const;
  expect(integrate(P('1/(1+2*exp(I*x))'), x, period)).toBe(sj.S.Zero);
  expect(integrate(P('1/(1+exp(I*x))'), x, period)).toBeInstanceOf(sj.Integral);
  expect(integrate(P('sin(1/x)'), x, [-1, 1])).toBe(sj.S.Zero);
});

it('evaluates the parameter branches of heuristic primitives at both bounds', () => {
  const f = P('cos(a*x+b)');
  const primitive = integrate(f, x, [1, y], { heurisch: true });
  expect(primitive.subs(a, 0).equals(P('y*cos(b)-cos(b)'))).toBe(true);
  expect(integrate(f, x, undefined, { heurisch: true, conds: 'none' }).equals(P('sin(a*x+b)/a'))).toBe(true);
  expect(sj.ask(sj.Q.zero(sj.integral(0, [x, 0, 1])))).toBe(true);
  expect(sj.ask(sj.Q.zero(sj.integral(1, [x, 0, 1])))).toBe(false);
});

it('recognizes uncovered intervals and known nonreal poles', () => {
  expect(integrate(sj.piecewise([1, sj.Gt(x, 2)]), x, [0, pp])).toBe(sj.S.NaN);
  expect(integrate(P('1/(x+I*p)**2'), x, [0, 1]).equals(P('-1/(I*p+1)-I/p'))).toBe(true);
});

it('uses the scaled quadratic primitive and takes one-sided exponential integral limits', () => {
  expect(integrate(P('(a+x**2)**(-3/2)'), x, [0, b]).equals(P('b/(a**(3/2)*sqrt(1+b**2/a))'))).toBe(true);
  expect(integrate(P('(1+x)*exp(-1/x)/x**2'), x, [0, sj.oo])).toBe(sj.oo);
});

it('checks numerical improper bounds with real and imaginary parameter-dependent poles', () => {
  expect(integrate(P('1/(x+I*p)**2'), x, [0, sj.oo]).equals(P('-I/p'))).toBe(true);
  expect(integrate(P('(x+r)**(-1/2)'), x, [0, sj.oo]).has(sj.oo)).toBe(true);
});

it('uses the algebraic primitive for a quadratic without a Meijer G reduction', () => {
  const f = P('(a*x**2+x+1)**(-3/2)');
  const primitive = integrate(f, x);
  expect(integrate(f, x, [0, y]).equals(sj.sub(primitive.subs(x, y), primitive.subs(x, 0)))).toBe(true);
});

it('clips symbolic piecewise intervals with disjunctions, holes and reversed bounds', () => {
  const f = P('Piecewise((1,(x<1)|(x>2)))');
  expect(String(integrate(f, x))).toBe('Piecewise((x, x < 1), (nan, x < 2), (x, True))');
  expect(integrate(P('Piecewise((x,Eq(x,a)),(2,True))'), x, [pp, 0]).equals(sj.mul(-2, pp))).toBe(true);
  expect(String(integrate(P('Piecewise((a,a<b),(2,a<c))'), a))).toContain('Max(b, c)');
});

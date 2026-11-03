// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/integrals/integrate.ts.
// Indefinite and definite integration. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { Sym, parse, integrate, symbols, diff, doit, latex, sstr } from '../../src';
import { Expr } from '../../src/core/nodes';
import { NoMatchResult } from '../../src/core/truth';

// Integrals (integrals/integrate.ts). Expected values are the str() forms printed by SymPy 1.14
// (p is a positive, q a negative and r a real symbol).

const syms = [new Sym('p', { positive: true }), new Sym('q', { negative: true }), new Sym('r', { real: true })];
const P = (s: string) => parse(s, { symbols: syms });
const V = (s: string): Sym => {
  const v = P(s);
  if (!(v instanceof Sym)) throw new TypeError(s);
  return v;
};
const [x, y, z, n, k, a, b, c, m, t] = [V('x'), V('y'), V('z'), V('n'), V('k'), V('a'), V('b'), V('c'), V('m'), V('t')];
const [pp, qq, rr] = [V('p'), V('q'), V('r')];
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
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(P('exp(-a*x**2 + x)'), x)", () => sj.integrate(P('exp(-a*x**2 + x)'), x), "Integral(exp(-a*x**2 + x), x)", "sqrt(pi)*exp(1/(4*a))*erfi((-2*a*x + 1)/(2*sqrt(-a)))/(2*sqrt(-a))"],
    // the same cases, with the condition written as Ne(y*z, 0)
    ["sj.integrate(P('exp(-x**2*y*z)'), x)", () => sj.integrate(P('exp(-x**2*y*z)'), x), "Piecewise((sqrt(pi)*erf(x*sqrt(y*z))/(2*sqrt(y*z)), Ne(y*z, 0)), (x, True))", "Piecewise((x, Eq(y, 0) | Eq(z, 0)), (sqrt(pi)*erf(x*sqrt(y*z))/(2*sqrt(y*z)), True))"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(P('exp(x**3)'), x)", () => sj.integrate(P('exp(x**3)'), x), "Integral(exp(x**3), x)", "exp(-I*pi/3)*gamma(1/3)*lowergamma(1/3, x**3*exp_polar(I*pi))/(9*gamma(4/3))"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(P('sin(x**3)'), x)", () => sj.integrate(P('sin(x**3)'), x), "Integral(sin(x**3), x)", "x**4*gamma(2/3)*hyper((2/3,), (3/2, 5/3), -x**6/4)/(6*gamma(5/3))"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(P('cos(x**2 + 1)'), x)", () => sj.integrate(P('cos(x**2 + 1)'), x), "Integral(cos(x**2 + 1), x)", "sqrt(2)*sqrt(pi)*(cos(1)*fresnelc(sqrt(2)*x/sqrt(pi)) - sin(1)*fresnels(sqrt(2)*x/sqrt(pi)))/2"],
    // the same value for q < 0, written with sqrt(-q)
    ["sj.integrate(P('sin(q*x**2)'), x)", () => sj.integrate(P('sin(q*x**2)'), x), "-3*sqrt(2)*sqrt(pi)*fresnels(sqrt(2)*x*sqrt(-q)/sqrt(pi))*gamma(3/4)/(8*sqrt(-q)*gamma(7/4))", "3*sqrt(2)*sqrt(pi)*fresnels(sqrt(2)*sqrt(q)*x/sqrt(pi))*gamma(3/4)/(8*sqrt(q)*gamma(7/4))"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(P('1/sqrt(4 + x**2)'), x)", () => sj.integrate(P('1/sqrt(4 + x**2)'), x), "Integral(1/sqrt(x**2 + 4), x)", "asinh(x/2)"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(P('1/sqrt(a - x**2)'), x)", () => sj.integrate(P('1/sqrt(a - x**2)'), x), "Integral(1/sqrt(a - x**2), x)", "Piecewise((-I*acosh(x/sqrt(a)), Abs(x**2/a) > 1), (asin(x/sqrt(a)), True))"],
    // completing the square is not implemented
    ["sj.integrate(P('1/sqrt(4 - x**2 + x)'), x)", () => sj.integrate(P('1/sqrt(4 - x**2 + x)'), x), "Integral(1/sqrt(-x**2 + x + 4), x)", "asin(2*sqrt(17)*(x - 1/2)/17)"],
    // log(cosh(x)) differs from SymPy's x - log(tanh(x) + 1) by a constant
    ["sj.integrate(P('tanh(x)'), x)", () => sj.integrate(P('tanh(x)'), x), "log(cosh(x))", "x - log(tanh(x) + 1)"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(P('log(2*x)'), x)", () => sj.integrate(P('log(2*x)'), x), "Integral(log(2*x), x)", "x*log(2*x) - x"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(P('asec(x)'), x)", () => sj.integrate(P('asec(x)'), x), "Integral(asec(x), x)", "x*asec(x) - Piecewise((acosh(x), Abs(x**2) > 1), (-I*asin(x), True))"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(P('sin(x)*cos(2*x)'), x)", () => sj.integrate(P('sin(x)*cos(2*x)'), x), "Integral(sin(x)*cos(2*x), x)", "2*sin(x)*sin(2*x)/3 + cos(x)*cos(2*x)/3"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(P('sin(x)**2*cos(x)**2'), x)", () => sj.integrate(P('sin(x)**2*cos(x)**2'), x), "Integral(sin(x)**2*cos(x)**2, x)", "x/8 - sin(2*x)*cos(2*x)/16"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(P('sin(x**2)**2'), x)", () => sj.integrate(P('sin(x**2)**2'), x), "Integral(sin(x**2)**2, x)", "-5*x*gamma(-5/4)/(8*gamma(-1/4)) + 5*sqrt(pi)*fresnelc(2*x/sqrt(pi))*gamma(-5/4)/(16*gamma(-1/4))"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(P('sin(x)*exp(x)*x'), x)", () => sj.integrate(P('sin(x)*exp(x)*x'), x), "Integral(x*exp(x)*sin(x), x)", "x*exp(x)*sin(x)/2 - x*exp(x)*cos(x)/2 + exp(x)*cos(x)/2"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(P('exp(x)*log(x)'), x)", () => sj.integrate(P('exp(x)*log(x)'), x), "Integral(exp(x)*log(x), x)", "exp(x)*log(x) - Ei(x)"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(P('log(x)**(1/2)*x'), x)", () => sj.integrate(P('log(x)**(1/2)*x'), x), "Integral(x*sqrt(log(x)), x)", "sqrt(2)*(sqrt(2)*x**2*sqrt(-log(x)) + sqrt(pi)*erfc(sqrt(2)*sqrt(-log(x)))/2)*sqrt(log(x))/(4*sqrt(-log(x)))"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(P('exp(a*x)*cos(3*x)'), x)", () => sj.integrate(P('exp(a*x)*cos(3*x)'), x), "Integral(exp(a*x)*cos(3*x), x)", "Piecewise((I*x*exp(-3*I*x)*sin(3*x)/2 + x*exp(-3*I*x)*cos(3*x)/2 + exp(-3*I*x)*sin(3*x)/6, Eq(a, -3*I)), (-I*x*exp(3*I*x)*sin(3*x)/2 + x*exp(3*I*x)*cos(3*x)/2 + exp(3*I*x)*sin(3*x)/6, Eq(a, 3*I)), (a*exp(a*x)*cos(3*x)/(a**2 + 9) + 3*exp(a*x)*sin(3*x)/(a**2 + 9), True))"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(P('exp(x)*sinh(x)'), x)", () => sj.integrate(P('exp(x)*sinh(x)'), x), "Integral(exp(x)*sinh(x), x)", "x*exp(x)*sinh(x)/2 - x*exp(x)*cosh(x)/2 + exp(x)*sinh(x)/2"],
    // the same value with the atan argument factored
    ["sj.integrate(P('1/(x**3 + 1)'), x)", () => sj.integrate(P('1/(x**3 + 1)'), x), "log(x + 1)/3 - log(x**2 - x + 1)/6 + sqrt(3)*atan(sqrt(3)*(2*x - 1)/3)/3", "log(x + 1)/3 - log(x**2 - x + 1)/6 + sqrt(3)*atan(2*sqrt(3)*x/3 - sqrt(3)/3)/3"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(P('1/(x**2 + 1)**2'), x)", () => sj.integrate(P('1/(x**2 + 1)**2'), x), "Integral((x**2 + 1)**(-2), x)", "x/(2*x**2 + 2) + atan(x)/2"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(P('1/(x**4 + 1)'), x)", () => sj.integrate(P('1/(x**4 + 1)'), x), "Integral(1/(x**4 + 1), x)", "-sqrt(2)*log(x**2 - sqrt(2)*x + 1)/8 + sqrt(2)*log(x**2 + sqrt(2)*x + 1)/8 + sqrt(2)*atan(sqrt(2)*x - 1)/4 + sqrt(2)*atan(sqrt(2)*x + 1)/4"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(P('1/(x**2 - y)'), x)", () => sj.integrate(P('1/(x**2 - y)'), x), "Integral(1/(x**2 - y), x)", "sqrt(1/y)*log(x - y*sqrt(1/y))/2 - sqrt(1/y)*log(x + y*sqrt(1/y))/2"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(P('Heaviside(x)'), x)", () => sj.integrate(P('Heaviside(x)'), x), "Integral(Heaviside(x), x)", "x*Heaviside(x)"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(sj.Piecewise([P('x'), P('x < 1')], [P('gamma(x)'), true]), x)", () => sj.integrate(sj.Piecewise([P('x'), P('x < 1')], [P('gamma(x)'), true]), x), "Integral(Piecewise((x, x < 1), (gamma(x), True)), x)", "Piecewise((x**2/2, x < 1), (Integral(gamma(x), (x, 1, x)) + 1/2, True))"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(sj.Piecewise([P('x'), P('x > 1')], [P('1'), true]), x)", () => sj.integrate(sj.Piecewise([P('x'), P('x > 1')], [P('1'), true]), x), "Integral(Piecewise((x, x > 1), (1, True)), x)", "Piecewise((x, x <= 1), (x**2/2 + 1/2, True))"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(sj.Piecewise([P('x'), P('y < 1')], [P('1'), true]), x)", () => sj.integrate(sj.Piecewise([P('x'), P('y < 1')], [P('1'), true]), x), "Integral(Piecewise((x, y < 1), (1, True)), x)", "Piecewise((x**2/2, (y > -oo) & (y < 1)), (x, True))"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(sj.mul(P('2'), sj.Piecewise([P('x'), P('x < 1')], [P('gamma(x)'), true])), x)", () => sj.integrate(sj.mul(P('2'), sj.Piecewise([P('x'), P('x < 1')], [P('gamma(x)'), true])), x), "Integral(2*Piecewise((x, x < 1), (gamma(x), True)), x)", "Piecewise((x**2, x < 1), (2*Integral(gamma(x), x) - 2*Integral(gamma(x), (x, 1)) + 1, True))"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(sj.add(sj.Piecewise([P('x'), P('x < 1')], [P('gamma(x)'), true]), P('x')), x)", () => sj.integrate(sj.add(sj.Piecewise([P('x'), P('x < 1')], [P('gamma(x)'), true]), P('x')), x), "Integral(x + Piecewise((x, x < 1), (gamma(x), True)), x)", "Piecewise((x**2, x < 1), (Integral(x + gamma(x), (x, 1, x)) + 1, True))"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(sj.Piecewise([P('1/x'), P('x > 0')], [P('0'), true]), x, [1, 2])", () => sj.integrate(sj.Piecewise([P('1/x'), P('x > 0')], [P('0'), true]), x, [1, 2]), "Integral(Piecewise((1/x, x > 0), (0, True)), (x, 1, 2))", "log(2)"],
    // the condition is rewritten for x < 0, the piecewise integral is not done
    ["sj.integrate(sj.Piecewise([P('1'), P('y/x < 0')], [P('2'), true]), x, [-2, -1])", () => sj.integrate(sj.Piecewise([P('1'), P('y/x < 0')], [P('2'), true]), x, [-2, -1]), "Integral(Piecewise((1, y > 0), (2, True)), (x, -2, -1))", "Integral(Piecewise((1, y/x < 0), (2, True)), (x, -2, -1))"],
    // the condition is rewritten for x < 0, the piecewise integral is not done
    ["sj.integrate(sj.Piecewise([P('1'), P('y*x**2 < 0')], [P('2'), true]), x, [-2, -1])", () => sj.integrate(sj.Piecewise([P('1'), P('y*x**2 < 0')], [P('2'), true]), x, [-2, -1]), "Integral(Piecewise((1, y < 0), (2, True)), (x, -2, -1))", "Integral(Piecewise((1, x**2*y < 0), (2, True)), (x, -2, -1))"],
    // SymPy raises TypeError
    ["sj.integrate(sj.Piecewise([P('1'), P('y*sin(x) < 0')], [P('2'), true]), x, [-2, -1])", () => sj.integrate(sj.Piecewise([P('1'), P('y*sin(x) < 0')], [P('2'), true]), x, [-2, -1]), "Integral(Piecewise((1, y*sin(x) < 0), (2, True)), (x, -2, -1))", "ERR TypeError"],
    // the condition is rewritten for x < 0, the piecewise integral is not done
    ["sj.integrate(sj.Piecewise([P('1'), P('y*x <= 0')], [P('2'), true]), x, [-2, -1])", () => sj.integrate(sj.Piecewise([P('1'), P('y*x <= 0')], [P('2'), true]), x, [-2, -1]), "Integral(Piecewise((1, y >= 0), (2, True)), (x, -2, -1))", "Integral(Piecewise((1, x*y <= 0), (2, True)), (x, -2, -1))"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(sj.Piecewise([P('1'), P('y*x < 0')], [P('2'), true]), x, [a, 1])", () => sj.integrate(sj.Piecewise([P('1'), P('y*x < 0')], [P('2'), true]), x, [a, 1]), "Integral(Piecewise((1, x*y < 0), (2, True)), (x, a, 1))", "Piecewise((Integral(Piecewise((1, x*y < 0), (2, True)), (x, a, 1)), a < 1), (-Integral(Piecewise((1, x*y < 0), (2, True)), (x, 1, a)), True))"],
    // the limit at oo is left for a symbolic y (SymPy uses the Mellin transform)
    ["sj.integrate(P('x*exp(-y*x)'), x, [0, sj.oo])", () => sj.integrate(P('x*exp(-y*x)'), x, [0, sj.oo]), "Limit(Piecewise(((-x/y - 1/y**2)*exp(-x*y), Ne(y, 0)), (x**2/2, True)), x, oo, dir='-') - Piecewise((-1/y**2, Ne(y, 0)), (0, True))", "Piecewise((y**(-2), Abs(arg(y)) < pi/2), (Integral(x*exp(-x*y), (x, 0, oo)), True))"],
    // the integral diverges: the antiderivative -x**2*cos(x) + 2*x*sin(x) + 2*cos(x) oscillates with unbounded
    // amplitude, so its values at oo fill AccumBounds(-oo, oo) (SymPy's oo*sign(AccumBounds(-1, 1)) - 2 is the
    // same set written unevaluated)
    ["sj.integrate(P('x**2*sin(x)'), x, [0, sj.oo])", () => sj.integrate(P('x**2*sin(x)'), x, [0, sj.oo]), "AccumBounds(-oo, oo)", "oo*sign(AccumBounds(-1, 1)) - 2"],
    // the same value with the fraction expanded
    ["sj.integrate(P('sin(y*x)**2'), x)", () => sj.integrate(P('sin(y*x)**2'), x), "Piecewise((x/2 - sin(x*y)*cos(x*y)/(2*y), Ne(y, 0)), (0, True))", "Piecewise(((x*y/2 - sin(x*y)*cos(x*y)/2)/y, Ne(y, 0)), (0, True))"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(P('x**(y)*log(x)'), x)", () => sj.integrate(P('x**(y)*log(x)'), x), "Integral(x**y*log(x), x)", "Piecewise((x*x**y*y*log(x)/(y**2 + 2*y + 1) + x*x**y*log(x)/(y**2 + 2*y + 1) - x*x**y/(y**2 + 2*y + 1), Ne(y, -1)), (log(x)**2/2, True))"],
    // the case y = 0 is kept (SymPy's form divides by y)
    ["sj.integrate(P('1/(y*x + 1)'), x)", () => sj.integrate(P('1/(y*x + 1)'), x), "Piecewise((log(x*y + 1)/y, Ne(y, 0)), (x, True))", "log(x*y + 1)/y"],
    // the same cases, with the condition written as Ne(y, 0)
    ["sj.integrate(P('2**(y*x)'), x)", () => sj.integrate(P('2**(y*x)'), x), "Piecewise((2**(x*y)/(y*log(2)), Ne(y, 0)), (x, True))", "Piecewise((2**(x*y)/(y*log(2)), Ne(y*log(2), 0)), (x, True))"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(P('sin(x)/x'), x)", () => sj.integrate(P('sin(x)/x'), x), "Integral(sin(x)/x, x)", "Si(x)"],
    // the same value, with the condition written as Ne(y, 0)
    ["sj.integrate(P('x*exp(y*x)'), x)", () => sj.integrate(P('x*exp(y*x)'), x), "Piecewise(((x/y - 1/y**2)*exp(x*y), Ne(y, 0)), (x**2/2, True))", "Piecewise(((x*y - 1)*exp(x*y)/y**2, Ne(y**2, 0)), (x**2/2, True))"],
    // not implemented in symjs (SymPy's result shown)
    ["sj.integrate(P('sin(log(x))'), x)", () => sj.integrate(P('sin(log(x))'), x), "Integral(sin(log(x)), x)", "x*sin(log(x))/2 - x*cos(log(x))/2"],
    // differs from SymPy's log(cos(x)) + 1/(2*cos(x)**2) by a constant
    ["sj.integrate(P('tan(x)**3'), x)", () => sj.integrate(P('tan(x)**3'), x), "-log(tan(x)**2 + 1)/2 + tan(x)**2/2", "log(cos(x)) + 1/(2*cos(x)**2)"],
    // integration by parts stops at a nesting depth of 24
    ["sj.integrate(P('log(x)**30'), x).toString().slice(0, 40)", () => sj.integrate(P('log(x)**30'), x).toString().slice(0, 40), "Integral(log(x)**30, x)", "x*log(x)**30 - 30*x*log(x)**29 + 870*x*l"],
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
    ["sj.integrate(P('x*(x**2 + 1)**(-3)'), x)", () => sj.integrate(P('x*(x**2 + 1)**(-3)'), x), "-1/(4*(x**2 + 1)**2)", "-1/(4*x**4 + 8*x**2 + 4)"],
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
    ['cos(x)/sin(x)', '1', '2'], // log(sin(2)) - log(sin(1))
    ['1/(x-y)**2', '0', '1'], // depends on whether y lies in the interval
    ['(4*x**3+1)/(x**4+x+1)', '0', '1'], // log(3)
    ['1/x**2', '1', 'a'], // depends on a (a > 0 gives 1 - 1/a)
    ['1/x**2', 'a', '1'],
  ])('%s on [%s, %s]', (f, lo, hi) => {
    expect(integrate(P(f), x, [P(lo), P(hi)])).toBeInstanceOf(sj.Integral);
  });
  it('keeps symbolic endpoints when the primitive extends continuously', () => {
    // SymPy: integrate(log(x), (x, 1, a))
    expect(String(integrate(P('log(x)'), x, [1, a]))).toBe('a*log(a) - a + 1');
  });
});

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/functions/special.ts.
//
// The special functions (gamma, zeta, error functions, LambertW and others): evaluation rules,
// derivatives, expand_func and double-precision numerics. Expected values are str() results of SymPy
// 1.14 (mpmath 1.3 values for the numerics) unless a comment says otherwise.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { acosh, asec, asech, atan, atan2, beta, binomial, catalan, ceiling, diff, digamma, E, E1, erf, erf2, erf2inv, erfc, erfcinv, erfi, erfinv, evalf, expandFunc, factorial, factorial2, ff, Float, float, fresnelc, fresnels, harmonic, LambertW, Li, li, lowergamma, Max, Min, NotImplementedError, parse, polygamma, pow, Rational, Rem, rf, S, subfactorial, Sym, symbols, toComplex, trigamma, uppergamma, zeta } from '../../src';
import { impl } from '../../src/core/nodes';

const [x] = symbols('x');
const y = new Sym('y');
// ---- table harness: each case is [kind, SymPy source, str() of the SymPy 1.14 result or [re, im]] ----
type Case = [kind: string, src: string, expected: string | [number, number]];
const locals = {
  p: new sj.Sym('p', { positive: true }),
  q: new sj.Sym('q', { positive: true }),
  n: new sj.Sym('n', { integer: true }),
  k: new sj.Sym('k', { integer: true }),
  m: new sj.Sym('m', { integer: true, positive: true }),
  r: new sj.Sym('r', { real: true }),
  ng: new sj.Sym('ng', { negative: true }),
  nn: new sj.Sym('nn', { nonnegative: true }),
  // functions the parser does not know by name
  bernoulli: sj.bernoulli,
  euler: sj.euler,
  genocchi: sj.genocchi,
  bell: (n: sj.Expr, a?: sj.Expr) => sj.bell(n, a),
  fibonacci: sj.fibonacci,
  lucas: sj.lucas,
  tribonacci: sj.tribonacci,
  partition: sj.partition,
  mobius: sj.mobius,
  primenu: sj.primenu,
  primeomega: sj.primeomega,
  multigamma: sj.multigamma,
  frac: sj.frac,
  totient: sj.totient,
  reduced_totient: sj.reducedTotient,
  divisor_sigma: sj.divisorSigma,
  primepi: sj.primepi,
  // bell(n, k, (a, b, ...)) of SymPy
  bellx: (n: sj.Expr, k: sj.Expr, ...xs: sj.Expr[]) => sj.bell(n, k, xs),
};
/** Parse a SymPy expression with the symbols and functions above. */
const P = (src: string): sj.Expr => sj.parse(src, { locals });
/** NV sources are `expr;x=1.5;y=0.5+2i`: the numeric values of the free symbols. */
function numericValues(spec: string[]): Record<string, number | { re: number; im: number }> {
  const vals: Record<string, number | { re: number; im: number }> = {};
  for (const item of spec) {
    const [name = '', v = ''] = item.split('=');
    const c = /^([-+]?[\d.]+)([-+][\d.]+)i$/.exec(v);
    vals[name] = c ? { re: Number(c[1]), im: Number(c[2]) } : Number(v);
  }
  return vals;
}
/** str() of the SymPy operation named by the case kind, or the double-precision value for N / NV. */
function run(kind: string, src: string): string | [number, number] {
  if (kind === 'N' || kind === 'NV') {
    const [e = '', ...vals] = src.split(';');
    const c = sj.toComplex(P(e), numericValues(vals));
    return [c.re, c.im];
  }
  const e = P(src);
  switch (kind) {
    case 'D':
      return String(sj.diff(e, x));
    case 'EF':
      return String(sj.expandFunc(e));
    case 'UP':
      return String(sj.unpolarify(e));
    case 'PL':
      return String(sj.polarify(e, { subs: false }));
    case 'C':
      return String(sj.conjugate(e));
    case 'T':
      return String(sj.transpose(e));
    case 'A':
      return String(sj.adjoint(e));
    case 'E':
      return String(sj.expand(e));
    case 'EFl':
      return String(sj.evalf(e));
    default:
      return String(e);
  }
}
function check(cases: readonly Case[]): void {
  it.each(cases)('%s %s', (kind, src, expected) => {
    const got = run(kind, src);
    if (typeof expected === 'string') {
      expect(got).toBe(expected);
      return;
    }
    if (typeof got === 'string') throw new TypeError(`expected a number, got ${got}`);
    const tol = (v: number) => 1e-9 * Math.max(1, Math.abs(v));
    expect(Math.abs(got[0] - expected[0])).toBeLessThanOrEqual(tol(expected[0]));
    expect(Math.abs(got[1] - expected[1])).toBeLessThanOrEqual(tol(expected[1]));
  });
}
const EVAL_CASES: Case[] = [
  ["s", "factorial(-1)", "zoo"],
  ["s", "factorial(-3)", "zoo"],
  ["s", "factorial2(5)", "15"],
  ["s", "factorial2(0)", "1"],
  ["s", "factorial2(6)", "48"],
  ["s", "factorial2(-1)", "1"],
  ["s", "factorial2(-5)", "1/3"],
  ["s", "factorial2(-7)", "-1/15"],
  ["s", "factorial2(x)", "factorial2(x)"],
  ["s", "binomial(x, -1)", "0"],
  ["s", "binomial(3, 5)", "0"],
  ["s", "binomial(x, 1)", "x"],
  ["s", "binomial(n, n)", "binomial(n, n)"],
  ["s", "binomial(x, x)", "binomial(x, x)"],
  ["s", "binomial(200001, 200000)", "200001"],
  ["s", "binomial(1/2, 3)", "1/16"],
  ["s", "binomial(x, y)", "binomial(x, y)"],
  ["s", "ff(x, 0)", "1"],
  ["s", "ff(x, 3)", "x*(x - 2)*(x - 1)"],
  ["s", "ff(x, -2)", "1/((x + 1)*(x + 2))"],
  ["s", "ff(x, x)", "FallingFactorial(x, x)"],
  ["s", "ff(n, n)", "factorial(n)"],
  ["s", "ff(x, y)", "FallingFactorial(x, y)"],
  ["s", "ff(5, 2)", "20"],
  ["s", "rf(1, x)", "factorial(x)"],
  ["s", "rf(x, 0)", "1"],
  ["s", "rf(x, 3)", "x*(x + 1)*(x + 2)"],
  ["s", "rf(x, -2)", "1/((x - 2)*(x - 1))"],
  ["s", "rf(x, y)", "RisingFactorial(x, y)"],
  ["s", "subfactorial(0)", "1"],
  ["s", "subfactorial(1)", "0"],
  ["s", "subfactorial(5)", "44"],
  ["s", "subfactorial(6)", "265"],
  ["s", "subfactorial(-1)", "subfactorial(-1)"],
  ["s", "subfactorial(x)", "subfactorial(x)"],
  ["s", "zeta(1)", "zoo"],
  ["s", "zeta(0)", "-1/2"],
  ["s", "zeta(-3)", "1/120"],
  ["s", "zeta(-2)", "0"],
  ["s", "zeta(3)", "zeta(3)"],
  ["s", "zeta(4)", "pi**4/90"],
  ["s", "zeta(6)", "pi**6/945"],
  ["s", "harmonic(oo)", "oo"],
  ["s", "harmonic(oo, 2)", "pi**2/6"],
  ["s", "harmonic(oo, ng)", "nan"],
  ["s", "harmonic(oo, p + 1)", "zeta(p + 1)"],
  ["s", "harmonic(oo, 1/2)", "oo"],
  ["s", "harmonic(oo, 0)", "oo"],
  ["s", "harmonic(oo, x)", "harmonic(oo, x)"],
  ["s", "harmonic(0, x)", "0"],
  ["s", "harmonic(3)", "11/6"],
  ["s", "harmonic(3, 2)", "49/36"],
  ["s", "harmonic(x)", "harmonic(x)"],
  ["s", "catalan(3)", "5"],
  ["s", "catalan(-1)", "-1/2"],
  ["s", "catalan(x)", "catalan(x)"],
  ["s", "gamma(-1/2)", "-2*sqrt(pi)"],
  ["s", "gamma(-3/2)", "4*sqrt(pi)/3"],
  ["s", "gamma(0)", "zoo"],
  ["s", "gamma(-2)", "zoo"],
  ["s", "gamma(oo)", "oo"],
  ["s", "loggamma(0)", "oo"],
  ["s", "loggamma(-2)", "oo"],
  ["s", "loggamma(1)", "0"],
  ["s", "loggamma(2)", "0"],
  ["s", "loggamma(5)", "log(24)"],
  ["s", "loggamma(1/2)", "log(sqrt(pi))"],
  ["s", "loggamma(m/2)", "log(2**(1 - m)*sqrt(pi)*gamma(m)/gamma(m/2 + 1/2))"],
  ["s", "loggamma(x/2)", "loggamma(x/2)"],
  ["s", "loggamma(oo)", "oo"],
  ["s", "loggamma(-oo)", "zoo"],
  ["s", "loggamma(m)", "log(gamma(m))"],
  ["s", "loggamma(-m)", "oo"],
  ["s", "loggamma(n)", "loggamma(n)"],
  ["s", "loggamma(x)", "loggamma(x)"],
  ["s", "polygamma(1, oo)", "0"],
  ["s", "polygamma(0, oo)", "oo"],
  ["s", "polygamma(1, -oo)", "polygamma(1, -oo)"],
  ["s", "polygamma(2, I*oo)", "polygamma(2, oo*I)"],
  ["s", "polygamma(-1, x)", "loggamma(x) - log(2*pi)/2"],
  ["s", "polygamma(0, -2)", "zoo"],
  ["s", "polygamma(0, 0)", "zoo"],
  ["s", "polygamma(0, 1)", "-EulerGamma"],
  ["s", "polygamma(0, 3)", "3/2 - EulerGamma"],
  ["s", "polygamma(0, 1/2)", "-2*log(2) - EulerGamma"],
  ["s", "polygamma(0, 1/3)", "-log(3) - sqrt(3)*pi/6 - EulerGamma - log(sqrt(3))"],
  ["s", "polygamma(0, 7/2)", "-2*log(2) - EulerGamma + 46/15"],
  ["s", "polygamma(0, -1/2)", "-2*log(2) - EulerGamma + 2"],
  ["s", "polygamma(0, -4/3)", "-log(3) - EulerGamma - log(sqrt(3)) + sqrt(3)*pi/6 + 15/4"],
  ["s", "polygamma(0, 1/7)", "polygamma(0, 1/7)"],
  ["s", "polygamma(1, 1)", "pi**2/6"],
  ["s", "polygamma(2, 3)", "9/4 - 2*zeta(3)"],
  ["s", "polygamma(1, 1/2)", "pi**2/2"],
  ["s", "polygamma(1, x)", "polygamma(1, x)"],
  ["s", "LambertW(x, 0)", "LambertW(x)"],
  ["s", "LambertW(0)", "0"],
  ["s", "LambertW(E)", "1"],
  ["s", "LambertW(-exp(-1))", "-1"],
  ["s", "LambertW(-log(2)/2)", "-log(2)"],
  ["s", "LambertW(oo)", "oo"],
  ["s", "LambertW(x)", "LambertW(x)"],
  ["s", "LambertW(-exp(-1), -1)", "-1"],
  ["s", "LambertW(0, -1)", "-oo"],
  ["s", "LambertW(x, -1)", "LambertW(x, -1)"],
  ["s", "LambertW(x, 1)", "LambertW(x, 1)"],
  ["s", "uppergamma(2, 0)", "1"],
  ["s", "uppergamma(3, x)", "2*(x**2/2 + x + 1)*exp(-x)"],
  ["s", "uppergamma(-1, x)", "expint(2, x)/x"],
  ["s", "uppergamma(0, x)", "expint(1, x)"],
  ["s", "uppergamma(5/2, x)", "-sqrt(x)*(-x - 3/2)*exp(-x) + 3*sqrt(pi)*erfc(sqrt(x))/4"],
  ["s", "uppergamma(-1/2, x)", "-2*sqrt(pi)*erfc(sqrt(x)) + 2*exp(-x)/sqrt(x)"],
  ["s", "uppergamma(1/2, x)", "sqrt(pi)*erfc(sqrt(x))"],
  ["s", "uppergamma(x, y)", "uppergamma(x, y)"],
  ["s", "lowergamma(x, 0)", "0"],
  ["s", "lowergamma(3, x)", "-2*(x**2/2 + x + 1)*exp(-x) + 2"],
  ["s", "lowergamma(-1, x)", "lowergamma(-1, x)"],
  ["s", "lowergamma(5/2, x)", "3*sqrt(pi)*(-(4*x**(3/2)/(3*sqrt(pi)) + 2*sqrt(x)/sqrt(pi))*exp(-x) + erf(sqrt(x)))/4"],
  ["s", "lowergamma(-1/2, x)", "-2*sqrt(pi)*erf(sqrt(x)) - 2*exp(-x)/sqrt(x)"],
  ["s", "lowergamma(x, y)", "lowergamma(x, y)"],
  ["s", "erf(0)", "0"],
  ["s", "erf(oo)", "1"],
  ["s", "erf(-oo)", "-1"],
  ["s", "erf(I*oo)", "oo*I"],
  ["s", "erf(-I*oo)", "-oo*I"],
  ["s", "erf(erfinv(x))", "x"],
  ["s", "erf(-x)", "-erf(x)"],
  ["s", "erfc(0)", "1"],
  ["s", "erfc(oo)", "0"],
  ["s", "erfc(-oo)", "2"],
  ["s", "erfc(I*oo)", "-oo*I"],
  ["s", "erfc(-I*oo)", "oo*I"],
  ["s", "erfc(erfcinv(x))", "x"],
  ["s", "erfc(-x)", "2 - erfc(x)"],
  ["s", "erfc(x)", "erfc(x)"],
  ["s", "erfi(0)", "0"],
  ["s", "erfi(oo)", "oo"],
  ["s", "erfi(-oo)", "-oo"],
  ["s", "erfi(I*oo)", "I"],
  ["s", "erfi(-I*oo)", "-I"],
  ["s", "erfi(-x)", "-erfi(x)"],
  ["s", "erfinv(0)", "0"],
  ["s", "erfinv(1)", "oo"],
  ["s", "erfinv(-1)", "-oo"],
  ["s", "erfinv(erf(1/2))", "1/2"],
  ["s", "erfinv(erf(x))", "erfinv(erf(x))"],
  ["s", "erfinv(-x)", "erfinv(-x)"],
  ["s", "erfinv(1/2)", "erfinv(1/2)"],
  ["s", "erfcinv(1)", "0"],
  ["s", "erfcinv(0)", "oo"],
  ["s", "erfcinv(2)", "-oo"],
  ["s", "erfcinv(x)", "erfcinv(x)"],
  ["s", "erf2(x, x)", "0"],
  ["s", "erf2(0, y)", "erf(y)"],
  ["s", "erf2(x, 0)", "-erf(x)"],
  ["s", "erf2(oo, y)", "erf(y) - 1"],
  ["s", "erf2(-oo, y)", "erf(y) + 1"],
  ["s", "erf2(x, oo)", "1 - erf(x)"],
  ["s", "erf2(x, -oo)", "-erf(x) - 1"],
  ["s", "erf2(-x, -y)", "-erf2(x, y)"],
  ["s", "erf2(x, y)", "erf2(x, y)"],
  ["s", "erf2inv(x, 0)", "x"],
  ["s", "erf2inv(0, y)", "erfinv(y)"],
  ["s", "erf2inv(oo, y)", "erfcinv(-y)"],
  ["s", "erf2inv(x, y)", "erf2inv(x, y)"],
  ["s", "Ei(0)", "-oo"],
  ["s", "Ei(oo)", "oo"],
  ["s", "Ei(-oo)", "0"],
  ["s", "li(0)", "0"],
  ["s", "li(1)", "-oo"],
  ["s", "li(oo)", "oo"],
  ["s", "li(x)", "li(x)"],
  ["s", "Li(2)", "0"],
  ["s", "Li(x)", "Li(x)"],
  ["s", "Si(0)", "0"],
  ["s", "Si(oo)", "pi/2"],
  ["s", "Si(-oo)", "-pi/2"],
  ["s", "Si(I*x)", "I*Shi(x)"],
  ["s", "Si(2*I*x)", "I*Shi(2*x)"],
  ["s", "Si(I)", "I*Shi(1)"],
  ["s", "Si(-x)", "-Si(x)"],
  ["s", "Shi(0)", "0"],
  ["s", "Shi(oo)", "oo"],
  ["s", "Shi(-oo)", "-oo"],
  ["s", "Shi(I*x)", "I*Si(x)"],
  ["s", "Shi(-x)", "-Shi(x)"],
  ["s", "Ci(0)", "zoo"],
  ["s", "Ci(oo)", "0"],
  ["s", "Ci(x)", "Ci(x)"],
  ["s", "Chi(0)", "zoo"],
  ["s", "Chi(oo)", "oo"],
  ["s", "Chi(x)", "Chi(x)"],
  ["s", "expint(0, z)", "exp(-z)/z"],
  ["s", "expint(-2, z)", "exp(-z)/z + 2*exp(-z)/z**2 + 2*exp(-z)/z**3"],
  ["s", "expint(-1, z)", "exp(-z)/z + exp(-z)/z**2"],
  ["s", "expint(1/2, z)", "sqrt(pi)*erfc(sqrt(z))/sqrt(z)"],
  ["s", "expint(2, z)", "expint(2, z)"],
  ["s", "expint(x, z)", "expint(x, z)"],
  ["s", "fresnels(0)", "0"],
  ["s", "fresnels(oo)", "1/2"],
  ["s", "fresnels(-oo)", "-1/2"],
  ["s", "fresnels(I*oo)", "-I/2"],
  ["s", "fresnels(-I*oo)", "I/2"],
  ["s", "fresnels(I*x)", "-I*fresnels(x)"],
  ["s", "fresnels(-I*x)", "I*fresnels(x)"],
  ["s", "fresnels(-x)", "-fresnels(x)"],
  ["s", "fresnelc(0)", "0"],
  ["s", "fresnelc(oo)", "1/2"],
  ["s", "fresnelc(-oo)", "-1/2"],
  ["s", "fresnelc(I*oo)", "I/2"],
  ["s", "fresnelc(-I*oo)", "-I/2"],
  ["s", "fresnelc(I*x)", "I*fresnelc(x)"],
  ["s", "fresnelc(-x)", "-fresnelc(x)"],
  ["s", "sign(0)", "0"],
  ["s", "sign(-2)", "-1"],
  ["s", "sign(3/2)", "1"],
  ["s", "sign(p)", "1"],
  ["s", "sign(ng)", "-1"],
  ["s", "sign(I)", "I"],
  ["s", "sign(2*x)", "sign(x)"],
  ["s", "sign(-3*x)", "-sign(x)"],
  ["s", "sign(x*y)", "sign(x*y)"],
  ["s", "sign(x + y)", "sign(x + y)"],
  ["s", "floor(5/2)", "2"],
  ["s", "floor(-5/2)", "-3"],
  ["s", "ceiling(-5/2)", "-2"],
  ["s", "ceiling(5/2)", "3"],
  ["s", "ceiling(3)", "3"],
  ["s", "floor(5*I/2)", "2*I"],
  ["s", "ceiling(5*I/2)", "3*I"],
  ["s", "floor(3/2 + 5*I/2)", "1 + 2*I"],
  ["s", "ceiling(3/2 + 5*I/2)", "2 + 3*I"],
  ["s", "floor(I*x)", "floor(I*x)"],
  ["s", "floor(n)", "n"],
  ["s", "floor(n + x)", "n + floor(x)"],
  ["s", "floor(n + x + 1/2)", "n + floor(x + 1/2)"],
  ["s", "floor(sqrt(2))", "1"],
  ["s", "ceiling(pi)", "4"],
  ["s", "floor(E)", "2"],
  ["s", "floor(sqrt(4))", "2"],
  ["s", "floor(subfactorial(1/2))", "floor(subfactorial(1/2))"],
  ["s", "floor(x)", "floor(x)"],
  ["s", "floor(I*sqrt(2))", "I"],
  ["s", "atan2(0, p)", "0"],
  ["s", "atan2(0, ng)", "pi"],
  ["s", "atan2(0, x)", "atan2(0, x)"],
  ["s", "atan2(p, 0)", "pi/2"],
  ["s", "atan2(ng, 0)", "-pi/2"],
  ["s", "atan2(x, 0)", "atan2(x, 0)"],
  ["s", "atan2(1, 1)", "pi/4"],
  ["s", "atan2(1, -1)", "3*pi/4"],
  ["s", "atan2(-1, -1)", "-3*pi/4"],
  ["s", "atan2(1, -sqrt(3))", "5*pi/6"],
  ["s", "atan2(y, p)", "atan2(y, p)"],
  ["s", "atan2(y, x)", "atan2(y, x)"],
  ["s", "atan2(1, 0)", "pi/2"],
  ["s", "Max(oo, x)", "oo"],
  ["s", "Max(x, oo)", "oo"],
  ["s", "Min(oo, x)", "x"],
  ["s", "Min(x, -oo)", "-oo"],
  ["s", "Max(x, -oo)", "x"],
  ["s", "Max(oo, oo)", "oo"],
  ["s", "Max(1, 2, x)", "Max(2, x)"],
  ["s", "Min(1, 2, x)", "Min(1, x)"],
  ["s", "Min(Min(x, y), z)", "Min(x, y, z)"],
  ["s", "Max(x, x + 1)", "x + 1"],
  ["s", "Min(x, Max(y, Min(x, z)))", "Min(x, Max(y, z))"],
  ["s", "Min(x, Max(y, Min(z, Max(x, w))))", "Min(x, Max(y, Min(x, z)))"],
  ["s", "Max(x, y)", "Max(x, y)"],
  ["s", "Max(p, 0)", "p"],
  ["s", "Min(3, 1, 2)", "1"],
  ["s", "Max(pi, 3)", "pi"],
  ["s", "Min(x, y, x)", "Min(x, y)"],
  ["s", "catalan(-2)", "0"],
  ["s", "catalan(-5/2)", "zoo"],
  ["s", "catalan(-1/2)", "zoo"],
  ["s", "catalan(1/2)", "catalan(1/2)"],
  ["s", "binomial(nn, nn)", "1"],
  ["s", "binomial(pi, pi)", "1"],
  ["s", "binomial(nn + 1, nn)", "nn + 1"],
  ["s", "floor(I*n)", "I*n"],
  ["s", "floor(I*(n + x))", "floor(I*(n + x))"],
  ["s", "floor(I*pi)", "3*I"],
  ["s", "ceiling(I*sqrt(2))", "2*I"],
  ["s", "floor(2 + I*sqrt(2))", "2 + I"],
  ["s", "floor(sqrt(2) + 3*I/2)", "1 + I"],
  ["s", "atan2(r, p)", "atan(r/p)"],
  ["s", "erfinv(erf(r))", "r"],
  ["s", "erfinv(-erf(r))", "-r"],
  ["s", "erfinv(-erf(x))", "erfinv(-erf(x))"],
  ["s", "polygamma(-1, 3)", "-log(2*pi)/2 + log(2)"],
  ["s", "polygamma(-1, 0)", "zoo"],
  ["s", "polygamma(2, 1/2)", "-14*zeta(3)"],
  ["s", "polygamma(0, -oo)", "oo"],
  ["s", "polygamma(0, I*oo)", "oo"],
  ["s", "polygamma(0, -I*oo)", "oo"],
  ["s", "expint(3/2, z)", "-2*sqrt(pi)*sqrt(z)*erfc(sqrt(z)) + 2*exp(-z)"],
  ["s", "expint(-1/2, z)", "exp(-z)/z + sqrt(pi)*erfc(sqrt(z))/(2*z**(3/2))"],
  ["s", "expint(5/2, z)", "4*sqrt(pi)*z**(3/2)*erfc(sqrt(z))/3 - 4*z*exp(-z)/3 + 2*exp(-z)/3"],
  ["s", "expint(1, z)", "expint(1, z)"],
  ["s", "expint(-3, z)", "exp(-z)/z + 3*exp(-z)/z**2 + 6*exp(-z)/z**3 + 6*exp(-z)/z**4"],
  ["s", "uppergamma(7/2, x)", "sqrt(x)*(x**2 + 5*x/2 + 15/4)*exp(-x) + 15*sqrt(pi)*erfc(sqrt(x))/8"],
  ["s", "uppergamma(-3/2, x)", "4*sqrt(pi)*erfc(sqrt(x))/3 - (4*x/3 - 2/3)*exp(-x)/x**(3/2)"],
  ["s", "lowergamma(7/2, x)", "15*sqrt(pi)*(-(8*x**(5/2)/(15*sqrt(pi)) + 4*x**(3/2)/(3*sqrt(pi)) + 2*sqrt(x)/sqrt(pi))*exp(-x) + erf(sqrt(x)))/8"],
  ["s", "lowergamma(-3/2, x)", "(4/(3*sqrt(x)) - 2/(3*x**(3/2)))*exp(-x) + 4*sqrt(pi)*erf(sqrt(x))/3"],
  ["s", "lowergamma(3/2, x)", "sqrt(pi)*(-2*sqrt(x)*exp(-x)/sqrt(pi) + erf(sqrt(x)))/2"],
  ["s", "uppergamma(3/2, x)", "sqrt(x)*exp(-x) + sqrt(pi)*erfc(sqrt(x))/2"],
  ["s", "uppergamma(0, p)", "-Ei(-p)"],
  ["s", "uppergamma(1, x)", "exp(-x)"],
  ["s", "lowergamma(1, x)", "1 - exp(-x)"],
  ["s", "uppergamma(-2, x)", "expint(3, x)/x**2"],
  ["s", "uppergamma(x, oo)", "0"],
  ["s", "uppergamma(x, 0)", "uppergamma(x, 0)"],
  ["s", "uppergamma(p, 0)", "gamma(p)"],
  ["s", "lowergamma(0, x)", "lowergamma(0, x)"],
  ["s", "lowergamma(-2, x)", "lowergamma(-2, x)"],
  ["s", "binomial(5, 1/2)", "512/(63*pi)"],
  ["s", "binomial(x, pi)", "gamma(x + 1)/(gamma(1 + pi)*gamma(x - pi + 1))"],
  ["s", "binomial(-2, 1/2)", "zoo"],
  ["s", "binomial(5/2, 3/2)", "5/2"],
  ["s", "uppergamma(-1, 0)", "zoo"],
  ["s", "uppergamma(-1/2, 0)", "zoo"],
  ["s", "uppergamma(1 + I, 0)", "gamma(1 + I)"],
  ["s", "uppergamma(5/2, 0)", "3*sqrt(pi)/4"],
  ["s", "catalan(-3/2)", "zoo"],
  ["s", "catalan(-1/3)", "2**(1/3)*gamma(1/6)/(2*sqrt(pi)*gamma(5/3))"],
  ["s", "Ci(-oo)", "I*pi"],
  ["s", "Chi(-oo)", "oo"],
  ["s", "polygamma(3, 1/2)", "pi**4"],
  ["s", "polygamma(0, 1/6)", "-sqrt(3)*pi/2 - log(6) - log(2) - EulerGamma - log(sqrt(3))"],
  ["s", "polygamma(0, 5/6)", "-log(6) - log(2) - EulerGamma - log(sqrt(3)) + sqrt(3)*pi/2"],
  ["s", "uppergamma(9/2, x)", "-sqrt(x)*(-x**3 - 7*x**2/2 - 35*x/4 - 105/8)*exp(-x) + 105*sqrt(pi)*erfc(sqrt(x))/16"],
  ["s", "uppergamma(-5/2, x)", "-8*sqrt(pi)*erfc(sqrt(x))/15 - (-8*x**2/15 + 4*x/15 - 2/5)*exp(-x)/x**(5/2)"],
  ["s", "lowergamma(9/2, x)", "105*sqrt(pi)*(-(16*x**(7/2)/(105*sqrt(pi)) + 8*x**(5/2)/(15*sqrt(pi)) + 4*x**(3/2)/(3*sqrt(pi)) + 2*sqrt(x)/sqrt(pi))*exp(-x) + erf(sqrt(x)))/16"],
  ["s", "lowergamma(-5/2, x)", "(-8/(15*sqrt(x)) + 4/(15*x**(3/2)) - 2/(5*x**(5/2)))*exp(-x) - 8*sqrt(pi)*erf(sqrt(x))/15"],
  ["s", "expint(-5/2, z)", "exp(-z)/z + 5*exp(-z)/(2*z**2) + 15*exp(-z)/(4*z**3) + 15*sqrt(pi)*erfc(sqrt(z))/(8*z**(7/2))"],
  ["s", "floor(sqrt(2) + I*sqrt(3))", "1 + I"],
];
const NUM_CASES: Case[] = [
  ["N", "gamma(1/3)", [2.6789385347077475, 0.0]],
  ["N", "gamma(-5/3)", [2.411044681236973, 0.0]],
  ["NV", "gamma(x);x=0.5+1.5i", [0.15443097618696283, -0.18052756337372855]],
  ["N", "factorial(1/3)", [0.8929795115692493, 0.0]],
  ["N", "binomial(5/2, 1/3)", [1.5870083613413584, 0.0]],
  ["N", "ff(5/2, 1/3)", [1.4171659513669208, 0.0]],
  ["N", "rf(5/2, 1/3)", [1.2972868013884662, 0.0]],
  ["N", "harmonic(1/2)", [0.6137056388801094, 0.0]],
  ["NV", "harmonic(x, y);x=2.5;y=1", [1.680372305546776, 0.0]],
  ["N", "catalan(1/3)", [0.8490700205447396, 0.0]],
  ["N", "loggamma(1/3)", [0.9854206469277671, 0.0]],
  ["N", "loggamma(-5/2)", [-0.056243716497674054, -9.42477796076938]],
  ["NV", "loggamma(x);x=0.5+2i", [-2.2226558640532583, -0.5925369819770346]],
  ["N", "polygamma(0, 1/7)", [-7.363980242224343, 0.0]],
  ["N", "polygamma(1, 1/3)", [10.095597125427094, 0.0]],
  ["N", "polygamma(2, 1/5)", [-251.47803611443592, 0.0]],
  ["NV", "polygamma(0, x);x=1.5+2i", [0.7998337581729537, 1.1001971357298588]],
  ["NV", "polygamma(3, x);x=20.5", [0.0002496881810853771, 0.0]],
  ["N", "lowergamma(1/3, 2)", [2.6108021202662886, 0.0]],
  ["N", "uppergamma(1/3, 2)", [0.06813641444145914, 0.0]],
  ["N", "beta(1/3, 1/4)", [6.353586485553421, 0.0]],
  ["NV", "beta(x, y);x=2;y=3", [0.08333333333333334, 0.0]],
  ["N", "zeta(5)", [1.03692775514337, 0.0]],
  ["N", "zeta(1/2)", [-1.4603545088095868, 0.0]],
  ["N", "erf(1/3)", [0.36264811176606293, 0.0]],
  ["N", "erf(3)", [0.9999779095030014, 0.0]],
  ["N", "erf(-3)", [-0.9999779095030014, 0.0]],
  ["N", "erf(1/2 + I/3)", [0.5716515782461846, 0.2983796622131996]],
  ["N", "erfc(1/3)", [0.6373518882339371, 0.0]],
  ["N", "erfc(3)", [2.209049699858544e-05, 0.0]],
  ["N", "erfc(-3)", [1.9999779095030015, 0.0]],
  ["N", "erfc(1/2 + I/3)", [0.4283484217538153, -0.2983796622131996]],
  ["N", "erfi(1/3)", [0.3905339043933966, 0.0]],
  ["N", "erfi(1/2 + I)", [0.18797346722338332, 0.9507097283189572]],
  ["NV", "erfinv(x);x=0.5", [0.4769362762044699, 0.0]],
  ["NV", "erfinv(x);x=-0.9", [-1.1630871536766743, 0.0]],
  ["N", "Ei(1/3)", [-0.15809210897115572, 0.0]],
  ["N", "Ei(-1/3)", [-0.8288877453485867, 0.0]],
  ["N", "Ei(1/2 + I)", [0.9228991905567888, 2.3258799201579685]],
  ["N", "li(3)", [2.1635885946671918, 0.0]],
  ["N", "Li(3)", [1.118424814549699, 0.0]],
  ["N", "Si(1/3)", [0.3312825659301884, 0.0]],
  ["N", "Ci(1/3)", [-0.549046117782153, 0.0]],
  ["N", "Shi(1/3)", [0.33539781818871545, 0.0]],
  ["N", "Chi(1/3)", [-0.49348992715987117, 0.0]],
  ["N", "Si(1 + I)", [1.1042226582355816, 0.8824538050079177]],
  ["N", "expint(1, 1/3)", [0.8288877453485867, 0.0]],
  ["N", "expint(3, 1/3)", [0.2848930893772957, 0.0]],
  ["NV", "expint(x, y);x=0;y=0.5", [1.2130613194252668, 0.0]],
  ["N", "expint(2, 1 + I)", [0.01915995085507258, -0.13051696506573468]],
  ["N", "fresnels(1/3)", [0.019350393064622225, 0.0]],
  ["N", "fresnelc(1/3)", [0.3323193728996362, 0.0]],
  ["N", "fresnels(1 + I/2)", [0.3393082523853172, 0.7169788451833594]],
  ["N", "LambertW(1/3)", [0.2576276530497367, 0.0]],
  ["N", "LambertW(-1/5, -1)", [-2.5426413577735265, 0.0]],
  ["NV", "sign(x);x=-2.5", [-1.0, 0.0]],
  ["NV", "sign(x);x=0", [0.0, 0.0]],
  ["NV", "sign(x);x=3+4i", [0.6, 0.8]],
  ["NV", "floor(x);x=2.5", [2.0, 0.0]],
  ["NV", "ceiling(x);x=2.5", [3.0, 0.0]],
  ["NV", "atan2(y, x);x=-1;y=0.5", [2.677945044588987, 0.0]],
  ["NV", "Min(x, y);x=-1;y=0.5", [-1.0, 0.0]],
  ["NV", "Max(x, y);x=-1;y=0.5", [0.5, 0.0]],
  ["N", "loggamma(-1/3)", [1.4017625638156332, -3.141592653589793]],
  ["NV", "loggamma(x);x=-2.5+0.5i", [-0.9350856212982774, -8.87096288524746]],
  ["NV", "loggamma(x);x=-2.5-0.5i", [-0.9350856212982774, 8.87096288524746]],
  ["NV", "loggamma(x);x=3+40i", [-52.689155060822635, 111.40513241545996]],
];
const DIFF_CASES: Case[] = [
  ["D", "factorial(x)", "gamma(x + 1)*polygamma(0, x + 1)"],
  ["D", "catalan(x)", "(polygamma(0, x + 1/2) - polygamma(0, x + 2) + log(4))*catalan(x)"],
  ["D", "gamma(x)", "gamma(x)*polygamma(0, x)"],
  ["D", "loggamma(x)", "polygamma(0, x)"],
  ["D", "polygamma(2, x)", "polygamma(3, x)"],
  ["D", "lowergamma(a, x)", "x**(a - 1)*exp(-x)"],
  ["D", "uppergamma(a, x)", "-x**(a - 1)*exp(-x)"],
  ["D", "beta(x, y)", "(polygamma(0, x) - polygamma(0, x + y))*beta(x, y)"],
  ["D", "beta(y, x)", "(polygamma(0, x) - polygamma(0, x + y))*beta(y, x)"],
  ["D", "erf(x)", "2*exp(-x**2)/sqrt(pi)"],
  ["D", "erfc(x)", "-2*exp(-x**2)/sqrt(pi)"],
  ["D", "erfi(x)", "2*exp(x**2)/sqrt(pi)"],
  ["D", "erf2(x, y)", "-2*exp(-x**2)/sqrt(pi)"],
  ["D", "erf2(y, x)", "2*exp(-x**2)/sqrt(pi)"],
  ["D", "erfinv(x)", "sqrt(pi)*exp(erfinv(x)**2)/2"],
  ["D", "erfcinv(x)", "-sqrt(pi)*exp(erfcinv(x)**2)/2"],
  ["D", "erf2inv(x, y)", "exp(-x**2 + erf2inv(x, y)**2)"],
  ["D", "erf2inv(y, x)", "sqrt(pi)*exp(erf2inv(y, x)**2)/2"],
  ["D", "LambertW(x)", "LambertW(x)/(x*(LambertW(x) + 1))"],
  ["D", "LambertW(x, k)", "LambertW(x, k)/(x*(LambertW(x, k) + 1))"],
  ["D", "Ei(x)", "exp(x)/x"],
  ["D", "li(x)", "1/log(x)"],
  ["D", "Li(x)", "1/log(x)"],
  ["D", "Si(x)", "sin(x)/x"],
  ["D", "Ci(x)", "cos(x)/x"],
  ["D", "Shi(x)", "sinh(x)/x"],
  ["D", "Chi(x)", "cosh(x)/x"],
  ["D", "expint(y, x)", "-expint(y - 1, x)"],
  ["D", "fresnels(x)", "sin(pi*x**2/2)"],
  ["D", "fresnelc(x)", "cos(pi*x**2/2)"],
  ["D", "atan2(x, y)", "y/(x**2 + y**2)"],
  ["D", "atan2(y, x)", "-y/(x**2 + y**2)"],
  ["D", "expint(x, y)", "-y**(x - 1)*meijerg(((), (1, 1)), ((0, 0, 1 - x), ()), y)"],
  ["EF", "gamma(7/3)", "4*gamma(1/3)/9"],
  ["EF", "gamma(-7/3)", "-27*gamma(2/3)/28"],
  ["EF", "gamma(x + 2)", "x*(x + 1)*gamma(x)"],
  ["EF", "gamma(x + 5/2)", "(x + 1/2)*(x + 3/2)*gamma(x + 1/2)"],
  ["EF", "gamma(x - 3/2)", "gamma(x + 1/2)/((x - 3/2)*(x - 1/2))"],
  ["EF", "binomial(x, 3)", "x*(x - 2)*(x - 1)/6"],
  ["EF", "harmonic(x + 2)", "harmonic(x) + 1/(x + 2) + 1/(x + 1)"],
  ["EF", "harmonic(x - 2)", "harmonic(x) - 1/(x - 1) - 1/x"],
  ["EF", "harmonic(x)", "harmonic(x)"],
  ["EF", "expint(3, z)", "z**2*expint(1, z)/2 + (1 - z)*exp(-z)/2"],
  ["EF", "expint(2, z)", "-z*expint(1, z) + exp(-z)"],
  ["EF", "GoldenRatio", "1/2 + sqrt(5)/2"],
  ["EF", "TribonacciConstant", "1/3 + (19 - 3*sqrt(33))**(1/3)/3 + (3*sqrt(33) + 19)**(1/3)/3"],
  ["EF", "sin(gamma(x + 1))", "sin(x*gamma(x))"],
  ["EF", "gamma(1/3)", "gamma(1/3)"],
];
const n = new Sym('n');
const cases: [string, string][] = [
  ['floor(sqrt(2)+2*I)', '1 + 2*I'],
  ['ceiling(sqrt(2)-3*I)', '2 - 3*I'],
  ['floor(sqrt(2)+I/2)', '1'],
  ['floor(sqrt(2)+2*I+x)', 'floor(x + sqrt(2)) + 2*I'],
];

describe('LambertW (SymPy)', () => {
  it('special values and derivative', () => {
    expect(String(LambertW(0))).toBe('0');
    expect(String(LambertW(E))).toBe('1');
    expect(String(LambertW(0, -1))).toBe('-oo');
    expect(String(diff(LambertW(x), x))).toBe('LambertW(x)/(x*(LambertW(x) + 1))');
  });
  it('numeric values on several branches', () => {
    expect(String(LambertW(float(1.2)))).toBe('0.635564016364870');
    expect(String(evalf(LambertW(float(1.2), -1)))).toBe('-1.34747534407696 - 4.41624341514535*I');
    expect(String(evalf(LambertW(1), 30))).toBe('0.567143290409783872999968662210');
    expect(String(evalf(LambertW(Rational.of(-1, 5), -1), 20))).toBe('-2.5426413577735264243');
  });
});

describe('functions: constructors and numerics', () => {
  it('constructors', () => {
    const got = [asec(x), acosh(x), asech(x), harmonic(x, 2), beta(x, y), zeta(x), li(x), Li(x), fresnels(x), fresnelc(x), erfi(x), subfactorial(x), catalan(x), ff(x, 2)].map(String);
    expect(got).toEqual(['asec(x)', 'acosh(x)', 'asech(x)', 'harmonic(x, 2)', 'beta(x, y)', 'zeta(x)', 'li(x)', 'Li(x)', 'fresnels(x)', 'fresnelc(x)', 'erfi(x)', 'subfactorial(x)', 'catalan(x)', 'x*(x - 1)']);
    expect(String(erfcinv(2))).toBe('-oo');
  });
  it('double-precision values with symbol values', () => {
    // SymPy N(binomial(5.5, 2.5)), N(erf(-3)), N(erfc(-0.5))
    expect(toComplex(binomial(x, y), { x: 5.5, y: 2.5 }).re).toBeCloseTo(14.4375, 10);
    expect(toComplex(erf(x), { x: -3 }).re).toBeCloseTo(-0.999977909503001, 12);
    expect(toComplex(erfc(x), { x: -0.5 }).re).toBeCloseTo(1.52049987781305, 12);
  });
});

describe('special functions: evaluation (SymPy eval)', () => check(EVAL_CASES));

describe('special functions: double-precision numerics', () => check(NUM_CASES));

describe('special functions: derivatives and expand_func', () => check(DIFF_CASES));

describe('special functions: cases outside the tables', () => {
  const y = new Sym('y');
  it('factorial2 of a negative even integer is a pole', () => {
    // SymPy raises ValueError; symjs returns the pole zoo of the gamma-based continuation
    expect(String(factorial2(-2))).toBe('zoo');
  });
  it('polygamma(n, oo) stays unevaluated for an order that may be 0', () => {
    // SymPy returns 0, which is wrong when n = 0 (polygamma(0, oo) = oo)
    expect(String(polygamma(y, P('oo')))).toBe('polygamma(y, oo)');
  });
  it('Rem', () => {
    expect(String(Rem(7, 3))).toBe('1');
    expect(String(Rem(-7, 3))).toBe('-1');
    expect(String(Rem(x, x))).toBe('0');
    expect(String(Rem(x, y))).toBe('Rem(x, y)');
  });
  it('digamma and trigamma, evaluated and not', () => {
    expect(String(digamma(1))).toBe('-EulerGamma');
    expect(String(trigamma(1))).toBe('pi**2/6');
    expect(String(digamma(x, { evaluate: false }))).toBe('digamma(x)');
    expect(String(trigamma(x, { evaluate: false }))).toBe('trigamma(x)');
    expect(String(E1(x))).toBe('expint(1, x)');
  });
  it('numerics of functions that evaluate on numbers', () => {
    // SymPy factorial2(7) = 105 and factorial2(6) = 48
    expect(toComplex(factorial2(x), { x: 7 }).re).toBe(105);
    expect(toComplex(factorial2(x), { x: 6 }).re).toBe(48);
    expect(() => toComplex(factorial2(x), { x: 2.5 })).toThrow(RangeError);
    expect(toComplex(erfinv(x), { x: 1 }).re).toBe(Infinity);
    expect(toComplex(erfinv(x), { x: -1 }).re).toBe(-Infinity);
    // mpmath: erfinv(0.7), erfinv(erf(0.2) + 0.3), erf(2/3) - erf(1/3)
    expect(toComplex(erfcinv(x), { x: 0.3 }).re).toBeCloseTo(0.732869077959217, 12);
    expect(toComplex(erf2inv(x, y), { x: 0.2, y: 0.3 }).re).toBeCloseTo(0.502509700700945, 12);
    expect(toComplex(erf2(P('1/3'), P('2/3'))).re).toBeCloseTo(0.2915733020827768, 12);
    expect(() => toComplex(harmonic(x, y), { x: 2, y: 2 })).toThrow(NotImplementedError);
  });
  it('derivatives with respect to an order are not implemented', () => {
    // SymPy: Derivative(polygamma(x, y), x) and meijerg expressions for the incomplete gamma functions
    expect(() => diff(P('polygamma(x, y)'), x)).toThrow(NotImplementedError);
    expect(() => diff(P('lowergamma(x, y)'), x)).toThrow(NotImplementedError);
    expect(() => diff(P('uppergamma(x, y)'), x)).toThrow(NotImplementedError);
  });
});

describe('special functions', () => {
  it.each(cases)('%s', (src, want) => {
    expect(String(parse(src))).toBe(want);
  });
  it('constructors', () => {
    expect(String(rf(x, 2))).toBe('x*(x + 1)');
    expect(String(harmonic(n))).toBe('harmonic(n)');
    expect(String(lowergamma(x, y))).toBe('lowergamma(x, y)');
    expect(String(uppergamma(x, y))).toBe('uppergamma(x, y)');
    expect(String(LambertW(x))).toBe('LambertW(x)');
    expect(String(LambertW(x, -1))).toBe('LambertW(x, -1)');
    expect(String(ceiling(x))).toBe('ceiling(x)');
    // SymPy expand_func(binomial(x, y)) and expand_func(1 + gamma(x + 2))
    expect(String(expandFunc(parse('binomial(x, y)')))).toBe('binomial(x, y)');
    expect(String(expandFunc(parse('1 + gamma(x + 2)')))).toBe('x*(x + 1)*gamma(x) + 1');
  });
  it('special values', () => {
    expect(String(factorial(S.Infinity))).toBe('oo');
    expect(String(binomial(x, 0))).toBe('1');
    expect(String(erfcinv(2))).toBe('-oo');
    expect(String(catalan(new Sym('m', { integer: true, negative: true })))).toBe('catalan(m)');
    // harmonic numbers of a negative order are power sums: SymPy harmonic(3, -2) = 14
    expect(String(harmonic(3, -2))).toBe('14');
  });
  it('binomial with a very large k', () => {
    // SymPy binomial(-5, 100001), binomial(-5, 100002), binomial(100010, 100005)
    expect(String(binomial(-5, 100001))).toBe('-4167250029583975005');
    expect(String(binomial(-5, 100002))).toBe('4167416716251425015');
    expect(String(binomial(100010, 100005))).toBe('83366671958750016270252');
    // SymPy computes this ~60000-digit number; symjs keeps it unevaluated
    expect(String(binomial(-200001, 100001))).toBe('binomial(-200001, 100001)');
  });
  it('more special values', () => {
    // SymPy erfcinv(1/2), harmonic(oo, 1/2), atan2(1, 0.0), atan2(0.0, -1)
    expect(String(erfcinv(S.Half))).toBe('erfcinv(1/2)');
    expect(String(harmonic(S.Infinity, S.Half))).toBe('oo');
    expect(String(atan2(1, new Float(0)))).toBe('pi/2');
    expect(String(atan2(new Float(0), -1))).toBe('pi');
    // the value of 2**-2000 underflows to 0.0 in double precision; SymPy atan2(1, 2**-2000) = atan(2**2000)
    expect(String(atan2(1, pow(2, -2000)))).toBe(String(atan(pow(2, 2000))));
  });
  it('the lambertW hook of the core', () => {
    expect(String(impl.lambertW?.(x, -1))).toBe('LambertW(x, -1)');
  });
  it('atan2 in the left half-plane', () => {
    expect(String(atan2(-1, parse('-sqrt(2)')))).toBe('-pi + atan(sqrt(2)/2)');
    expect(String(atan2(1, parse('-sqrt(2)')))).toBe('pi - atan(sqrt(2)/2)');
  });
  it('Min and Max of numbers ordered numerically', () => {
    // pi - 3 < 1/7 is decided numerically
    expect(String(Min(parse('pi - 3'), parse('1/7'), x))).toBe('Min(x, -3 + pi)');
    expect(String(Max(parse('pi - 3'), parse('1/7'), x))).toBe('Max(1/7, x)');
  });
  it('floor when the imaginary part is numerically an integer but not decided', () => {
    // the imaginary part is 1 (sqrt(5 + 2*sqrt(6)) = sqrt(2) + sqrt(3)); SymPy gives
    // 1 + I*(-sqrt(2*sqrt(6) + 5) + 1 + sqrt(2) + sqrt(3)), symjs keeps floor unevaluated
    expect(String(parse('floor(sqrt(2) + I*(1 + sqrt(2)+sqrt(3)-sqrt(5+2*sqrt(6))))'))).toBe('floor(sqrt(2) + I*(-sqrt(2*sqrt(6) + 5) + 1 + sqrt(2) + sqrt(3)))');
  });
  it('erfc for large arguments (continued fraction)', () => {
    // mpmath erfc(3), erfc(6)
    expect(toComplex(erfc(x), { x: 3 }).re).toBeCloseTo(2.20904969985854e-5, 15);
    expect(toComplex(erfc(x), { x: 6 }).re / 2.15197367124989e-17).toBeCloseTo(1, 10);
  });
});

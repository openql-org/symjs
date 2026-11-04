// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/functions/elementary/complexes.ts.
//
// Polar numbers (exp_polar, polar_lift), periodic_argument, principal_branch, unpolarify, polarify,
// extract_branch_factor and the branch rules of the exponential integrals. Expected values are str()
// results of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../../src';
import { add, diff, expint, expPolar, extractBranchFactor, mul, periodicArgument, polarify, polarLift, pow, principalBranch, S, sin, sqrt, Sym, unbranchedArgument } from '../../../src';
import { isPolar } from '../../../src/functions/elementary/complexes';

// ---- table harness: each case is [kind, SymPy source, str() of the SymPy 1.14 result or [re, im]] ----
type Case = [kind: string, src: string, expected: string | [number, number]];
const x = new sj.Sym('x');
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
  exp_polar: sj.expPolar,
  polar_lift: sj.polarLift,
  periodic_argument: sj.periodicArgument,
  principal_branch: sj.principalBranch,
  unbranched_argument: sj.unbranchedArgument,
  jn: sj.jn,
  yn: sj.yn,
  KroneckerDelta: sj.KroneckerDelta,
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
    case 'EB':
    case 'EBH': {
      const [a, b] = sj.extractBranchFactor(e, kind === 'EBH');
      return `(${String(a)}, ${String(b)})`;
    }
    case 'EF':
      return String(sj.expandFunc(e));
    case 'UP':
      return String(sj.unpolarify(e));
    case 'UPE':
      return String(sj.unpolarify(e, { exponentsOnly: true }));
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
const POLAR_CASES: Case[] = [
  ["s", "exp_polar(0)", "exp_polar(0)"],
  ["s", "exp_polar(I*pi)", "exp_polar(I*pi)"],
  ["s", "polar_lift(4)", "4*exp_polar(0)"],
  ["s", "polar_lift(-4)", "4*exp_polar(I*pi)"],
  ["s", "polar_lift(I)", "exp_polar(I*pi/2)"],
  ["s", "polar_lift(-2*I)", "2*exp_polar(-I*pi/2)"],
  ["s", "polar_lift(1 + I)", "polar_lift(1 + I)"],
  ["s", "polar_lift(oo)", "oo"],
  ["s", "polar_lift(p)", "p*exp_polar(0)"],
  ["s", "polar_lift(2*p)", "2*p*exp_polar(0)"],
  ["s", "polar_lift(p*x)", "p*polar_lift(x)"],
  ["s", "polar_lift(x)", "polar_lift(x)"],
  ["s", "polar_lift(exp_polar(I)*p)", "p*exp_polar(I)"],
  ["s", "polar_lift(exp_polar(I)*x)", "exp_polar(I)*polar_lift(x)"],
  ["s", "polar_lift(exp_polar(I))", "exp_polar(I)"],
  ["s", "periodic_argument(x, -1)", "periodic_argument(x, -1)"],
  ["s", "periodic_argument(x, y)", "periodic_argument(x, y)"],
  ["s", "periodic_argument(principal_branch(x, pi), oo)", "periodic_argument(x, pi)"],
  ["s", "periodic_argument(polar_lift(x), oo)", "arg(x)"],
  ["s", "periodic_argument(polar_lift(x), 2*pi)", "periodic_argument(x, 2*pi)"],
  ["s", "periodic_argument(polar_lift(x), 3*pi)", "periodic_argument(x, 3*pi)"],
  ["s", "periodic_argument(polar_lift(x), pi)", "periodic_argument(polar_lift(x), pi)"],
  ["s", "periodic_argument(2*x, pi)", "periodic_argument(x, pi)"],
  ["s", "periodic_argument(p*x, 2*pi)", "periodic_argument(x, 2*pi)"],
  ["s", "periodic_argument(exp_polar(5*I*pi), 2*pi)", "pi"],
  ["s", "periodic_argument(exp_polar(5*I*pi), oo)", "5*pi"],
  ["s", "periodic_argument(exp_polar(5*I*pi), pi)", "0"],
  ["s", "periodic_argument(exp_polar(3*I)*polar_lift(-1), 2*pi)", "3 - pi"],
  ["s", "periodic_argument(exp_polar(I*x), 2*pi)", "periodic_argument(exp_polar(I*x), 2*pi)"],
  ["s", "periodic_argument(exp_polar(5*I*pi)*x, 2*pi)", "periodic_argument(x*exp_polar(5*I*pi), 2*pi)"],
  ["s", "periodic_argument(polar_lift(x)**2, 2*pi)", "periodic_argument(polar_lift(x)**2, 2*pi)"],
  ["s", "periodic_argument(I, 2*pi)", "pi/2"],
  ["s", "periodic_argument(-1, 2*pi)", "pi"],
  ["s", "periodic_argument(x, 2*pi)", "periodic_argument(x, 2*pi)"],
  ["s", "principal_branch(polar_lift(x), 2*pi)", "principal_branch(x, 2*pi)"],
  ["s", "principal_branch(x, oo)", "x"],
  ["s", "principal_branch(exp_polar(3*I*pi), 2*pi)", "exp_polar(I*pi)"],
  ["s", "principal_branch(exp_polar(3*I*pi)*x, 2*pi)", "principal_branch(x*exp_polar(I*pi), 2*pi)"],
  ["s", "principal_branch(exp_polar(2*I*pi)*x, 2*pi)", "principal_branch(x, 2*pi)"],
  ["s", "principal_branch(exp_polar(4*I*pi)*p, 2*pi)", "p*exp_polar(0)"],
  ["s", "principal_branch(exp_polar(2*I*pi), 2*pi)", "exp_polar(0)"],
  ["s", "principal_branch(3*exp_polar(I*pi/2), 2*pi)", "3*exp_polar(I*pi/2)"],
  ["s", "principal_branch(-1, 2*pi)", "exp_polar(I*pi)"],
  ["s", "principal_branch(x, 2*pi)", "principal_branch(x, 2*pi)"],
  ["s", "principal_branch(exp_polar(I*x), 2*pi)", "principal_branch(exp_polar(I*x), 2*pi)"],
  ["s", "principal_branch(exp_polar(I)*x, 2*pi)", "principal_branch(x*exp_polar(I), 2*pi)"],
  ["s", "principal_branch(2*x, 2*pi)", "2*principal_branch(x, 2*pi)"],
  ["UP", "exp_polar(I*pi)*x", "-x"],
  ["UP", "polar_lift(x)**2", "x**2"],
  ["UP", "principal_branch(x, 2*pi)", "x"],
  ["UP", "principal_branch(x, pi)", "principal_branch(x, pi)"],
  ["UP", "x + 1", "x + 1"],
  ["UP", "sin(polar_lift(x))", "sin(x)"],
  // the arguments of functions that are not unbranched stay polar (SymPy _unpolarify)
  ["UP", "besselj(y, polar_lift(x))", "besselj(y, polar_lift(x))"],
  ["UP", "besselj(y, polar_lift(x))**2 + exp_polar(I*pi)", "besselj(y, polar_lift(x))**2 - 1"],
  ["UP", "log(polar_lift(x))", "log(polar_lift(x))"],
  ["UP", "polar_lift(x)**y", "polar_lift(x)**y"],
  ["UP", "Piecewise((polar_lift(x), y > 0), (1, True))", "Piecewise((polar_lift(x), y > 0), (1, True))"],
  ["UP", "Integral(polar_lift(x), x)", "Integral(polar_lift(x), x)"],
  ["UP", "gamma(polar_lift(x))", "gamma(x)"],
  ["UP", "erf(exp_polar(I*pi)*x)", "-erf(x)"],
  ["UP", "Abs(polar_lift(x)*y)", "Abs(x*y)"],
  ["UP", "sqrt(polar_lift(x)**2)", "x"],
  // relations: Eq and Ne only against 0, the others always; the boolean connectives
  ["UP", "Eq(polar_lift(x), 1)", "Eq(polar_lift(x), 1)"],
  ["UP", "Eq(polar_lift(x), 0)", "Eq(x, 0)"],
  ["UP", "polar_lift(x) > 1", "x > 1"],
  ["UP", "(polar_lift(x) > 0) & Eq(polar_lift(y), 2)", "(x > 0) & Eq(polar_lift(y), 2)"],
  ["PL", "x", "x"],
  ["PL", "2*x + 1", "2*x + 1"],
  ["PL", "exp(x + 1)", "exp(x + 1)"],
  ["PL", "sin(x)*y", "y*sin(x)"],
  ["PL", "x**2", "x**(2*exp_polar(0))"],
  ["PL", "oo", "oo"],
  ["N", "exp_polar(1 + I)", [1.4686939399158851, 2.2873552871788423]],
  ["N", "polar_lift(2 + I)", [2.0, 1.0]],
  ["EFl", "exp_polar(1 + I)", "1.46869393991589 + 2.28735528717884*I"],
  ["EFl", "polar_lift(-2)", "-2.00000000000000"],
  ["s", "Ei(exp_polar(2*I*pi)*x)", "Ei(x) + 2*I*pi"],
  ["s", "Ei(exp_polar(I*pi)*x)", "Ei(x*exp_polar(I*pi))"],
  ["s", "Ei(x)", "Ei(x)"],
  ["s", "Ci(polar_lift(I)*x)", "Chi(x) + I*pi/2"],
  ["s", "Ci(polar_lift(-I)*x)", "Chi(x) - I*pi/2"],
  ["s", "Ci(polar_lift(-1)*x)", "Ci(x) + I*pi"],
  ["s", "Ci(exp_polar(2*I*pi)*x)", "Ci(x) + 2*I*pi"],
  ["s", "Chi(polar_lift(I)*x)", "Ci(x) + I*pi/2"],
  ["s", "Chi(polar_lift(-1)*x)", "Chi(x) + I*pi"],
  ["s", "Chi(exp_polar(2*I*pi)*x)", "Chi(x) + 2*I*pi"],
  ["s", "Si(polar_lift(I)*x)", "I*Shi(x)"],
  ["s", "Si(polar_lift(-I)*x)", "-I*Shi(x)"],
  ["s", "Si(polar_lift(-1)*x)", "-Si(x)"],
  ["s", "Si(exp_polar(2*I*pi)*x)", "Si(x)"],
  ["s", "Shi(polar_lift(I)*x)", "I*Si(x)"],
  ["s", "Shi(polar_lift(-1)*x)", "-Shi(x)"],
  ["s", "Shi(exp_polar(4*I*pi)*x)", "Shi(x)"],
  ["s", "Si(x)", "Si(x)"],
  ["s", "Ci(x)", "Ci(x)"],
  ["s", "expint(2, exp_polar(2*I*pi)*x)", "2*I*pi*x + expint(2, x)"],
  ["s", "expint(1, exp_polar(2*I*pi)*x)", "expint(1, x) - 2*I*pi"],
  ["s", "expint(-1, exp_polar(2*I*pi)*x)", "exp(-x)/x + exp(-x)/x**2"],
  ["s", "expint(nu, exp_polar(2*I*pi)*x)", "x**(nu - 1)*(exp(2*I*pi*nu) - 1)*gamma(1 - nu) + expint(nu, x)"],
  ["s", "expint(1/3, exp_polar(2*I*pi)*x)", "expint(1/3, x) + (-1 + exp(2*I*pi/3))*gamma(2/3)/x**(2/3)"],
  ["s", "expint(2, x)", "expint(2, x)"],
  ["s", "polar_lift(-oo)", "-oo"],
  ["s", "polar_lift(zoo)", "polar_lift(zoo)"],
  ["s", "periodic_argument(x, oo)", "arg(x)"],
  ["s", "periodic_argument(exp_polar(I*pi/2)*x, oo)", "arg(x) + pi/2"],
  ["s", "unbranched_argument(exp_polar(15*I))", "15"],
  ["s", "expint(-2, exp_polar(4*I*pi)*x)", "exp(-x)/x + 2*exp(-x)/x**2 + 2*exp(-x)/x**3"],
  ["s", "uppergamma(2, exp_polar(2*I*pi)*x)", "(x + 1)*exp(-x)"],
  ["s", "periodic_argument(exp_polar(I*atan(r)), 2*pi)", "periodic_argument(exp_polar(I*atan(r)), 2*pi)"],
  ["s", "lowergamma(2, exp_polar(2*I*pi)*x)", "-(x + 1)*exp(-x) + 1"],
  ["s", "lowergamma(2, x)", "-(x + 1)*exp(-x) + 1"],
  ["EB", "exp_polar(5*I*pi)*x", "(x*exp_polar(I*pi), 2)"],
  ["EB", "exp_polar(-3*I*pi)*x", "(x*exp_polar(I*pi), -2)"],
  ["EB", "exp_polar(I*pi)*x", "(x*exp_polar(I*pi), 0)"],
  ["EBH", "exp_polar(I*pi)*x", "(x, 1/2)"],
  ["EBH", "exp_polar(3*I*pi)*x", "(x, 3/2)"],
  ["EB", "exp_polar(2*I*pi + 3)*x", "(x*exp_polar(3), 1)"],
  ["EB", "exp_polar(2*I*pi*y + 4*I*pi)", "(exp_polar(2*I*pi*y), 2)"],
  ["EB", "exp_polar(I*y + 2*I*pi)", "(exp_polar(I*y), 1)"],
  ["EB", "exp_polar(sqrt(2)*I*pi)", "(exp_polar(I*pi*(-2 + sqrt(2))), 1)"],
  ["EB", "x", "(x, 0)"],
  ["EB", "exp_polar(2*I*pi)", "(1, 1)"],
  ["EB", "exp_polar(-sqrt(2)*I*pi)*x", "(x*exp_polar(I*pi*(2 - sqrt(2))), -1)"],
  ["EB", "exp_polar(I*I*pi)", "(exp_polar(-pi), 0)"],
  // unpolarify(e, exponents_only=True)
  ["UPE", "exp_polar(2*I*pi)*x**exp_polar(I*pi)", "exp_polar(2*I*pi)/x"],
  ["UPE", "polar_lift(x)**polar_lift(2)", "polar_lift(x)**2"],
  ["UPE", "polar_lift(x)**2", "polar_lift(x)**2"],
  ["UPE", "exp_polar(I*pi)*polar_lift(x)**polar_lift(2)*sin(polar_lift(y))**exp_polar(0)", "exp_polar(I*pi)*sin(polar_lift(y))*polar_lift(x)**2"],
  ["UPE", "polar_lift(x)**(2*exp_polar(0)) + polar_lift(y)", "polar_lift(x)**2 + polar_lift(y)"],
  ["UPE", "exp_polar(polar_lift(2))*x", "x*exp_polar(2)"],
  ["UPE", "principal_branch(polar_lift(x), 2*pi)**polar_lift(3)", "principal_branch(x, 2*pi)**3"],
  ["UPE", "gamma(polar_lift(x))**polar_lift(2)", "gamma(polar_lift(x))**2"],
  ["UPE", "(polar_lift(x)**polar_lift(y))**polar_lift(2)", "polar_lift(x)**(2*y)"],
  ["UPE", "polar_lift(0)**polar_lift(2) + x**exp_polar(I*pi)", "1/x"],
  ["UPE", "besselj(polar_lift(a), x)**polar_lift(2)", "besselj(a, x)**2"],
  ["UPE", "sin(polar_lift(x))", "sin(polar_lift(x))"],
  ["UPE", "x**principal_branch(y, 2*pi)", "x**y"],
  ["UPE", "x**principal_branch(y, pi)", "x**principal_branch(y, pi)"],
  // periodic_argument of powers of polar numbers (_getunbranched)
  ["s", "periodic_argument(polar_lift(x)**2, oo)", "2*arg(x)"],
  ["s", "periodic_argument(polar_lift(x)**2, 2*pi)", "periodic_argument(polar_lift(x)**2, 2*pi)"],
  ["s", "periodic_argument(polar_lift(2 + I)**2, 2*pi)", "periodic_argument(polar_lift(2 + I)**2, 2*pi)"],
  ["s", "periodic_argument(polar_lift(2)**I, oo)", "log(2)"],
  ["s", "periodic_argument(exp_polar(3*I)**2*polar_lift(y), 2*pi)", "periodic_argument(exp_polar(6*I)*polar_lift(y), 2*pi)"],
  // log, Abs, arg and conjugate of polar numbers
  ["s", "log(exp_polar(x))", "x"],
  ["s", "log(exp_polar(2*I*pi))", "2*I*pi"],
  ["s", "log(exp_polar(polar_lift(x)))", "x"],
  ["s", "log(exp_polar(3)*x)", "log(x*exp_polar(3))"],
  ["s", "log(8, 2)", "3"],
  ["s", "Abs(exp_polar(0))", "1"],
  ["s", "Abs(exp_polar(2 + I))", "exp(2)"],
  ["s", "Abs(2*exp_polar(x))", "2*exp(re(x))"],
  ["s", "Abs(x*polar_lift(y))", "Abs(x*polar_lift(y))"],
  ["s", "Abs(2*polar_lift(y))", "2*Abs(polar_lift(y))"],
  ["s", "Abs(2*x*polar_lift(y))", "2*Abs(x*polar_lift(y))"],
  ["s", "Abs(x*exp_polar(y))", "exp(re(y))*Abs(x)"],
  ["s", "Abs(polar_lift(x)*exp_polar(y))", "exp(re(y))*Abs(polar_lift(x))"],
  ["s", "Abs(polar_lift(x))", "Abs(x)"],
  ["s", "Abs(principal_branch(x, 2*pi))", "Abs(principal_branch(x, 2*pi))"],
  ["s", "arg(exp_polar(I))", "1"],
  ["s", "arg(exp_polar(x))", "im(x)"],
  ["C", "exp_polar(I)", "exp_polar(-I)"],
  ["C", "exp_polar(x)", "exp_polar(conjugate(x))"],
];
const y = new Sym('y');
const I = S.I;
const pi = S.Pi;
const str = (v: unknown): string => (Array.isArray(v) ? `(${v.map(str).join(', ')})` : String(v));

describe('polar numbers and branches (SymPy eval)', () => check(POLAR_CASES));

describe('polar: cases outside the table', () => {
  const y = new Sym('y');
  it('the derivative of exp_polar', () => {
    // SymPy leaves Derivative(exp_polar(x), x) unevaluated (exp_polar has no fdiff)
    expect(String(diff(expPolar(x), x))).toBe('Derivative(exp_polar(x), x)');
  });
  it('the parser builds the polar functions (SymPy sympify)', () => {
    // SymPy log(exp_polar(I*pi/2)) = I*pi/2, expand_log(log(2*x*exp_polar(I*pi/2))) = log(x) + log(2) + I*pi/2
    expect(String(sj.parse('log(exp_polar(I*pi/2))'))).toBe('I*pi/2');
    expect(String(sj.expandLog(sj.parse('log(2*x*exp_polar(I*pi/2))')))).toBe('log(x) + log(2) + I*pi/2');
    // SymPy log(exp_polar(x)) = x, unpolarify(polar_lift(x)**2) = x**2, periodic_argument(exp_polar(3*I*pi), 2*pi) = pi
    expect(String(sj.parse('log(exp_polar(x))'))).toBe('x');
    expect(String(sj.unpolarify(sj.parse('polar_lift(x)**2')))).toBe('x**2');
    expect(String(sj.parse('periodic_argument(exp_polar(3*I*pi), 2*pi)'))).toBe('pi');
    expect(String(sj.parse('principal_branch(exp_polar(3*I*pi), 2*pi)'))).toBe('exp_polar(I*pi)');
    expect(String(sj.parse('unbranched_argument(exp_polar(3*I*pi))'))).toBe('3*pi');
    expect(() => sj.parse('exp_polar(1, 2)')).toThrow(TypeError);
    expect(() => sj.parse('periodic_argument(x)')).toThrow('periodic_argument takes 2 arguments (1 given)');
    expect(() => sj.parse('polar_lift(x, y)')).toThrow('polar_lift takes 1 argument (2 given)');
  });
  it('unpolarify of Ne against 0', () => {
    // SymPy unpolarify(Ne(polar_lift(x), 0)) and unpolarify(Ne(polar_lift(x), 1))
    expect(String(sj.unpolarify(sj.Ne(polarLift(x), 0)))).toBe('Ne(x, 0)');
    expect(String(sj.unpolarify(sj.Ne(polarLift(x), 1)))).toBe('Ne(polar_lift(x), 1)');
  });
  it('unpolarify with a substitution', () => {
    // SymPy unpolarify(polar_lift(x)**2, {x: exp_polar(y)})
    expect(String(sj.unpolarify(pow(polarLift(x), 2), { subs: [[x, expPolar(y)]] }))).toBe('exp(2*y)');
  });
  it('isPolar', () => {
    expect(isPolar(polarLift(x))).toBe(true);
    expect(isPolar(new Sym('w', { polar: true }))).toBe(true);
    expect(isPolar(sj.mul(2, polarLift(x)))).toBe(true);
    expect(isPolar(pow(polarLift(x), 2))).toBe(true);
    // SymPy (polar_lift(x)**y).is_polar is True (Pow.is_polar = base.is_polar), and a product is
    // polar when its other factors are positive: (q*polar_lift(x)).is_polar, but not x*polar_lift(x)
    expect(isPolar(pow(polarLift(x), y))).toBe(true);
    expect(isPolar(sj.mul(new Sym('q', { positive: true }), polarLift(x)))).toBe(true);
    expect(isPolar(sj.mul(x, polarLift(x)))).toBe(false);
    expect(isPolar(x)).toBe(false);
    expect(String(unbranchedArgument(expPolar(sj.mul(3, sj.I))))).toBe('3');
  });
  it('polarify with lift and with the substitution of polar dummies', () => {
    expect(String(polarify(P('x + 1'), { lift: true }))).toBe('polar_lift(x + 1)');
    expect(String(polarify(P('x*exp(y)'), { lift: true }))).toBe('exp(polar_lift(y))*polar_lift(x)');
    expect(String(polarify(P('2*x'), { lift: true }))).toBe('2*exp_polar(0)*polar_lift(x)');
    expect(String(polarify(P('sin(x) + exp(2)'), { subs: false }))).toBe('sin(x) + exp(2*exp_polar(0))');
    const r = polarify(P('x*y + 2'));
    if (!Array.isArray(r)) throw new TypeError('expected [expr, reps]');
    const [e, reps] = r;
    expect(String(e)).toBe('_x*_y + 2');
    expect(reps.map(([d, s]) => [String(d), String(s), isPolar(d)])).toEqual([
      ['_x', 'x', true],
      ['_y', 'y', true],
    ]);
  });
});

describe('polar numbers', () => {
  it('extract_branch_factor', () => {
    // SymPy exp_polar(...).extract_branch_factor()
    expect(str(extractBranchFactor(expPolar(mul(I, pi, x))))).toBe('(exp_polar(I*pi*x), 0)');
    expect(str(extractBranchFactor(expPolar(mul(I, pi, add(1, I)))))).toBe('(exp_polar(I*pi*(1 - I)), I)');
    expect(str(extractBranchFactor(expPolar(mul(I, pi, add(sqrt(2), I)))))).toBe('(exp_polar(I*pi*(-2 + sqrt(2) - I)), 1 + I)');
    expect(str(extractBranchFactor(expPolar(mul(I, pi, sqrt(7)))))).toBe('(exp_polar(I*pi*(-2 + sqrt(7))), 1)');
  });
  it('periodic_argument and principal_branch that stay unevaluated', () => {
    const p = new Sym('p', { polar: true });
    expect(String(periodicArgument(p, mul(2, pi)))).toBe('periodic_argument(p, 2*pi)');
    expect(String(principalBranch(add(1, mul(2, I)), mul(2, pi)))).toBe('principal_branch(1 + 2*I, 2*pi)');
  });
  it('numeric value of exp_polar near the negative axis (SymPy exp_polar._eval_evalf)', () => {
    // SymPy N(log(3*exp_polar(I*pi)/10), 20) = -1.2039728043259359926 + 3.1415926535897932385*I:
    // exp_polar(I*pi) is -1 approached from above, so the logarithm has the imaginary part +pi
    const e = sj.log(mul(sj.Rational.of(3n, 10n), expPolar(mul(S.I, S.Pi))));
    const c = e.toComplex();
    expect(c.re).toBeCloseTo(-1.2039728043259361, 14);
    expect(c.im).toBeCloseTo(Math.PI, 14);
    const v = e.evalf(20).toComplex();
    expect(v.im).toBeCloseTo(Math.PI, 14);
  });
  it('numeric value of polar_lift', () => {
    // SymPy N(polar_lift(1 + I))
    expect(String(polarLift(add(1, I)).evalf())).toBe('1.0 + 1.0*I');
  });
  it('polarify', () => {
    // SymPy polarify(polar_lift(x), subs=False) and polarify(x*y + 1)
    expect(String(polarify(polarLift(x), { subs: false }))).toBe('polar_lift(x)');
    expect(str(polarify(add(mul(x, y), 1)))).toBe('(_x*_y + 1, ((_x, x), (_y, y)))');
    // SymPy polarify(b + sin(a)) = (_b + sin(_a), {_b: b, _a: a}); symjs lists the pairs by name
    const a = new Sym('a');
    const b = new Sym('b');
    expect(str(polarify(add(b, sin(a))))).toBe('(_b + sin(_a), ((_a, a), (_b, b)))');
  });
  it('expint of a non-positive order on another branch', () => {
    // SymPy expint(-1, x*exp_polar(2*I*pi)), expint(0, x*exp_polar(2*I*pi))
    const z = mul(x, expPolar(mul(2, I, pi)));
    expect(String(expint(-1, z))).toBe('exp(-x)/x + exp(-x)/x**2');
    expect(String(expint(0, z))).toBe('exp(-x)/x');
  });
});

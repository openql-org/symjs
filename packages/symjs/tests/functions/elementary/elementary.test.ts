// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/functions/elementary/elementary.ts.
//
// The elementary functions: sin/cos/tan tables, inverse functions, exp, log (with a base), abs, re,
// im, arg, conjugate, adjoint and transpose. Expected values are str() results of SymPy 1.14 unless a
// comment says otherwise.

import { describe, expect, it } from 'vitest';
import * as sj from '../../../src';
import { abs, AccumBounds, add, adjoint, arg, conjugate, cos, cosh, exp, Float, fn, hyper, I, mul, parse, pi, pow, rational, re, S, sin, Sym, symbol, transpose } from '../../../src';
import { forEachEntry } from '../../../src/functions/elementary/elementary';

const x = new Sym('x');
const r = new Sym('r', { real: true });
const A = new Sym('A', { commutative: false });
const B = new Sym('B', { commutative: false });
const theta = symbol('theta', { real: true });
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
  exp_polar: sj.expPolar,
  polar_lift: sj.polarLift,
  periodic_argument: sj.periodicArgument,
  principal_branch: sj.principalBranch,
  unbranched_argument: sj.unbranchedArgument,
  jn: sj.jn,
  yn: sj.yn,
  KroneckerDelta: sj.KroneckerDelta,
  // H(p, q, a1..ap, b1..bq, z) = hyper((a1..ap), (b1..bq), z); G(n, p, m, q, ..., z) = meijerg
  H: (np: sj.Expr, nq: sj.Expr, ...r: sj.Expr[]) => {
    const [a, b] = [np.toNumber(), nq.toNumber()];
    return sj.hyper(r.slice(0, a), r.slice(a, a + b), r[r.length - 1] ?? 0);
  },
  G: (n: sj.Expr, p: sj.Expr, m: sj.Expr, q: sj.Expr, ...r: sj.Expr[]) => {
    const [a, b, c, d] = [n.toNumber(), p.toNumber(), m.toNumber(), q.toNumber()];
    return sj.meijerg(r.slice(0, a), r.slice(a, a + b), r.slice(a + b, a + b + c), r.slice(a + b + c, a + b + c + d), r[r.length - 1] ?? 0);
  },
  transpose: sj.transpose,
  adjoint: sj.adjoint,
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
  if (kind === 'RW') {
    const [e0 = '', target = ''] = src.split(';');
    return String(sj.rewrite(P(e0), target));
  }
  const e = P(src);
  switch (kind) {
    case 'D':
      return String(sj.diff(e, x));
    case 'L':
      return sj.latex(e);
    case 'KS':
      return String(sj.kroneckersimp(e));
    case 'SUB':
      return String(sj.subs(e, { x: 2 }));
    case 'EB':
    case 'EBH': {
      const [a, b] = sj.extractBranchFactor(e, kind === 'EBH');
      return `(${String(a)}, ${String(b)})`;
    }
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
const ELEM_CASES: Case[] = [
  ["s", "sin(5*pi/12)", "sqrt(2)/4 + sqrt(6)/4"],
  ["s", "cos(5*pi/12)", "-sqrt(2)/4 + sqrt(6)/4"],
  ["s", "sin(7*pi/12)", "sqrt(2)/4 + sqrt(6)/4"],
  ["s", "cos(pi/12)", "sqrt(2)/4 + sqrt(6)/4"],
  ["s", "sin(-5*pi/12)", "-sqrt(6)/4 - sqrt(2)/4"],
  ["s", "sin(asin(x))", "x"],
  ["s", "cos(acos(x))", "x"],
  ["s", "tan(pi/2)", "zoo"],
  ["s", "tan(3*pi/2)", "zoo"],
  ["s", "tan(x + pi)", "tan(x)"],
  ["s", "tan(x + 5*pi/4)", "tan(x + pi/4)"],
  ["s", "tan(x + 2*pi)", "tan(x)"],
  ["s", "tan(-x)", "-tan(x)"],
  ["s", "tan(atan(x))", "x"],
  ["s", "tan(pi/5)", "sqrt(5 - 2*sqrt(5))"],
  ["s", "asin(oo)", "-oo*I"],
  ["s", "asin(-oo)", "oo*I"],
  ["s", "asin(sqrt(2)/2)", "pi/4"],
  ["s", "asin(sqrt(3)/2)", "pi/3"],
  ["s", "asin(-sqrt(3)/2)", "-pi/3"],
  ["s", "acos(oo)", "oo*I"],
  ["s", "acos(-oo)", "-oo*I"],
  ["s", "acos(sqrt(2)/2)", "pi/4"],
  ["s", "acos(sqrt(3)/2)", "pi/6"],
  ["s", "atan(sqrt(3))", "pi/3"],
  ["s", "atan(sqrt(3)/3)", "pi/6"],
  ["s", "atan(-sqrt(3))", "-pi/3"],
  ["s", "sinh(oo)", "oo"],
  ["s", "sinh(-oo)", "-oo"],
  ["s", "cosh(oo)", "oo"],
  ["s", "cosh(-oo)", "oo"],
  ["s", "tanh(oo)", "1"],
  ["s", "tanh(-oo)", "-1"],
  ["s", "tanh(0)", "0"],
  ["s", "tanh(-x)", "-tanh(x)"],
  ["s", "log(nan)", "nan"],
  ["s", "log(oo)", "oo"],
  ["s", "log(-oo)", "oo"],
  ["s", "log(zoo)", "zoo"],
  ["s", "log(I)", "I*pi/2"],
  ["s", "log(-I)", "-I*pi/2"],
  ["s", "log(1 + I)", "log(sqrt(2)) + I*pi/4"],
  ["s", "log(2 - 3*I)", "log(2 - 3*I)"],
  ["s", "log(1/8)", "-log(8)"],
  ["s", "log(-2)", "log(2) + I*pi"],
  ["s", "log(exp(r))", "r"],
  ["s", "log(exp(x))", "log(exp(x))"],
  ["s", "log(1 + gamma(1/3)*I)", "log(1 + I*gamma(1/3))"],
  ["s", "log(8, 2)", "3"],
  ["s", "log(x, E)", "log(x)"],
  ["s", "log(1, 1)", "nan"],
  ["s", "log(3, 1)", "zoo"],
  ["s", "log(x, 1)", "zoo"],
  ["s", "log(1/8, 2)", "-3"],
  ["s", "log(-8, 2)", "3 + I*pi/log(2)"],
  ["s", "log(24, 2)", "log(3)/log(2) + 3"],
  ["s", "log(3/16, 2)", "-4 + log(3)/log(2)"],
  ["s", "log(x, 3)", "log(x)/log(3)"],
  ["s", "log(5, 2)", "log(5)/log(2)"],
  ["s", "log(9, 3)", "2"],
  ["s", "abs(nan)", "nan"],
  ["s", "abs(oo)", "oo"],
  ["s", "abs(-oo)", "oo"],
  ["s", "abs(zoo)", "oo"],
  ["s", "abs(I)", "1"],
  ["s", "abs(p)", "p"],
  ["s", "abs(ng)", "-ng"],
  ["s", "abs(3*x)", "3*Abs(x)"],
  ["s", "abs(x*y)", "Abs(x*y)"],
  ["s", "abs(r**2)", "r**2"],
  ["s", "abs(exp(x))", "exp(re(x))"],
  ["s", "abs(abs(x))", "Abs(x)"],
  ["s", "abs(conjugate(x))", "Abs(x)"],
  ["s", "abs(r + 2*I)", "sqrt(r**2 + 4)"],
  ["s", "abs(x + I)", "Abs(x + I)"],
  ["s", "abs(1 - sqrt(5))", "-1 + sqrt(5)"],
  ["s", "abs(pi - 4)", "4 - pi"],
  ["s", "abs((-1)**(1/3))", "1"],
  ["s", "abs(I**(1/3))", "1"],
  ["s", "re(re(x))", "re(x)"],
  ["s", "re(conjugate(x))", "re(x)"],
  ["s", "re(I*x)", "-im(x)"],
  ["s", "re((-1)**(1/3))", "1/2"],
  ["s", "re(I**(2/5))", "1/4 + sqrt(5)/4"],
  ["s", "im(I*x)", "re(x)"],
  ["s", "im(2*I*x)", "2*re(x)"],
  ["s", "im(conjugate(x))", "-im(x)"],
  ["s", "im(im(x))", "0"],
  ["s", "im((-1)**(1/3))", "sqrt(3)/2"],
  ["s", "arg(p)", "0"],
  ["s", "arg(ng)", "pi"],
  ["s", "arg(-1 + I)", "3*pi/4"],
  ["s", "arg(-1 - I)", "-3*pi/4"],
  ["s", "arg(1 + I)", "pi/4"],
  ["s", "arg(2*I)", "pi/2"],
  ["s", "arg(-2*I)", "-pi/2"],
  ["s", "arg(I)", "pi/2"],
  ["s", "arg(exp(2*I))", "2"],
  ["s", "arg(exp(5*I))", "5 - 2*pi"],
  ["s", "arg(exp(x*I))", "arg(exp(I*x))"],
  ["s", "arg(x)", "arg(x)"],
  ["s", "arg(0)", "nan"],
  ["s", "arg(1 + sqrt(2)*I)", "atan(sqrt(2))"],
  ["C", "x**2", "conjugate(x)**2"],
  ["C", "p**y", "p**conjugate(y)"],
  ["C", "x**r", "conjugate(x**r)"],
  ["C", "x**(1/2)", "conjugate(sqrt(x))"],
  ["C", "exp(x)", "exp(conjugate(x))"],
  ["C", "conjugate(x)", "x"],
  ["C", "sin(x)", "sin(conjugate(x))"],
  ["C", "cos(x)", "cos(conjugate(x))"],
  ["C", "tan(x)", "tan(conjugate(x))"],
  ["C", "sinh(x)", "sinh(conjugate(x))"],
  ["C", "cosh(x)", "cosh(conjugate(x))"],
  ["C", "tanh(x)", "tanh(conjugate(x))"],
  ["C", "re(x)", "re(x)"],
  ["C", "im(x)", "im(x)"],
  ["C", "abs(x)", "Abs(x)"],
  ["C", "arg(x)", "arg(x)"],
  ["C", "gamma(x)", "gamma(conjugate(x))"],
  ["C", "log(x)", "conjugate(log(x))"],
  ["C", "f(x)", "conjugate(f(x))"],
  ["C", "transpose(x)", "conjugate(x)"],
  ["C", "adjoint(x)", "x"],
  ["A", "x", "conjugate(x)"],
  ["A", "x**2", "conjugate(x)**2"],
  ["A", "transpose(x)", "conjugate(x)"],
  ["A", "conjugate(x)", "x"],
  ["A", "adjoint(x)", "x"],
  ["A", "sin(x)", "sin(conjugate(x))"],
  ["A", "exp(x)", "exp(conjugate(x))"],
  ["T", "x**2", "x**2"],
  ["T", "transpose(x)", "x"],
  ["T", "conjugate(x)", "conjugate(x)"],
  ["T", "adjoint(x)", "conjugate(x)"],
  ["T", "exp(x)", "exp(x)"],
  ["T", "sin(x)", "sin(x)"],
  ["s", "log(2*I)", "log(2) + I*pi/2"],
  ["s", "log(-3*I/2)", "log(3/2) - I*pi/2"],
  ["s", "log(I*oo)", "oo"],
  ["s", "log(1 + sqrt(3)*I)", "log(2) + I*pi/3"],
  ["s", "log(-1 + I)", "log(sqrt(2)) + 3*I*pi/4"],
  ["s", "abs((-1)**n)", "1"],
  ["s", "abs(r**(2*n))", "r**(2*n)"],
  ["s", "abs(p**x)", "p**re(x)"],
  ["s", "abs(ng**x)", "(-ng)**re(x)*exp(-pi*im(x))"],
  ["s", "abs(r**x)", "Abs(r**x)"],
  ["s", "abs(2**I)", "1"],
  ["s", "arg(exp(-5*I))", "-5 + 2*pi"],
  ["s", "arg(exp(9*I))", "9 - 2*pi"],
  ["s", "conjugate(x**n)", "conjugate(x)**n"],
  ["s", "conjugate(x**y)", "conjugate(x**y)"],
  ["s", "conjugate(nn**r)", "conjugate(nn**r)"],
  ["s", "conjugate(exp(x))", "exp(conjugate(x))"],
  ["s", "tan(pi/5)", "sqrt(5 - 2*sqrt(5))"],
  ["s", "tan(2*pi/5)", "sqrt(2*sqrt(5) + 5)"],
  ["s", "tan(3*pi/5)", "-sqrt(2*sqrt(5) + 5)"],
  ["s", "tan(pi/10)", "sqrt(1 - 2*sqrt(5)/5)"],
  ["s", "tan(7*pi/10)", "-sqrt(2*sqrt(5)/5 + 1)"],
  ["s", "cot(pi/5)", "sqrt(2*sqrt(5)/5 + 1)"],
  ["s", "cot(3*pi/10)", "sqrt(5 - 2*sqrt(5))"],
  ["s", "tan(-pi/5)", "-sqrt(5 - 2*sqrt(5))"],
  ["s", "tan(4*pi/5)", "-sqrt(5 - 2*sqrt(5))"],
  ["s", "tan(9*pi/10)", "-sqrt(1 - 2*sqrt(5)/5)"],
  ["s", "cot(-2*pi/5)", "-sqrt(1 - 2*sqrt(5)/5)"],
  ["s", "tan(x + pi/5)", "tan(x + pi/5)"],
];
const cases: [string, string][] = [
  // rational multiples of pi outside the tables (SymPy sin/cos/tan.eval reductions)
  ['sin(8*pi/7)', '-sin(pi/7)'],
  ['sin(-8*pi/7)', 'sin(pi/7)'],
  ['sin(5*pi/7)', 'sin(2*pi/7)'],
  ['sin(pi/7)', 'sin(pi/7)'],
  ['sin(13*pi/7)', '-sin(pi/7)'],
  ['sin(15*pi/7)', 'sin(pi/7)'],
  ['cos(8*pi/7)', '-cos(pi/7)'],
  ['cos(-5*pi/7)', '-cos(2*pi/7)'],
  ['cos(5*pi/7)', '-cos(2*pi/7)'],
  ['cos(13*pi/7)', 'cos(pi/7)'],
  ['cos(15*pi/7)', 'cos(15*pi/7)'],
  ['cos(23*pi/7)', '-cos(2*pi/7)'],
  ['tan(5*pi/7)', '-tan(2*pi/7)'],
  ['tan(-8*pi/7)', '-tan(pi/7)'],
  ['tan(13*pi/7)', '-tan(pi/7)'],
  ['tan(-pi/7)', '-tan(pi/7)'],
  ['tan(pi/7)', 'tan(pi/7)'],
  ['tan(pi/2)', 'zoo'],
  ['tan(3*pi/2)', 'zoo'],
  // _peeloff_pi: the multiple of pi/2 taken out of a sum
  ['sin(x + 8*pi/7)', '-sin(x + pi/7)'],
  ['sin(x - pi/3)', '-cos(x + pi/6)'],
  ['sin(x + 5*pi/4)', '-sin(x + pi/4)'],
  ['sin(-x - pi/3)', '-sin(x + pi/3)'],
  ['cos(x - pi/3)', 'sin(x + pi/6)'],
  ['cos(x + 2*pi)', 'cos(x)'],
  ['cos(x + 3*pi/2)', 'sin(x)'],
  ['cos(x + 5*pi/7)', '-sin(x + 3*pi/14)'],
  ['cot(9*pi/7)', 'cot(2*pi/7)'],
  ['cot(5*pi/7)', '-cot(2*pi/7)'],
  ['cot(pi/7)', 'cot(pi/7)'],
  ['cot(23*pi/7)', 'cot(2*pi/7)'],
  ['sec(23*pi/7)', '-sec(2*pi/7)'],
  ['csc(23*pi/7)', '-csc(2*pi/7)'],
  ['sec(5*pi/7)', '-sec(2*pi/7)'],
  ['csc(5*pi/7)', 'csc(2*pi/7)'],
  ['log(0)', 'zoo'],
  // the sign of a function of a number is decided numerically
  ['Abs(sin(4))', '-sin(4)'],
  ['arg(sin(4))', 'pi'],
  ['arg(sin(1))', '0'],
  ['Abs(I*y + 1)', 'Abs(I*y + 1)'],
  ['Abs(f(1))', 'Abs(f(1))'],
  ['re((-1)**(1/7))', 'cos(pi/7)'],
  ['im((-1)**(1/7))', 'sin(pi/7)'],
  ['re(I**(1/7))', 'cos(pi/14)'],
  // a negative rational base: (-2)**(1/3) = 2**(1/3)*(-1)**(1/3)
  ['re((-2)**(1/3))', '2**(1/3)/2'],
  ['im((-2)**(1/3))', '2**(1/3)*sqrt(3)/2'],
  ['re((-8)**(1/5))', '2**(3/5)*(1/4 + sqrt(5)/4)'],
  ['im((-1/2)**(2/3))', '2**(1/3)*sqrt(3)/4'],
  ['re(x*y)', 're(x*y)'],
  ['im(x*y)', 'im(x*y)'],
  ['re(2*I*y)', '-2*im(y)'],
  ['im(2*I*y)', '2*re(y)'],
  ['arg(I*(pi-3))', 'pi/2'],
  ['arg(pi - 3 + I)', 'atan(1/(-3 + pi))'],
  ['arg(-(pi-3)+I)', 'atan(1/(3 - pi)) + pi'],
  ['arg(-I*(pi-3))', '-pi/2'],
  ['arg(3-pi - I)', '-pi - atan(1/(3 - pi))'],
  ['f(1.5)', 'f(1.5)'],
  ['sin(1 + 2.5*I)', '5.1601436675797 + 3.26893943207955*I'],
  ['sin(1.5 + 2*I)', '3.7527713404793 + 0.256553956090482*I'],
];

describe('adjoint and transpose (SymPy semantics)', () => {
  it('adjoint', () => {
    expect(adjoint(x).toString()).toBe('conjugate(x)');
    expect(adjoint(r).toString()).toBe('r');
    expect(adjoint(add(2, mul(3, I))).toString()).toBe('2 - 3*I');
    expect(adjoint(mul(A, B)).toString()).toBe('adjoint(B)*adjoint(A)');
    expect(adjoint(mul(A, B, x)).toString()).toBe('conjugate(x)*adjoint(B)*adjoint(A)');
    expect(adjoint(add(A, B)).toString()).toBe('adjoint(A) + adjoint(B)');
    expect(adjoint(pow(A, 2)).toString()).toBe('adjoint(A)**2');
    expect(adjoint(adjoint(A)).toString()).toBe('A');
    expect(adjoint(mul(r, A)).toString()).toBe('r*adjoint(A)');
    expect(adjoint(conjugate(A)).toString()).toBe('transpose(A)');
    expect(adjoint(transpose(A)).toString()).toBe('conjugate(A)');
    expect(adjoint(exp(A)).toString()).toBe('exp(adjoint(A))');
  });
  it('transpose', () => {
    expect(transpose(x).toString()).toBe('x');
    expect(transpose(mul(A, B)).toString()).toBe('transpose(B)*transpose(A)');
    expect(transpose(mul(I, A)).toString()).toBe('I*transpose(A)');
    expect(conjugate(mul(A, B)).toString()).toBe('conjugate(A)*conjugate(B)');
  });
});

describe('functions', () => {
  it('evaluates special values', () => {
    expect(sin(pi).toString()).toBe('0');
    expect(cos(pi).toString()).toBe('-1');
    expect(sin(mul(rational(1, 4), pi)).toString()).toBe('sqrt(2)/2');
    expect(cos(mul(rational(1, 3), pi)).toString()).toBe('1/2');
    expect(sin(mul(rational(5, 6), pi)).toString()).toBe('1/2');
    expect(cos(mul(rational(7, 6), pi)).toString()).toBe('-sqrt(3)/2');
  });

  it('uses parity and shifts', () => {
    expect(sin(mul(-1, x)).toString()).toBe('-sin(x)');
    expect(cos(mul(-1, x)).toString()).toBe('cos(x)');
    expect(sin(add(x, pi)).toString()).toBe('-sin(x)');
    expect(cos(add(x, mul(rational(1, 2), pi))).toString()).toBe('-sin(x)');
    expect(sin(add(x, mul(2, pi))).toString()).toBe('sin(x)');
  });

  it('conjugates', () => {
    expect(exp(mul(I, theta)).conjugate().toString()).toBe('exp(-I*theta)');
    expect(add(1, mul(2, I)).conjugate().toString()).toBe('1 - 2*I');
    expect(x.conjugate().toString()).toBe('conjugate(x)');
    expect(cos(theta).conjugate().toString()).toBe('cos(theta)');
  });
});

describe('elementary functions (SymPy eval)', () => check(ELEM_CASES));

describe('elementary: cases outside the table', () => {
  const y = new Sym('y');
  it('arg of a complex Float', () => {
    // SymPy arg(1.0 + 2.0*I) = 1.10714871779409
    const v = arg(sj.add(new Float(1), sj.mul(new Float(2), sj.I)));
    expect(String(v)).toBe('1.10714871779409');
  });
  it('transpose and adjoint of a commutative power', () => {
    // SymPy leaves transpose(x**y) unevaluated; a commutative scalar is its own transpose
    expect(String(transpose(pow(x, y)))).toBe('x**y');
    expect(String(adjoint(pow(x, y)))).toBe('conjugate(x**y)');
  });
  it('Abs of a power of a complex base', () => {
    // SymPy keeps Abs(x**2) and Abs(x**r); symjs pulls the real exponent out
    expect(String(sj.abs(pow(x, 2)))).toBe('Abs(x)**2');
    expect(String(sj.abs(pow(x, new Sym('r', { real: true }))))).toBe('Abs(x)**r');
  });
  it('forEachEntry skips missing entries', () => {
    const seen: string[] = [];
    forEachEntry<string, number>({ a: 1, b: undefined }, (k) => seen.push(k));
    expect(seen).toEqual(['a']);
  });
});

describe('functions: constructors and numerics', () => {
  it('arg of real constants decided numerically', () => {
    expect(String(arg(parse('1 - sqrt(2)')))).toBe('pi');
    expect(String(arg(parse('sqrt(3) - 1')))).toBe('0');
    expect(String(conjugate(re(x)))).toBe('re(x)');
  });
  it('adjoint and transpose of non-commutative symbols', () => {
    expect(String(transpose(pow(A, 2)))).toBe('transpose(A)**2');
    expect(String(transpose(transpose(A)))).toBe('A');
    expect(String(transpose(conjugate(A)))).toBe('adjoint(A)');
    expect(String(transpose(adjoint(A)))).toBe('conjugate(A)');
    expect(String(transpose(exp(A)))).toBe('exp(transpose(A))');
    expect(String(adjoint(transpose(A)))).toBe('conjugate(A)');
    expect(String(adjoint(conjugate(A)))).toBe('transpose(A)');
    expect(String(adjoint(pow(A, 2)))).toBe('adjoint(A)**2');
    expect(String(adjoint(adjoint(A)))).toBe('A');
    expect(String(fn('transpose', [transpose(A)]))).toBe('A');
    expect(String(fn('adjoint', [adjoint(A)]))).toBe('A');
    expect(String(fn('transpose', [A]))).toBe('transpose(A)');
    expect(String(fn('adjoint', [A]))).toBe('adjoint(A)');
  });
});

describe('elementary evaluation', () => {
  it.each(cases)('%s', (src, want) => {
    expect(String(parse(src))).toBe(want);
  });
  it('Abs of a power of a real base', () => {
    // SymPy Abs(r**-3), Abs(r**5), Abs(1/r), Abs(r**3) for real r
    expect(String(abs(pow(r, -3)))).toBe('1/(r**2*Abs(r))');
    expect(String(abs(pow(r, 5)))).toBe('r**4*Abs(r)');
    expect(String(abs(pow(r, -1)))).toBe('1/Abs(r)');
    expect(String(abs(pow(r, 3)))).toBe('r**2*Abs(r)');
  });
  it('re with a real factor and I', () => {
    // SymPy re(2*r*I*y) = -2*r*im(y), im(2*r*I*y) = 2*r*re(y)
    const y = new Sym('y');
    expect(String(parse('re(2*I*y)'))).toBe('-2*im(y)');
    expect(String(mul(2, r, S.I, y))).toBe('2*I*r*y');
    expect(String(parse('re(2*I*r*y)', { locals: { r } }))).toBe('-2*r*im(y)');
  });
  it('functions of an AccumBounds', () => {
    // SymPy sin(AccumBounds(0, 1)) = AccumBounds(0, sin(1)); cosh(AccumBounds(0, 1)) stays
    const ab = AccumBounds(0, 1);
    expect(String(sin(ab))).toBe('AccumBounds(0, sin(1))');
    expect(String(cosh(ab))).toBe('cosh(AccumBounds(0, 1))');
  });
  it('unevaluated calls', () => {
    // SymPy sin(0, evaluate=False)
    expect(String(fn('sin', [0], { evaluate: false }))).toBe('sin(0)');
  });
  it('functions without a numeric value', () => {
    // SymPy lucas(1.5) and Abs(lucas(1.5)) stay unevaluated
    expect(String(fn('lucas', [new Float(1.5)]))).toBe('lucas(1.5)');
    expect(String(abs(fn('lucas', [new Float(1.5)])))).toBe('Abs(lucas(1.5))');
  });
  it('arg of complex numbers with a Float part', () => {
    // SymPy arg(2.0 + 3*I), arg(2 + 3.0*I)
    expect(String(arg(add(new Float(2), mul(3, S.I))))).toBe('0.982793723247329');
    expect(String(arg(add(2, mul(new Float(3), S.I))))).toBe('0.982793723247329');
  });
  it('arg when the sign of the real part cannot be decided', () => {
    // the real part is zero (sqrt(5 + 2*sqrt(6)) = sqrt(2) + sqrt(3)) but is neither decided nor
    // decidable numerically; SymPy gives pi/2 and nan here, symjs keeps arg unevaluated
    expect(String(parse('arg(sqrt(2)+sqrt(3)-sqrt(5+2*sqrt(6)) + I)'))).toBe('arg(-sqrt(2*sqrt(6) + 5) + sqrt(2) + sqrt(3) + I)');
    expect(String(parse('arg(I*(sqrt(2)+sqrt(3)-sqrt(5+2*sqrt(6))))'))).toBe('arg(I*(-sqrt(2*sqrt(6) + 5) + sqrt(2) + sqrt(3)))');
  });
  it('conjugate, transpose and adjoint of hyper and of non-commutative sums', () => {
    // SymPy: conjugate(hyper((1,), (2,), x)) stays, transpose is the identity, adjoint is the conjugate
    const h = hyper([1], [2], x);
    expect(String(conjugate(h))).toBe('conjugate(hyper((1,), (2,), x))');
    expect(String(transpose(h))).toBe('hyper((1,), (2,), x)');
    expect(String(adjoint(h))).toBe('conjugate(hyper((1,), (2,), x))');
    const A = new Sym('A', { commutative: false });
    const B = new Sym('B', { commutative: false });
    expect(String(transpose(add(A, B)))).toBe('transpose(A) + transpose(B)');
    // SymPy adjoint(sin(A)) = transpose(sin(conjugate(A))); transpose(sin(A)) and adjoint(f(A)) stay
    expect(String(adjoint(sin(A)))).toBe('transpose(sin(conjugate(A)))');
    expect(String(transpose(sin(A)))).toBe('transpose(sin(A))');
    // adjoint(f(A)) stays for an undefined f: SymPy adjoint(lucas(A))
    expect(String(adjoint(fn('lucas', [A])))).toBe('adjoint(lucas(A))');
  });
});

describe('functions at a number with an infinite part', () => {
  // [source, value]: the limit where it exists (zoo where the modulus grows without bound in no fixed
  // direction), SymPy's value where SymPy evaluates. SymPy 1.14 leaves the cases marked "limit"
  // unevaluated (or rewrites them, erf(-oo + I) = -erf(oo - I)); their values are the limits along
  // x + I*c, a + I*y and x + I*y (checked with mpmath at |x|, |y| = 1e6, 1e12, 1e24)
  const cases: [string, string][] = [
    // limit: gamma(-x + I) and gamma(a + I*y) -> 0, |gamma(x + I)| -> oo with a turning phase
    ['gamma(oo + I)', 'zoo'],
    ['gamma(-oo - I)', '0'],
    ['gamma(oo*I)', '0'],
    ['gamma(1 - oo*I)', '0'],
    ['gamma(-oo + oo*I)', '0'],
    // no limit (gamma(x + I*x**2) -> 0, gamma(x**2 + I*x) -> oo) and SymPy's own values
    ['gamma(oo + oo*I)', 'gamma(oo + oo*I)'],
    ['gamma(-oo)', 'gamma(-oo)'],
    ['gamma(zoo)', 'gamma(zoo)'],
    ['gamma(oo)', 'oo'],
    // SymPy: loggamma is zoo at all of these
    ['loggamma(oo*I)', 'zoo'],
    ['loggamma(1 + oo*I)', 'zoo'],
    ['loggamma(oo + oo*I)', 'zoo'],
    ['loggamma(zoo)', 'zoo'],
    ['loggamma(oo)', 'oo'],
    // limit: erf(x + I) -> 1, erf(-x + I) -> -1, |erf(1 + I*y)| -> oo (exp(y**2)); erfc = 1 - erf
    ['erf(oo + I)', '1'],
    ['erf(-oo - I)', '-1'],
    ['erf(1 + oo*I)', 'zoo'],
    ['erf(oo*I)', 'oo*I'],
    ['erf(oo + oo*I)', 'erf(oo + oo*I)'],
    ['erfc(oo - I)', '0'],
    ['erfc(-oo + I)', '2'],
    ['erfc(1 - oo*I)', 'zoo'],
    ['erfc(oo*I)', '-oo*I'],
    // limit: erfi(z) = -I*erf(I*z)
    ['erfi(oo + I)', 'zoo'],
    ['erfi(1 + oo*I)', 'I'],
    ['erfi(-1 - oo*I)', '-I'],
    ['erfi(oo + oo*I)', 'erfi(oo + oo*I)'],
    // limit: Ei(z) = -E1(-z) + I*pi*sign(im(z)), E1(w) -> 0 as re(w) -> oo or |im(w)| -> oo
    ['Ei(oo + I)', 'zoo'],
    ['Ei(-oo + I)', 'I*pi'],
    ['Ei(-oo - 2*I)', '-I*pi'],
    ['Ei(-oo + I*pi)', 'I*pi'],
    ['Ei(-oo - I*pi)', '-I*pi'],
    ['Ei(oo*I)', 'I*pi'],
    ['Ei(1 - oo*I)', '-I*pi'],
    ['Ei(-oo + oo*I)', 'I*pi'],
    ['Ei(oo + oo*I)', 'Ei(oo + oo*I)'],
    ['Ei(oo)', 'oo'],
    // limit: |li(z)| ~ |z/log(z)| -> oo
    ['li(-oo)', 'zoo'],
    ['li(zoo)', 'zoo'],
    ['li(oo + I)', 'zoo'],
    ['li(oo*I)', 'zoo'],
    ['li(-oo - oo*I)', 'zoo'],
    ['li(oo)', 'oo'],
    // limit: asin(x + I) -> pi/2 + oo*I, asin(1 + I*y) -> oo*I (SymPy asin(oo*I) = oo*I, asin(zoo) = zoo)
    ['asin(oo + I)', 'pi/2 + oo*I'],
    ['asin(-oo - I)', '-pi/2 - oo*I'],
    ['asin(1 - oo*I)', '-oo*I'],
    ['asin(oo + oo*I)', 'zoo'],
    ['asin(zoo)', 'zoo'],
    ['asin(oo)', '-oo*I'],
    // limit: acos = pi/2 - asin (SymPy acos(oo*I) = pi/2 - oo*I, acos(zoo) = zoo)
    ['acos(oo + I)', '-oo*I'],
    ['acos(-oo + I)', 'pi - oo*I'],
    ['acos(1 + oo*I)', 'pi/2 - oo*I'],
    ['acos(oo*I)', 'pi/2 - oo*I'],
    ['acos(-oo - oo*I)', 'zoo'],
    ['acos(zoo)', 'zoo'],
    // limit: asinh(z) = -I*asin(I*z); SymPy asinh(oo*I) = oo is kept
    ['asinh(oo + I)', 'oo'],
    ['asinh(-oo - I)', '-oo'],
    ['asinh(1 + oo*I)', 'oo + I*pi/2'],
    ['asinh(-1 - oo*I)', '-oo - I*pi/2'],
    ['asinh(oo*I)', 'oo'],
    ['asinh(oo - oo*I)', 'zoo'],
    // limit: acosh(-x + I) -> oo + I*pi (SymPy acosh(oo*I) = oo + I*pi/2)
    ['acosh(oo - I)', 'oo'],
    ['acosh(-oo + I)', 'oo + I*pi'],
    ['acosh(-oo - I)', 'oo - I*pi'],
    ['acosh(1 - oo*I)', 'oo - I*pi/2'],
    ['acosh(oo*I)', 'oo + I*pi/2'],
    ['acosh(-oo + oo*I)', 'zoo'],
    ['acosh(zoo)', 'zoo'],
    // limit: atanh -> I*pi/2 times the sign of the imaginary part (SymPy atanh(oo) = -I*pi/2)
    ['atanh(oo + I)', 'I*pi/2'],
    ['atanh(-oo - I)', '-I*pi/2'],
    ['atanh(1 - oo*I)', '-I*pi/2'],
    ['atanh(-oo + oo*I)', 'I*pi/2'],
    ['atanh(oo)', '-I*pi/2'],
    ['atanh(zoo)', 'I*AccumBounds(-pi/2, pi/2)'],
    ['acoth(oo + I)', '0'],
    ['acoth(-1 + oo*I)', '0'],
    ['acoth(oo - oo*I)', '0'],
    ['acoth(zoo)', '0'],
    // limit: asech(z) = acosh(1/z), 1/z -> 0 from the side opposite to z (SymPy asech(oo*I) = -I*pi/2)
    ['asech(oo + I)', '-I*pi/2'],
    ['asech(-oo - I)', 'I*pi/2'],
    ['asech(1 + oo*I)', '-I*pi/2'],
    ['asech(oo - oo*I)', 'I*pi/2'],
    ['asech(oo)', 'I*pi/2'],
    ['acsch(1 + oo*I)', '0'],
    ['acsch(-oo + oo*I)', '0'],
    ['acsch(oo + I)', '0'],
    // limit: atan -> pi/2 times the sign of the real part; acot, asec, acsc -> 0, pi/2, 0
    ['atan(oo - I)', 'pi/2'],
    ['atan(-1 + oo*I)', '-pi/2'],
    ['atan(-oo + oo*I)', '-pi/2'],
    ['atan(oo*I)', 'pi/2'],
    ['atan(oo)', 'pi/2'],
    ['acot(-oo + I)', '0'],
    ['acot(oo + oo*I)', '0'],
    ['asec(1 + oo*I)', 'pi/2'],
    ['asec(-oo - oo*I)', 'pi/2'],
    ['acsc(1 - oo*I)', '0'],
    ['acsc(oo + oo*I)', '0'],
    // limit: log(oo + oo*I) (the modulus grows, the argument has no limit; SymPy keeps it)
    ['log(oo + oo*I)', 'zoo'],
    // arg and sign: the limits, SymPy's arg(oo + oo*I) = pi/4, arg(-oo + oo*I) = pi and
    // arg(-oo - oo*I) = -3*pi/4 where there is none; SymPy gives arg(-1 + oo*I) = nan, sign(oo + I)
    // stays (limits pi/2 and 1)
    ['arg(oo + oo*I)', 'pi/4'],
    ['arg(oo - oo*I)', '-pi/4'],
    ['arg(-oo + oo*I)', 'pi'],
    ['arg(-oo - oo*I)', '-3*pi/4'],
    ['arg(-1 + oo*I)', 'pi/2'],
    ['arg(1 - oo*I)', '-pi/2'],
    ['arg(zoo)', 'nan'],
    ['arg(oo + I)', '0'],
    ['sign(oo*I)', 'I'],
    ['sign(1 - oo*I)', '-I'],
    ['sign(-oo + I)', '-1'],
    ['sign(oo + oo*I)', 'sign(oo + oo*I)'],
    ['re(zoo)', 'nan'],
    ['im(zoo)', 'nan'],
    ['re(oo + I)', 'oo'],
    // forms that are not decided: a symbol, a finite part of undecided sign where the value depends on
    // it, a non-real finite term. The imaginary part sqrt(2) + sqrt(3) - sqrt(5 + 2*sqrt(6)) is 0, which
    // symjs does not decide: SymPy gives erf(...) = 1 (the value for any sign) and asin(...) = -oo*I
    // (the value at oo), symjs keeps the asin
    ['asin(x + oo*I)', 'asin(x + oo*I)'],
    ['erf(oo + I*(sqrt(2) + sqrt(3) - sqrt(5 + 2*sqrt(6))))', '1'],
    ['asin(oo + I*(sqrt(2) + sqrt(3) - sqrt(5 + 2*sqrt(6))))', 'asin(oo + I*(-sqrt(2*sqrt(6) + 5) + sqrt(2) + sqrt(3)))'],
    ['erf(sqrt(2) + sqrt(3) - sqrt(5 + 2*sqrt(6)) + oo*I)', 'erf(-sqrt(2*sqrt(6) + 5) + sqrt(2) + sqrt(3) + oo*I)'],
    ['erf(sqrt(I) + oo*I)', 'erf(sqrt(I) + oo*I)'],
    ['acoth(nan)', 'nan'],
  ];
  it.each(cases)('%s = %s', (src, want) => {
    expect(String(parse(src))).toBe(want);
  });
  it('atan(zoo) stays unevaluated', () => {
    // SymPy atan(zoo) = AccumBounds(-pi/2, pi/2)
    expect(String(parse('atan(zoo)'))).toBe('atan(zoo)');
  });
});

describe('Abs of a sum', () => {
  it('takes out the minus sign (SymPy signsimp in Abs.eval)', () => {
    const [x, y] = [symbol('x'), symbol('y')];
    expect(String(abs(add(1, mul(-1, x))))).toBe('Abs(x - 1)');
    expect(String(abs(add(y, mul(-1, x))))).toBe('Abs(x - y)');
    expect(String(abs(add(x, mul(-1, y))))).toBe('Abs(x - y)');
  });
});

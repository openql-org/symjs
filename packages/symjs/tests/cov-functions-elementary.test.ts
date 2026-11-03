// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Coverage of functions/elementary.ts: sin/cos/tan tables, inverse functions, log (with a
// base), abs, re, im, arg, conjugate, adjoint and transpose. Expected values are str() results
// of SymPy 1.14 unless a comment says otherwise.

import { describe, expect, it } from 'vitest';
import * as sj from '../src';
import { Float, Sym, adjoint, arg, pow, transpose } from '../src';
import { forEachEntry } from '../src/functions/elementary';

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

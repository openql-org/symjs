// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/functions/hyper.ts.
//
// hyper, meijerg, the spherical Bessel functions jn and yn, KroneckerDelta and kroneckersimp. Expected
// values are str() results of SymPy 1.14 (mpmath 1.3 values for the numerics) unless a comment says
// otherwise.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { diff, evalf, expand, expandJn, Float, hyper, jn, KroneckerDelta, NotImplementedError, parse, sstr, Sym, symbols, toComplex } from '../../src';

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
const HYPER_CASES: Case[] = [
  ["s", "H(2, 1, a, b, c, 0)", "hyper((a, b), (c,), 0)"],
  ["s", "H(2, 1, a, b, c, x)", "hyper((a, b), (c,), x)"],
  ["s", "H(1, 0, a, x)", "hyper((a,), (), x)"],
  ["SUB", "H(2, 1, a, b, c, x)", "hyper((a, b), (c,), 2)"],
  ["L", "H(2, 1, a, b, c, x)", "{{}_{2}F_{1}\\left(\\begin{matrix} a, b \\\\ c \\end{matrix}\\middle| {x} \\right)}"],
  ["L", "H(1, 0, a, x)", "{{}_{1}F_{0}\\left(\\begin{matrix} a \\\\  \\end{matrix}\\middle| {x} \\right)}"],
  ["D", "H(2, 1, a, b, c, x)", "a*b*hyper((a + 1, b + 1), (c + 1,), x)/c"],
  ["D", "H(2, 1, a, b, c, x**2)", "2*a*b*x*hyper((a + 1, b + 1), (c + 1,), x**2)/c"],
  ["s", "G(0, 2, 3, 0, 1, 1, 0, 0, a, x)", "meijerg(((), (1, 1)), ((0, 0, a), ()), x)"],
  ["SUB", "G(0, 2, 3, 0, 1, 1, 0, 0, a, x)", "meijerg(((), (1, 1)), ((0, 0, a), ()), 2)"],
  ["D", "expint(nu, x)", "-expint(nu - 1, x)"],
  ["D", "expint(x, z)", "-z**(x - 1)*meijerg(((), (1, 1)), ((0, 0, 1 - x), ()), z)"],
  ["RW", "catalan(n);hyper", "hyper((-n, 1 - n), (2,), 1)"],
  ["RW", "rf(x, n);gamma", "Piecewise((gamma(n + x)/gamma(x), x > 0), ((-1)**n*gamma(1 - x)/gamma(-n - x + 1), True))"],
  ["RW", "rf(p, n);gamma", "gamma(n + p)/gamma(p)"],
  ["RW", "rf(-p, n);gamma", "(-1)**n*gamma(p + 1)/gamma(-n + p + 1)"],
  ["RW", "rf(2, n);gamma", "gamma(n + 2)"],
  ["RW", "rf(-2, n);gamma", "2*(-1)**n/gamma(3 - n)"],
  ["RW", "sinc(x);jn", "jn(0, x)"],
  ["s", "jn(2, 0)", "0"],
  ["s", "jn(0, 0)", "1"],
  ["s", "jn(x, 0)", "jn(x, 0)"],
  ["s", "yn(2, x)", "yn(2, x)"],
  ["s", "yn(2, 0)", "yn(2, 0)"],
  ["D", "jn(2, x)", "jn(1, x) - 3*jn(2, x)/x"],
  ["D", "yn(n, x)", "yn(n - 1, x) - (n + 1)*yn(n, x)/x"],
  ["N", "jn(2, 3/2)", [0.12734928368840823, 0.0]],
  ["N", "yn(2, 3/2)", [-1.345712693620451, 0.0]],
  ["N", "jn(1, 1 + I)", [0.3950657977082261, 0.26208507473901843]],
  ["s", "KroneckerDelta(1, 1)", "1"],
  ["s", "KroneckerDelta(1, 2)", "0"],
  ["s", "KroneckerDelta(x, x)", "1"],
  ["s", "KroneckerDelta(x, y)", "KroneckerDelta(x, y)"],
  ["s", "KroneckerDelta(x, x + 1)", "0"],
  ["s", "KroneckerDelta(I, 2)", "0"],
  ["KS", "KroneckerDelta(0, x)*KroneckerDelta(1, x)", "0"],
  ["KS", "KroneckerDelta(x, 0)*KroneckerDelta(1, x)", "0"],
  ["KS", "KroneckerDelta(0, x)*KroneckerDelta(x, 1)", "0"],
  ["KS", "KroneckerDelta(x, 0)*KroneckerDelta(x, 1)", "0"],
  ["KS", "KroneckerDelta(x, 0)*KroneckerDelta(x, 0)", "KroneckerDelta(0, x)"],
  ["KS", "KroneckerDelta(x, 0)*KroneckerDelta(y, 1)", "KroneckerDelta(0, x)*KroneckerDelta(1, y)"],
  ["KS", "1 + KroneckerDelta(0, x)*KroneckerDelta(1, x)*y", "1"],
  ["KS", "KroneckerDelta(0, x) + 1", "KroneckerDelta(0, x) + 1"],
  ["s", "KroneckerDelta(x, 0)", "KroneckerDelta(0, x)"],
  ["s", "KroneckerDelta(y, x)", "KroneckerDelta(x, y)"],
  ["s", "KroneckerDelta(p, -p)", "0"],
  ["s", "jn(-1, 0)", "zoo"],
  ["s", "jn(n, 0)", "zoo"],
  ["s", "jn(2, oo)", "0"],
  ["s", "jn(x, -oo)", "0"],
  ["s", "KroneckerDelta(gamma(1/3), 2)", "0"],
  ["s", "KroneckerDelta(subfactorial(1/2), 2)", "KroneckerDelta(2, subfactorial(1/2))"],
];

describe('hyper, meijerg, spherical Bessel, KroneckerDelta and Gamma limits', () => {
  it('match SymPy', async () => {
    const { hyper, jn, KroneckerDelta, kroneckersimp, rewrite, limit, oo } = await import('../../src');
    const [x, z, n, nu, i] = symbols('x z n nu i');
    const P = (s: string) => parse(s, { symbols: { x, z, n, nu } } as never);
    expect(sstr(kroneckersimp(parse('1 + KD', { symbols: { KD: KroneckerDelta(0, i).mul(KroneckerDelta(1, i)) } } as never)))).toBe('1');
    expect(sstr(rewrite(P('sinc(x)'), 'jn'))).toBe('jn(0, x)');
    expect(sstr(diff(jn(0, x), x))).toBe('jn(-1, x) - jn(0, x)/x');
    expect(sstr(rewrite(P('catalan(n)'), 'hyper'))).toBe('hyper((-n, 1 - n), (2,), 1)');
    expect(sstr(diff(hyper([1, 2], [3], z), z))).toBe('2*hyper((2, 3), (4,), z)/3');
    expect(sstr(diff(P('expint(nu, z)'), nu))).toBe('-z**(nu - 1)*meijerg(((), (1, 1)), ((0, 0, 1 - nu), ()), z)');
    expect(sstr(rewrite(P('rf(1 - pi/2, n)'), 'gamma'))).toBe('(-1)**n*gamma(pi/2)/gamma(-n + pi/2)');
    expect(sstr(limit(P('4**n*factorial(n)**2/(2**(2*n)*rf(1/2, n)*rf(3/2, n))'), n, oo))).toBe('pi/2');
  });
});

describe('hypergeometric functions, spherical Bessel functions and KroneckerDelta (SymPy)', () => check(HYPER_CASES));

describe('hyper: cases outside the table', () => {
  const z = new Sym('z');
  it('numeric values of hyper by its power series', () => {
    // mpmath: hyp2f1(1, 2, 3, 1/2) and hyp1f1(1, 3, 1/2 + I/3)
    const v = toComplex(evalf(hyper([1, 2], [3], sj.Rational.of(1, 2))));
    expect(v.re).toBeCloseTo(1.54517744447956, 12);
    const w = toComplex(evalf(hyper([1], [3], sj.add(sj.Rational.of(1, 2), sj.mul(sj.Rational.of(1, 3), sj.I)))));
    expect(w.re).toBeCloseTo(1.17725852093618, 12);
    expect(w.im).toBeCloseTo(0.142700680013728, 12);
    // SymPy continues analytically (-1 - pi*I/2 here); outside the unit disk the series is not used
    expect(String(evalf(hyper([1, 2], [3], 2)))).toBe('hyper((1.0, 2.0), (3.0,), 2.0)');
  });
  it('derivatives with respect to a parameter are not implemented', () => {
    // SymPy: Derivative(hyper((b, x), (c,), z), x)
    expect(() => diff(hyper([x, 2], [3], z), x)).toThrow(NotImplementedError);
    // SymPy: Derivative(jn(x, z), x)
    expect(() => diff(jn(x, z), x)).toThrow(NotImplementedError);
  });
  it('expandJn agrees with SymPy expand_func (after expand)', () => {
    // expand(expand_func(jn(n, z))) and expand(expand_func(yn(n, z))) in SymPy
    expect(String(expandJn(0, z))).toBe('sin(z)/z');
    expect(String(expandJn(0, z, 'yn'))).toBe('-cos(z)/z');
    expect(String(expand(expandJn(1, z)))).toBe('-cos(z)/z + sin(z)/z**2');
    expect(String(expand(expandJn(3, z)))).toBe('cos(z)/z - 6*sin(z)/z**2 - 15*cos(z)/z**3 + 15*sin(z)/z**4');
    expect(String(expand(expandJn(3, z, 'yn')))).toBe('sin(z)/z + 6*cos(z)/z**2 - 15*sin(z)/z**3 - 15*cos(z)/z**4');
  });
});

describe('KroneckerDelta', () => {
  it('arguments that differ structurally but not in value', () => {
    // SymPy KroneckerDelta(1, 1.0)
    expect(String(KroneckerDelta(1, new Float(1)))).toBe('1');
  });
});

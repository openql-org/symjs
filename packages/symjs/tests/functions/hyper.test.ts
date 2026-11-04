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
    // SymPy hyper((1, 2), (3,), 2).evalf() = -1.0 - 1.5707963267949*I (mpmath hyp2f1, the 1/z transformation)
    expect(String(evalf(hyper([1, 2], [3], 2)))).toBe('-1.0 - 1.5707963267949*I');
  });
  it('2F1 at any precision, with the analytic continuation of mpmath hyp2f1', () => {
    // hyper((a, b), (c,), z) of SymPy, the parameters and the argument as SymPy sources
    const ev = (a: string, b: string, c: string, z: string, n?: number) => String(evalf(hyper([sj.parse(a), sj.parse(b)], [sj.parse(c)], sj.parse(z)), n));
    // SymPy 1.14 evalf; exp(+-I*pi/3) is reached by Gosper's recurrence
    expect(ev('1', '2', '3', 'exp(I*pi/3)')).toBe('0.813799364234218 + 0.68485325637228*I');
    expect(ev('1', '2', '3', 'exp(-I*pi/3)')).toBe('0.813799364234218 - 0.68485325637228*I');
    expect(ev('1/2', '1', '3/2', 'exp(I*pi/3)')).toBe('0.962958578924434 + 0.350935287356627*I');
    expect(ev('1', '2', '3', 'exp(I*pi/3)', 30)).toBe('0.813799364234217850594078257642 + 0.684853256372279547373231880413*I');
    expect(ev('1', '2', '3', '2.5')).toBe('-0.929748834594613 - 1.00530964914873*I');
    expect(ev('1', '2', '3', '2*I')).toBe('0.402359478108525 + 0.446425641102955*I');
    // z = 1: Gauss's theorem where the series converges, the infinity approached from below otherwise
    expect(ev('1/2', '1/3', '2', '1', 30)).toBe('1.15959526696392836576999205157');
    expect(ev('1', '2', '3', '1')).toBe('oo');
    expect(ev('1', '2', '-1/2', '1')).toBe('-oo');
    // SymPy gives -oo + oo*I for hyper((I, 2), (1,), 1), whose value at 1 - eps is not real; symjs keeps it
    expect(ev('I', '2', '1', '1')).toBe('hyper((2.0, 1.0*I), (1.0,), 1.0)');
    // c a nonpositive integer: a pole of the series unless it terminates first (SymPy: oo, 1.91666666666667, oo)
    expect(ev('1', '2', '-3', '1/2')).toBe('oo');
    expect(ev('-2', '2', '-3', '1/2')).toBe('1.91666666666667');
    expect(ev('-4', '2', '-3', '1/2')).toBe('oo');
    // 2F2 by the power series (SymPy hyper((1, 2), (3, 4), 1/2).evalf())
    expect(String(evalf(hyper([1, 2], [3, 4], sj.Rational.of(1, 2))))).toBe('1.09002619782383');
    // outside the unit disk other functions are not evaluated (SymPy hyper((1, 2), (3, 4), 2).evalf() = 1.46803038322526)
    expect(String(evalf(hyper([1, 2], [3, 4], 2)))).toBe('hyper((1.0, 2.0), (3.0, 4.0), 2.0)');
    // a symbol stays (SymPy hyper((1, 2), (3,), x).evalf())
    expect(ev('1', '2', '3', 'x')).toBe('hyper((1.0, 2.0), (3.0,), x)');
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

describe('meijerg accessors (SymPy an, aother, bm, bother, nu, delta, get_period)', () => {
  it('parameters and invariants', () => {
    const [a, b, zz] = [new Sym('a'), new Sym('b'), new Sym('z')];
    const g = sj.meijerg([a], [1], [b, 2], [], zz);
    if (!(g instanceof sj.MeijerG)) throw new TypeError('meijerg');
    expect([g.an, g.aother, g.bm, g.bother, g.ap, g.bq].map((l) => l.map(String).join(','))).toEqual(['a', '1', 'b,2', '', 'a,1', 'b,2']);
    expect(String(g.argument)).toBe('z');
    expect(String(g.nu)).toBe('-a + b + 1');
    expect(String(g.delta)).toBe('1');
    // SymPy get_period: oo for parameters that are not rational
    expect(String(g.getPeriod())).toBe('oo');
  });
  it('get_period', () => {
    const G = (an: sj.ExprLike[], ap: sj.ExprLike[], bm: sj.ExprLike[], bq: sj.ExprLike[]) => {
      const g = sj.meijerg(an, ap, bm, bq, x);
      if (!(g instanceof sj.MeijerG)) throw new TypeError('meijerg');
      return String(g.getPeriod());
    };
    expect(G([], [], [0], [])).toBe('2*pi');
    expect(G([], [], [sj.Rational.of(1n, 2n)], [0])).toBe('4*pi');
    expect(G([0], [], [1], [])).toBe('2*pi');
    expect(G([1, 2], [], [], [])).toBe('oo');
    expect(G([sj.Rational.of(1n, 3n)], [], [], [])).toBe('6*pi');
    expect(G([], [], [0, 1], [])).toBe('oo');
  });
});

/** str() of the SymPy operation named by kind applied to src (the tables of the hyper parameters, expand_func and appellf1 (SymPy hyper) block below). */
function runAppell(kind: string, src: string): string {
  // (H(p, q, a1..ap, b1..bq, z) is hyper((a1..ap), (b1..bq), z) and G the meijerg of the locals above)
  const e = sj.parse(src, { locals: { ...locals, exp_polar: sj.expPolar } });
  if (kind === 'E') return String(e);
  if (kind === 'F') return String(sj.expandFunc(e));
  if (kind === 'D') return String(sj.diff(e, new sj.Sym('x')));
  if (kind.startsWith('D:')) return String(sj.diff(e, new sj.Sym(kind.slice(2))));
  return String(sj.evalf(e, kind.length > 1 ? Number(kind.slice(1)) : 15));
}

describe('hyper parameters, expand_func and appellf1 (SymPy hyper)', () => {
  const cases: [string, string, string][] = [
    ['E', 'H(3, 2, 3, 1, 2, 3, 4, x)', 'hyper((1, 2), (4,), x)'],
    ['E', 'H(2, 1, n, a, n**2, x)', 'hyper((a, n), (n**2,), x)'],
    ['E', 'H(2, 1, 1, 1, 2, x)', 'hyper((1, 1), (2,), x)'],
    ['E', 'H(2, 2, 2, 1, 1, 2, x)', 'hyper((), (), x)'],
    ['E', 'H(1, 0, 1, exp_polar(I*pi)/2)', 'hyper((1,), (), -1/2)'],
    ['E', 'H(2, 1, 1, 2, 3, exp_polar(I*pi)/2)', 'hyper((1, 2), (3,), -1/2)'],
    ['E', 'H(2, 1, 1, 2, 3, 2*exp_polar(I*pi))', 'hyper((1, 2), (3,), 2*exp_polar(I*pi))'],
    ['E', 'H(1, 1, 1, 2, exp_polar(I*pi)*x)', 'hyper((1,), (2,), -x)'],
    ['F', 'H(2, 1, a, b, c, 1)', 'gamma(c)*gamma(-a - b + c)/(gamma(-a + c)*gamma(-b + c))'],
    ['F', 'x*H(2, 1, 1, 1, 2, -x)', 'log(x + 1)'],
    ['F', 'G(0, 0, 1, 0, 0, -x)', 'exp(x)'],
    ['F', 'H(1, 0, a, x)', '(1 - x)**(-a)'],
    ['E', 'appellf1(a, b1, b2, c, x, y)', 'appellf1(a, b1, b2, c, x, y)'],
    ['E', 'appellf1(a, b2, b1, c, x, y)', 'appellf1(a, b1, b2, c, y, x)'],
    ['E', 'appellf1(a, b, b, c, y, x)', 'appellf1(a, b, b, c, x, y)'],
    ['E', 'appellf1(a, b1, b2, c, 0, 0)', '1'],
    ['E', 'appellf1(40, 2, 6, 4, 15, 60)', 'appellf1(40, 2, 6, 4, 15, 60)'],
    ['E', 'appellf1(2., 1., 6., 4., 5., 6.)', '0.00633394262926730'],
    ['E', 'appellf1(12., 12., 6., 4., 0.5, 0.12)', '172870711.659936'],
    ['E', 'appellf1(20., 12., 10., 3., 0.5, 0.12)', '15605338197184.4'],
    ['D', 'appellf1(a, b1, b2, c, x, y)', 'a*b1*appellf1(a + 1, b2, b1 + 1, c + 1, y, x)/c'],
    ['D:y', 'appellf1(a, b1, b2, c, x, y)', 'a*b2*appellf1(a + 1, b1, b2 + 1, c + 1, x, y)/c'],
    ['D:a', 'appellf1(a, b1, b2, c, x, y)', 'Derivative(appellf1(a, b1, b2, c, x, y), a)'],
    ['N', 'appellf1(1, -2, 1, 4, 3, 1/2)', '0.472077083991796'],
    ['N', 'appellf1(-2, 1, 2, 4, 5, 6)', '11.8000000000000'],
    ['N', 'appellf1(1, -2, 1, 4, 1/4, 1/2)', '1.00847077083992'],
  ];
  it.each(cases)('%s %s', (kind, src, expected) => {
    expect(runAppell(kind, src)).toBe(expected);
  });
  it('builds appellf1 with the public constructor and evaluates it in double precision', () => {
    const s = sj.symbols('a b1 b2 c x y') as sj.Sym[];
    expect(String(sj.appellf1(...(s as [sj.Sym, sj.Sym, sj.Sym, sj.Sym, sj.Sym, sj.Sym])))).toBe('appellf1(a, b1, b2, c, x, y)');
    const v = sj.toComplex(new sj.Fn('appellf1', [1, -2, 1, 4, sj.Rational.of(1n, 4n), sj.Rational.of(1n, 2n)].map((k) => sj.sympify(k))));
    expect(v.re).toBeCloseTo(1.0084707708399179, 13);
  });
  it('keeps duplicate parameters with evaluate false (sorted)', () => {
    expect(String(sj.hyper([3, 1, 2], [3, 4], new sj.Sym('x'), { evaluate: false }))).toBe('hyper((1, 2, 3), (3, 4), x)');
  });
});

describe('hyper and appellf1 at arguments without a value or a continuation', () => {
  it('keeps an argument whose modulus is unknown', () => {
    // SymPy: hyper((1,), (), stieltjes(1)) stays
    expect(String(sj.hyper([1], [], sj.stieltjes(1)))).toBe('hyper((1,), (), stieltjes(1))');
  });
  it('raises where mpmath has no analytic continuation of F1', () => {
    // mpmath appellf1(1/2, 1/3, 1/5, 1/7, 2, 10) raises ValueError (analytic continuation not implemented)
    const r = (p: bigint, q: bigint) => sj.Rational.of(p, q);
    const e = new sj.Fn('appellf1', [r(1n, 2n), r(1n, 3n), r(1n, 5n), r(1n, 7n), sj.sympify(2), sj.sympify(10)]);
    expect(() => sj.toComplex(e)).toThrow(NotImplementedError);
  });
});

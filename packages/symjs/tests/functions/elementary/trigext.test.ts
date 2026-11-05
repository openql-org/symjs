// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/functions/elementary/trigext.ts.
//
// cot/sec/csc, the hyperbolic and inverse functions, sinc and the compositions with inverse functions.
// Expected values are str() results of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../../src';
import { mul, parse, S, tan } from '../../../src';

// ---- table harness: each case is [kind, SymPy source, str() of the SymPy 1.14 result or [re, im]] ----
type Case = [kind: string, src: string, expected: string | [number, number]];
const x = new sj.Sym('x');
it('evaluates acos on imaginary arguments and logs of negative constants', () => {
  for (const [source, expected] of [
    ['acos(I)', 'pi/2 - I*log(1 + sqrt(2))'],
    ['acos(-I)', 'pi/2 + I*log(1 + sqrt(2))'],
    ['acos(2*I)', 'pi/2 - I*asinh(2)'],
    ['log(-1-sqrt(2))', 'log(1 + sqrt(2)) + I*pi'],
    ['log(-x-1)', 'log(-x - 1)'],
  ] as const) expect(String(sj.parse(source))).toBe(expected);
});
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
const TRIG_CASES: Case[] = [
  ["s", "sin(asin(x))", "x"],
  ["s", "sin(acos(x))", "sqrt(1 - x**2)"],
  ["s", "sin(atan(x))", "x/sqrt(x**2 + 1)"],
  ["s", "sin(acot(x))", "1/(x*sqrt(1 + x**(-2)))"],
  ["s", "sin(acsc(x))", "1/x"],
  ["s", "sin(asec(x))", "sqrt(1 - 1/x**2)"],
  ["s", "sin(atan2(y, x))", "y/sqrt(x**2 + y**2)"],
  ["s", "cos(asin(x))", "sqrt(1 - x**2)"],
  ["s", "cos(acos(x))", "x"],
  ["s", "cos(atan(x))", "1/sqrt(x**2 + 1)"],
  ["s", "cos(acot(x))", "1/sqrt(1 + x**(-2))"],
  ["s", "cos(acsc(x))", "sqrt(1 - 1/x**2)"],
  ["s", "cos(asec(x))", "1/x"],
  ["s", "cos(atan2(y, x))", "x/sqrt(x**2 + y**2)"],
  ["s", "tan(asin(x))", "x/sqrt(1 - x**2)"],
  ["s", "tan(acos(x))", "sqrt(1 - x**2)/x"],
  ["s", "tan(atan(x))", "x"],
  ["s", "tan(acot(x))", "1/x"],
  ["s", "tan(acsc(x))", "1/(x*sqrt(1 - 1/x**2))"],
  ["s", "tan(asec(x))", "x*sqrt(1 - 1/x**2)"],
  ["s", "tan(atan2(y, x))", "y/x"],
  ["s", "cot(asin(x))", "sqrt(1 - x**2)/x"],
  ["s", "cot(acos(x))", "x/sqrt(1 - x**2)"],
  ["s", "cot(atan(x))", "1/x"],
  ["s", "cot(acot(x))", "x"],
  ["s", "cot(acsc(x))", "x*sqrt(1 - 1/x**2)"],
  ["s", "cot(asec(x))", "1/(x*sqrt(1 - 1/x**2))"],
  ["s", "cot(atan2(y, x))", "x/y"],
  ["s", "sinh(asinh(x))", "x"],
  ["s", "sinh(acosh(x))", "sqrt(x - 1)*sqrt(x + 1)"],
  ["s", "sinh(atanh(x))", "x/sqrt(1 - x**2)"],
  ["s", "sinh(acoth(x))", "1/(sqrt(x - 1)*sqrt(x + 1))"],
  ["s", "cosh(asinh(x))", "sqrt(x**2 + 1)"],
  ["s", "cosh(acosh(x))", "x"],
  ["s", "cosh(atanh(x))", "1/sqrt(1 - x**2)"],
  ["s", "cosh(acoth(x))", "x/(sqrt(x - 1)*sqrt(x + 1))"],
  ["s", "tanh(asinh(x))", "x/sqrt(x**2 + 1)"],
  ["s", "tanh(acosh(x))", "sqrt(x - 1)*sqrt(x + 1)/x"],
  ["s", "tanh(atanh(x))", "x"],
  ["s", "tanh(acoth(x))", "1/x"],
  ["s", "coth(asinh(x))", "sqrt(x**2 + 1)/x"],
  ["s", "coth(acosh(x))", "x/(sqrt(x - 1)*sqrt(x + 1))"],
  ["s", "coth(atanh(x))", "1/x"],
  ["s", "coth(acoth(x))", "x"],
  ["s", "sec(asec(x))", "x"],
  ["s", "sec(acsc(x))", "1/sqrt(1 - 1/x**2)"],
  ["s", "sec(asech(x))", "sec(asech(x))"],
  ["s", "sec(acsch(x))", "sec(acsch(x))"],
  ["s", "sec(asin(x))", "1/sqrt(1 - x**2)"],
  ["s", "sec(acos(x))", "1/x"],
  ["s", "sec(atan(x))", "sqrt(x**2 + 1)"],
  ["s", "sec(asinh(x))", "sec(asinh(x))"],
  ["s", "csc(asec(x))", "1/sqrt(1 - 1/x**2)"],
  ["s", "csc(acsc(x))", "x"],
  ["s", "csc(asech(x))", "csc(asech(x))"],
  ["s", "csc(acsch(x))", "csc(acsch(x))"],
  ["s", "csc(asin(x))", "1/x"],
  ["s", "csc(acos(x))", "1/sqrt(1 - x**2)"],
  ["s", "csc(atan(x))", "sqrt(x**2 + 1)/x"],
  ["s", "csc(asinh(x))", "csc(asinh(x))"],
  ["s", "sech(asec(x))", "sech(asec(x))"],
  ["s", "sech(acsc(x))", "sech(acsc(x))"],
  ["s", "sech(asech(x))", "x"],
  ["s", "sech(acsch(x))", "sech(acsch(x))"],
  ["s", "sech(asin(x))", "sech(asin(x))"],
  ["s", "sech(acos(x))", "sech(acos(x))"],
  ["s", "sech(atan(x))", "sech(atan(x))"],
  ["s", "sech(asinh(x))", "1/sqrt(x**2 + 1)"],
  ["s", "csch(asec(x))", "csch(asec(x))"],
  ["s", "csch(acsc(x))", "csch(acsc(x))"],
  ["s", "csch(asech(x))", "csch(asech(x))"],
  ["s", "csch(acsch(x))", "x"],
  ["s", "csch(asin(x))", "csch(asin(x))"],
  ["s", "csch(acos(x))", "csch(acos(x))"],
  ["s", "csch(atan(x))", "csch(atan(x))"],
  ["s", "csch(asinh(x))", "1/x"],
  ["s", "asec(x)", "asec(x)"],
  ["s", "acosh(x)", "acosh(x)"],
  ["s", "asech(x)", "asech(x)"],
  ["s", "tan(3*pi/8)", "1 + sqrt(2)"],
  ["s", "tan(-3*pi/8)", "-sqrt(2) - 1"],
  ["s", "tan(pi/2 + x)", "-cot(x)"],
  ["s", "tan(3*pi/2 + x)", "-cot(x)"],
  ["s", "tan(2*I)", "I*tanh(2)"],
  ["s", "tan(-2*I)", "-I*tanh(2)"],
  ["s", "tan(I*x)", "I*tanh(x)"],
  ["s", "sinh(zoo)", "nan"],
  ["s", "cosh(zoo)", "nan"],
  ["s", "tanh(zoo)", "nan"],
  ["s", "sinh(x + I*pi)", "-sinh(x)"],
  ["s", "sinh(x + I*pi/2)", "I*cosh(x)"],
  ["s", "cosh(x + I*pi)", "-cosh(x)"],
  ["s", "cosh(x + 3*I*pi/2)", "-I*sinh(x)"],
  ["s", "tanh(x + I*pi)", "tanh(x)"],
  ["s", "tanh(x + I*pi/2)", "coth(x)"],
  ["s", "tanh(-2*I)", "-I*tan(2)"],
  ["s", "tanh(2*I)", "I*tan(2)"],
  ["s", "asin(2*I)", "I*asinh(2)"],
  ["s", "atan(2*I)", "I*atanh(2)"],
  ["s", "cot(nan)", "nan"],
  ["s", "cot(zoo)", "nan"],
  ["s", "cot(0)", "zoo"],
  ["s", "cot(-x)", "-cot(x)"],
  ["s", "cot(I*x)", "-I*coth(x)"],
  ["s", "cot(pi)", "zoo"],
  ["s", "cot(3*pi/2)", "0"],
  ["s", "cot(pi/8)", "1 + sqrt(2)"],
  ["s", "cot(3*pi/8)", "-1 + sqrt(2)"],
  ["s", "cot(pi/3)", "sqrt(3)/3"],
  ["s", "cot(pi/7)", "cot(pi/7)"],
  ["s", "cot(x + pi)", "cot(x)"],
  ["s", "cot(x + pi/2)", "-tan(x)"],
  ["s", "sec(-x)", "sec(x)"],
  ["s", "csc(-x)", "-csc(x)"],
  ["s", "sec(5*pi/3)", "2"],
  ["s", "csc(5*pi/3)", "-2*sqrt(3)/3"],
  ["s", "sec(2*pi/3)", "-2"],
  ["s", "csc(2*pi/3)", "2*sqrt(3)/3"],
  ["s", "sec(pi/3)", "2"],
  ["s", "csc(pi/6)", "2"],
  ["s", "sec(x + pi)", "-sec(x)"],
  ["s", "csc(x + pi/2)", "sec(x)"],
  ["s", "sec(pi/7)", "sec(pi/7)"],
  ["s", "csc(I*x)", "-I/sinh(x)"],
  ["s", "sec(I*x)", "1/cosh(x)"],
  ["s", "coth(nan)", "nan"],
  ["s", "coth(zoo)", "nan"],
  ["s", "coth(oo)", "1"],
  ["s", "coth(-oo)", "-1"],
  ["s", "coth(0)", "zoo"],
  ["s", "coth(-2)", "-coth(2)"],
  ["s", "coth(I*x)", "-I*cot(x)"],
  ["s", "coth(-I*x)", "I*cot(x)"],
  ["s", "coth(-x)", "-coth(x)"],
  ["s", "coth(x + I*pi)", "coth(x)"],
  ["s", "coth(x + I*pi/2)", "tanh(x)"],
  ["s", "sech(-x)", "sech(x)"],
  ["s", "csch(-x)", "-csch(x)"],
  ["s", "sech(I*x)", "1/cos(x)"],
  ["s", "csch(I*x)", "-I/sin(x)"],
  ["s", "sech(0)", "1"],
  ["s", "csch(0)", "zoo"],
  ["s", "asinh(nan)", "nan"],
  ["s", "asinh(oo)", "oo"],
  ["s", "asinh(-oo)", "-oo"],
  ["s", "asinh(zoo)", "zoo"],
  ["s", "asinh(-1)", "log(-1 + sqrt(2))"],
  ["s", "asinh(-2)", "-asinh(2)"],
  ["s", "acosh(nan)", "nan"],
  ["s", "acosh(oo)", "oo"],
  ["s", "acosh(-oo)", "oo"],
  ["s", "acosh(zoo)", "zoo"],
  ["s", "acosh(-1)", "I*pi"],
  ["s", "acosh(2)", "acosh(2)"],
  ["s", "acosh(-2)", "acosh(-2)"],
  ["s", "atanh(nan)", "nan"],
  ["s", "atanh(-1)", "-oo"],
  ["s", "atanh(oo)", "-I*pi/2"],
  ["s", "atanh(-oo)", "I*pi/2"],
  ["s", "atanh(-2)", "-atanh(2)"],
  ["s", "atanh(zoo)", "I*AccumBounds(-pi/2, pi/2)"],
  ["s", "atanh(tanh(2))", "2"],
  ["s", "atanh(tanh(x))", "atanh(tanh(x))"],
  ["s", "acoth(nan)", "nan"],
  ["s", "acoth(oo)", "0"],
  ["s", "acoth(-oo)", "0"],
  ["s", "acoth(-1)", "-oo"],
  ["s", "acoth(-2)", "-acoth(2)"],
  ["s", "acoth(zoo)", "0"],
  ["s", "acot(nan)", "nan"],
  ["s", "acot(oo)", "0"],
  ["s", "acot(-oo)", "0"],
  ["s", "acot(-1)", "-pi/4"],
  ["s", "acot(zoo)", "0"],
  ["s", "acot(cot(x))", "acot(cot(x))"],
  ["s", "acot(-x)", "-acot(x)"],
  ["s", "asec(-1)", "pi"],
  ["s", "asec(oo)", "pi/2"],
  ["s", "asec(-oo)", "pi/2"],
  ["s", "asec(zoo)", "pi/2"],
  ["s", "asec(nan)", "nan"],
  ["s", "asec(2)", "pi/3"],
  ["s", "acsc(-1)", "-pi/2"],
  ["s", "acsc(oo)", "0"],
  ["s", "acsc(-oo)", "0"],
  ["s", "acsc(zoo)", "0"],
  ["s", "acsc(nan)", "nan"],
  ["s", "asech(nan)", "nan"],
  ["s", "asech(-1)", "I*pi"],
  ["s", "asech(oo)", "I*pi/2"],
  ["s", "asech(-oo)", "I*pi/2"],
  ["s", "asech(zoo)", "I*AccumBounds(-pi/2, pi/2)"],
  ["s", "asech(2)", "I*pi/3"],
  ["s", "asech(1/2)", "asech(1/2)"],
  ["s", "acsch(nan)", "nan"],
  ["s", "acsch(oo)", "0"],
  ["s", "acsch(-oo)", "0"],
  ["s", "acsch(-1)", "-log(1 + sqrt(2))"],
  ["s", "acsch(zoo)", "0"],
  ["s", "acsch(2)", "log(1/2 + sqrt(5)/2)"],
  ["s", "sinc(oo)", "0"],
  ["s", "sinc(-oo)", "0"],
  ["s", "sinc(nan)", "nan"],
  ["s", "sinc(zoo)", "nan"],
  ["s", "sinc(0)", "1"],
  ["s", "sinc(pi)", "0"],
  ["s", "sinc(pi/2)", "2/pi"],
  ["s", "sinc(3*pi/2)", "-2/(3*pi)"],
  ["s", "sinc(x)", "sinc(x)"],
  ["N", "sinc(0)", [1.0, 0.0]],
  ["N", "acot(0)", [1.5707963267948966, 0.0]],
  ["NV", "sinc(x);x=0", [1.0, 0.0]],
  ["NV", "acot(x);x=0", [1.5707963267948966, 0.0]],
  ["NV", "acot(x);x=0.5", [1.1071487177940904, 0.0]],
  ["NV", "sinc(x);x=0.5", [0.958851077208406, 0.0]],
  ["EFl", "acot(0)", "1.57079632679490"],
  ["EFl", "sinc(0)", "1.00000000000000"],
];
const cases: [string, string][] = [
  // _peeloff_ipi / _peeloff_pi with a coefficient below 1/2 and with negative coefficients
  ['sinh(x + I*pi/4)', 'sinh(x + I*pi/4)'],
  ['sinh(x - 3*I*pi/2)', 'I*cosh(x)'],
  ['cosh(x - I*pi)', '-cosh(x)'],
  ['tan(x - 3*pi/2)', '-cot(x)'],
  ['tan(x - pi)', 'tan(x)'],
  ['cot(x-3*pi/2)', '-tan(x)'],
  // csc and sec through the value of sin and cos
  ['csc(x + pi)', '-csc(x)'],
  ['sec(x+pi)', '-sec(x)'],
  ['csc(x+pi/2)', 'sec(x)'],
  // the half-angle formula does not apply when cos(2*x) does not evaluate
  ['tan(pi/14)', 'tan(pi/14)'],
  ['cot(pi/14)', 'cot(pi/14)'],
  ['tan(I*y - I*x)', '-I*tanh(x - y)'],
  // table values at non-real arguments
  ['acosh(I)', 'log(1 + sqrt(2)) + I*pi/2'],
  ['asech(I)', 'log(1 + sqrt(2)) - I*pi/2'],
  ['acot(sqrt(3))', 'pi/6'],
  ['acot(1-sqrt(2))', '-3*pi/8'],
  ['acot(-1-sqrt(2))', '-pi/8'],
  ['acot(sqrt(3)-2)', '-5*pi/12'],
  ['asec(3)', 'asec(3)'],
  ['acsc(3)', 'acsc(3)'],
  ['sinc(pi/2)', '2/pi'],
  ['sinc(3*pi/2)', '-2/(3*pi)'],
  ['sinc(pi/3)', 'sinc(pi/3)'],
  ['csc(asin(x))', '1/x'],
  ['cot(acot(x))', 'x'],
];

describe('trigonometric and hyperbolic functions (SymPy eval and numerics)', () => check(TRIG_CASES));

describe('trigext evaluation', () => {
  it.each(cases)('%s', (src, want) => {
    expect(String(parse(src))).toBe(want);
  });
  it('tan of an imaginary multiple', () => {
    // SymPy tan(I*(1 - x)) = -I*tanh(x - 1)
    expect(String(tan(mul(S.I, parse('1 - x'))))).toBe('-I*tanh(x - 1)');
  });
});

describe('trigonometric functions at infinities (SymPy eval)', () => {
  const { oo, zoo, nan } = sj;
  const moo = mul(-1, oo);
  it.each([
    ['sin', sj.sin, 'AccumBounds(-1, 1)'],
    ['cos', sj.cos, 'AccumBounds(-1, 1)'],
    ['tan', sj.tan, 'AccumBounds(-oo, oo)'],
    ['cot', sj.cot, 'AccumBounds(-oo, oo)'],
    ['sec', sj.sec, 'AccumBounds(-oo, oo)'],
    ['csc', sj.csc, 'AccumBounds(-oo, oo)'],
  ] as const)('%s(oo) = %s, of zoo and nan nan', (_name, fn, want) => {
    expect(sj.str(fn(oo))).toBe(want);
    expect(sj.str(fn(moo))).toBe(want);
    expect(fn(zoo)).toBe(nan);
    expect(fn(nan)).toBe(nan);
  });
  it('sech and csch', () => {
    // SymPy: sech(oo) = csch(oo) = 0, sech(nan) = csch(nan) = nan
    for (const fn of [sj.sech, sj.csch]) {
      expect(fn(oo)).toBe(S.Zero);
      expect(fn(nan)).toBe(nan);
    }
  });
});

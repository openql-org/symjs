// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// The Mellin transform and its inverse (integrals/transforms/mellin.ts).
// Expected values are the str() / latex() forms printed by SymPy 1.14
// (mellin_transform, inverse_mellin_transform, _rewrite_gamma); where symjs
// deliberately differs, the SymPy result is quoted in a comment.

import { describe, expect, it } from 'vitest';
import type { Expr } from '../src';
import { DiracDelta, Heaviside, IntegralTransformError, InverseMellinTransform, MellinTransform, S, SymFunction, inverseMellinTransform, latex, mellinTransform, parse, subs, symbol, symbols } from '../src';
import { MellinTransformStripError, rewriteGamma } from '../src/integrals/transforms/mellin';

const [x, s, a, r, nu] = symbols('x s a r nu');
const p = symbol('p', { positive: true });
const P = (q: string) => parse(q, { symbols: [x, s, a, r, nu, p], locals: { Heaviside, DiracDelta } });
const show = (v: unknown): string => (Array.isArray(v) ? `(${v.map(show).join(', ')})` : String(v));

const M = (f: string) => show(mellinTransform(P(f), x, s));
const strip = (lo: string | undefined, hi: string | undefined): [Expr | undefined, Expr | undefined] => [lo === undefined ? undefined : P(lo), hi === undefined ? undefined : P(hi)];
const IM = (F: string, lo: string | undefined, hi: string | undefined) => show(inverseMellinTransform(P(F), s, x, strip(lo, hi)));
const RG = (F: string, lo: string | undefined, hi: string | undefined) => show(rewriteGamma(P(F), s, lo === undefined ? undefined : P(lo), hi === undefined ? undefined : P(hi)));

describe('mellin_transform from the table', () => {
  it('exp(-b*x**p)', () => {
    expect(M('3*exp(-x)')).toBe('(3*gamma(s), (0, oo), True)');
    expect(M('exp(-a*x)')).toBe('(gamma(s)/a**s, (0, oo), Abs(arg(a)) < pi/2)');
    expect(M('exp(-2*x**3)')).toBe('(gamma(s/3)/(3*2**(s/3)), (0, oo), True)');
    expect(M('exp(-2/x)')).toBe('(2**s*gamma(-s), (-oo, 0), True)');
    expect(M('exp(sin(x))')).toBe('MellinTransform(exp(sin(x)), x, s)');
    // SymPy: (a*gamma(1 + s/a)/(s*Abs(a)), (-oo, oo), re(_s/a) > 0); symjs needs a rational power
    expect(M('exp(-x**a)')).toBe('MellinTransform(exp(-x**a), x, s)');
    // SymPy: (exp(-I*pi*s)*lowergamma(s, -oo), (-oo, oo), True), but the integral diverges for every s
    expect(M('exp(x)')).toBe('MellinTransform(exp(x), x, s)');
  });
  it('Heaviside(b - x) and Heaviside(x - b)', () => {
    expect(M('Heaviside(2 - x)')).toBe('(2**s/s, (0, oo), True)');
    expect(M('Heaviside(x - 2)')).toBe('(-2**s/s, (-oo, 0), True)');
    expect(M('Heaviside(p - x)')).toBe('(p**s/s, (0, oo), True)');
    expect(M('Heaviside(x - p)')).toBe('(-p**s/s, (-oo, 0), True)');
    expect(M('x*Heaviside(2 - x)')).toBe('(2**(s + 1)/(s + 1), (-1, oo), True)');
    // SymPy: (-a**s/s, (-oo, 0), (a > 0) & (a < 0) & Ne(1/a, 0)), a contradictory condition
    expect(M('Heaviside(a - x)')).toBe('MellinTransform(Heaviside(a - x), x, s)');
    // SymPy: (-1/(2**s*s), (-oo, 0), True)
    expect(M('Heaviside(2*x - 1)')).toBe('MellinTransform(Heaviside(2*x - 1), x, s)');
    expect(M('Heaviside(x)')).toBe('MellinTransform(Heaviside(x), x, s)');
  });
  it('(1 + b*x)**(-r)', () => {
    // SymPy gives the condition Ne(a, 0), which is wrong for a < 0 (1/(1 - x) has no transform)
    expect(M('1/(1 + a*x)')).toBe('(pi/(a**s*sin(pi*s)), (0, 1), Abs(arg(a)) < pi)');
    // SymPy: (pi/(2*sin(pi*s/2)), (0, 2), True)
    expect(M('1/(x**2 + 1)')).toBe('MellinTransform(1/(x**2 + 1), x, s)');
  });
  it('sin, cos and besselj', () => {
    expect(M('sin(2*x)')).toBe('(sqrt(pi)*gamma(s/2 + 1/2)/(2*gamma(1 - s/2)), (-1, 1), True)');
    expect(M('sin(3*x)')).toBe('(2**s*sqrt(pi)*gamma(s/2 + 1/2)/(2*3**s*gamma(1 - s/2)), (-1, 1), True)');
    expect(M('cos(2*x)')).toBe('(sqrt(pi)*gamma(s/2)/(2*gamma(1/2 - s/2)), (0, 1), True)');
    expect(M('besselj(nu, x)')).toBe('(2**s*gamma(nu/2 + s/2)/(2*gamma(nu/2 - s/2 + 1)), (-re(nu), 3/2), True)');
    expect(M('besselj(nu, p*x)')).toBe('(2**s*gamma(nu/2 + s/2)/(2*p**s*gamma(nu/2 - s/2 + 1)), (-re(nu), 3/2), True)');
    expect(M('besselj(nu, 2*x)')).toBe('(gamma(nu/2 + s/2)/(2*gamma(nu/2 - s/2 + 1)), (-re(nu), 3/2), True)');
    expect(M('besselj(1, x)')).toBe('(2**s*gamma(s/2 + 1/2)/(2*gamma(3/2 - s/2)), (-1, 3/2), True)');
    // SymPy: (2**(s/2)*sqrt(pi)*gamma(s/4 + 1/2)/(4*gamma(1 - s/4)), (-2, 2), True)
    expect(M('sin(x**2)')).toBe('MellinTransform(sin(x**2), x, s)');
    // SymPy: (2**s*sqrt(pi)*gamma(s/2 + 1/2)/(2*a**s*gamma(1 - s/2)), (-1, 1), Eq(Abs(arg(a)), 0))
    expect(M('sin(a*x)')).toBe('MellinTransform(sin(a*x), x, s)');
    // SymPy: (pi/(s*sin(pi*s)), (-1, 0), True)
    expect(M('log(x + 1)')).toBe('MellinTransform(log(x + 1), x, s)');
  });
  it('products with a Heaviside factor', () => {
    expect(M('(x - 1)**r*Heaviside(x - 1)')).toBe('(gamma(-r - s)*gamma(r + 1)/gamma(1 - s), (-oo, -re(r)), re(r) > -1)');
    expect(M('(x - 1)**(r + 2)*Heaviside(x - 1)')).toBe('(gamma(r + 3)*gamma(-r - s - 2)/gamma(1 - s), (-oo, -re(r) - 2), re(r) > -3)');
    expect(M('(1 - x)**r*Heaviside(1 - x)')).toBe('(gamma(s)*gamma(r + 1)/gamma(r + s + 1), (0, oo), re(r) > -1)');
    expect(M('(1 - x)**(a + r)*Heaviside(1 - x)')).toBe('(gamma(s)*gamma(a + r + 1)/gamma(a + r + s + 1), (0, oo), re(a) + re(r) > -1)');
    // SymPy: (-lowergamma(s, 1) + gamma(s + 1)/s, (-oo, oo), True) and (lowergamma(s, 1), (0, oo), True)
    expect(M('exp(-x)*Heaviside(x - 1)')).toBe('MellinTransform(exp(-x)*Heaviside(x - 1), x, s)');
    expect(M('exp(-x)*Heaviside(1 - x)')).toBe('MellinTransform(exp(-x)*Heaviside(1 - x), x, s)');
    expect(M('x**2')).toBe('MellinTransform(x**2, x, s)');
  });
  it('sums combine the strips', () => {
    expect(M('Heaviside(1 - x) + Heaviside(2 - x)')).toBe('((2**s + 1)/s, (0, oo), True)');
    // the strips (-oo, 0) and (0, oo) do not overlap
    expect(M('Heaviside(x - 1) + Heaviside(1 - x)')).toBe('MellinTransform(Heaviside(1 - x) + Heaviside(x - 1), x, s)');
  });
  it('hints and the unevaluated class', () => {
    expect(show(mellinTransform(P('exp(-x**2)'), x, s, { simplify: false }))).toBe('(gamma(s/2)/2, (0, oo), True)');
    expect(show(mellinTransform(P('exp(-x)'), x, s, { noconds: true }))).toBe('gamma(s)');
    const f = SymFunction('f');
    const T = new MellinTransform(f(x), x, s);
    expect(T.transformName).toBe('Mellin');
    expect(MellinTransform.transformName).toBe('Mellin');
    expect(String(subs(T, [[s, 2]]))).toBe('MellinTransform(f(x), x, 2)');
  });
});

describe('inverse_mellin_transform', () => {
  it('Meijer G functions with closed forms', () => {
    expect(IM('gamma(-s)/gamma(1 + s)', '-oo', '0')).toBe('besselj(0, 2/sqrt(x))');
    // SymPy leaves meijerg(((), ()), ((0, 0), ()), 1/x), which is 2*besselk(0, 2/sqrt(x))
    expect(IM('gamma(-s)**2', '-oo', '0')).toBe('2*besselk(0, 2/sqrt(x))');
    expect(IM('gamma(-s)/gamma(1 - s)', '-oo', '0')).toBe('Heaviside(x - 1)');
    expect(IM('gamma(s)/gamma(s + 1)', '0', 'oo')).toBe('Heaviside(1 - x)');
    expect(IM('p**s*gamma(-s)/gamma(1 - s)', '-oo', '0')).toBe('Heaviside(-p + x)');
    expect(IM('2**s*gamma(s)/gamma(s + 1)', '0', 'oo')).toBe('Heaviside(2 - x)');
    expect(IM('gamma(s)/gamma(s + 3/2)', '0', 'oo')).toBe('2*sqrt(1 - x)*Heaviside(1 - x)/sqrt(pi)');
    expect(IM('gamma(-s)/gamma(3/2 - s)', '-oo', '0')).toBe('2*sqrt(1 - 1/x)*Heaviside(x - 1)/sqrt(pi)');
    expect(IM('gamma(2*s)/gamma(s)', '0', 'oo')).toBe('sqrt(x)*exp(-x/4)/(4*sqrt(pi))');
    expect(IM('gamma(-2*s)', '-oo', '0')).toBe('exp(-1/sqrt(x))/2');
  });
  it('transforms that do not converge or are not recognised stay unevaluated', () => {
    expect(IM('1/gamma(s)', '0', 'oo')).toBe('InverseMellinTransform(1/gamma(s), s, x, 0, oo)');
    expect(IM('gamma(s)/gamma(2*s)', '0', 'oo')).toBe('InverseMellinTransform(gamma(s)/gamma(2*s), s, x, 0, oo)');
    expect(IM('gamma(s)*gamma(sqrt(2)*s)', '0', 'oo')).toBe('InverseMellinTransform(gamma(s)*gamma(sqrt(2)*s), s, x, 0, oo)');
    expect(IM('gamma(s)*gamma(I*s)', '0', 'oo')).toBe('InverseMellinTransform(gamma(s)*gamma(I*s), s, x, 0, oo)');
    expect(IM('gamma(s)*gamma(a*s)', '0', 'oo')).toBe('InverseMellinTransform(gamma(s)*gamma(a*s), s, x, 0, oo)');
    expect(IM('s/(s + 1)', '0', 'oo')).toBe('InverseMellinTransform(s/(s + 1), s, x, 0, oo)');
    expect(IM('sqrt(s + 1)', '0', 'oo')).toBe('InverseMellinTransform(sqrt(s + 1), s, x, 0, oo)');
    expect(IM('(s + 1)**a', '0', 'oo')).toBe('InverseMellinTransform((s + 1)**a, s, x, 0, oo)');
    expect(IM('besselj(s, 1)', '0', 'oo')).toBe('InverseMellinTransform(besselj(s, 1), s, x, 0, oo)');
    expect(IM('s**s*gamma(s)', '0', 'oo')).toBe('InverseMellinTransform(s**s*gamma(s), s, x, 0, oo)');
    expect(IM('2**(s**2)*gamma(s)', '0', 'oo')).toBe('InverseMellinTransform(2**(s**2)*gamma(s), s, x, 0, oo)');
    // SymPy raises NotImplementedError('Gammas partially over the strip.')
    expect(IM('gamma(s - 2)', '0', '1')).toBe('InverseMellinTransform(gamma(s - 2), s, x, 0, 1)');
  });
  it('rational functions by residues', () => {
    expect(IM('1/(s*(s + 1))', '0', 'oo')).toBe('(1 - x)*Heaviside(1 - x)');
    expect(IM('1/(s**2*(s + 1))', '0', 'oo')).toBe('(x - log(x) - 1)*Heaviside(1 - x)');
    expect(IM('1/(s*(s - 1))', undefined, 'oo')).toBe('(1 - x)*Heaviside(1 - x)/x');
    expect(IM('1/(s*(s - 1))', '0', '1')).toBe('-Heaviside(1 - x) - Heaviside(x - 1)/x');
    // without a strip every pole is taken to the left of it, as for the strip (None, oo)
    // (SymPy fails with TypeError on None)
    expect(IM('1/(s*(s - 1))', undefined, undefined)).toBe('(1 - x)*Heaviside(1 - x)/x');
  });
  it('a pole inside the strip', () => {
    expect(() => inverseMellinTransform(P('1/(s*(s - 1))'), s, x, strip('-1', '2'))).toThrow(MellinTransformStripError);
    expect(() => inverseMellinTransform(P('1/s'), s, x, strip('-1', '1'))).toThrow('Pole inside critical strip?');
    expect(() => inverseMellinTransform(P('gamma(s)/(s - 1)'), s, x, strip('0', '2'))).toThrow(MellinTransformStripError);
  });
  it('sums', () => {
    // SymPy 1.14 fails here with TypeError: 'set' object is not subscriptable
    expect(IM('1/s + gamma(s)', '0', 'oo')).toBe('Heaviside(1 - x) + exp(-x)');
  });
  it('hints and the unevaluated class', () => {
    expect(show(inverseMellinTransform(P('gamma(s)'), s, x, strip('0', 'oo'), { noconds: false }))).toBe('(exp(-x), True)');
    const f = SymFunction('f');
    const T = new InverseMellinTransform(f(s), s, x, 0, 1);
    expect(T.transformName).toBe('Inverse Mellin');
    expect(InverseMellinTransform.transformName).toBe('Inverse Mellin');
    expect(latex(T)).toBe('\\mathcal{M}^{-1}_{s}\\left[f{\\left(s \\right)}\\right]\\left(x\\right)');
    expect(String(T.asIntegral)).toBe('-I*Integral(f(s)/x**s, (s, _c - oo*I, _c + oo*I))/(2*pi)');
    expect(String(subs(T, [[x, 2]]))).toBe('InverseMellinTransform(f(s), s, 2, 0, 1)');
  });
});

describe('_rewrite_gamma', () => {
  it('trigonometric factors', () => {
    expect(RG('sin(pi*s)*gamma(s)', '0', '1')).toBe('(((1), (1)), ((), (1)), 1, 1, pi)');
    expect(RG('cos(pi*s)*gamma(s)', '0', '1')).toBe('(((1), (1/2)), ((), (1/2)), 1, 1, pi)');
    expect(RG('gamma(s)/tan(pi*s)', '0', '1')).toBe('(((1, 1), (1/2)), ((1), (1/2)), 1, 1, 1)');
    expect(RG('gamma(s)*tan(pi*s)', '0', '1/2')).toBe('(((1/2, 1), (1)), ((1/2), (1)), 1, 1, 1)');
    expect(RG('cot(pi*s)', '0', '1')).toBe('(((1), (1/2)), ((1), (1/2)), 1, 1, 1)');
    expect(RG('1/cot(pi*s)', '0', '1/2')).toBe('(((1/2), (1)), ((1/2), (1)), 1, 1, 1)');
    expect(RG('1/sin(pi*s)', '0', undefined)).toBe('(((1), ()), ((1), ()), 1, 1, 1/pi)');
    // SymPy fails with TypeError (None in the arithmetic)
    expect(() => rewriteGamma(P('1/sin(pi*s)'), s, undefined, 1)).toThrow(IntegralTransformError);
  });
  it('linear factors and the strip', () => {
    expect(RG('gamma(s)', 'a', 'r')).toBe('(((1), ()), ((), ()), 1, 1, 1)');
    expect(RG('1/s', 'a', 'r')).toBe('(((), (1)), ((0), ()), 1, 1, -1)');
    expect(RG('s', 'a', 'r')).toBe('(((), (0)), ((1), ()), 1, 1, -1)');
    expect(RG('s', '-1', '1')).toBe('(((), (0)), ((1), ()), 1, 1, -1)');
    expect(RG('1/s', undefined, '1')).toBe('(((1), ()), ((), (0)), 1, 1, 1)');
    expect(RG('s - 1', undefined, 'oo')).toBe('(((1), ()), ((), (2)), 1, 1, 1)');
    // as for (None, oo); SymPy fails with TypeError on None
    expect(RG('s - 1', undefined, undefined)).toBe('(((1), ()), ((), (2)), 1, 1, 1)');
    expect(RG('gamma(s)*(s - 1)', '0', '2')).toBe('(((1), (1)), ((2), ()), 1, 1, -1)');
    expect(() => rewriteGamma(P('1/s'), s, -1, 1)).toThrow(MellinTransformStripError);
  });
  it('polynomial factors', () => {
    expect(RG('gamma(s)*(s**2 + 1)', '0', 'oo')).toBe('(((1, -I, I), ()), ((), (1 - I, 1 + I)), 1, 1, 1)');
    expect(RG('gamma(s)/(s**2 + 1)', '0', 'oo')).toBe('(((1, 1 - I, 1 + I), ()), ((), (-I, I)), 1, 1, 1)');
    // SymPy places the roots by CRootOf and raises MellinTransformStripError: a real root lies in (0, oo)
    expect(() => rewriteGamma(P('gamma(s)/(s**5 - s - 1)'), s, 0, S.Infinity)).toThrow(IntegralTransformError);
  });
  it('multiples of s', () => {
    expect(RG('gamma(2*s)', '0', 'oo')).toBe('(((1), ()), ((), ()), 1, 1/2, 1/2)');
    expect(RG('1/gamma(2*s)', '0', 'oo')).toBe('(((), ()), ((), (1)), 1, 1/2, 1/2)');
    expect(RG('gamma(-2*s)', '-oo', '0')).toBe('(((), ()), ((0), ()), 1, 1/2, 1/2)');
    expect(RG('gamma(3*s/2)*gamma(s)', '0', 'oo')).toBe('(((1/3, 1/2, 2/3, 1, 1), ()), ((), ()), 108, 2, sqrt(3)/(6*pi**(3/2)))');
    expect(RG('gamma(sqrt(2)*s)/gamma(1 - sqrt(2)*s)', '0', 'oo')).toBe('(((1), (1)), ((), ()), 1, sqrt(2)/2, sqrt(2)/2)');
  });
  it('unrecognised forms', () => {
    for (const F of ['gamma(s)*gamma(sqrt(2)*s)', 'gamma(s)*gamma(I*s)', 'gamma(s)*gamma(a*s)', 'gamma(s)*2**(1/s)', 'gamma(s)*2**(s**2)', 'gamma(s)*s**s', 'gamma(s)*sqrt(s)', 'besselj(s, 1)']) {
      expect(() => rewriteGamma(P(F), s, 0, S.Infinity)).toThrow(IntegralTransformError);
    }
  });
});

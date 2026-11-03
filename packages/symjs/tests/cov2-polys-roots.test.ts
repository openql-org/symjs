// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * Numerical roots, partial fractions and RootSum (polys/nroots, partfrac,
 * rootsum); expected values from SymPy 1.14.
 */

import { describe, expect, it } from 'vitest';
import * as sj from '../src';

const { parse } = sj;
const [x, y, t, b] = sj.symbols('x y t b') as [sj.Sym, sj.Sym, sj.Sym, sj.Sym];
const show = (r: unknown): string => (Array.isArray(r) ? `[${r.map(show).join(', ')}]` : String(r));
const lam = (v: sj.Sym, e: string) => sj.Lambda(v, parse(e));

describe('nroots', () => {
  it.each([
    ['x**3 - x', '[-1.00000000000000, 0, 1.00000000000000]'],
    ['x**2 + 1', '[-1.0*I, 1.0*I]'],
    ['I*x - 1', '[-1.0*I]'],
    ['x**2 - sqrt(2)', '[-1.18920711500272, 1.18920711500272]'],
    ['sqrt(2)*x**2 - 1', '[-0.840896415253715, 0.840896415253715]'],
    ['x**2', '[0, 0]'],
    ['(x - 1)**2*(x + 2)', '[-2.00000000000000, 1.00000000000000, 1.00000000000000]'],
    [
      'x**4 + 1',
      '[-0.707106781186548 - 0.707106781186548*I, -0.707106781186548 + 0.707106781186548*I, 0.707106781186548 - 0.707106781186548*I, 0.707106781186548 + 0.707106781186548*I]',
    ],
  ])('nroots(%s)', (f, expected) => {
    expect(show(sj.nroots(parse(f)))).toBe(expected);
  });
  it('a Poly, a generator and symbolic coefficients', () => {
    expect(show(sj.nroots(sj.Poly.from(parse('x**2 - 2'), [x]), 10))).toBe('[-1.414213562, 1.414213562]');
    expect(show(sj.nroots(parse('x**2 - 2'), 10, x))).toBe('[-1.414213562, 1.414213562]');
    // SymPy: MultivariatePolynomialError Cannot compute numerical roots of Poly(x**2 - a, x, a, domain='ZZ')
    expect(() => sj.nroots(parse('x**2 - a'), 15, x)).toThrow(sj.DomainError);
  });
});

describe('apart', () => {
  it('generators and factors free of the variable', () => {
    expect(String(sj.apart(parse('1/(y*(x + 1))'), x))).toBe('1/(y*(x + 1))');
    expect(String(sj.apart(parse('(x**2 + 1)/(x + 1)')))).toBe('x - 1 + 2/(x + 1)');
    expect(String(sj.apart(parse('1/((x + 1)*(x + 2))')))).toBe('-1/(x + 2) + 1/(x + 1)');
    // SymPy: NotImplementedError multivariate partial fraction decomposition
    expect(() => sj.apart(parse('x/(x + y)'))).toThrow(sj.NotImplementedError);
    expect(String(sj.apart(parse('1/2')))).toBe('1/2');
    expect(String(sj.apart(parse('x**2 + 1')))).toBe('x**2 + 1');
  });
});

describe('RootSum', () => {
  const P = parse('x**3 + x + 1');
  it.each([
    ['2', '6'],
    ['b + 1', 'RootSum(x**3 + x + 1) + 3'],
    ['b**2 + 1', 'RootSum(x**3 + x + 1, Lambda(b, b**2)) + 3'],
    ['3*b**2 + 1', '3*RootSum(x**3 + x + 1, Lambda(b, b**2)) + 3'],
    ['b*y', 'y*RootSum(x**3 + x + 1)'],
    ['1/(b - 1)', 'RootSum(x**3 + x + 1, Lambda(b, 1/(b - 1)))'],
  ])('RootSum(x**3 + x + 1, Lambda(b, %s), auto=False)', (body, expected) => {
    expect(String(sj.RootSum(P, x, lam(b, body)))).toBe(expected);
  });
  it('linear factors, printing and free symbols', () => {
    expect(String(sj.RootSum(parse('(x - 1)*(x**3 + x + 1)'), x, lam(b, 'b**2')))).toBe('RootSum(x**3 + x + 1, Lambda(b, b**2)) + 1');
    const r = sj.RootSum(P, x, lam(b, '1/(b - 1)'));
    expect(sj.latex(r)).toBe('\\operatorname{RootSum} {\\left(x^{3} + x + 1, \\left( b \\mapsto \\frac{1}{b - 1} \\right)\\right)}');
    expect([...r.freeSymbols()].map(String)).toEqual([]);
    // the identity function is not printed
    expect(sj.latex(sj.RootSum(P, x, lam(b, 'b*y')))).toBe('y \\operatorname{RootSum} {\\left(x^{3} + x + 1\\right)}');
  });
});

describe('apart_list and assemble_partfrac_list', () => {
  it('explicit roots', () => {
    const a = new sj.Dummy('a');
    const pfd: [sj.Expr, sj.Poly, sj.PartfracTerm[], sj.Sym] = [
      sj.S.One,
      sj.Poly.from(parse('0'), [x]),
      [[[parse('sqrt(2)'), parse('-sqrt(2)')], sj.Lambda(a, sj.mul(a, sj.Rational.of(1n, 2n))), sj.Lambda(a, sj.add(x, sj.mul(-1, a))), 1]],
      new sj.Dummy('w'),
    ];
    expect(String(sj.assemblePartfracList(pfd))).toBe('-sqrt(2)/(2*(x + sqrt(2))) + sqrt(2)/(2*(x - sqrt(2)))');
  });
  it('symbolic coefficients', () => {
    expect(String(sj.apart(parse('1/(2*(x + 1))'), x, { full: true }))).toBe('1/(2*(x + 1))');
    const r = sj.apart(parse('t/(x**2 + x + t)'), x, { full: true });
    expect(String(r)).toBe('RootSum(_w**2 + _w + t, Lambda(_a, (-2*_a*t/(4*t - 1) - t/(4*t - 1))/(-_a + x)))');
    void t;
    void y;
  });
  it.each([
    ['(x + 1)/(x**2 + t*x + 1)', 'RootSum(_w**2 + _w*t + 1, Lambda(_a, (-_a/(t + 2) + 1/(t + 2))/(-_a + x)))'],
    ['1/(t*x**2 + x + 1)', 'RootSum(_w**2*t + _w + 1, Lambda(_a, (-2*_a*t/(4*t - 1) - 1/(4*t - 1))/(-_a + x)))'],
    ['(x + t)/(x**2 + x + t + 1)', 'RootSum(_w**2 + _w + t + 1, Lambda(_a, (_a*(1 - 2*t)/(4*t + 3) + (t + 2)/(4*t + 3))/(-_a + x)))'],
    [
      '1/((x**2 + t)*(x + 1))',
      'RootSum(_w**2 + t, Lambda(_a, (_a**2*(3*t - 1)/(2*t**3 + 4*t**2 + 2*t) - _a/(2*t**2 + 2*t) + (t - 1)/(t**2 + 2*t + 1))/(-_a + x))) + 1/((t + 1)*(x + 1))',
    ],
    [
      '(x + 1)/((x**2 + t)**2)',
      'RootSum(_w**2 + t, Lambda(_a, (-_a/(4*t) - 1/(4*t))/(-_a + x)**2)) - RootSum(_w**2 + t, Lambda(_a, _a/(-_a + x)))/(4*t**2)',
    ],
    ['1/(2*x**2 + 2*t)', '-RootSum(_w**2 + t, Lambda(_a, _a/(-_a + x)))/(4*t)'],
    ['x/(x**2 + t)', 'RootSum(_w**2 + t, Lambda(_a, 1/(-_a + x)))/2'],
  ])('apart(%s, x, full=True)', (f, expected) => {
    expect(String(sj.apart(parse(f), x, { full: true }))).toBe(expected);
  });
  it('RootSum of polynomials with a content', () => {
    expect(String(sj.RootSum(parse('2*t*x**2 + 2*t*x + 2*t'), x, lam(b, '1/(b + 1)')))).toBe('RootSum(x**2 + x + 1, Lambda(b, 1/(b + 1)))');
    expect(String(sj.RootSum(parse('2*x**3 + 2*x + 2'), x, lam(b, 'b**2')))).toBe('RootSum(x**3 + x + 1, Lambda(b, b**2))');
  });
});

describe('UPoly (deprecated dense univariate polynomial)', () => {
  const U = (e: string) => {
    const p = sj.UPoly.fromExpr(parse(e), x);
    if (!p) throw new TypeError('not a polynomial');
    return p;
  };
  it('leading coefficient, sums, values and rational roots', () => {
    // Poly(0, x).LC() -> 0
    expect(String(new sj.UPoly([]).lc)).toBe('0');
    expect(String(U('x**3 + 1').add(U('2*x')).toExpr(x))).toBe('x**3 + 2*x + 1');
    expect(String(U('2*x').add(U('x**3 + 1')).toExpr(x))).toBe('x**3 + 2*x + 1');
    expect(String(U('2*x**3 - x + 5').evalAt(sj.Rational.of(1n, 2n)))).toBe('19/4');
    // roots(f, filter='Q'): {-3: 1, 1/2: 1, 0: 1} and {2/3: 1}
    expect(show(U('(2*x - 1)*(x + 3)*(x**2 + 1)*x').rationalRoots())).toBe('[-3, 0, 1/2]');
    expect(show(U('(x**2 - 2)**2*(3*x - 2)').rationalRoots())).toBe('[2/3]');
    expect(show(U('5').rationalRoots())).toBe('[]');
  });
});

describe('roots with symbolic coefficients (SymPy roots(f, x))', () => {
  const a = new sj.Sym('a', { positive: true });
  const c = (s: string) => sj.subs(parse(s), [[new sj.Sym('a'), a]]);
  const keys = (f: string) => [...sj.roots(c(f), x).keys()];
  it('binomials and quadratics', () => {
    expect(show(keys('x**2 + a'))).toBe('[-I*sqrt(a), I*sqrt(a)]');
    expect(show(keys('-a*x**2 + b*x + c'))).toBe('[b/(2*a) - sqrt(4*a*c + b**2)/(2*a), b/(2*a) + sqrt(4*a*c + b**2)/(2*a)]');
    // multiple=True lists the roots in ordered() order
    expect(show(sj.roots(c('x**2 + a'), x, { multiple: true }))).toBe('[I*sqrt(a), -I*sqrt(a)]');
    expect(show(sj.roots(parse('(x - 1)**2*(x + 2)'), x, { multiple: true }))).toBe('[-2, 1, 1]');
  });
  it.each([
    // SymPy writes (-1)**(5/6)*sqrt(3) and (-1)**(3/4) where symjs keeps I*(-1)**(1/3) and I*(-1)**(1/4)
    // (the core does not merge I with powers of -1), so the roots are compared at a = 2
    ['x**3 + a', '[-1.25992104989487, 0.629960524947437 - 1.09112363597172*I, 0.629960524947437 + 1.09112363597172*I]'],
    [
      'x**4 + a',
      '[-0.840896415253715 - 0.840896415253715*I, -0.840896415253715 + 0.840896415253715*I, 0.840896415253715 - 0.840896415253715*I, 0.840896415253715 + 0.840896415253715*I]',
    ],
  ])('roots(%s) at a = 2', (f, expected) => {
    expect(show(keys(f).map((r) => sj.evalf(sj.subs(r, [[a, sj.Rational.of(2n)]]), 15)))).toBe(expected);
  });
});

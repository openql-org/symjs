// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/polys/rootsum.ts: RootSum, apart_list and assemble_partfrac_list; expected values from SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';

const { parse } = sj;
const [x, y, t, b] = sj.symbols('x y t b') as [sj.Sym, sj.Sym, sj.Sym, sj.Sym];
const lam = (v: sj.Sym, e: string) => sj.Lambda(v, parse(e));

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

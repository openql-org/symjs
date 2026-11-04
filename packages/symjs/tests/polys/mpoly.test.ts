// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/polys/mpoly.ts: multivariate gcd, exact division and factorization; expected values from SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';

const { parse } = sj;
const [x, y, z] = sj.symbols('x y z') as [sj.Sym, sj.Sym, sj.Sym];
const show = (r: unknown): string => (Array.isArray(r) ? `[${r.map(show).join(', ')}]` : String(r));

describe('multivariate gcd, exact division and factorization (polys/mpoly)', () => {
  it('deprecated mgcd and divExact', () => {
    expect(String(sj.mgcd(parse('x*y'), parse('0'), [x, y]))).toBe('x*y');
    expect(String(sj.mgcd(parse('0'), parse('-x*y'), [x, y]))).toBe('x*y');
    expect(String(sj.mlcm(parse('x*y'), parse('x*z'), [x, y, z]))).toBe('x*y*z');
    expect(String(sj.divExact(parse('x**2 + x*y'), parse('x + y'), [x, y]))).toBe('x');
    expect(sj.divExact(parse('x*y + 1'), y, [x, y])).toBe(sj.NoMatch);
    expect(sj.divExact(parse('x*y'), parse('x*z'), [x, y, z])).toBe(sj.NoMatch);
    expect(() => sj.divExact(x, parse('0'), [x])).toThrow(RangeError);
    expect(() => sj.mgcd(parse('sin(x)'), parse('x**2'), [x])).toThrow(sj.PolynomialError);
  });
  it('factor', () => {
    expect(String(sj.factor(parse('x**2 - y**2')))).toBe('(x - y)*(x + y)');
    expect(String(sj.factor(parse('x**2 + 2*x*y + y**2 + 1')))).toBe('x**2 + 2*x*y + y**2 + 1');
    expect(String(sj.factor(parse('x**2*y + x*y**2 + x + y')))).toBe('(x + y)*(x*y + 1)');
    expect(show(sj.factorList(parse('2*x**2*y - 2*y**3')))).toBe('[2, [[y, 1], [x - y, 1], [x + y, 1]]]');
  });
  it('square-free decomposition (SymPy factor)', () => {
    expect(String(sj.factor(sj.expand(parse('(x - z)*(x + z)**2'))))).toBe('(x - z)*(x + z)**2');
    expect(String(sj.factor(sj.expand(parse('(x + y)*(x**2 + y - 3)**2'))))).toBe('(x + y)*(x**2 + y - 3)**2');
    // images at y = 3 that are not square-free or lose degree: the gcd decides
    expect(String(sj.factor(parse('x**2 + y - 3')))).toBe('x**2 + y - 3');
    expect(String(sj.factor(parse('x**3 + x**2*y - 4*x**2 + y - 3')))).toBe('x**3 + x**2*y - 4*x**2 + y - 3');
    expect(String(sj.factor(parse('x**2*y - 3*x**2 + x + 1')))).toBe('x**2*y - 3*x**2 + x + 1');
  });
  it("multivariate factorization by Wang's EEZ algorithm (SymPy factor)", () => {
    expect(String(sj.factor(parse('x**3 - y**3')))).toBe('(x - y)*(x**2 + x*y + y**2)');
    expect(String(sj.factor(parse('(x + a)**4 - 1')))).toBe('(a + x - 1)*(a + x + 1)*(a**2 + 2*a*x + x**2 + 1)');
    expect(String(sj.factor(sj.expand(parse('(3*t + a)*(t**2 + a**3)'))))).toBe('(a + 3*t)*(a**3 + t**2)');
    expect(String(sj.factor(parse('x**4 - y**4')))).toBe('(x - y)*(x + y)*(x**2 + y**2)');
    expect(String(sj.factor(parse('x**2*y - x*y**2 + x*y - x - y + 1')))).toBe('x**2*y - x*y**2 + x*y - x - y + 1');
    expect(String(sj.factor(parse('x**6 - y**6')))).toBe('(x - y)*(x + y)*(x**2 - x*y + y**2)*(x**2 + x*y + y**2)');
    expect(String(sj.factor(parse('x**3 + y**3 + z**3 - 3*x*y*z')))).toBe('(x + y + z)*(x**2 - x*y - x*z + y**2 - y*z + z**2)');
    expect(String(sj.factor(parse('x**4 + 4*y**4')))).toBe('(x**2 - 2*x*y + 2*y**2)*(x**2 + 2*x*y + 2*y**2)');
    expect(String(sj.factor(parse('x**8 - y**8')))).toBe('(x - y)*(x + y)*(x**2 + y**2)*(x**4 + y**4)');
    expect(String(sj.factor(parse('x**2*y**2 + x**2*y*z + 1')))).toBe('x**2*y**2 + x**2*y*z + 1');
  });
  it('SymPy test_factortools multivariate cases (factor_list)', () => {
    const cases: [string, string][] = [
    ['x**2*y*z**2 + 2*x**2*y*z + 3*x**2*y + 2*x**2 + 3*x + 4*y**2*z**2 + 5*y**2*z + 6*y**2 + y*z**2 + 2*y*z + y + 1', '[1, [[x**2*y*z**2 + 2*x**2*y*z + 3*x**2*y + 2*x**2 + 3*x + 4*y**2*z**2 + 5*y**2*z + 6*y**2 + y*z**2 + 2*y*z + y + 1, 1]]]'],
    ['x**3*y*z + x**2*y**2*z**2 + x**2*y**2 + 20*x**2*y*z + 30*x**2*y + x**2*z**2 + 10*x**2*z + x*y**3*z + 30*x*y**2*z + 20*x*y**2 + x*y*z**3 + 10*x*y*z**2 + x*y*z + 610*x*y + 20*x*z**2 + 230*x*z + 300*x + y**2*z**2 + 10*y**2*z + 30*y*z**2 + 320*y*z + 200*y + 600*z + 6000', '[1, [[x + y*z + 20, 1], [x*y + z + 10, 1], [x*z + y + 30, 1]]]'],
    ['x**5*y**3 + x**5*y**2*z + x**5*y*z**2 + x**5*z**3 + x**3*y**2 + x**3*y*z + 90*x**3*y + 90*x**3*z + x**2*y**2*z - 11*x**2*y**2 + x**2*z**3 - 11*x**2*z**2 + y*z - 11*y + 90*z - 990', '[1, [[x**2*y**2 + x**2*z**2 + y + 90, 1], [x**3*y + x**3*z + z - 11, 1]]]'],
    ['x**5*y**2 + x**4*z**4 + x**4 + x**3*y**3*z + x**3*z + x**2*y**4 + x**2*y**3*z**3 + x**2*y*z**5 + x**2*y*z + x*y**2*z**4 + x*y**2 + x*y*z**7 + x*y*z**3 + x*y*z**2 + y**2*z + y*z**4', '[1, [[x**2*y**2 + x*z**4 + x + z, 1], [x**3 + x*y*z + y**2 + y*z**3, 1]]]'],
    ['-x**9*y**8*z - x**8*y**5*z**3 - x**7*y**12*z**2 - 5*x**7*y**8 - x**6*y**9*z**4 + x**6*y**7*z**3 + 3*x**6*y**7*z - 5*x**6*y**5*z**2 - x**6*y**4*z**3 + x**5*y**4*z**5 + 3*x**5*y**4*z**3 - x**5*y*z**5 + x**4*y**11*z**4 + 3*x**4*y**11*z**2 - x**4*y**8*z**4 + 5*x**4*y**7*z**2 + 15*x**4*y**7 - 5*x**4*y**4*z**2 + x**3*y**8*z**6 + 3*x**3*y**8*z**4 - x**3*y**5*z**6 + 5*x**3*y**4*z**4 + 15*x**3*y**4*z**2 + x**3*y**3*z**5 + 3*x**3*y**3*z**3 - 5*x**3*y*z**4 + x**2*z**7 + 3*x**2*z**5 + x*y**7*z**6 + 3*x*y**7*z**4 + 5*x*y**3*z**4 + 15*x*y**3*z**2 + y**4*z**8 + 3*y**4*z**6 + 5*z**6 + 15*z**4', '[-1, [[x*y**3 + z**2, 1], [x**2*z + y**4*z**2 + 5, 1], [x**3*y - z**2 - 3, 1], [x**3*y**4 + z**2, 1]]]'],
    ['-x**3 - 3*x**2*y + 3*x**2*z - 3*x*y**2 + 6*x*y*z - 3*x*z**2 - y**3 + 3*y**2*z - 3*y*z**2 + z**3', '[-1, [[x + y - z, 3]]]'],
    ['2*t**3*z**4 - 2*t**3*z + 45*t**2*x**3*z**3 - 45*t**2*x**3 - 9*t**2*y**3*z**3 + 9*t**2*y**3 - t**2*y**2*z**3 + t**2*y**2 + 3*t**2*z**6 - 3*t**2*z**3 + 94*t*x*y*z + 2115*x**4*y - 423*x*y**4 - 47*x*y**3 + 141*x*y*z**3', '[1, [[t**2*z**3 - t**2 + 47*x*y, 1], [2*t*z + 45*x**3 - 9*y**3 - y**2 + 3*z**3, 1]]]'],
    ['x**2*y**2 + 6*x**2*y + 9*x**2 - 1', '[1, [[x*y + 3*x - 1, 1], [x*y + 3*x + 1, 1]]]'],
    ['x**2*y**2*z**2*u**2 - 9', '[1, [[u*x*y*z - 3, 1], [u*x*y*z + 3, 1]]]'],
    ['-12*x**16*y + 240*x**12*y**3 - 768*x**10*y**4 + 1080*x**8*y**5 - 768*x**6*y**6 + 240*x**4*y**7 - 12*y**9', '[-12, [[y, 1], [x**2 - y, 6], [x**4 + 6*x**2*y + y**2, 1]]]'],
    ['2*x**2 + y*z - y - z**2 + z', '[1, [[2*x**2 + y*z - y - z**2 + z, 1]]]'],
    ['4*x**2*y + 4*x*y**2', '[4, [[x, 1], [y, 1], [x + y, 1]]]'],
    ['x**2/2*y + x*y**2/2', '[1/2, [[x, 1], [y, 1], [x + y, 1]]]'],
    ];
    for (const [f, fl] of cases) expect(show(sj.factorList(parse(f)))).toBe(fl);
  });
  it('SymPy test_factortools w_1 (three factors of degree 2 in x)', () => {
    expect(show(sj.factorList(parse('4*x**6*y**4*z**2 + 4*x**6*y**3*z**3 - 4*x**6*y**2*z**4 - 4*x**6*y*z**5 + x**5*y**4*z**3 + 12*x**5*y**3*z - x**5*y**2*z**5 + 12*x**5*y**2*z**2 - 12*x**5*y*z**3 - 12*x**5*z**4 + 8*x**4*y**4 + 6*x**4*y**3*z**2 + 8*x**4*y**3*z - 4*x**4*y**2*z**4 + 4*x**4*y**2*z**3 - 8*x**4*y**2*z**2 - 4*x**4*y*z**5 - 2*x**4*y*z**4 - 8*x**4*y*z**3 + 2*x**3*y**4*z + x**3*y**3*z**3 - x**3*y**2*z**5 - 2*x**3*y**2*z**3 + 9*x**3*y**2*z - 12*x**3*y*z**3 + 12*x**3*y*z**2 - 12*x**3*z**4 + 3*x**3*z**3 + 6*x**2*y**3 - 6*x**2*y**2*z**2 + 8*x**2*y**2*z - 2*x**2*y*z**4 - 8*x**2*y*z**3 + 2*x**2*y*z**2 + 2*x*y**3*z - 2*x*y**2*z**3 - 3*x*y*z + 3*x*z**3 - 2*y**2 + 2*y*z**2')))).toBe('[1, [[x**2*y**2 - x**2*z**2 + y - z**2, 1], [x**2*y*z**2 + 3*x*z + 2*y, 1], [4*x**2*y + 4*x**2*z + x*y*z - 1, 1]]]');
  });
});

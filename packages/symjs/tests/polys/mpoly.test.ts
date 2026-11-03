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
});

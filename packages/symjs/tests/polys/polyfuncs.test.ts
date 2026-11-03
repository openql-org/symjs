// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/polys/polyfuncs.ts: symmetrize and rational_interpolate; expected values from SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';

const [x, y] = sj.symbols('x y') as [sj.Sym, sj.Sym];
const s = (e: unknown): string => (Array.isArray(e) ? `(${e.map(s).join(', ')})` : String(e));

describe('symmetrize', () => {
  it('formal form with the elementary symmetric polynomials', () => {
    expect(s(sj.symmetrize(sj.parse('x**2 + y**2')))).toBe('(s1**2 - 2*s2, 0, ((s1, x + y), (s2, x*y)))');
    expect(s(sj.symmetrize(sj.parse('x**2 - y**2')))).toBe('(s1**2 - 2*s2, -2*y**2, ((s1, x + y), (s2, x*y)))');
    expect(s(sj.symmetrize(sj.parse('x**3 + y**3 + z**3')))).toBe(
      '(s1**3 - 3*s1*s2 + 3*s3, 0, ((s1, x + y + z), (s2, x*y + x*z + y*z), (s3, x*y*z)))',
    );
    expect(s(sj.symmetrize(sj.parse('x**2 + y**2'), [x, y]))).toBe('(s1**2 - 2*s2, 0, ((s1, x + y), (s2, x*y)))');
    expect(s(sj.symmetrize(sj.parse('x + 2*y')))).toBe('(s1, y, ((s1, x + y), (s2, x*y)))');
    expect(s(sj.symmetrize(5))).toBe('(5, 0, ())');
  });
  it('formal=False substitutes the polynomials back', () => {
    expect(s(sj.symmetrizeExpr(sj.parse('x**2 + y**2')))).toBe('(-2*x*y + (x + y)**2, 0)');
  });
});

describe('rationalInterpolate', () => {
  it('fits a rational function', () => {
    const data: [number, number][] = [
      [1, 2],
      [2, 3],
      [3, 5],
      [4, 7],
    ];
    expect(sj.rationalInterpolate(data, 1).equals(sj.parse('(57/2 - 9*x/2)/(x**2 - 17*x/2 + 39/2)'))).toBe(true);
    expect(sj.rationalInterpolate(data, 2, y).equals(sj.parse('(2*y**2 - 3*y + 1)/(y - 1)'))).toBe(true);
    expect(() => sj.rationalInterpolate([[1, 2]], 2)).toThrow(RangeError);
  });
});

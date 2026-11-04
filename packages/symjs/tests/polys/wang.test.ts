// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/polys/wang.ts: Wang's EEZ multivariate factorization over ZZ (SymPy dmp_zz_wang);
// expected values from SymPy 1.14 (sympy/polys/tests/test_factortools.py and factor_list).

import { describe, expect, it } from 'vitest';
import type { ZPoly } from '../../src/polys/wang';
import { wangFactor, zpoly } from '../../src/polys/wang';

/** A polynomial in x, y from [[ex, ey], c] terms. */
const P = (...ts: [number, number, number][]): ZPoly => zpoly(ts.map(([a, b, c]) => [[a, b], BigInt(c)] as const));
const show = (f: ZPoly): string =>
  [...f.values()]
    .map((t) => `${t.c}*x^${t.e[0]}*y^${t.e[1]}`)
    .sort()
    .join(' + ');
/** A randint returning the given points in turn (SymPy's _randint with a sequence). */
const seq = (xs: number[]) => {
  let i = 0;
  return (): number => xs[i++ % xs.length] ?? 0;
};
const lcOne = (): [bigint, ZPoly[]] => [1n, []];
const lcY = (): [bigint, ZPoly[]] => [1n, [P([0, 1, 1])]];

describe("Wang's EEZ algorithm (polys/wang)", () => {
  it('splits x**2 - y**2 at the default points', () => {
    const fs = wangFactor(P([2, 0, 1], [0, 2, -1]), 2, lcOne).map(show).sort();
    expect(fs).toEqual(['-1*x^0*y^1 + 1*x^1*y^0', '1*x^0*y^1 + 1*x^1*y^0']);
  });
  it('an irreducible image at the origin', () => {
    // x**2 + y + 1: x**2 + 1 at y = 0 is irreducible
    const f = P([2, 0, 1], [0, 1, 1], [0, 0, 1]);
    expect(wangFactor(f, 2, lcOne)).toEqual([f]);
  });
  it('fewer univariate factors at a later point (x**2 - y)', () => {
    const f = P([2, 0, 1], [0, 1, -1]);
    // y = 1 splits x**2 - 1, y = 2 shows x**2 - y irreducible
    expect(wangFactor(f, 2, lcOne, seq([1, 2]))).toEqual([f]);
  });
  it('extraneous univariate factors: Hensel lifting fails and the algorithm restarts', () => {
    const f = P([2, 0, 1], [0, 1, -1]);
    // three points 1, 4, 9 at which x**2 - y splits, a repeated point, then 2
    expect(wangFactor(f, 2, lcOne, seq([1, 1, 1, 1, 1, 4, 9, 2]))).toEqual([f]);
  });
  it('extraneous univariate factors: the leading coefficients do not fit (y*x**2 + x - 1)', () => {
    const f = P([2, 1, 1], [1, 0, 1], [0, 0, -1]);
    // y = 6, 12, 20: (3x - 1)(2x + 1), (4x - 1)(3x + 1), (5x - 1)(4x + 1); then y = 3 is irreducible
    expect(wangFactor(f, 2, lcY, seq([6, 12, 20, 3]))).toEqual([f]);
  });
  it('more univariate factors at a later point are skipped ((x**2 - y)*(x + y))', () => {
    const f = P([3, 0, 1], [2, 1, 1], [1, 1, -1], [0, 2, -1]);
    const fs = wangFactor(f, 2, lcOne, seq([2, 4, 3, 5])).map(show).sort();
    expect(fs).toEqual(['-1*x^0*y^1 + 1*x^2*y^0', '1*x^0*y^1 + 1*x^1*y^0']);
  });
  it('a univariate image with a content ((y*x + 2)*(x + y))', () => {
    const f = P([2, 1, 1], [1, 2, 1], [1, 0, 2], [0, 1, 2]);
    // y = 6: 2*(3x + 1)*(x + 6), y = -6 and 10 also have the content 2
    const fs = wangFactor(f, 2, lcY, seq([6, -6, 10])).map(show).sort();
    expect(fs).toEqual(['1*x^0*y^1 + 1*x^1*y^0', '1*x^1*y^1 + 2*x^0*y^0']);
  });
  it('a content of the image left after the leading coefficients ((x*y + 1)*(2*x + y))', () => {
    // SymPy dmp_zz_wang_lead_coeffs at y = -6 returns f scaled by cs = -2
    const f = P([2, 1, 2], [1, 2, 1], [1, 0, 2], [0, 1, 1]);
    const lc2y = (): [bigint, ZPoly[]] => [2n, [P([0, 1, 1])]];
    const fs = wangFactor(f, 2, lc2y, seq([-6, 7, 8, 9, 10, 11, 12])).map(show).sort();
    expect(fs).toEqual(['1*x^0*y^0 + 1*x^1*y^1', '1*x^0*y^1 + 2*x^1*y^0']);
  });
});

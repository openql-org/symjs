// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/matrices/linsys.ts.
//
// Linear system solving (linsolve, gauss_jordan_solve and friends). Expected values are those of SymPy
// 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { linearEqToMatrix, linsolve } from '../../src/matrices/linsys';
import { NonlinearError } from '../../src/core/errors';

const [x, y, a] = sj.symbols('x y a');
const P = (s: string): sj.Expr => sj.parse(s, { symbols: { x, y, a } } as never);
const s = (e: unknown): string => String(e);

describe('matrices', () => {
  it('linsolve outside a rational function field keeps the free unknown', () => {
    expect(String(sj.linsolve([P('x + sin(a)*y - 1')], [x, y]))).toBe('-y*sin(a) + 1,y');
  });
});

describe('matrices/linalg, linsys, domainmatrix, mutable', () => {

  it('linear_eq_to_matrix and linsolve', () => {
    // SymPy: NonlinearError for 1/x and for x*y; a relation other than Eq is an expression
    expect(linearEqToMatrix([sj.pow(x, -1)], [x])).toBe(undefined);
    expect(() => linsolve([sj.mul(x, y)], [x, y])).toThrow(NonlinearError);
    const r = linearEqToMatrix([sj.Eq(sj.add(x, y), 2), sj.sub(x, y)], [x, y]);
    expect(r?.map(s)).toEqual(['Matrix([[1, 1], [1, -1]])', 'Matrix([[2], [0]])']);
    expect(() => linsolve([sj.Lt(x, 1)], [x])).toThrow(NonlinearError);
  });
});

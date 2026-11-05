// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/tensor/functions.ts. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';

describe('shape', () => {
  it('shapes of arrays, matrices and integrals of them', () => {
    const x = sj.symbol('x');
    const A = sj.ImmutableDenseNDimArray([1, 2]);
    const M = sj.Matrix.of([[x], [x]]);
    expect(sj.shape(A)).toEqual([2]);
    expect(sj.shape(M)).toEqual([2, 1]);
    expect(sj.shape(new sj.Integral([A, x]))).toEqual([2]);
    expect(sj.shape(sj.MatrixSymbol('X', 2, 3)).map(String)).toEqual(['2', '3']);
    expect(() => sj.shape(x)).toThrow(sj.NoShapeError);
    expect(() => sj.shape(x)).toThrow('x does not have shape, or its type is not registered to shape().');
    expect(() => sj.shape(3)).toThrow('3 does not have shape');
  });
});

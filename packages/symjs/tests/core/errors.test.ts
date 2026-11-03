// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/errors.ts.
// Error classes, which follow the SymPy hierarchy (sympy.matrices.exceptions).

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';

describe('matrix error classes (SymPy sympy.matrices.exceptions)', () => {
  it('follows the SymPy hierarchy', () => {
    // SymPy: NonSquareMatrixError(ShapeError), ShapeError(ValueError, MatrixError), NonPositiveDefiniteMatrixError(ValueError, MatrixError)
    const e = new sj.NonSquareMatrixError();
    expect(e).toBeInstanceOf(sj.ShapeError);
    expect(e).toBeInstanceOf(sj.MatrixError);
    expect(new sj.ShapeError()).toBeInstanceOf(sj.MatrixError);
    expect(new sj.ShapeError().message).toBe('Matrices are not aligned');
    const p = new sj.NonPositiveDefiniteMatrixError();
    expect(p).toBeInstanceOf(sj.MatrixError);
    expect(p.message).toBe('Matrix must be positive-definite');
    expect(p.name).toBe('NonPositiveDefiniteMatrixError');
    expect(new sj.NonInvertibleMatrixError()).toBeInstanceOf(sj.MatrixError);
  });
});

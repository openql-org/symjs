// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/matrices/mutable.ts.
//
// MutableDenseMatrix constructors. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { MutableDenseMatrix } from '../../src/matrices/mutable';

const s = (e: unknown): string => String(e);

describe('matrices', () => {
  it('MutableDenseMatrix.fromFunction', () => {
    const m = MutableDenseMatrix.fromFunction(2, 2, (i, j) => i + j);
    expect(m instanceof MutableDenseMatrix).toBe(true);
    expect(String(m)).toBe('Matrix([[0, 1], [1, 2]])');
  });
});

describe('matrices/linalg, linsys, domainmatrix, mutable', () => {

  it('MutableDenseMatrix.of', () => {
    const A = MutableDenseMatrix.of([[1, 2], [3, 4]]);
    expect(A).toBeInstanceOf(MutableDenseMatrix);
    expect(s(A)).toBe('Matrix([[1, 2], [3, 4]])');
  });
});

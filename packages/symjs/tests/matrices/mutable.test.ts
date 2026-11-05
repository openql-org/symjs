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

describe('MutableDenseMatrix in-place methods', () => {
  const rows = [[1, 2], [3, 4]];
  it('row_del and col_del delete in place', () => {
    const A = MutableDenseMatrix.of(rows);
    A.rowDel(0);
    expect(s(A)).toBe('Matrix([[3, 4]])');
    expect(A.shape).toEqual([1, 2]);
    const B = MutableDenseMatrix.of(rows);
    B.rowDel(-1);
    expect(s(B)).toBe('Matrix([[1, 2]])');
    const C = MutableDenseMatrix.of(rows);
    C.colDel(0);
    expect(s(C)).toBe('Matrix([[2], [4]])');
    const D = MutableDenseMatrix.of(rows);
    D.colDel(-1);
    expect(s(D)).toBe('Matrix([[1], [3]])');
    // SymPy IndexError
    expect(() => MutableDenseMatrix.of(rows).rowDel(5)).toThrow('Row 5 is out of range.');
    expect(() => MutableDenseMatrix.of(rows).colDel(-3)).toThrow('Column -1 is out of range.');
  });
  it('copy and as_mutable give mutable copies', () => {
    const A = MutableDenseMatrix.of(rows);
    const c = A.copy();
    expect(c).toBeInstanceOf(MutableDenseMatrix);
    c.set(0, 0, 9);
    expect(s(A)).toBe('Matrix([[1, 2], [3, 4]])');
    const m = A.asMutable();
    expect(m).toBeInstanceOf(MutableDenseMatrix);
    expect(m).not.toBe(A);
    expect(s(m)).toBe(s(A));
  });
});

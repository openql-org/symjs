// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/matrices/sparse.ts (SymPy sympy/matrices/sparse.py and immutable.py).
// Expected values are the str() forms printed by SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Float, ImmutableDenseMatrix, ImmutableMatrix, ImmutableSparseMatrix, Matrix, MutableDenseMatrix, MutableSparseMatrix, SparseMatrix, str, symbols } from '../../src';
import type { MatrixPosition } from '../../src';

const [x] = symbols('x');
const pos = (i: number, j: number): MatrixPosition => [i, j];

describe('SparseMatrix', () => {
  it('is MutableSparseMatrix, a mutable matrix', () => {
    expect(SparseMatrix).toBe(MutableSparseMatrix);
    const m = new SparseMatrix(2, 2, [0, 1, 2, 3]);
    expect(m).toBeInstanceOf(MutableDenseMatrix);
    expect(String(m)).toBe('Matrix([[0, 1], [2, 3]])');
    m.set(0, 0, 5);
    expect(String(m)).toBe('Matrix([[5, 1], [2, 3]])');
  });

  it('accepts the constructor forms of SymPy', () => {
    const s = (m: Matrix) => String(m);
    expect(s(new SparseMatrix(2, 2, new Map([[pos(1, 1), 2]])))).toBe('Matrix([[0, 0], [0, 2]])');
    expect(s(new SparseMatrix([[1, 2, 3], [1, 2], [1]]))).toBe('Matrix([[1, 2, 3], [1, 2, 0], [1, 0, 0]])');
    expect(s(new SparseMatrix(2, 2, [[1, 2]]))).toBe('Matrix([[1, 2], [0, 0]])');
    expect(s(new SparseMatrix(null, [[1, 2, 3]]))).toBe('Matrix([[1, 2, 3]])');
    expect(
      s(
        new SparseMatrix(
          null,
          new Map([
            [pos(1, 1), 1],
            [pos(3, 3), 3],
          ]),
        ),
      ),
    ).toBe('Matrix([[0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 3]])');
    expect(s(new SparseMatrix(4, 4, new Map([[pos(1, 1), Matrix.of([[1, 1], [1, 1]])]])))).toBe('Matrix([[0, 0, 0, 0], [0, 1, 1, 0], [0, 1, 1, 0], [0, 0, 0, 0]])');
    expect(
      s(
        new SparseMatrix(
          3,
          3,
          new Map<MatrixPosition, Matrix | number>([
            [pos(0, 0), Matrix.of([[1, 1], [1, 1]])],
            [pos(1, 1), 1],
          ]),
        ),
      ),
    ).toBe('Matrix([[1, 1, 0], [1, 1, 0], [0, 0, 0]])');
    expect(s(new SparseMatrix(2, 3, (i, j) => i + j))).toBe('Matrix([[0, 1, 2], [1, 2, 3]])');
    expect(new SparseMatrix().shape).toEqual([0, 0]);
    expect(s(new SparseMatrix([1, 0, 2]))).toBe('Matrix([[1], [0], [2]])');
    expect(new SparseMatrix([]).shape).toEqual([0, 0]);
    expect(new SparseMatrix([[], []]).shape).toEqual([0, 0]);
    expect(new SparseMatrix(null, new Map()).shape).toEqual([0, 0]);
    expect(new SparseMatrix(null, null, [[1], [0, 2]]).shape).toEqual([2, 2]);
    expect(s(new SparseMatrix(1, 1, new Map([[pos(0, 0), 0]])))).toBe('Matrix([[0]])');
    expect(
      s(
        new SparseMatrix(
          2,
          2,
          new Map([
            [pos(0, 0), new Float(1)],
            [pos(1, 1), new Float(0)],
          ]),
        ),
      ),
    ).toBe('Matrix([[1.00000000000000, 0], [0, 0]])');
    expect(s(new SparseMatrix(new SparseMatrix(2, 2, [1, 0, 0, x])))).toBe('Matrix([[1, 0], [0, x]])');
    expect(new SparseMatrix(0, 3, new Map()).shape).toEqual([0, 3]);
    // SymPy raises "collision at (0, 1)": its recursive call for a list value replaces the
    // dictionary being filled; the block [[1, 2], [3]] belongs at (0, 1)
    expect(s(new SparseMatrix(3, 3, new Map([[pos(0, 1), [[1, 2], [3]]]])))).toBe('Matrix([[0, 1, 2], [0, 3, 0], [0, 0, 0]])');
  });

  it('rejects inconsistent input', () => {
    expect(() => new SparseMatrix(2, 2, [1, 2])).toThrow('The length of the flat list (2) does not match the specified size (2 * 2).');
    expect(() => new SparseMatrix(2, 2, [[1, 2, 3]])).toThrow('The location (0, 2) is out of the designated range[0, 1]x[0, 1]');
    expect(() => new SparseMatrix(2, 2, [[1, 2], [3], [4]])).toThrow('The location (2, 0) is out of the designated range[0, 1]x[0, 1]');
    expect(
      () =>
        new SparseMatrix(
          3,
          3,
          new Map<MatrixPosition, Matrix | number>([
            [pos(0, 0), Matrix.of([[1, 1], [1, 1]])],
            [pos(1, 1), 2],
          ]),
        ),
    ).toThrow('There is a collision at (1, 1) for 2 and 1.');
    expect(() => new SparseMatrix(null, null, (i) => i)).toThrow('null and null must be integers for this specification.');
    // SymPy raises a TypeError (None * None)
    expect(() => new SparseMatrix(null, [1, 2])).toThrow(RangeError);
  });

  it('lists the nonzero entries', () => {
    expect([...new SparseMatrix(2, 2, new Map([[pos(1, 0), x]])).todok()].map(([k, v]) => [k, str(v)])).toEqual([[[1, 0], 'x']]);
  });
});

describe('ImmutableSparseMatrix', () => {
  it('is an immutable explicit matrix', () => {
    expect(str(new ImmutableSparseMatrix(1, 1, new Map()))).toBe('Matrix([[0]])');
    const m = new ImmutableSparseMatrix(Matrix.eye(3));
    expect(str(m)).toBe('Matrix([[1, 0, 0], [0, 1, 0], [0, 0, 1]])');
    expect(m.shape.map(str)).toEqual(['3', '3']);
    expect([...m.todok()].map(([k, v]) => [k, str(v)])).toEqual([
      [[0, 0], '1'],
      [[1, 1], '1'],
      [[2, 2], '1'],
    ]);
    expect(new ImmutableSparseMatrix(0, 3, new Map()).shape.map(str)).toEqual(['0', '3']);
  });

  it('has ImmutableDenseMatrix as ImmutableMatrix', () => {
    expect(ImmutableDenseMatrix).toBe(ImmutableMatrix);
  });
});

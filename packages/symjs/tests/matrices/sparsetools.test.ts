// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/matrices/sparsetools.ts (SymPy sympy.matrices.sparsetools.banded); expected values printed by SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Matrix, Rational, banded, pow, add, symbols } from '../../src';
import type { BandedValue } from '../../src';

const [x] = symbols('x');
const sq = (d: number) => pow(add(1, d), 2);

describe('banded', () => {
  it('builds matrices from diagonals like SymPy', () => {
    const cases: [ReturnType<typeof banded>, string][] = [
      [banded(new Map<number, BandedValue>([[1, [1, 2, 3]], [-1, [4, 5, 6]], [0, x]])), 'Matrix([[x, 1, 0, 0], [4, x, 2, 0], [0, 5, x, 3], [0, 0, 6, x]])'],
      [banded(5, new Map<number, BandedValue>([[0, sq], [2, sq], [-2, 2]])), 'Matrix([[1, 0, 1, 0, 0], [0, 4, 0, 4, 0], [2, 0, 9, 0, 9], [0, 2, 0, 16, 0], [0, 0, 2, 0, 25]])'],
      [banded(new Map<number, BandedValue>([[0, Matrix.col(1, 2, 3)]]), { cols: 3 }), 'Matrix([[1, 0, 0], [2, 1, 0], [3, 2, 1], [0, 3, 2], [0, 0, 3]])'],
      [banded(Rational.of(4n), new Map<number, BandedValue>([[0, Matrix.ones(2)]])), 'Matrix([[1, 1, 0, 0], [1, 1, 0, 0], [0, 0, 1, 1], [0, 0, 1, 1]])'],
      [banded(new Map<number, BandedValue>([[0, 2], [2, [Matrix.ones(2), Matrix.ones(2), Matrix.ones(2)]]])), 'Matrix([[2, 0, 1, 1, 0, 0, 0, 0], [0, 2, 1, 1, 0, 0, 0, 0], [0, 0, 2, 0, 1, 1, 0, 0], [0, 0, 0, 2, 1, 1, 0, 0], [0, 0, 0, 0, 2, 0, 1, 1], [0, 0, 0, 0, 0, 2, 1, 1]])'],
      [banded(2, 3, new Map<number, BandedValue>([[0, 1]])), 'Matrix([[1, 0, 0], [0, 1, 0]])'],
      [banded(new Map<number, BandedValue>([[0, 1]]), { rows: 3 }), 'Matrix([[1, 0, 0], [0, 1, 0], [0, 0, 1]])'],
      [banded(new Map<number, BandedValue>([[1, [[1, 2]]]])), 'Matrix([[0, 1], [0, 2]])'],
      [banded(new Map<number, BandedValue>([[0, [[1], 2]]])), 'Matrix([[1, 0], [0, 2]])'],
      [banded(new Map<number, BandedValue>([[0, [[[1, 2], [3, 4]]]]])), 'Matrix([[1, 2], [3, 4]])'],
      [banded(new Map<number, BandedValue>([[0, Matrix.ones(2)]]), { rows: 4 }), 'Matrix([[1, 1, 0, 0], [1, 1, 0, 0], [0, 0, 1, 1], [0, 0, 1, 1]])'],
      [banded(new Map<number, BandedValue>([[0, Matrix.ones(2)]])), 'Matrix([[1, 1], [1, 1]])'],
      [banded(new Map<number, BandedValue>([[0, 0], [1, [1]]])), 'Matrix([[0, 1]])'],
      [banded(3, new Map<number, BandedValue>([[0, 1], [1, [2, 3]], [-1, [4, 5]]])), 'Matrix([[1, 2, 0], [4, 1, 3], [0, 5, 1]])'],
      [banded(1, 2, new Map<number, BandedValue>([[0, 1]])), 'Matrix([[1, 0]])'],
      [banded(new Map<number, BandedValue>([[0, 1]]), {}), 'Matrix([[1]])'],
      [banded(new Map<number, BandedValue>()), 'Matrix(0, 0, [])'],
    ];
    for (const [m, s] of cases) expect(String(m)).toBe(s);
  });

  it('gives 0 where a function diagonal is 0 (SymPy leaves a Dummy there)', () => {
    expect(String(banded(3, new Map<number, BandedValue>([[0, (i: number) => i]])))).toBe('Matrix([[0, 0, 0], [0, 1, 0], [0, 0, 2]])');
    expect(String(banded(new Map<number, BandedValue>([[0, (i: number) => i]])))).toBe('Matrix([[0]])');
  });

  it('rejects invalid input like SymPy', () => {
    expect(() => banded(new Map<number, BandedValue>([[0, [1, 2]]]), { cols: 1 })).toThrow('Designated cols 1 < needed 2');
    expect(() => banded(new Map<number, BandedValue>([[0, [1, 2]]]), { rows: 1 })).toThrow('Designated rows 1 < needed 2');
    expect(() => banded(3, new Map<number, BandedValue>([[0, Matrix.ones(2)]]))).toThrow('sequence does not fit');
    expect(() => banded(new Map<number, BandedValue>([[0, Matrix.ones(2)]]), { cols: 3 })).toThrow('sequence does not fit');
    expect(() => banded(new Map<number, readonly (number | readonly number[])[]>([[0, [1, 2]], [1, [[3, 4], [5, 6]]]]))).toThrow('collision at (1, 1)');
    expect(() => banded(x, new Map<number, BandedValue>([[0, 1]]))).toThrow(TypeError);
    expect(() => banded(new Map<number, BandedValue>([[0.5, 1]]))).toThrow(TypeError);
    expect(() => banded(new Map<number, BandedValue>([[0, 1]]), new Map<number, BandedValue>([[1, 2]]) as never)).toThrow(TypeError);
    expect(() => banded(1 as never)).toThrow(TypeError);
  });
});

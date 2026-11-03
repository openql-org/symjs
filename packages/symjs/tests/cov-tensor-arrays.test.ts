// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Edge cases of sympy.tensor.array (slicing, construction, assignment,
// sparse arrays, derivatives), ArrayComprehension and Idx; expected values
// from SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Indexed, Matrix, S, diff, latex, mul, pi, symbols, sympify } from '../src';
import {
  ArrayComprehension,
  ArrayComprehensionMap,
  Idx,
  ImmutableDenseNDimArray as IDA,
  ImmutableSparseNDimArray as ISA,
  MutableDenseNDimArray as MDA,
  MutableSparseNDimArray as MSA,
  SymArray,
  deriveByArray,
  permutedims,
  slice,
  tensorcontraction,
  tensordiagonal,
} from '../src/tensor';

const [x, y, n, i, j] = symbols('x y n i j');
const s = (v: unknown): string => String(v);
const a = IDA([0, 1, 2, 3, 4, 5], [2, 3]);

describe('slicing', () => {
  it('negative and out-of-range bounds are clipped as in Python', () => {
    expect(s(a.get(0, '::-1'))).toBe('[2, 1, 0]');
    expect(s(a.get('-1:', ':'))).toBe('[[3, 4, 5]]');
    expect(s(a.get(':', '10:'))).toBe('ImmutableDenseNDimArray([], (2, 0))');
    expect(s(a.get(':', '-10:'))).toBe('[[0, 1, 2], [3, 4, 5]]');
    expect(s(a.get(':', '5:-10:-1'))).toBe('[[2, 1, 0], [5, 4, 3]]');
    // SymPy 1.14 gives [[2], [5]] for a[:, ::-2], dropping the element at
    // index 0; Python's range(3)[::-2] is [2, 0], which is kept here.
    expect(s(a.get(':', '::-2'))).toBe('[[2, 0], [5, 3]]');
    expect(s(a.get(-1))).toBe('[3, 4, 5]');
    expect(s(a.get(-1, -1))).toBe('5');
  });
  it('invalid slices and indices', () => {
    expect(() => slice(1.5)).toThrow(TypeError);
    expect(() => a.get(0, slice(0, 2, 0))).toThrow(RangeError);
    expect(() => a.get(S.Half)).toThrow(TypeError);
    expect(() => a.get(0, [1])).toThrow(TypeError);
    expect(s(slice(1, 3))).toBe('1:3');
    expect(s(slice(undefined, undefined, 2))).toBe('::2');
  });
  it('symbolic indices outside the bounds of an Idx', () => {
    expect(() => a.get(Idx('i', [3, 5]), 0)).toThrow(RangeError);
    expect(() => a.get(0, Idx('j', [-3, -1]))).toThrow(RangeError);
  });
});

describe('construction', () => {
  it('nested arrays and matrices with a shape, integer shapes', () => {
    expect(s(SymArray([SymArray([1, 2]), Matrix.of([[3, 4]])], [4]))).toBe('[1, 2, 3, 4]');
    expect(s(SymArray([0, 1, 2, 3], [2n, sympify(2)]))).toBe('[[0, 1], [2, 3]]');
    expect(() => SymArray([0, 1, 2, 3], [2.5])).toThrow(TypeError);
    // Python None has no counterpart; other non-numeric elements are rejected.
    expect(() => SymArray([null as unknown as number])).toThrow(TypeError);
  });
  it('from a Map of positions (SymPy 1.14 fails with IndexError here)', () => {
    expect(s(SymArray(new Map<number | number[], number>([[0, 1], [1, 0], [3, 5]]), [2, 2]))).toBe('[[1, 0], [0, 5]]');
    expect(
      s(
        IDA(
          new Map<number | number[], number>([
            [0, 1],
            [[1, 1], 5],
          ]),
          [2, 2],
        ),
      ),
    ).toBe('[[1, 0], [0, 5]]');
  });
  it('tolist and latex of empty and rank-0 arrays', () => {
    // SymPy Array(5).tolist() fails with IndexError.
    expect(() => SymArray(5).tolist()).toThrow(RangeError);
    expect(SymArray([], [2, 0]).tolist()).toEqual([[], []]);
    // SymPy 1.14 latex(Array([], (2, 0))) fails with IndexError.
    expect(latex(SymArray([], [2, 0]))).toBe('\\left[\\begin{matrix}\\end{matrix}\\right]');
  });
});

describe('arithmetic, substitution and evaluation', () => {
  it('scalar zero on the left', () => {
    expect(s(SymArray([1, x]).rmul(0))).toBe('[0, 0]');
    expect(s(ISA([1, x]).rmul(0))).toBe('[0, 0]');
  });
  it('subs needs a replacement; evalf and n are elementwise', () => {
    expect(() => SymArray([x]).subs(x)).toThrow(TypeError);
    expect(s(SymArray([pi]).evalf(3))).toBe('[3.14]');
    expect(s(SymArray([pi]).n(3))).toBe('[3.14]');
  });
});

describe('sparse arrays', () => {
  const sp = ISA([1, x, 0, 0]);
  it('reshape, applyfunc and equality', () => {
    expect(() => sp.reshape(3)).toThrow(RangeError);
    expect(s(sp.applyfunc((e) => mul(e, 0)))).toBe('[0, 0, 0, 0]');
    expect(sp.equals(ISA([1, x]))).toBe(false);
    expect(sp.equals(ISA([1, x, 0, 0], [2, 2]))).toBe(false);
    expect(sp.equals(ISA([1, 0, 0, 0]))).toBe(false);
    expect(sp.equals(SymArray([1, x, 0, 0]))).toBe(true);
    expect(s(sp.subs(x, 3))).toBe('[1, 3, 0, 0]');
    expect(s(sp.withArgs([sympify(7), y]))).toBe('[7, y, 0, 0]');
  });
  it('a mutable sparse array is its own mutable form', () => {
    const m = MSA([1, 0]);
    expect(m.asMutable()).toBe(m);
  });
});

describe('assignment', () => {
  it('errors', () => {
    const m = MDA.zeros(2, 2);
    expect(() => m.set([0], 5)).toThrow(RangeError);
    // SymPy 1.14 stores a nested list as an element here; the index has
    // more positions than the rank, as in a[0, 0, :].
    expect(() => m.set(0, 0, ':', [1])).toThrow(RangeError);
    expect(() => m.set(x, 0, 1)).toThrow(TypeError);
    // SymPy raises NotImplementedError.
    expect(() => m.set(0, 0, [1])).toThrow(TypeError);
    expect(() => (m.set as (...args: unknown[]) => void)()).toThrow(TypeError);
    expect(() => (m.set as (...args: unknown[]) => void)(true, 1)).toThrow(TypeError);
    expect(s(m)).toBe('[[0, 0], [0, 0]]');
    m.set(-1, 5);
    expect(s(m)).toBe('[[0, 0], [0, 5]]');
  });
});

describe('derivatives', () => {
  it('diff counts', () => {
    expect(s(a.diff(x, 2))).toBe('[[0, 0, 0], [0, 0, 0]]');
    expect(s(SymArray([mul(x, x)]).diff(x, 2))).toBe('[2]');
    expect(s(SymArray([mul(x, y)]).diff(x, y))).toBe('[1]');
    expect(s(SymArray([x]).diff(x, undefined))).toBe('[1]');
    expect(() => SymArray([x]).diff(2)).toThrow(TypeError);
    expect(() => SymArray([x]).diff(x, -1)).toThrow(RangeError);
    expect(() => SymArray([x]).diff()).toThrow(TypeError);
  });
  it('symbolic indexing of an array', () => {
    const A = SymArray([
      [x, mul(x, x)],
      [1, y],
    ]);
    expect(s(diff(A.get(i, j), x))).toBe('[[1, 2*x], [0, 0]][i, j]');
    expect(s(diff(A.get(i, j), A.get(i, j)))).toBe('1');
    const B = symbols('B')[0];
    const bij = A.get(i, j).subs(A, B);
    expect(s(bij)).toBe('B[i, j]');
    expect(bij).toBeInstanceOf(Indexed);
    expect(s(diff(bij, x))).toBe('0');
  });
  it('derive_by_array', () => {
    expect(s(deriveByArray([x, y], [x, y]))).toBe('[[1, 0], [0, 1]]');
    expect(s(deriveByArray(ISA([x, 0]), [x, y]))).toBe('[[1, 0], [0, 0]]');
    expect(s(deriveByArray(mul(x, y), x))).toBe('y');
    expect(s(deriveByArray([mul(x, y), y], x))).toBe('[y, 0]');
    expect(s(deriveByArray(MDA([mul(x, y), y]), x))).toBe('[y, 0]');
    expect(s(deriveByArray(mul(x, y), [x, y]))).toBe('[y, x]');
  });
});

describe('array operations: errors', () => {
  const a3 = SymArray([0, 1, 2, 3, 4, 5, 6, 7], [2, 2, 2]);
  it('tensordiagonal', () => {
    expect(() => tensordiagonal(a3, [0, 3])).toThrow(RangeError);
    expect(() => tensordiagonal(a, [0, 1])).toThrow(RangeError);
    expect(() => tensordiagonal(a3, [0, 0])).toThrow(RangeError);
  });
  it('permutedims', () => {
    expect(() => permutedims(a3, [1, 0, 2], { indexOrderNew: 'abc' })).toThrow(RangeError);
    expect(() => permutedims(a3, [1, 0, 2], { indexOrderOld: 'abc' })).toThrow(RangeError);
    expect(() => permutedims(a3, { indexOrderNew: 'ab', indexOrderOld: 'abc' })).toThrow(RangeError);
    expect(() => permutedims(a3, { indexOrderNew: 'abc', indexOrderOld: 'ab' })).toThrow(RangeError);
    expect(() => permutedims(a3, { indexOrderNew: 'abd', indexOrderOld: 'abc' })).toThrow(RangeError);
    expect(s(permutedims(a3, { indexOrderNew: 'cab', indexOrderOld: 'abc' }))).toBe('[[[0, 2], [4, 6]], [[1, 3], [5, 7]]]');
    expect(s(permutedims(a3, undefined, { indexOrderNew: 'cab', indexOrderOld: 'abc' }))).toBe('[[[0, 2], [4, 6]], [[1, 3], [5, 7]]]');
    // SymPy raises ValueError: there were repeated elements.
    expect(() => permutedims(SymArray([0, 1, 2, 3], [2, 2]), [0, 0])).toThrow(RangeError);
  });
  it('a scalar is not an array (SymPy AttributeError)', () => {
    expect(() => tensorcontraction(5, [0, 1])).toThrow(TypeError);
  });
});

describe('ArrayComprehension and Idx', () => {
  it('rank 0 and symbolic shapes', () => {
    // SymPy len(Array(5)) == 1: a rank-0 array has one element (SymPy 1.14
    // fails on len(ArrayComprehension(x)) with AttributeError).
    expect(ArrayComprehension(x).length).toBe(1);
    expect(s(ArrayComprehension(x).doit())).toBe('x');
    expect(() => ArrayComprehension(x, [x, 1, n]).length).toThrow(RangeError);
    expect(ArrayComprehension(x, [x, 1, n]).doitSelf()).toBeUndefined();
    expect(s(ArrayComprehensionMap(() => 1, [x, 1, 2]).doit())).toBe('[1, 1]');
  });
  it('Idx labels', () => {
    expect(() => Idx(S.Half)).toThrow(TypeError);
    expect(() => new Idx(sympify(3))).toThrow(TypeError);
  });
});

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/tensor/arrayop.ts.
// Array operations: tensorproduct, tensorcontraction, derive_by_array, permutedims. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Matrix, sin, symbols, transpose } from '../../src';
import {
  SymArray as SArray,
  ImmutableDenseNDimArray,
  ImmutableSparseNDimArray,
  MutableDenseNDimArray,
  NDimArray,
  permutedims,
  tensorcontraction,
  tensordiagonal,
  tensorproduct,
  ImmutableDenseNDimArray as IDA,
  SymArray,
} from '../../src/tensor';

// SymPy sympy.tensor.array (every doctest of its modules that implement
// sympy.tensor.array.__all__) and sympy.tensor.indexed.Idx; expected
// values from SymPy 1.14.

const [x, y, z, t] = symbols('x y z t');
const [a, b, c, d, e, f, g, h] = symbols('a b c d e f g h');
const range = (n: number): number[] => Array.from({ length: n }, (_, i) => i);
const s = (v: unknown): string => String(v);

describe('sympy.tensor.array module docstring', () => {
  it('tensorproduct', () => {
    const A = SArray([x, y, z, t]);
    const B = SArray([1, 2, 3, 4]);
    expect(s(tensorproduct(A, B))).toBe('[[x, 2*x, 3*x, 4*x], [y, 2*y, 3*y, 4*y], [z, 2*z, 3*z, 4*z], [t, 2*t, 3*t, 4*t]]');
    const p1 = tensorproduct(A, Matrix.eye(4)) as NDimArray;
    expect(s(p1)).toBe(
      '[[[x, 0, 0, 0], [0, x, 0, 0], [0, 0, x, 0], [0, 0, 0, x]], [[y, 0, 0, 0], [0, y, 0, 0], [0, 0, y, 0], [0, 0, 0, y]], [[z, 0, 0, 0], [0, z, 0, 0], [0, 0, z, 0], [0, 0, 0, z]], [[t, 0, 0, 0], [0, t, 0, 0], [0, 0, t, 0], [0, 0, 0, t]]]',
    );
    expect(s(p1.get(0, ':', ':'))).toBe('[[x, 0, 0, 0], [0, x, 0, 0], [0, 0, x, 0], [0, 0, 0, x]]');
  });

  it('tensorcontraction', () => {
    const C = SArray([
      [x, y],
      [z, t],
    ]);
    expect(s(tensorcontraction(C, [0, 1]))).toBe('t + x');
    const D = SArray([
      [2, 1],
      [0, -1],
    ]);
    expect(s(tensorcontraction(tensorproduct(C, D) as NDimArray, [1, 2]))).toBe('[[2*x, x - y], [2*z, -t + z]]');
    expect(s(Matrix.of([[x, y], [z, t]]).mul(Matrix.of([[2, 1], [0, -1]])))).toBe('Matrix([[2*x, x - y], [2*z, -t + z]])');
    expect(s(C.tomatrix().mul(D.tomatrix()))).toBe('Matrix([[2*x, x - y], [2*z, -t + z]])');
  });

  it('tensordiagonal of a Matrix', () => {
    const m = Matrix.of([
      [a, b],
      [c, d],
    ]);
    expect(s(tensorcontraction(m, [0, 1]))).toBe('a + d');
    expect(s(tensordiagonal(m, [0, 1]))).toBe('[a, d]');
  });
});

describe('sympy.tensor.array.arrayop', () => {
  it('permutedims', () => {
    const A = SArray([
      [x, y, z],
      [t, sin(x), 0],
    ]);
    expect(s(A)).toBe('[[x, y, z], [t, sin(x), 0]]');
    expect(s(permutedims(A, [1, 0]))).toBe('[[x, t], [y, sin(x)], [z, 0]]');
    expect(s(transpose(A))).toBe('[[x, t], [y, sin(x)], [z, 0]]');
    const B = SArray([
      [
        [1, 2],
        [3, 4],
      ],
      [
        [5, 6],
        [7, 8],
      ],
    ]);
    expect(s(permutedims(B, [2, 1, 0]))).toBe('[[[1, 5], [3, 7]], [[2, 6], [4, 8]]]');
    expect(s(permutedims(B, [1, 2, 0]))).toBe('[[[1, 5], [2, 6]], [[3, 7], [4, 8]]]');
    expect(s(permutedims(B, { indexOrderOld: 'cba', indexOrderNew: 'abc' }))).toBe('[[[1, 5], [3, 7]], [[2, 6], [4, 8]]]');
    expect(s(permutedims(B, { indexOrderOld: 'cab', indexOrderNew: 'abc' }))).toBe('[[[1, 5], [2, 6]], [[3, 7], [4, 8]]]');
    // a Permutation (anything with an arrayForm) works too
    expect(s(permutedims(B, { arrayForm: [1, 2, 0] }))).toBe('[[[1, 5], [2, 6]], [[3, 7], [4, 8]]]');
  });

  it('tensorcontraction', () => {
    expect(s(tensorcontraction(Matrix.eye(3), [0, 1]))).toBe('3');
    const A = SArray(range(18), [3, 2, 3]);
    expect(s(A)).toBe('[[[0, 1, 2], [3, 4, 5]], [[6, 7, 8], [9, 10, 11]], [[12, 13, 14], [15, 16, 17]]]');
    expect(s(tensorcontraction(A, [0, 2]))).toBe('[21, 30]');
    const m1 = Matrix.of([
      [a, b],
      [c, d],
    ]);
    const m2 = Matrix.of([
      [e, f],
      [g, h],
    ]);
    const p = tensorproduct(m1, m2) as NDimArray;
    expect(s(p)).toBe('[[[[a*e, a*f], [a*g, a*h]], [[b*e, b*f], [b*g, b*h]]], [[[c*e, c*f], [c*g, c*h]], [[d*e, d*f], [d*g, d*h]]]]');
    expect(s(tensorcontraction(p, [1, 2]))).toBe('[[a*e + b*g, a*f + b*h], [c*e + d*g, c*f + d*h]]');
    expect(s(m1.mul(m2))).toBe('Matrix([[a*e + b*g, a*f + b*h], [c*e + d*g, c*f + d*h]])');
  });

  it('tensordiagonal', () => {
    expect(s(tensordiagonal(Matrix.eye(3), [0, 1]))).toBe('[1, 1, 1]');
    const m1 = Matrix.of([
      [a, b],
      [c, d],
    ]);
    expect(s(tensordiagonal(m1, [0, 1]))).toBe('[a, d]');
    const A = SArray(range(18), [3, 2, 3]);
    expect(s(tensordiagonal(A, [0, 2]))).toBe('[[0, 7, 14], [3, 10, 17]]');
    const expected = permutedims(SArray([A.get(0, ':', 0), A.get(1, ':', 1), A.get(2, ':', 2)] as NDimArray[]), [1, 0]);
    expect(tensordiagonal(A, [0, 2]).equals(expected)).toBe(true);
  });

  it('tensorproduct', () => {
    const A = SArray([
      [1, 2],
      [3, 4],
    ]);
    const B = SArray([x, y]);
    expect(s(tensorproduct(A, B))).toBe('[[[x, y], [2*x, 2*y]], [[3*x, 3*y], [4*x, 4*y]]]');
    expect(s(tensorproduct(A, x))).toBe('[[x, 2*x], [3*x, 4*x]]');
    expect(s(tensorproduct(A, B, B))).toBe(
      '[[[[x**2, x*y], [x*y, y**2]], [[2*x**2, 2*x*y], [2*x*y, 2*y**2]]], [[[3*x**2, 3*x*y], [3*x*y, 3*y**2]], [[4*x**2, 4*x*y], [4*x*y, 4*y**2]]]]',
    );
    const m = Matrix.of([
      [x, y],
      [z, t],
    ]);
    expect(s(tensorproduct(Matrix.eye(3), m))).toBe(
      '[[[[x, y], [z, t]], [[0, 0], [0, 0]], [[0, 0], [0, 0]]], [[[0, 0], [0, 0]], [[x, y], [z, t]], [[0, 0], [0, 0]]], [[[0, 0], [0, 0]], [[0, 0], [0, 0]], [[x, y], [z, t]]]]',
    );
  });
});

describe('array operations: more cases', () => {
  it('tensorproduct', () => {
    expect(s(tensorproduct())).toBe('1');
    expect(s(tensorproduct(x))).toBe('x');
    expect(s(tensorproduct([1, 2]))).toBe('[1, 2]');
    expect(s(tensorproduct(x, y))).toBe('x*y');
    expect(s(tensorproduct(x, SArray([1, 2])))).toBe('[x, 2*x]');
    const sp = tensorproduct(ImmutableSparseNDimArray([0, 1]), ImmutableSparseNDimArray([2, 0]));
    expect(s(sp)).toBe('[[0, 0], [2, 0]]');
    expect(sp).toBeInstanceOf(ImmutableSparseNDimArray);
    expect(tensorproduct(ImmutableSparseNDimArray([0, 1]), SArray([2, 0]))).toBeInstanceOf(ImmutableDenseNDimArray);
    expect(tensorproduct(MutableDenseNDimArray([0, 1]), SArray([2, 0]))).toBeInstanceOf(ImmutableDenseNDimArray);
  });

  it('tensorcontraction', () => {
    expect(s(tensorcontraction(MutableDenseNDimArray([[0, 1], [1, 1]]), [0, 1]))).toBe('1');
    expect(tensorcontraction(MutableDenseNDimArray(range(8), [2, 2, 2]), [0, 1])).toBeInstanceOf(MutableDenseNDimArray);
    const sc = tensorcontraction(ImmutableSparseNDimArray(range(8), [2, 2, 2]), [0, 1]);
    expect(s(sc)).toBe('[6, 8]');
    expect(sc).toBeInstanceOf(ImmutableSparseNDimArray);
    expect(s(tensorcontraction(SArray(range(16), [2, 2, 2, 2]), [0, 1], [2, 3]))).toBe('30');
    expect(s(tensorcontraction(SArray(range(16), [2, 2, 2, 2]), [0, 1, 2]))).toBe('[14, 16]');
    expect(s(tensorcontraction(SArray(range(8), [2, 2, 2])))).toBe('[[[0, 1], [2, 3]], [[4, 5], [6, 7]]]');
    expect(() => tensorcontraction(SArray(range(8), [2, 2, 2]), [0, 0])).toThrow('dimension specified more than once');
    expect(() => tensorcontraction(SArray(range(12), [2, 3, 2]), [0, 1])).toThrow(
      'cannot contract or diagonalize between axes of different dimension',
    );
    expect(() => tensorcontraction(SArray(range(8), [2, 2, 2]), 0 as never)).toThrow('collections of contraction/diagonal axes expected');
  });

  it('tensordiagonal', () => {
    expect(s(tensordiagonal(SArray(range(8), [2, 2, 2]), [0, 1, 2]))).toBe('[0, 7]');
    expect(s(tensordiagonal(SArray(range(16), [2, 2, 2, 2]), [0, 1], [2, 3]))).toBe('[[0, 3], [12, 15]]');
    const sd = tensordiagonal(ImmutableSparseNDimArray(range(8), [2, 2, 2]), [0, 1]);
    expect(s(sd)).toBe('[[0, 6], [1, 7]]');
    expect(sd).toBeInstanceOf(ImmutableSparseNDimArray);
    expect(s(tensordiagonal(SArray(range(4), [2, 2]), [0, 1]))).toBe('[0, 3]');
    expect(() => tensordiagonal(SArray(range(8), [2, 2, 2]), [0])).toThrow('need at least two axes to diagonalize');
    expect(() => tensordiagonal(SArray(range(12), [2, 3, 2]), [0, 1])).toThrow('diagonalizing indices of different dimensions');
    expect(() => tensordiagonal(SArray(range(8), [2, 2, 2]), [0, 3])).toThrow('index is larger than expression shape');
    expect(() => tensordiagonal(SArray(range(8), [2, 2, 2]))).toThrow(TypeError);
  });

  it('permutedims', () => {
    const A = SArray(range(6), [2, 3]);
    expect(() => permutedims(A, {})).toThrow('Permutation not defined');
    expect(() => permutedims(A, [0, 1, 2])).toThrow('wrong permutation size');
    expect(() => permutedims(A, [1, 0], { indexOrderOld: 'ab' })).toThrow('index_order_old cannot be defined with permutation');
    expect(s(permutedims(A, { indexOrderOld: 'ab', indexOrderNew: 'ba' }))).toBe('[[0, 3], [1, 4], [2, 5]]');
    expect(s(permutedims(A, { indexOrderOld: ['a', 'b'], indexOrderNew: ['b', 'a'] }))).toBe('[[0, 3], [1, 4], [2, 5]]');
    expect(() => permutedims(A, { indexOrderOld: 'ab', indexOrderNew: 'bc' })).toThrow(
      'index_order_new and index_order_old must have the same indices',
    );
    expect(s(permutedims(ImmutableSparseNDimArray([0, 1, 0, 2, 0, 3], [2, 3]), [1, 0]))).toBe('[[0, 2], [1, 0], [0, 3]]');
    expect(s(permutedims([[1, 2], [3, 4]], [1, 0]))).toBe('[[1, 3], [2, 4]]');
    expect(s(permutedims(Matrix.of([[1, 2], [3, 4]]), [1, 0]))).toBe('[[1, 3], [2, 4]]');
  });
});

// Edge cases of sympy.tensor.array (slicing, construction, assignment,
// sparse arrays, derivatives), ArrayComprehension and Idx; expected values
// from SymPy 1.14.
const ida = IDA([0, 1, 2, 3, 4, 5], [2, 3]);

describe('array operations: errors', () => {
  const a3 = SymArray([0, 1, 2, 3, 4, 5, 6, 7], [2, 2, 2]);
  it('tensordiagonal', () => {
    expect(() => tensordiagonal(a3, [0, 3])).toThrow(RangeError);
    expect(() => tensordiagonal(ida, [0, 1])).toThrow(RangeError);
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

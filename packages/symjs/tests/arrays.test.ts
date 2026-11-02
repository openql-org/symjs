// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// SymPy sympy.tensor.array (every doctest of its modules that implement
// sympy.tensor.array.__all__) and sympy.tensor.indexed.Idx; expected
// values from SymPy 1.14.

import { describe, expect, it } from 'vitest';
import {
  I,
  Integral,
  Matrix,
  S,
  Sym,
  add,
  adjoint,
  conjugate,
  cos,
  diff,
  exp,
  latex,
  mul,
  oo,
  pow,
  simplify,
  sin,
  symbols,
  transpose,
} from '../src';
import { Indexed } from '../src/core/indexed';
import { isIntegerQ } from '../src/core/assumptions';
import { NoMatch } from '../src/core/truth';
import {
  SymArray as SArray,
  ArrayComprehension,
  ArrayComprehensionMap,
  ArrayKind,
  BooleanKind,
  DenseNDimArray,
  Flatten,
  Idx,
  ImmutableDenseNDimArray,
  ImmutableSparseNDimArray,
  MutableDenseNDimArray,
  MutableSparseNDimArray,
  NDimArray,
  NumberKind,
  SparseNDimArray,
  UndefinedKind,
  deriveByArray,
  kindOf,
  permutedims,
  slice,
  tensorcontraction,
  tensordiagonal,
  tensorproduct,
} from '../src/tensor';

const [x, y, z, t] = symbols('x y z t');
const [a, b, c, d, e, f, g, h] = symbols('a b c d e f g h');
const range = (n: number): number[] => Array.from({ length: n }, (_, i) => i);
const s = (v: unknown): string => String(v);

describe('sympy.tensor.array module docstring', () => {
  it('construction, shape and rank', () => {
    const a1 = SArray([
      [1, 2],
      [3, 4],
      [5, 6],
    ]);
    expect(s(a1)).toBe('[[1, 2], [3, 4], [5, 6]]');
    expect(a1.shape).toEqual([3, 2]);
    expect(a1.rank()).toBe(2);
    const a2 = SArray([
      [
        [x, y],
        [z, mul(x, z)],
      ],
      [
        [1, mul(x, y)],
        [pow(x, -1), mul(x, pow(y, -1))],
      ],
    ]);
    expect(s(a2)).toBe('[[[x, y], [z, x*z]], [[1, x*y], [1/x, x/y]]]');
    expect(a2.shape).toEqual([2, 2, 2]);
    expect(a2.rank()).toBe(3);
  });

  it('flat list and shape, indexing, reshape, slices', () => {
    const m1 = SArray(range(12), [3, 4]);
    expect(s(m1)).toBe('[[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11]]');
    const m2 = SArray(range(12), [3, 2, 2]);
    expect(s(m2)).toBe('[[[0, 1], [2, 3]], [[4, 5], [6, 7]], [[8, 9], [10, 11]]]');
    expect(s(m2.get(1, 1, 1))).toBe('7');
    expect(s(m2.reshape(4, 3))).toBe('[[0, 1, 2], [3, 4, 5], [6, 7, 8], [9, 10, 11]]');
    expect(s(m2.get(':', 1, 1))).toBe('[3, 7, 11]');
    expect(s(m2.get(slice(), 1, 1))).toBe('[3, 7, 11]');
    expect(s(m2.tolist())).toBe(s([[[0, 1], [2, 3]], [[4, 5], [6, 7]], [[8, 9], [10, 11]]]));
    expect(Array.isArray(m2.tolist())).toBe(true);
    expect(s(m1.tomatrix())).toBe('Matrix([[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11]])');
  });

  it('diff, scalar product, applyfunc', () => {
    const m3 = SArray([pow(x, 3), mul(x, y), z]);
    expect(s(m3.diff(x))).toBe('[3*x**2, y, 0]');
    expect(s(m3.diff(z))).toBe('[0, 0, 1]');
    expect(s(m3.rmul(add(1, x)))).toBe('[x**3*(x + 1), x*y*(x + 1), z*(x + 1)]');
    expect(s(m3.applyfunc((v) => mul(v, S.Half)))).toBe('[x**3/2, x*y/2, z/2]');
  });

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

  it('derive_by_array', () => {
    expect(s(deriveByArray(sin(mul(x, y)), x))).toBe('y*cos(x*y)');
    expect(s(deriveByArray(sin(mul(x, y)), [x, y, z]))).toBe('[y*cos(x*y), x*cos(x*y), 0]');
    const ax = deriveByArray([exp(x), sin(mul(y, z)), t], [x, y, z]);
    expect(s(ax)).toBe('[[exp(x), 0, 0], [0, z*cos(y*z), 0], [0, y*cos(y*z), 0]]');
    expect(s(tensorcontraction(ax as NDimArray, [0, 1]))).toBe('z*cos(y*z) + exp(x)');
  });
});

describe('sympy.tensor.array.ndim_array', () => {
  it('ArrayKind', () => {
    expect(s(kindOf(NDimArray([1, 2, 3])))).toBe('ArrayKind(NumberKind)');
    const intA = new Integral([NDimArray([1, 2, 3]), x]);
    expect(intA instanceof NDimArray).toBe(false);
    expect(s(kindOf(intA))).toBe('ArrayKind(NumberKind)');
    const boolA = NDimArray([true, false]);
    expect(kindOf(boolA) instanceof ArrayKind).toBe(true);
    expect(kindOf(boolA) === ArrayKind(NumberKind)).toBe(false);
    expect(kindOf(boolA)).toBe(ArrayKind(BooleanKind));
    expect(ArrayKind()).toBe(ArrayKind(NumberKind));
    expect(s(ArrayKind(ArrayKind()))).toBe('ArrayKind(ArrayKind(NumberKind))');
    expect(s(kindOf(SArray([])))).toBe('ArrayKind(UndefinedKind)');
    expect(s(kindOf(SArray([x, true])))).toBe('ArrayKind(UndefinedKind)');
    expect(kindOf(x)).toBe(NumberKind);
    expect(kindOf(S.true)).toBe(BooleanKind);
    expect(kindOf(new Sym('A', { commutative: false }))).toBe(UndefinedKind);
  });

  it('NDimArray construction', () => {
    expect(s(MutableDenseNDimArray.zeros(2, 3, 4))).toBe(
      '[[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]], [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]]',
    );
    expect(
      s(
        MutableDenseNDimArray([
          [2, 3],
          [4, 5],
        ]),
      ),
    ).toBe('[[2, 3], [4, 5]]');
    expect(s(MutableDenseNDimArray([[[1, 2], [3, 4], [5, 6]], [[7, 8], [9, 10], [11, 12]]]))).toBe(
      '[[[1, 2], [3, 4], [5, 6]], [[7, 8], [9, 10], [11, 12]]]',
    );
    expect(s(MutableDenseNDimArray([1, 2, 3, 4, 5, 6], [2, 3]))).toBe('[[1, 2, 3], [4, 5, 6]]');
    const m = Matrix.of([
      [1, 2],
      [3, 4],
    ]);
    expect(s(m)).toBe('Matrix([[1, 2], [3, 4]])');
    expect(s(MutableDenseNDimArray(m))).toBe('[[1, 2], [3, 4]]');
    const p = MutableDenseNDimArray([1, 1, 1, 1], [2, 2]);
    const q = MutableDenseNDimArray([4, 4, 4, 4], [2, 2]);
    expect(s(p.add(q))).toBe('[[5, 5], [5, 5]]');
    expect(s(p.sub(q))).toBe('[[-3, -3], [-3, -3]]');
  });

  it('__eq__', () => {
    const p = MutableDenseNDimArray.zeros(2, 3);
    const q = MutableDenseNDimArray.zeros(2, 3);
    expect(p.equals(q)).toBe(true);
    const r = p.reshape(3, 2);
    expect(r.equals(q)).toBe(false);
    p.set(0, 0, 1);
    q.set(0, 0, 2);
    expect(p.equals(q)).toBe(false);
  });

  it('__len__, applyfunc, diff, rank, shape, tolist', () => {
    const z3 = MutableDenseNDimArray.zeros(3, 3);
    expect(s(z3)).toBe('[[0, 0, 0], [0, 0, 0], [0, 0, 0]]');
    expect(z3.length).toBe(9);
    const m = ImmutableDenseNDimArray(
      [0, 1, 2, 3].map((v) => v),
      [2, 2],
    );
    expect(s(m)).toBe('[[0, 1], [2, 3]]');
    expect(s(m.applyfunc((i) => mul(2, i)))).toBe('[[0, 2], [4, 6]]');
    const M = ImmutableDenseNDimArray([
      [x, y],
      [1, mul(x, y)],
    ]);
    expect(s(M.diff(x))).toBe('[[1, 0], [0, y]]');
    expect(MutableDenseNDimArray.zeros(3, 4, 5, 6, 3).rank()).toBe(5);
    expect(MutableDenseNDimArray.zeros(3, 3).shape).toEqual([3, 3]);
    const l = MutableDenseNDimArray([1, 2, 3, 4], [2, 2]);
    expect(s(l)).toBe('[[1, 2], [3, 4]]');
    expect(s(l.tolist())).toBe(s([[1, 2], [3, 4]]));
  });
});

describe('sympy.tensor.array.dense_ndim_array', () => {
  it('__getitem__', () => {
    const [i, j] = symbols('i j');
    const m = MutableDenseNDimArray([0, 1, 2, 3], [2, 2]);
    expect(s(m)).toBe('[[0, 1], [2, 3]]');
    expect(s(m.get(0, 0))).toBe('0');
    expect(s(m.get(1, 1))).toBe('3');
    expect(s(m.get(0))).toBe('[0, 1]');
    expect(s(m.get(1))).toBe('[2, 3]');
    const ij = m.get(i, j);
    expect(s(ij)).toBe('[[0, 1], [2, 3]][i, j]');
    expect(s(ij.subs(new Map([[i, 1], [j, 1]])))).toBe('3');
  });

  it('reshape', () => {
    const m = MutableDenseNDimArray([1, 2, 3, 4, 5, 6], [2, 3]);
    expect(m.shape).toEqual([2, 3]);
    expect(s(m)).toBe('[[1, 2, 3], [4, 5, 6]]');
    const r = m.reshape(3, 2);
    expect(r.shape).toEqual([3, 2]);
    expect(s(r)).toBe('[[1, 2], [3, 4], [5, 6]]');
  });

  it('tomatrix', () => {
    const m = MutableDenseNDimArray(
      range(9).map(() => 1),
      [3, 3],
    );
    expect(s(m.tomatrix())).toBe('Matrix([[1, 1, 1], [1, 1, 1], [1, 1, 1]])');
  });

  it('__setitem__', () => {
    const m = MutableDenseNDimArray.zeros(2, 2);
    m.set(0, 0, 1);
    m.set(1, 1, 1);
    expect(s(m)).toBe('[[1, 0], [0, 1]]');
  });
});

describe('sympy.tensor.array.sparse_ndim_array', () => {
  it('__setitem__', () => {
    const m = MutableSparseNDimArray.zeros(2, 2);
    m.set(0, 0, 1);
    m.set(1, 1, 1);
    expect(s(m)).toBe('[[1, 0], [0, 1]]');
  });

  it('__getitem__', () => {
    const [i, j] = symbols('i j');
    const m = MutableSparseNDimArray(range(4), [2, 2]);
    expect(s(m)).toBe('[[0, 1], [2, 3]]');
    expect(s(m.get(0, 0))).toBe('0');
    expect(s(m.get(1, 1))).toBe('3');
    expect(s(m.get(0))).toBe('[0, 1]');
    expect(s(m.get(1))).toBe('[2, 3]');
    expect(s(m.get(i, j))).toBe('[[0, 1], [2, 3]][i, j]');
    expect(s(m.get(i, j).subs(new Map([[i, 0], [j, 0]])))).toBe('0');
  });

  it('tomatrix', () => {
    const m = MutableSparseNDimArray(
      range(9).map(() => 1),
      [3, 3],
    );
    expect(s(m.tomatrix())).toBe('Matrix([[1, 1, 1], [1, 1, 1], [1, 1, 1]])');
  });
});

describe('sympy.tensor.array.arrayop', () => {
  it('Flatten', () => {
    const A = SArray(range(6)).reshape(2, 3);
    expect(s(new Flatten(A))).toBe('Flatten([[0, 1, 2], [3, 4, 5]])');
    expect([...new Flatten(A)].map(s)).toEqual(['0', '1', '2', '3', '4', '5']);
    expect([...new Flatten([[1, 2], [3, 4]])].map(s)).toEqual(['1', '2', '3', '4']);
    expect([...new Flatten(Matrix.of([[1, 2], [3, 4]]))].map(s)).toEqual(['1', '2', '3', '4']);
  });

  it('derive_by_array', () => {
    expect(s(deriveByArray(cos(mul(x, t)), x))).toBe('-t*sin(t*x)');
    expect(s(deriveByArray(cos(mul(x, t)), [x, y, z, t]))).toBe('[-t*sin(t*x), 0, 0, -x*sin(t*x)]');
    expect(
      s(
        deriveByArray(
          [x, mul(pow(y, 2), z)],
          [
            [x, y],
            [z, t],
          ],
        ),
      ),
    ).toBe('[[[1, 0], [0, 2*y*z]], [[0, y**2], [0, 0]]]');
  });

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

describe('sympy.tensor.array.array_comprehension', () => {
  const [i, j, k] = symbols('i j k');
  const f10ij = add(mul(10, i), j);

  it('ArrayComprehension', () => {
    const ac = ArrayComprehension(f10ij, [i, 1, 4], [j, 1, 3]);
    expect(s(ac)).toBe('ArrayComprehension(10*i + j, (i, 1, 4), (j, 1, 3))');
    expect(s(ac.doit())).toBe('[[11, 12, 13], [21, 22, 23], [31, 32, 33], [41, 42, 43]]');
    const bc = ArrayComprehension(f10ij, [i, 1, 4], [j, 1, k]);
    expect(s(bc.doit())).toBe('ArrayComprehension(10*i + j, (i, 1, 4), (j, 1, k))');
    expect(ac.length).toBe(12);
  });

  it('free_symbols, function, is_shape_numeric, limits, rank, shape', () => {
    const ac = ArrayComprehension(f10ij, [i, 1, 4], [j, 1, 3]);
    const bc = ArrayComprehension(f10ij, [i, 1, 4], [j, 1, add(k, 3)]);
    expect(ac.freeSymbols().size).toBe(0);
    expect([...bc.freeSymbols()].map(s)).toEqual(['k']);
    expect(s(ac.function)).toBe('10*i + j');
    expect(ac.isShapeNumeric).toBe(true);
    expect(bc.isShapeNumeric).toBe(false);
    expect(ac.limits.map((l) => `(${l.map(s).join(', ')})`)).toEqual(['(i, 1, 4)', '(j, 1, 3)']);
    expect(ac.rank()).toBe(2);
    expect(ac.shape.map(s)).toEqual(['4', '3']);
    expect(bc.shape.map(s)).toEqual(['4', 'k + 3']);
  });

  it('tolist, tomatrix, variables', () => {
    const ac = ArrayComprehension(f10ij, [i, 1, 4], [j, 1, 3]);
    expect(s(ac.tolist())).toBe(s([[11, 12, 13], [21, 22, 23], [31, 32, 33], [41, 42, 43]]));
    expect(s(ac.tomatrix())).toBe('Matrix([[11, 12, 13], [21, 22, 23], [31, 32, 33], [41, 42, 43]])');
    expect(ac.variables.map(s)).toEqual(['i', 'j']);
  });

  it('ArrayComprehensionMap', () => {
    expect(s(ArrayComprehensionMap(() => 1, [i, 1, 4]).doit())).toBe('[1, 1, 1, 1]');
    expect(s(ArrayComprehensionMap((n: number) => n + 1, [j, 1, 4]).doit())).toBe('[2, 3, 4, 5]');
  });
});

describe('sympy.tensor.indexed.Idx', () => {
  const [n, i, L, U] = symbols('n i L U', { integer: true });

  it('Idx', () => {
    const q = Idx('qwerty');
    expect(s(q)).toBe('qwerty');
    expect([(q as Idx).lower, (q as Idx).upper]).toEqual([NoMatch, NoMatch]);
    const iLU = Idx(i, [L, U]) as Idx;
    expect(s(iLU)).toBe('i');
    expect([s(iLU.lower), s(iLU.upper)]).toEqual(['L', 'U']);
    const iN = Idx(i, n) as Idx;
    expect([s(iN.lower), s(iN.upper)]).toEqual(['0', 'n - 1']);
    const i4 = Idx(i, 4) as Idx;
    expect([s(i4.lower), s(i4.upper)]).toEqual(['0', '3']);
    const iOo = Idx(i, oo) as Idx;
    expect([s(iOo.lower), s(iOo.upper)]).toEqual(['0', 'oo']);
  });

  it('label, lower, upper', () => {
    const xi = new Sym('x', { integer: true });
    expect(s((Idx(xi) as Idx).label)).toBe('x');
    const jj = new Sym('j', { integer: true });
    expect(s((Idx(jj) as Idx).label)).toBe('j');
    expect(s((Idx(add(jj, 1)) as Idx).label)).toBe('j + 1');
    expect(s((Idx('j', 2) as Idx).lower)).toBe('0');
    expect(s((Idx('j', 5) as Idx).lower)).toBe('0');
    expect((Idx('j') as Idx).lower).toBe(NoMatch);
    expect(s((Idx('j', 2) as Idx).upper)).toBe('1');
    expect(s((Idx('j', 5) as Idx).upper)).toBe('4');
    expect((Idx('j') as Idx).upper).toBe(NoMatch);
  });
});

// ---- behaviour beyond the doctests (expected values from SymPy 1.14) ----------------

describe('printing', () => {
  it('str of empty and rank-0 arrays', () => {
    expect(s(SArray([]))).toBe('ImmutableDenseNDimArray([], (0,))');
    expect(s(MutableDenseNDimArray([]))).toBe('MutableDenseNDimArray([], (0,))');
    expect(s(ImmutableSparseNDimArray([], [0]))).toBe('ImmutableSparseNDimArray([], (0,))');
    const e2 = SArray([[], []]);
    expect(s(e2)).toBe('ImmutableDenseNDimArray([], (2, 0))');
    expect(e2.shape).toEqual([2, 0]);
    const r0 = SArray(5);
    expect(s(r0)).toBe('5');
    expect(r0.shape).toEqual([]);
    expect(r0.rank()).toBe(0);
    expect(r0.length).toBe(1);
    expect([...r0].map(s)).toEqual(['5']);
    expect(s(MutableDenseNDimArray.zeros())).toBe('0');
    expect(s(SArray([[add(x, 1)]]))).toBe('[[x + 1]]');
  });

  it('latex', () => {
    expect(latex(SArray([[1, 2], [3, 4]]))).toBe('\\left[\\begin{matrix}1 & 2\\\\3 & 4\\end{matrix}\\right]');
    expect(SArray([1, 2, 3]).toLatex()).toBe('\\left[\\begin{matrix}1 & 2 & 3\\end{matrix}\\right]');
    expect(latex(SArray(range(8), [2, 2, 2]))).toBe(
      '\\left[\\begin{matrix}\\left[\\begin{matrix}0 & 1\\\\2 & 3\\end{matrix}\\right] & \\left[\\begin{matrix}4 & 5\\\\6 & 7\\end{matrix}\\right]\\end{matrix}\\right]',
    );
    expect(latex(SArray(range(4), [1, 1, 4]))).toBe('\\left[\\begin{matrix}\\left[\\left[\\begin{matrix}0 & 1 & 2 & 3\\end{matrix}\\right]\\right]\\end{matrix}\\right]');
    expect(latex(SArray(range(12), [1, 12]))).toBe(
      '\\left[\\left[\\begin{array}{c}0 & 1 & 2 & 3 & 4 & 5 & 6 & 7 & 8 & 9 & 10 & 11\\end{array}\\right]\\right]',
    );
    expect(latex(SArray(5))).toBe('5');
    expect(latex(SArray([[[1]]]))).toBe('\\left[\\begin{matrix}\\left[\\left[\\begin{matrix}1\\end{matrix}\\right]\\right]\\end{matrix}\\right]');
    expect(latex(SArray(range(16), [2, 2, 2, 2]))).toBe(
      '\\left[\\begin{matrix}\\left[\\begin{matrix}0 & 1\\\\2 & 3\\end{matrix}\\right] & \\left[\\begin{matrix}4 & 5\\\\6 & 7\\end{matrix}\\right]\\\\\\left[\\begin{matrix}8 & 9\\\\10 & 11\\end{matrix}\\right] & \\left[\\begin{matrix}12 & 13\\\\14 & 15\\end{matrix}\\right]\\end{matrix}\\right]',
    );
    expect(latex(MutableDenseNDimArray([1, 2]))).toBe('\\left[\\begin{matrix}1 & 2\\end{matrix}\\right]');
    expect(latex(ImmutableSparseNDimArray([1, 0]))).toBe('\\left[\\begin{matrix}1 & 0\\end{matrix}\\right]');
    expect(latex(SArray([[mul(pow(x, 2), S.Half)]]))).toBe('\\left[\\left[\\begin{matrix}\\frac{x^{2}}{2}\\end{matrix}\\right]\\right]');
    const [i, j] = symbols('i j');
    expect(latex(SArray([1, 2, 3, 4], [2, 2]).get(i, j))).toBe('{\\left[\\begin{matrix}1 & 2\\\\3 & 4\\end{matrix}\\right]}_{i,j}');
  });
});

describe('indexing', () => {
  const A = SArray([
    [1, 2],
    [3, 4],
  ]);
  const [i, j] = symbols('i j');

  it('negative indices and slices', () => {
    expect(s(SArray([1, 2, 3]).get(-1))).toBe('3');
    expect(s(A.get(-1, -1))).toBe('4');
    expect(s(A.get(-1, 0))).toBe('3');
    expect(s(A.get(0, -1))).toBe('2');
    expect(s(A.get(-1))).toBe('[3, 4]');
    expect(s(SArray(range(10)).get('::-1'))).toBe('[9, 8, 7, 6, 5, 4, 3, 2, 1, 0]');
    expect(s(SArray(range(12), [3, 4]).get('1:', '::2'))).toBe('[[4, 6], [8, 10]]');
    expect(s(SArray(range(12), [3, 4]).get(slice(1), slice(undefined, undefined, 2)))).toBe('[[4, 6], [8, 10]]');
    expect(s(A.get(0, ':'))).toBe('[1, 2]');
    expect(s(A.get(':', 0))).toBe('[1, 3]');
    expect(s(A.get('0:1', '0:1'))).toBe('[[1]]');
    expect(s(A.get('1:1'))).toBe('ImmutableDenseNDimArray([], (0, 2))');
    expect(s(A.get([0, 1]))).toBe('2');
    expect(s(A.get(1n, S.One))).toBe('4');
    // Python slice semantics (SymPy 1.14 drops the last element of 2:7:2)
    expect(s(SArray(range(10)).get('2:7:2'))).toBe('[2, 4, 6]');
  });

  it('index errors', () => {
    expect(() => A.get(0, 1, 1)).toThrow('Dimension of index greater than rank of array');
    expect(() => A.get(2, 0)).toThrow('Index (2, 0) out of border');
    expect(() => A.get(-3, 0)).toThrow('Index (-3, 0) out of border');
    expect(() => A.get(3)).toThrow(RangeError);
    expect(() => A.get(0.5, 0)).toThrow(TypeError);
    expect(() => A.get('a:b')).toThrow(TypeError);
    expect(() => A.get(i, 5)).toThrow('index out of range');
    expect(() => A.get(-1, i)).toThrow('index out of range');
    expect(() => SArray([]).get(0)).toThrow('Index not valid with an empty array');
  });

  it('symbolic indices', () => {
    const ij = A.get(i, j);
    expect(ij).toBeInstanceOf(Indexed);
    expect(s(ij.subs(i, 1))).toBe('[[1, 2], [3, 4]][1, j]');
    expect(() => ij.subs(new Map([[i, 1], [j, 5]]))).toThrow('out of border');
    expect(s(diff(ij, i))).toBe('[[0, 0], [0, 0]][i, j]');
    expect(s(diff(ij, ij))).toBe('1');
    expect(s(A.get(mul(-1, i), j))).toBe('[[1, 2], [3, 4]][-i, j]');
    expect(s(A.get(add(i, 2), j))).toBe('[[1, 2], [3, 4]][i + 2, j]');
    expect(s(A.get(i))).toBe('[[1, 2], [3, 4]][i]');
    expect(s(A.get(i).subs(i, 1))).toBe('[3, 4]');
    expect(s(A.get(1, i))).toBe('[[1, 2], [3, 4]][1, i]');
    const [ii] = symbols('i', { integer: true });
    expect(s(A.get(Idx(ii, 2), j))).toBe('[[1, 2], [3, 4]][i, j]');
    expect(s(A.get(Idx(ii, 3), j))).toBe('[[1, 2], [3, 4]][i, j]');
    expect(() => A.get(Idx(ii, [3, 5]), j)).toThrow('index out of range');
    const [p] = symbols('p', { positive: true });
    expect(() => A.get(mul(-1, p), j)).toThrow('index out of range');
    expect(() => A.get(i, ':')).toThrow(TypeError);
  });

  it('iteration', () => {
    expect([...A].map(s)).toEqual(['[1, 2]', '[3, 4]']);
    expect([...SArray([1, 2])].map(s)).toEqual(['1', '2']);
  });
});

describe('construction', () => {
  it('inputs', () => {
    expect(s(SArray(range(6), 3))).toBe('[0, 1, 2]');
    expect(s(SArray(range(6), [2, 3]))).toBe('[[0, 1, 2], [3, 4, 5]]');
    expect(s(SArray([SArray([1, 2]), SArray([3, 4])]))).toBe('[[1, 2], [3, 4]]');
    // a Matrix inside a list counts as its rows (SymPy 1.14 flattens it: [1])
    expect(s(SArray([Matrix.of([[1]])]))).toBe('[[[1]]]');
    expect(s(SArray(Matrix.of([[1, 2], [3, 4]])))).toBe('[[1, 2], [3, 4]]');
    expect(s(SArray(new Set([1, 2])))).toBe('[1, 2]');
    expect(s(new ImmutableDenseNDimArray([1, 2]))).toBe('[1, 2]');
    expect(NDimArray([1, 2])).toBeInstanceOf(ImmutableDenseNDimArray);
    expect(DenseNDimArray([1, 2])).toBeInstanceOf(ImmutableDenseNDimArray);
    expect(SparseNDimArray([1, 0])).toBeInstanceOf(ImmutableSparseNDimArray);
    expect(SArray([1, 2])).toBeInstanceOf(NDimArray);
    expect(SArray([1, 2])).toBeInstanceOf(DenseNDimArray);
    expect(SArray([1, 2]).isScalar).toBe(false);
    expect(s(ImmutableDenseNDimArray.zeros(2, 2))).toBe('[[0, 0], [0, 0]]');
    expect(s(ImmutableSparseNDimArray.zeros(2, 2))).toBe('[[0, 0], [0, 0]]');
  });

  it('errors', () => {
    expect(() => SArray([1, [2]])).toThrow('could not determine shape unambiguously');
    expect(() => SArray([[1, 2], [3]])).toThrow('could not determine shape unambiguously');
    expect(() => SArray([1, 2], [3])).toThrow(RangeError);
    expect(() => SArray(range(6), [2, x])).toThrow('Shape should contain integers only.');
    expect(() => SArray([1, 2], [])).toThrow('arrays without shape need one scalar value');
    expect(() => SArray([1], [0])).toThrow('if array shape is (0,) there cannot be elements');
    expect(() => SArray(new Map([[0, 1]]))).toThrow(TypeError);
    expect(() => ImmutableSparseNDimArray.zeros()).toThrow('arrays without shape need one scalar value');
  });

  it('sparse inputs', () => {
    expect(s(ImmutableSparseNDimArray(new Map([[[0, 1], 5]]), [2, 2]))).toBe('[[0, 5], [0, 0]]');
    expect(s(ImmutableSparseNDimArray(new Map([[1, 5]]), [2, 2]))).toBe('[[0, 5], [0, 0]]');
    expect([...MutableSparseNDimArray([0, 0, 3], [3]).sparseArray].map(([k, v]) => [k, s(v)])).toEqual([[2, '3']]);
    const sm = ImmutableSparseNDimArray(Matrix.of([[1, 0], [0, 4]]));
    expect(s(sm)).toBe('[[1, 0], [0, 4]]');
    expect(s(sm.tomatrix())).toBe('Matrix([[1, 0], [0, 4]])');
    expect(s(ImmutableSparseNDimArray([[1, 2], [3, 4]]).get(-1))).toBe('[3, 4]');
    expect(s(ImmutableSparseNDimArray([[0, 2], [3, 0]]).get(':', 0))).toBe('[0, 3]');
    expect(s(ImmutableSparseNDimArray([0, x]).applyfunc((v) => add(v, 1)))).toBe('[1, x + 1]');
    expect(s(ImmutableSparseNDimArray([0, x]).applyfunc((v) => mul(2, v)))).toBe('[0, 2*x]');
    expect(ImmutableSparseNDimArray([0, 1, 0, 2]).args.map(s)).toEqual(['1', '2']);
  });
});

describe('arithmetic and equality', () => {
  it('operations', () => {
    expect(s(SArray([1, x]).neg())).toBe('[-1, -x]');
    expect(s(SArray([2, x]).div(2))).toBe('[1, x/2]');
    expect(s(SArray([1, x]).mul(x))).toBe('[x, x**2]');
    const sp = ImmutableSparseNDimArray([0, 1]).rmul(x);
    expect(s(sp)).toBe('[0, x]');
    expect(sp).toBeInstanceOf(ImmutableSparseNDimArray);
    expect(s(ImmutableSparseNDimArray([0, 1]).mul(0))).toBe('[0, 0]');
    expect(s(ImmutableSparseNDimArray([1, 0]).div(0))).toBe('[zoo, nan]');
    expect(s(ImmutableSparseNDimArray([1, 0]).neg())).toBe('[-1, 0]');
    expect(SArray([1, 2]).add(MutableDenseNDimArray([1, 2]))).toBeInstanceOf(ImmutableDenseNDimArray);
    expect(MutableDenseNDimArray([1, 2]).add(SArray([1, 2]))).toBeInstanceOf(MutableDenseNDimArray);
    expect(() => SArray([x]).add(1)).toThrow(TypeError);
    expect(() => SArray([1, 2]).add(SArray([1, 2, 3]))).toThrow('array shape mismatch');
    expect(() => SArray([1, 2]).mul(SArray([1, 2]))).toThrow('scalar expected, use tensorproduct(...) for tensorial product');
    expect(() => SArray([1, 2]).div(SArray([1, 2]))).toThrow('scalar expected');
    expect(() => SArray([1, 2]).pow(2)).toThrow(TypeError);
  });

  it('equality', () => {
    expect(SArray([1, 2]).equals(SArray([1, 2]))).toBe(true);
    expect(SArray([1, 2]).equals(MutableDenseNDimArray([1, 2]))).toBe(true);
    expect(SArray([1, 0]).equals(ImmutableSparseNDimArray([1, 0]))).toBe(true);
    expect(ImmutableSparseNDimArray([[0, 1]]).equals(ImmutableSparseNDimArray([[0, 1]]))).toBe(true);
    expect(ImmutableSparseNDimArray([[0, 1]]).equals(ImmutableSparseNDimArray([[1, 0]]))).toBe(false);
    expect(SArray([1]).equals(1)).toBe(false);
    expect(SArray([1, 2]).key).toBe(SArray([1, 2]).key);
  });

  it('transpose, conjugate, adjoint', () => {
    const A = SArray([
      [1, 2],
      [3, 4],
    ]);
    expect(s(A.transpose())).toBe('[[1, 3], [2, 4]]');
    expect(s(transpose(A))).toBe('[[1, 3], [2, 4]]');
    expect(s(adjoint(A))).toBe('[[1, 3], [2, 4]]');
    expect(s(SArray([mul(I, x), 1]).conjugate())).toBe('[-I*conjugate(x), 1]');
    expect(s(conjugate(SArray([I])))).toBe('[-I]');
    expect(s(SArray([[I, x], [2, 3]]).adjoint())).toBe('[[-I, 2], [conjugate(x), 3]]');
    expect(() => SArray([1, 2]).transpose()).toThrow('array rank not 2');
    expect(MutableDenseNDimArray([[1, 2], [3, 4]]).transpose()).toBeInstanceOf(MutableDenseNDimArray);
  });

  it('subs, diff, simplify, free symbols', () => {
    expect(s(SArray([x, y]).subs(x, 2))).toBe('[2, y]');
    expect(s(SArray([x, y]).subs(new Map([[x, 1], [y, 2]])))).toBe('[1, 2]');
    expect(s(SArray([x, y]).diff(x, 2))).toBe('[0, 0]');
    expect(s(SArray([pow(x, 2), y]).diff(x, 2))).toBe('[2, 0]');
    expect(s(diff(SArray([pow(x, 2), y]), x))).toBe('[2*x, 0]');
    expect(s(SArray([pow(x, 2), y]).diff(SArray([x, y])))).toBe('[[2*x, 0], [0, 1]]');
    expect(s(SArray([sin(x)]).diff(x, x))).toBe('[-sin(x)]');
    expect(s(SArray([sin(x)]).diff(x, 3))).toBe('[-cos(x)]');
    expect(s(SArray([sin(mul(x, y))]).diff(x, y))).toBe('[-x*y*sin(x*y) + cos(x*y)]');
    expect(s(SArray([x]).diff(SArray([[x, y]])))).toBe('[[[1], [0]]]');
    expect(MutableDenseNDimArray([[1, 2], [3, 4]]).diff(x)).toBeInstanceOf(ImmutableDenseNDimArray);
    expect(ImmutableSparseNDimArray([0, x]).diff(x)).toBeInstanceOf(ImmutableSparseNDimArray);
    expect(s(simplify(SArray([add(pow(sin(x), 2), pow(cos(x), 2))])))).toBe('[1]');
    expect(s(SArray([add(pow(sin(x), 2), pow(cos(x), 2))]).simplify())).toBe('[1]');
    expect(s(SArray([mul(x, add(x, 1))]).expand())).toBe('[x**2 + x]');
    expect([...SArray([x, y]).freeSymbols()].map(s).sort()).toEqual(['x', 'y']);
    expect(SArray([x, y]).has(x)).toBe(true);
    expect(s(SArray([[x, 2], [3, 4]]).asMutable().subs(x, 1))).toBe('[[1, 2], [3, 4]]');
  });

  it('reshape, tomatrix, as_mutable, as_immutable', () => {
    expect(s(SArray([1, 2]).reshape(2, 1))).toBe('[[1], [2]]');
    expect(s(SArray([[1, 2], [3, 4]]).reshape(4))).toBe('[1, 2, 3, 4]');
    expect(() => SArray([1, 2]).reshape(3)).toThrow('Expecting reshape size to 2 but got prod((3,)) = 3');
    expect(() => SArray([1, 2]).tomatrix()).toThrow('Dimensions must be of size of 2');
    expect(s(SArray([[1, 2], [3, 4]]).tomatrix())).toBe('Matrix([[1, 2], [3, 4]])');
    const m = SArray([[1, 2], [3, 4]]).asMutable();
    expect(m).toBeInstanceOf(MutableDenseNDimArray);
    expect(s(m)).toBe('[[1, 2], [3, 4]]');
    expect(m.asImmutable()).toBeInstanceOf(ImmutableDenseNDimArray);
    expect(m.asMutable()).toBe(m);
    expect(MutableSparseNDimArray([[1, 2], [3, 4]]).asImmutable()).toBeInstanceOf(ImmutableSparseNDimArray);
    expect(MutableSparseNDimArray([[1, 2], [3, 4]]).reshape(4)).toBeInstanceOf(MutableSparseNDimArray);
    expect(MutableDenseNDimArray([[1, 2], [3, 4]]).applyfunc((v) => v)).toBeInstanceOf(MutableDenseNDimArray);
    expect(MutableDenseNDimArray([[1, 2], [3, 4]]).get(0, ':')).toBeInstanceOf(MutableDenseNDimArray);
    expect(MutableDenseNDimArray([[1, 2], [3, 4]]).neg()).toBeInstanceOf(MutableDenseNDimArray);
    expect(ImmutableSparseNDimArray([1, 0]).asMutable()).toBeInstanceOf(MutableSparseNDimArray);
  });
});

describe('mutable arrays', () => {
  const m22 = (): MutableDenseNDimArray =>
    MutableDenseNDimArray([
      [1, 2],
      [3, 4],
    ]);
  const s22 = (): MutableSparseNDimArray =>
    MutableSparseNDimArray([
      [1, 2],
      [3, 4],
    ]);

  it('dense item assignment', () => {
    let m = m22();
    m.set(0, ':', [9, 8]);
    expect(s(m)).toBe('[[9, 8], [3, 4]]');
    m = m22();
    m.set(':', 1, SArray([9, 8]));
    expect(s(m)).toBe('[[1, 9], [3, 8]]');
    m = m22();
    m.set(0, 5);
    expect(s(m)).toBe('[[5, 2], [3, 4]]');
    m = m22();
    m.set(3, x);
    expect(s(m)).toBe('[[1, 2], [3, x]]');
    m = m22();
    m.set(-1, -1, x);
    expect(s(m)).toBe('[[1, 2], [3, x]]');
    m = m22();
    m.set([1, 0], x);
    expect(s(m)).toBe('[[1, 2], [x, 4]]');
    const v = MutableDenseNDimArray([1, 2, 3, 4]);
    v.set('1:3', [7, 8]);
    expect(s(v)).toBe('[1, 7, 8, 4]');
    expect(() => m22().set(1, 1, [5])).toThrow(TypeError);
    expect(() => m22().set(x, 0, 1)).toThrow(TypeError);
    expect(() => m22().set(4, 1)).toThrow('Only a tuple index is accepted');
  });

  it('the key follows the contents', () => {
    const m = m22();
    const k1 = m.key;
    m.set(0, 0, 7);
    expect(m.key).not.toBe(k1);
    expect(m.equals(MutableDenseNDimArray([[7, 2], [3, 4]]))).toBe(true);
    expect(m.args.map(s)).toEqual(['7', '2', '3', '4']);
  });

  it('sparse item assignment', () => {
    let m = s22();
    m.set(0, ':', [0, 8]);
    expect(s(m)).toBe('[[0, 8], [3, 4]]');
    expect([...m.sparseArray.keys()]).toEqual([1, 2, 3]);
    m = s22();
    m.set(0, 0, 0);
    expect(s(m)).toBe('[[0, 2], [3, 4]]');
    expect([...m.sparseArray.keys()]).toEqual([1, 2, 3]);
    m = s22();
    m.set(3, x);
    expect(s(m)).toBe('[[1, 2], [3, x]]');
    const z2 = MutableSparseNDimArray.zeros(2, 2);
    const k1 = z2.key;
    z2.set(1, 0, x);
    expect(z2.key).not.toBe(k1);
    expect(z2.args.map(s)).toEqual(['x']);
    expect([...z2.freeSymbols()].map(s)).toEqual(['x']);
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

  it('derive_by_array', () => {
    expect(s(deriveByArray(x, x))).toBe('1');
    expect(s(deriveByArray(x, Matrix.of([[x], [y]])))).toBe('[[1], [0]]');
    expect(s(deriveByArray(Matrix.of([[mul(x, y)]]), [x, y]))).toBe('[[[y]], [[x]]]');
    const sp = deriveByArray(ImmutableSparseNDimArray([0, mul(x, y)]), [x, y]);
    expect(s(sp)).toBe('[[0, y], [0, x]]');
    expect(sp).toBeInstanceOf(ImmutableSparseNDimArray);
    const md = deriveByArray(MutableDenseNDimArray([0, mul(x, y)]), [x, y]);
    expect(s(md)).toBe('[[0, y], [0, x]]');
    expect(md).toBeInstanceOf(ImmutableDenseNDimArray);
    const l = deriveByArray([mul(x, y)], x);
    expect(s(l)).toBe('[y]');
    expect(l).toBeInstanceOf(ImmutableDenseNDimArray);
    expect(s(deriveByArray(SArray([x, y]), SArray([x, y])))).toBe('[[1, 0], [0, 1]]');
    expect(() => deriveByArray(mul(x, y), [add(x, 1)])).toThrow('cannot derive by this array');
  });

  it('kinds', () => {
    // SymPy gives UndefinedKind for sparse arrays (they do not define kind); symjs gives ArrayKind
    expect(s(kindOf(ImmutableSparseNDimArray([1, 0, 0], [3])))).toBe('ArrayKind(NumberKind)');
    expect(s(kindOf(SArray([[1, 0]])))).toBe('ArrayKind(NumberKind)');
    expect(kindOf(ArrayComprehension(x, [x, 1, 2]))).toBe(UndefinedKind);
  });
});

describe('array comprehensions: more cases', () => {
  const [i, j] = symbols('i j');
  it('evaluation and shape', () => {
    expect(s(ArrayComprehension(i, [i, 1, 4]).doit())).toBe('[1, 2, 3, 4]');
    const sym = ArrayComprehension(i, [i, 1, y]);
    expect(sym.doit()).toBe(sym);
    expect(sym.shape.map(s)).toEqual(['y']);
    expect(sym.rank()).toBe(1);
    expect(() => sym.length).toThrow('Symbolic length is not supported');
    expect(() => sym.tolist()).toThrow('A symbolic array cannot be expanded to a list');
    expect(() => sym.tomatrix()).toThrow('A symbolic array cannot be expanded to a matrix');
    expect(() => ArrayComprehension(i, [i, 1, 4]).tomatrix()).toThrow('Dimensions must be of size of 2');
    expect(s(ArrayComprehension(i, [i, 1, 2], [j, 1, 2]).doit())).toBe('[[1, 1], [2, 2]]');
    const yy = ArrayComprehension(i, [i, y, add(y, 2)]);
    expect(yy.shape.map(s)).toEqual(['3']);
    expect(yy.isShapeNumeric).toBe(false);
    expect(s(yy.doit())).toBe('ArrayComprehension(i, (i, y, y + 2))');
    expect(s(ArrayComprehension(mul(i, j), [i, 1, 2], [j, 2, 4]).doit())).toBe('[[2, 3, 4], [4, 6, 8]]');
    expect(s(ArrayComprehension(i, [i, -2, 2]).doit())).toBe('[-2, -1, 0, 1, 2]');
    expect(s(ArrayComprehension(i, [j, 1, 4]).doit())).toBe('[i, i, i, i]');
    expect(s(ArrayComprehension(i, [i, 1, 1]).doit())).toBe('[1]');
    expect(s(ArrayComprehension(mul(i, x), [i, 1, 4]).doitSelf())).toBe('[x, 2*x, 3*x, 4*x]');
  });

  it('substitution and free symbols', () => {
    expect(s(ArrayComprehension(i, [i, 1, 4]).subs(x, 2))).toBe('ArrayComprehension(i, (i, 1, 4))');
    expect(s(ArrayComprehension(mul(i, x), [i, 1, 4]).subs(x, 2))).toBe('ArrayComprehension(2*i, (i, 1, 4))');
    const r = ArrayComprehension(mul(i, x), [i, 1, y]).subs(y, 2);
    expect(s(r)).toBe('ArrayComprehension(i*x, (i, 1, 2))');
    expect(s((r as ArrayComprehension).doit())).toBe('[x, 2*x]');
    expect([...ArrayComprehension(mul(i, x), [i, 1, 4]).freeSymbols()].map(s)).toEqual(['x']);
    // the index variable is bound: substituting it changes nothing (SymPy substitutes it)
    expect(s(ArrayComprehension(i, [i, 1, 4]).subs(i, 2))).toBe('ArrayComprehension(i, (i, 1, 4))');
    expect(ArrayComprehension(i, [i, 1, 4]).equals(ArrayComprehension(i, [i, 1, 4]))).toBe(true);
  });

  it('errors', () => {
    expect(() => ArrayComprehension(i, [i, 3, 1])).toThrow('Lower bound should be inferior to upper bound');
    expect(() => ArrayComprehension(i, [i, 1, i])).toThrow('Variable should not be part of its bounds');
    expect(() => ArrayComprehension(i, [i, 1, add(x, 0.5)])).toThrow('Bounds should be an Expression(combination of Integer and Symbol)');
    expect(() => ArrayComprehension(i, [i, 1, [1, 2]] as never)).toThrow('Bounds should be an Expression(combination of Integer and Symbol)');
    expect(() => ArrayComprehension(i, [i, 1] as never)).toThrow('ArrayComprehension requires values lower and upper bound for the expression');
  });

  it('printing', () => {
    expect(latex(ArrayComprehension(add(mul(10, i), j), [i, 1, 4], [j, 1, 3]))).toBe(
      '\\operatorname{ArrayComprehension}\\left(10 i + j, \\left( i, \\  1, \\  4\\right), \\left( j, \\  1, \\  3\\right)\\right)',
    );
    expect(latex(ArrayComprehension(i, [i, 1, 4]))).toBe('\\operatorname{ArrayComprehension}\\left(i, \\left( i, \\  1, \\  4\\right)\\right)');
  });

  it('ArrayComprehensionMap', () => {
    const one = ArrayComprehensionMap(() => 1, [i, 1, 4]);
    expect(s(one)).toBe('ArrayComprehensionMap((i, 1, 4))');
    expect(latex(one)).toBe('\\operatorname{ArrayComprehensionMap}\\left(\\left( i, \\  1, \\  4\\right)\\right)');
    expect(one).toBeInstanceOf(ArrayComprehension);
    expect(s(ArrayComprehensionMap((n: number) => n + 1, [j, 1, 4], [i, 1, 2]).doit())).toBe('[[2, 3], [3, 5], [4, 7], [5, 9]]');
    expect(s(ArrayComprehensionMap((n: number) => n + 1, [j, 1, y]).doit())).toBe('ArrayComprehensionMap((j, 1, y))');
    const sub = ArrayComprehensionMap((n: number) => n * 2, [j, 1, y]).subs(y, 3);
    expect(s((sub as ArrayComprehension).doit())).toBe('[2, 4, 6]');
    expect(() => ArrayComprehensionMap(((p: number, q: number) => p + q) as never, [j, 1, 4])).toThrow(TypeError);
    expect(() => ArrayComprehensionMap(1 as never, [j, 1, 4])).toThrow('Data type not supported');
    expect(() => one.function).toThrow(TypeError);
    expect(one.lambda.length).toBe(0);
    expect(one.equals(ArrayComprehensionMap(() => 2, [i, 1, 4]))).toBe(false);
  });
});

describe('Idx: more cases', () => {
  const [i, n] = symbols('i n', { integer: true });
  it('construction', () => {
    expect(s(Idx(3))).toBe('3');
    expect(Idx(3).equals(Idx(3n))).toBe(true);
    expect(() => Idx(x)).toThrow('Idx object requires an integer label.');
    expect(() => Idx(i, 2.5)).toThrow('Idx object requires an integer dimension.');
    expect(() => Idx(i, [1, 2, 3])).toThrow('Idx range tuple must have length 2, but got 3');
    expect(() => Idx(i, [1.5, 2])).toThrow('Idx object requires integer bounds.');
    expect(s((Idx(i, [mul(-1, oo), oo]) as Idx).lower)).toBe('-oo');
    expect(s((Idx(i, [n, oo]) as Idx).upper)).toBe('oo');
    expect(s(Idx(i, x))).toBe('i');
    expect(() => new Idx(3 as never)).toThrow(TypeError);
  });

  it('a symbol with a range', () => {
    const i4 = Idx(i, 4) as Idx;
    expect(i4).toBeInstanceOf(Idx);
    expect(i4).toBeInstanceOf(Sym);
    expect(i4.name).toBe('i');
    expect([...i4.freeSymbols()]).toEqual([i4]);
    expect(isIntegerQ(i4)).toBe(true);
    expect(s(diff(i4, i4))).toBe('1');
    expect(s(mul(2, i4))).toBe('2*i');
    expect(i4.equals(i)).toBe(false);
    expect(i4.equals(Idx(i, 4))).toBe(true);
    expect(i4.equals(Idx(i, 5))).toBe(false);
  });

  it('latex', () => {
    expect((Idx(i, 4) as Idx).toLatex()).toBe('{i}_{0\\mathrel{..}\\nobreak 3}');
    expect((Idx(i, [1, y]) as Idx).toLatex()).toBe('{i}_{1\\mathrel{..}\\nobreak y}');
    expect((Idx(i) as Idx).toLatex()).toBe('i');
    expect((Idx(i, oo) as Idx).toLatex()).toBe('{i}_{0\\mathrel{..}\\nobreak \\infty}');
  });
});

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/tensor/ndimarray.ts.
// N-dimensional arrays (dense and sparse, mutable and immutable). Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import type { Expr } from '../../src';
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
  pow,
  simplify,
  sin,
  symbols,
  transpose,
  Indexed,
  pi,
  sympify,
} from '../../src';
import {
  SymArray as SArray,
  ArrayComprehension,
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
  slice,
  tensorcontraction,
  ImmutableDenseNDimArray as IDA,
  ImmutableSparseNDimArray as ISA,
  MutableDenseNDimArray as MDA,
  MutableSparseNDimArray as MSA,
  SymArray,
} from '../../src/tensor';

// SymPy sympy.tensor.array (every doctest of its modules that implement
// sympy.tensor.array.__all__) and sympy.tensor.indexed.Idx; expected
// values from SymPy 1.14.

const [x, y, z, t] = symbols('x y z t');
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

// Edge cases of sympy.tensor.array (slicing, construction, assignment,
// sparse arrays, derivatives), ArrayComprehension and Idx; expected values
// from SymPy 1.14.

const [i, j] = symbols('i j');
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

describe('SymPy Basic methods of arrays', async () => {
  const sj = await import('../../src');
  const [x, y] = sj.symbols('x y') as [Sym, Sym];
  const b = sj.ImmutableDenseNDimArray([x, sj.add(sj.mul(2, x), 1)]);
  it('delegates to the expression functions', () => {
    expect(b.atoms().map(String).sort()).toEqual(['1', '2', 'x']);
    expect([b.count(x), b.countOps(), b.compare(b), b.compare(sj.ImmutableDenseNDimArray([y])), b.couldExtractMinusSign(), b.hasFree(x), b.hasXfree([x]), b.isSame(b), b.dummyEq(b)]).toEqual([2, 2, 0, 1, false, true, true, true, true]);
    expect([String(b.xreplace(new Map([[x, y]]))), String(b.copy()), String(b.find(x)), String(b.asDummy()), String(b.replace(x, y))]).toEqual(['[y, 2*y + 1]', '[x, 2*x + 1]', 'x', '[x, 2*x + 1]', '[y, 2*y + 1]']);
    expect(b.copy()).not.toBe(b);
    expect(b.asContentPrimitive().map(String)).toEqual(['1', '[x, 2*x + 1]']);
    expect([b.classKey(), String(b.sortKey()).startsWith('5,0,ImmutableDenseNDimArray')]).toEqual([[5, 0, 'ImmutableDenseNDimArray'], true]);
    expect(String(sj.ImmutableDenseNDimArray.fromiter([[1, 2, 3, 4], [2, 2]]))).toBe('[[1, 2], [3, 4]]');
    expect(String(sj.ImmutableDenseNDimArray([sj.abs(x)]).refine(sj.Q.positive(x)))).toBe('[x]');
    const w = new sj.Wild('w');
    const pattern = sj.ImmutableDenseNDimArray([w, sj.add(sj.mul(2, w), 1)]);
    const entries = (m: unknown): string[] => [...(m as Map<Expr, Expr>)].map(([k, v]) => `${k.toString()}: ${v.toString()}`);
    expect([entries(b.match(pattern)), entries(pattern.matches(b))]).toEqual([['w_: x'], ['w_: x']]);
    expect(b.match(sj.ImmutableDenseNDimArray([y]))).toBe(sj.NoMatch);
    // an array is not a hypergeometric term (SymPy raises ValueError: scalar expected, dividing two arrays)
    expect(b.isHypergeometric(x)).toBe(false);
  });
  it('evaluates and calls the elements', () => {
    const a = sj.ImmutableDenseNDimArray([x, 1, new sj.Integral([x, x]), sj.Lambda(y, sj.mul(2, y))]);
    expect(String(a.doit())).toBe('[x, 1, x**2/2, Lambda(y, 2*y)]');
    expect(String(a.rcall(3))).toBe('[x, 1, Integral(x, x), 6]');
    expect(String(sj.ImmutableDenseNDimArray([sj.add(x, sj.Lambda(y, y))]).rcall(3))).toBe('[x + 3]');
  });
});

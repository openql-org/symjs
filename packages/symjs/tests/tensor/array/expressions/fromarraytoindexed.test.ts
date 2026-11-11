// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { ArraySymbol, ArrayTensorProduct as TP, ArrayContraction as AC, ArrayDiagonal as AD, ArrayAdd, ArrayElementwiseApplyFunc, PermuteDims, Reshape, OneArray, ZeroArray, SymArray, Matrix, MatrixSymbol, IndexedBase, Sym, S, Sum, add, mul, sin, str, convertArrayToIndexed as convert, convertIndexedToArray, doit, floor, Mod, dummyEq } from '../../../../src';
const i = new Sym('i'), j = new Sym('j'), k = new Sym('k'), A = new ArraySymbol('A', [3, 3, 3]), B = new ArraySymbol('B', [3, 3]);
it('converts entries, products, diagonals, permutations and sums', () => {
  expect(convert(A, [i, j, k]).key).toBe(A.at(i, j, k).key);
  const product = new TP(S.Two, A, B), index = [i, j, k, 0, 1];
  // Scalar coefficients multiply entries directly; SymPy's 2[] is not a scalar.
  expect(convert(product, index).key).toBe(mul(2, A.at(i, j, k), B.at(0, 1)).key);
  expect(convert(new AD(A, [0, 2]), [i, j]).key).toBe(A.at(j, i, j).key);
  expect(convert(new AD(A), [i, j, k]).key).toBe(A.at(i, j, k).key);
  expect(convert(new PermuteDims(A, [1, 2, 0]), [i, j, k]).key).toBe(A.at(k, i, j).key);
  const sum = new ArrayAdd(B, new PermuteDims(B, [1, 0]));
  expect(convert(sum, [i, j]).key).toBe(add(B.at(i, j), B.at(j, i)).key);
  expect(convertIndexedToArray(convert(product, [i, j, k, new Sym('l'), new Sym('m')])).key).toBe(product.key);
  expect(convert(new ArrayElementwiseApplyFunc(sin, A), [i, j, k]).key).toBe(sin(A.at(i, j, k)).key);
  expect(convert(new ZeroArray(3, 3), [i, j])).toBe(S.Zero);
  expect(convert(new OneArray(3, 3), [i, j])).toBe(S.One);
});
it('allocates independent summation dummies without capturing free indices', () => {
  const free = new Sym('d0'), expr = new AC(new TP(new AC(A, [0, 2]), B), [1, 2]);
  const result = convert(expr, [free]);
  expect(str(result)).toBe('Sum(B[_d0, _d0]*Sum(A[_d1, d0, _d1], (_d1, 0, 2)), (_d0, 0, 2))');
  expect(result.freeSymbols().has(free)).toBe(true);
  expect(convert(new AC(A), [i, j, k]).key).toBe(A.at(i, j, k).key);
  expect(dummyEq(convert(new AC(B, [0], [1]), []), Sum(B.at(i, j), [i, 0, 2], [j, 0, 2]))).toBe(true);
});
it('converts explicit arrays, matrices, scalar and symbolic matrix entries', () => {
  const array = SymArray([[1, 2], [3, 4]]), matrix = Matrix.of([[1, 2], [3, 4]]), M = MatrixSymbol('M', 2, 2);
  expect(str(convert(array, [1, 0]))).toBe('3');
  expect(str(convert(matrix, [1, 0]))).toBe('3');
  expect(convert(M, [i, j]).key).toBe(M.at(i, j).key);
  expect(convert(i, [])).toBe(i);
  expect(convert(2, []).key).toBe(S.Two.key);
  expect(str(convert(new IndexedBase('V', { shape: [3] }), [i]))).toBe('V[i]');
  expect(() => convert(new IndexedBase('V', { shape: [3] }), [3])).toThrow(RangeError);
  expect(str(convert(new IndexedBase('V'), [i]))).toBe('V[i]');
  expect(str(convert(new Sym('V'), [i]))).toBe('V[i]');
  expect(str(convert(new ArraySymbol('a', []), []))).toBe('a[]');
  expect(str(convert(SymArray(2, []), []))).toBe('2');
  expect(() => convert(new ArraySymbol('a', []), [i])).toThrow(RangeError);
  expect(() => convert(A, [i])).toThrow(RangeError);
  expect(() => convert(M, [i])).toThrow(RangeError);
});
it('maps row-major reshape coordinates with floor and remainder', () => {
  expect(convert(new Reshape(A, [27]), [i]).key).toBe(A.at(floor(i.div(9)), Mod(floor(i.div(3)), 3), Mod(i, 3)).key);
  const X = new ArraySymbol('X', [30]);
  expect(convert(new Reshape(X, [2, 3, 5]), [i, j, k]).key).toBe(X.at(add(mul(15, i), mul(5, j), k)).key);
  const data = SymArray(Array.from({ length: 30 }, (_, n) => n), [2, 3, 5]);
  for (let n = 0; n < 30; n++) expect(str(convert(new Reshape(data, [30]), [n]))).toBe(String(n));
  expect(str(doit(convert(new AC(data, [0]), [1, 2])))).toBe('29');
});

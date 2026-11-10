// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { ArraySymbol, ArrayTensorProduct as TP, ArrayContraction as C, ArrayAdd, PermuteDims as P, MatrixSymbol, Rational, SymArray, str, expand, sub, convertArrayToMatrix, convertMatrixToArray } from '../../../../src/index';
import { at, cast } from '../../../../src/core/guard';
import { explicitArray } from '../../../../src/tensor/array/expressions/arrayexpressions';
const M = MatrixSymbol('M', 2, 2), N = MatrixSymbol('N', 2, 2), A = new ArraySymbol('A', [2, 2]);
it('recognizes both orientations and closed cycles of matrix chains', () => {
  for (const [axes, answer] of [ [[1, 2], 'M*N'], [[0, 2], 'M.T*N'], [[1, 3], 'M*N.T'], [[0, 3], 'M.T*N.T'] ] as const) {
    const expr = new C(new TP(M, N), axes), matrix = convertArrayToMatrix(expr);
    expect(str(matrix)).toBe(answer); // SymPy 1.14.0
    expect(str(explicitArray(convertMatrixToArray(matrix)))).toBe(str(expr.asExplicit()));
  }
  expect(str(convertArrayToMatrix(new P(new C(new TP(M, N), [1, 2]), [1, 0])))).toBe('N.T*M.T');
  expect(str(convertArrayToMatrix(new C(new TP(M, N), [0, 3], [1, 2])))).toBe('Trace(M*N)');
  expect(str(convertArrayToMatrix(new C(new TP(M, N), [0, 1], [2, 3])))).toBe('Trace(M)*Trace(N)');
  expect(str(convertArrayToMatrix(new C(M, [0, 1])))).toBe('Trace(M)');
});
it('preserves the ordering of independent matrix chains', () => {
  const X = MatrixSymbol('X', 2, 2), Y = MatrixSymbol('Y', 2, 2);
  for (const axes of [[[1, 2], [5, 6]], [[1, 4], [3, 6]]]) {
    const expr = new C(new TP(M, N, X, Y), ...axes), converted = convertArrayToMatrix(expr);
    const a = cast(explicitArray(convertMatrixToArray(converted)), SymArray), b = cast(expr.asExplicit(), SymArray);
    expect(a.shape).toEqual(b.shape);
    a.flatElements().forEach((value, i) => {
        const residual = expand(sub(value, at(b.flatElements(), i)));
        expect(str(residual)).toBe('0');
      });
  }
  expect(str(convertArrayToMatrix(new C(new TP(Rational.of(2), M, N), [1, 2])))).toBe('2*M*N');
  expect(str(convertArrayToMatrix(new C(new TP(M, N), [0, 1])))).toBe('Trace(M)*N');
  expect(str(convertArrayToMatrix(new C(new TP(Rational.of(2), M, N, X, Y), [1, 2], [5, 6])))).toBe('ArrayTensorProduct(2*M*N, X*Y)'); // SymPy 1.14.0
  const scalarProduct = convertArrayToMatrix(new TP(Rational.of(2), Rational.of(3)));
  expect(str(scalarProduct)).toBe('6');
});
it('retains array expressions when they are not matrix chains', () => {
  const diagonal = new C(new TP(M, N), [0, 1, 2]);
  expect(str(convertArrayToMatrix(diagonal))).toBe(str(diagonal.doit()));
  const array = new C(A, [0, 1]);
  expect(convertArrayToMatrix(array)).toBe(array);
  expect(() => convertArrayToMatrix(new ArrayAdd(A, A))).toThrow(TypeError);
  expect(convertArrayToMatrix(new C(M))).toBe(M);
  expect(convertArrayToMatrix(new P(M, [0, 1]))).toBe(M);
  expect(str(convertArrayToMatrix(new P(A, [1, 0])))).toBe('PermuteDims(A, (0 1))');
  expect(str(convertArrayToMatrix(new TP(M, N)))).toBe('ArrayTensorProduct(M, N)');
  const scalarSum = new ArrayAdd(new C(A, [0, 1]), new C(A, [0, 1]));
  expect(str(convertArrayToMatrix(scalarSum))).toBe(str(scalarSum));
});

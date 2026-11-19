// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { passingModuleCases, runTestCase } from '../../../../../../tools/sympy-corpus/tests-harness';
import { readFileSync } from 'node:fs';
import { expect, it } from 'vitest';
import { type Expr, ArraySymbol, ArrayTensorProduct as TP, ArrayContraction as C, ArrayAdd, ArrayDiagonal, ArrayElementwiseApplyFunc, sin, mul, pow, add, PermuteDims as P, MatrixSymbol, Rational, SymArray, str, expand, sub, convertArrayToMatrix, convertMatrixToArray } from '../../../../src/index';
import { at, cast } from '../../../../src/core/guard';
import { explicitArray } from '../../../../src/tensor/array/expressions/arrayexpressions';
const refs: Record<string, string> = JSON.parse(readFileSync(new URL('./references.json', import.meta.url), 'utf8'));
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

it('recognizes transposed Hadamard factors and preserves nonmatrix elementwise arrays', () => {
  expect(str(convertArrayToMatrix(new ArrayDiagonal(new TP(M, N), [0, 3], [1, 2])))).toBe('HadamardProduct(M, N.T)');
  const separate = new ArrayDiagonal(new TP(M, N), [0, 1], [2, 3]);
  expect(convertArrayToMatrix(separate)).toBe(separate);
  const elementwise = new ArrayElementwiseApplyFunc(sin, A);
  expect(str(convertArrayToMatrix(elementwise))).toBe(str(elementwise));
});

it('recognizes elementwise powers with scalar coefficients', () => {
  expect(str(convertArrayToMatrix(new ArrayElementwiseApplyFunc((x) => pow(x, 3), M)))).toBe(refs['elementwise_power_back']);
  expect(str(convertArrayToMatrix(new ArrayElementwiseApplyFunc((x) => mul(2, pow(x, 3)), M)))).toBe(refs['elementwise_scaled_power_back']);
  expect(str(convertArrayToMatrix(new ArrayElementwiseApplyFunc((x) => x, M)))).toBe(refs['elementwise_identity_back']);
  expect(str(convertArrayToMatrix(new ArrayElementwiseApplyFunc(() => Rational.of(3), M)))).toBe(refs['elementwise_constant_back']);
  const row = MatrixSymbol('R', 1, 2), single = MatrixSymbol('X', 1, 1);
  expect(str(convertArrayToMatrix(new ArrayElementwiseApplyFunc((x) => pow(x, 3), row)))).toBe('HadamardPower(R, 3)');
  expect(str(convertArrayToMatrix(new ArrayElementwiseApplyFunc((x) => pow(x, 3), single)))).toBe('X**3');
  for (const func of [(x: Expr) => pow(x, x), (x: Expr) => pow(sin(x), 2), (x: Expr) => add(x, pow(x, 2)), (x: Expr) => mul(x, sin(x))]) {
    expect(str(convertArrayToMatrix(new ArrayElementwiseApplyFunc(func, M)))).toContain('Lambda');
  }
});

it('converts local transposes, matrix elements and shaped zeros', async () => {
  const { ArrayElement, ZeroArray } = await import('../../../../src');
  expect(str(convertArrayToMatrix(new ZeroArray(2, 2)))).toBe('0');
  const vectorZero = new ZeroArray(2);
  expect(convertArrayToMatrix(vectorZero)).toBe(vectorZero);
  expect(str(convertArrayToMatrix(new P(new TP(M, N), [0, 1, 3, 2])))).toBe('ArrayTensorProduct(M, N.T)');
  expect(str(convertArrayToMatrix(new P(new TP(M, N), [3, 2, 1, 0])))).toBe('ArrayTensorProduct(N.T, M.T)');
  const mixed = new P(new TP(M, A), [0, 2, 1, 3]);
  expect(str(convertArrayToMatrix(mixed))).toBe(str(mixed));
  expect(str(convertArrayToMatrix(new ArrayElement(new C(new TP(M, N), [1, 3]), [0, 1])))).toBe('(M*N.T)[0, 1]');
  expect(str(convertArrayToMatrix(A.at(0, 1)))).toBe('A[0, 1]');
});

it('replays the upstream test_convert_array_to_matrix assertions', () => {
  for (const c of passingModuleCases('tensor', 'sympy.tensor.array.expressions.tests.test_convert_array_to_matrix')) {
    expect(['pass', 'equivalent'], c.src).toContain(runTestCase(c).status);
  }
});
it('replays the upstream test_convert_indexed_to_array assertions', () => {
  for (const c of passingModuleCases('tensor', 'sympy.tensor.array.expressions.tests.test_convert_indexed_to_array')) {
    expect(['pass', 'equivalent'], c.src).toContain(runTestCase(c).status);
  }
});

it('preserves matrix orientation when combining row vectors and scalars', () => {
  const row = MatrixSymbol('R', 1, 2), single = MatrixSymbol('X', 1, 1);
  expect(str(convertArrayToMatrix(new TP(row, single)))).toBe('X*R');
  expect(str(convertArrayToMatrix(new TP(row, row)))).toBe('R.T*R');
  expect(str(convertArrayToMatrix(new C(M, [1])))).toBe('M*1');
  expect(str(convertArrayToMatrix(new C(M, [0])))).toBe('1*M');
});

it('eliminates traced identity factors with a shared summation index', async () => {
  const { Identity, identifyRemovableIdentityMatrices } = await import('../../../../src');
  const trace = new C(M, [0, 1]);
  expect(identifyRemovableIdentityMatrices(trace)).toBe(trace);
  expect(str(convertArrayToMatrix(new C(new TP(M, N, Identity(2)), [1, 2, 4, 5])))).toBe('M*N');
  expect(str(convertArrayToMatrix(new C(new TP(M, N, M, N), [1, 3], [0, 4, 6])))).toBe('ArrayContraction(ArrayTensorProduct(M*N.T, M, N), (0, 2, 4))');
});

it('tracks retained diagonal axes across singleton removal and permutations', async () => {
  const { Identity } = await import('../../../../src');
  const row = MatrixSymbol('R', 1, 2), col = MatrixSymbol('a', 2, 1);
  const trivial = Identity(1);
  const retained = new ArrayDiagonal(new TP(trivial, M, N), [2, 4]);
  expect(str(convertArrayToMatrix(retained))).toBe('ArrayDiagonal(ArrayTensorProduct(M, N), (0, 2))');
  const permuted = new ArrayDiagonal(new TP(trivial, row, M), [0, 2]);
  expect(str(convertArrayToMatrix(permuted))).toBe('PermuteDims(ArrayTensorProduct(R.T, M), (1 2 3))');
  const shared = new ArrayDiagonal(new TP(col, M, N), [0, 2, 4]);
  expect(convertArrayToMatrix(shared)).toBe(shared);
});

it('retains unrecognized factors and distributes contraction over tensor sums', async () => {
  const { Identity, OneArray, identifyRemovableIdentityMatrices } = await import('../../../../src');
  const identity = Identity(2);
  expect(str(identifyRemovableIdentityMatrices(new C(new TP(identity, new OneArray(2)), [1])))).toBe('ArrayTensorProduct(OneArray(2), OneArray(2))');
  expect(str(identifyRemovableIdentityMatrices(new C(new TP(identity, M), [0])))).toBe('ArrayTensorProduct(OneArray(2), M)');
  expect(str(identifyRemovableIdentityMatrices(new C(new TP(identity, M), [0, 2])))).toBe('ArrayContraction(ArrayTensorProduct(I, M), (0, 2))');
  expect(str(convertArrayToMatrix(new C(new TP(identity, M, N, A), [1, 3], [0, 4, 6])))).toBe('ArrayContraction(ArrayTensorProduct(M, N, A), (1, 2, 4))');
  expect(str(convertArrayToMatrix(new C(new TP(M, A, N), [0, 2], [1, 4, 5])))).toBe('ArrayContraction(ArrayTensorProduct(M, N, A), (0, 4), (1, 2, 3))');
  const pairs = new ArrayAdd(new TP(M, N), new TP(N, M));
  expect(str(convertArrayToMatrix(new C(new TP(pairs, M), [1, 4], [2, 5])))).toBe('M**2*N + N*M**2');
});

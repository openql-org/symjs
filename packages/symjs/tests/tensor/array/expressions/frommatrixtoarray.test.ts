// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { cast } from '../../../../src/core/guard';
import { MatrixExpr } from '../../../../src';
import { readFileSync } from 'node:fs';
import { expect, it } from 'vitest';
import { MatrixSymbol, Trace, Transpose, MatMul, MatAdd, MatPow, HadamardProduct, HadamardPower, ElementwiseApplyFunction, sin, S, mul, convertMatrixToArray, convertArrayToMatrix, str } from '../../../../src/index';
const refs: Record<string, string> = JSON.parse(readFileSync(new URL('./references.json', import.meta.url), 'utf8'));
const M = MatrixSymbol('M', 2, 2), N = MatrixSymbol('N', 2, 2);
const cases = {
  matrix_product: MatMul(M, N), matrix_trace: Trace(MatMul(M, N)), matrix_transpose: Transpose(M), matrix_sum: MatAdd(M, N),
  matrix_power: MatPow(M, 3), matrix_scaled: MatMul(3, M, N), matrix_long: MatMul(M, N, M, N),
};
for (const [name, expr] of Object.entries(cases)) it(name, () => {
  const result = convertMatrixToArray(expr);
  expect(str(result)).toBe(refs[name]);
  expect(str(convertArrayToMatrix(result))).toBe(refs[`${name}_back`]);
});
it('keeps unsupported inverse powers and handles scalar or single-matrix inputs', () => {
  expect(convertMatrixToArray(S.One)).toBe(S.One);
  expect(convertMatrixToArray(M)).toBe(M);
  const inverse = MatPow(M, -1), zero = MatPow(M, 0), large = MatPow(M, 101);
  expect(convertMatrixToArray(inverse)).toBe(inverse);
  expect(convertMatrixToArray(zero)).toBe(zero);
  expect(str(convertArrayToMatrix(convertMatrixToArray(large)))).toBe('M**101');
  expect(str(convertMatrixToArray(MatMul(3, M)))).toBe('ArrayTensorProduct(3, M)'); // SymPy 1.14.0
  expect(str(convertArrayToMatrix(convertMatrixToArray(mul(2, M))))).toBe('2*M');
});

it('converts Hadamard and nonlinear elementwise operations', () => {
  for (const expr of [HadamardProduct(M, N), HadamardProduct(M), HadamardPower(M, 3), ElementwiseApplyFunction(sin, M)]) {
    const arr = convertMatrixToArray(expr);
    const back = convertArrayToMatrix(arr);
    expect(String(cast(back, MatrixExpr).asExplicit())).toBe(String(cast(expr, MatrixExpr).asExplicit()));
  }
});

it('converts scalar trace products, Hadamard powers and Kronecker products', async () => {
  const { Pow, Sym, KroneckerProduct, Rational } = await import('../../../../src');
  const { explicitArray } = await import('../../../../src/tensor/array/expressions/arrayexpressions');
  expect(str(convertMatrixToArray(mul(3, Trace(M))))).toBe('ArrayContraction(ArrayTensorProduct(3, M), (0, 1))');
  expect(str(convertMatrixToArray(new Pow(Trace(M), Rational.of(2))))).toBe('ArrayContraction(ArrayTensorProduct(M, M), (0, 1), (2, 3))');
  const x = new Sym('x');
  for (const exponent of [-1, x, Rational.of(1, 2)]) {
    expect(str(convertMatrixToArray(HadamardPower(M, exponent)))).toContain('ArrayElementwiseApplyFunc');
  }
  expect(str(convertMatrixToArray(HadamardPower(M, 2)))).toBe('ArrayDiagonal(ArrayTensorProduct(M, M), (0, 2), (1, 3))');
  for (const expr of [KroneckerProduct(M, N), KroneckerProduct(M, N, M, N)]) {
    const converted = convertMatrixToArray(expr);
    expect(str(converted)).toContain('Reshape(PermuteDims(ArrayTensorProduct(');
    expect(str(explicitArray(converted))).toBe(str(explicitArray(expr)));
  }
  expect(str(convertMatrixToArray(new Pow(x, x)))).toBe('x**x');
  expect(str(convertMatrixToArray(new Pow(x, Rational.of(-1))))).toBe('1/x');
});

it('flattens products inside lifted trace and Hadamard contractions', () => {
  const traced = convertMatrixToArray(mul(3, Trace(M), Trace(M)));
  expect(str(traced)).toBe('ArrayContraction(ArrayTensorProduct(3, M, M), (0, 1), (2, 3))');
  const hadamard = convertMatrixToArray(HadamardProduct(MatMul(M, N), MatMul(N, M)));
  expect(str(hadamard)).toBe('ArrayDiagonal(ArrayContraction(ArrayTensorProduct(M, N, N, M), (1, 2), (5, 6)), (0, 2), (1, 3))');
});

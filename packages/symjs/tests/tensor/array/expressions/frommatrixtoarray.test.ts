// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { readFileSync } from 'node:fs';
import { expect, it } from 'vitest';
import { MatrixSymbol, Trace, Transpose, MatMul, MatAdd, MatPow, S, mul, convertMatrixToArray, convertArrayToMatrix, str } from '../../../../src/index';
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
  expect(convertMatrixToArray(large)).toBe(large);
  expect(str(convertMatrixToArray(MatMul(3, M)))).toBe('ArrayTensorProduct(3, M)'); // SymPy 1.14.0
  expect(str(convertArrayToMatrix(convertMatrixToArray(mul(2, M))))).toBe('2*M');
});

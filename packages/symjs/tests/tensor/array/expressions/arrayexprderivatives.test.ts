// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { readFileSync } from 'node:fs';
import { expect, it } from 'vitest';
import { ArraySymbol, ArrayTensorProduct as TP, ArrayDiagonal as D, ArrayAdd, ZeroArray, Reshape, MatrixExpr, MatrixSymbol, Trace, Transpose, MatMul, MatAdd, arrayDerive, str, S } from '../../../../src/index';
import { NotImplementedError } from '../../../../src/core/errors';
import { explicitArray } from '../../../../src/tensor/array/expressions/arrayexpressions';
const refs: Record<string, string> = JSON.parse(readFileSync(new URL('./references.json', import.meta.url), 'utf8'));
const M = MatrixSymbol('M', 2, 2), N = MatrixSymbol('N', 2, 2);
const cases = { derive_self: M, derive_other: N, derive_product: MatMul(M, N), derive_square: MatMul(M, M), derive_transpose: Transpose(M), derive_trace: Trace(M), derive_sum: MatAdd(M, N), derive_tensor: new TP(M, N), derive_diagonal: new D(M, [0, 1]) };
for (const shape of [[3], [2, 3], [2, 3, 4]]) it(`derivative axes for shape ${shape}`, () => {
  const a = new ArraySymbol('R', shape), derivative = arrayDerive(a, a), name = shape.join('_');
  expect(str(derivative)).toBe(refs[`derive_shape_repr_${name}`]);
  const explicit = derivative instanceof MatrixExpr ? String(derivative.asExplicit()) : str(explicitArray(derivative));
  expect(explicit).toBe(refs[`derive_shape_${name}`]);
});
for (const [name, expr] of Object.entries(cases)) it(name, () => {
  const derivative = arrayDerive(expr, M);
  // SymPy array_derive(Trace(M), M) incorrectly returns zero. Its independent
  // entrywise derivative is I: d(M[0,0]+M[1,1])/dM[0,0] = 1, not zero.
  if (name === 'derive_trace') expect(refs['derive_trace_explicit']).toBe('[[0, 0], [0, 0]]');
  expect(str(explicitArray(derivative))).toBe(refs[name === 'derive_trace' ? 'derive_trace_correct' : `${name}_explicit`]);
  if (name === 'derive_self') expect(str(derivative)).toBe(refs[name]);
});
it('handles constant products, array symbols and unsupported variables', () => {
  const A = new ArraySymbol('A', [2, 2]);
  expect(str(explicitArray(arrayDerive(A, A)))).toBe(refs['derive_self_explicit']);
  expect(arrayDerive(new TP(N, N), M)).toBeInstanceOf(ZeroArray);
  expect(str(explicitArray(arrayDerive(new ArrayAdd(M, N), M)))).toBe(refs['derive_sum_explicit']);
  expect(() => arrayDerive(M, S.One)).toThrow(NotImplementedError);
  expect(() => arrayDerive(new Reshape(A, [4]), A)).toThrow(NotImplementedError);
});

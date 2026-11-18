// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { readFileSync } from 'node:fs';
import { expect, it } from 'vitest';
import { ArraySymbol, ArrayTensorProduct as TP, ArrayDiagonal as D, ArrayAdd, ZeroArray, Reshape, MatrixExpr, MatrixSymbol, Trace, Transpose, MatMul, MatAdd, arrayDerive, ArrayDerivativeNode, ArrayDerivative, MatPow, Rational, subs, mul, Inverse, ArrayElementwiseApplyFunc, sin, str, S } from '../../../../src/index';
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
  expect(str(arrayDerive(new Reshape(A, [4]), A))).toBe('Reshape(PermuteDims(ArrayTensorProduct(I, I), (3)(1 2)), (2, 2, 4))');
});

it('differentiates inverse matrices and elementwise functions', () => {
  const X = MatrixSymbol('X', 1, 1);
  expect(str(explicitArray(arrayDerive(Inverse(X), X)))).toBe('[[[[-1/X[0, 0]**2]]]]');
  expect(str(explicitArray(arrayDerive(new ArrayElementwiseApplyFunc(sin, X), X)))).toBe('[[[[cos(X[0, 0])]]]]');
});

it('preserves matrix fractional powers and their formal derivatives', () => {
  const expr = MatPow(M, Rational.of(1, 2));
  const derivative = ArrayDerivative(expr, M, { evaluate: true });
  expect(derivative).toBeInstanceOf(ArrayDerivativeNode);
  expect(derivative.args[0]).toBe(expr);
  expect(() => arrayDerive(expr, M)).toThrow(NotImplementedError);
});

it('matches every inverse derivative component for a nonsymmetric matrix', () => {
  const derivative = explicitArray(arrayDerive(Inverse(M), M));
  const values = new Map([[M.at(0, 0), 2], [M.at(0, 1), 1], [M.at(1, 0), 3], [M.at(1, 1), 4]]);
  expect(str(subs(derivative, values))).toBe(refs['derive_inverse_2x2_numeric']);
});

it('keeps captured matrix-dependent elementwise parameters in a formal derivative', () => {
  const X = MatrixSymbol('X', 1, 1);
  const expr = new ArrayElementwiseApplyFunc((x) => mul(X.at(0, 0), x), X);
  expect(() => arrayDerive(expr, X)).toThrow(NotImplementedError);
  expect(ArrayDerivative(expr, X, { evaluate: true })).toBeInstanceOf(ArrayDerivativeNode);
});

it('differentiates scalar combinations of traces by the array chain rule', async () => {
  const { add, pow, diff, cos } = await import('../../../../src');
  const t = Trace(M), u = Trace(N);
  expect(str(diff(t, M))).toBe('I');
  expect(str(diff(Trace(MatMul(M, N)), M))).toBe('N.T');
  expect(str(diff(Trace(MatMul(M, M)), M))).toBe('2*M.T');
  for (const expression of [add(t, u), mul(t, t, u), pow(t, 3), sin(t)]) {
    const actual = explicitArray(arrayDerive(expression, M));
    const expected = M.asExplicit().map((entry) => diff(expression, entry));
    expect(str(actual)).toBe(str(new (await import('../../../../src')).SymArray(expected.toArray())));
  }
  expect(str(diff(sin(t), M))).toBe(str(mul(cos(t), diff(t, M))));
  expect(arrayDerive(mul(u, u), M)).toBeInstanceOf(ZeroArray);
});

it('distributes the derivative of a product with a matrix sum', async () => {
  const { diff } = await import('../../../../src');
  const expression = Trace(MatMul(MatAdd(M, N), MatAdd(M, N)));
  expect(str(diff(expression, M))).toBe('2*M.T + 2*N.T');
  expect(str(diff(MatAdd(M, MatMul(M, M)), M))).toContain('ArrayAdd');
});

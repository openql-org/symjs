// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it, vi } from 'vitest';
import { ArrayDerivative as D, ArrayDerivativeNode, Derivative, Sym, SymArray, Matrix, ImmutableMatrix, MatrixSymbol, ArraySymbol, ZeroMatrix, S, str, sin, pow, doit, shape, subs, Trace, Transpose, MatMul, getShape, IndexedBase, SymFunction, ExtensionExpr, Expr, DiagonalMatrix } from '../../../src';
import { cast } from '../../../src/core/guard';
import * as symbolicDerivatives from '../../../src/tensor/array/expressions/arrayexprderivatives';
import { explicitArray } from '../../../src/tensor/array/expressions/arrayexpressions';
const x = new Sym('x'), y = new Sym('y'), z = new Sym('z'), t = new Sym('t');
const m = Matrix.of([[x, y], [z, t]]), M = MatrixSymbol('M', 3, 2), N = MatrixSymbol('N', 4, 3);
const evaluate = (e: Parameters<typeof D>[0], ...v: Parameters<typeof D> extends [unknown, ...infer V] ? V : never) => D(e, ...v, { evaluate: true });
it('preserves shape through construction, evaluation and substitution', () => {
  for (const [e, v, expected] of [[x, m, [2, 2]], [m, m, [2, 2, 2, 2]], [m, x, [2, 2]], [M, N, [4, 3, 3, 2]]] as const) {
    const d = cast(D(e, v), ArrayDerivativeNode);
    expect(d).toBeInstanceOf(Derivative);
    expect(d.isScalar).toBe(false);
    expect(d.shape.map(String)).toEqual(expected.map(String));
    expect(shape(d.doit()).map(String)).toEqual(expected.map(String));
    expect(shape(doit(d)).map(String)).toEqual(expected.map(String));
  }
  const second = cast(D(M, [N, 2]), ArrayDerivativeNode);
  expect(second.shape.map(String)).toEqual(['4', '3', '4', '3', '3', '2']);
  expect(second.doit()).toBeInstanceOf(D);
  expect(shape(evaluate(M.asExplicit(), [N.asExplicit(), 2])).map(String)).toEqual(second.shape.map(String));
  const substituted = subs(D(pow(x, 3), SymArray([x, y])), [[x, z]]);
  expect(substituted).toBeInstanceOf(D);
  expect(str(doit(substituted))).toBe('[3*z**2, 0]');
});
it('computes explicit derivatives with variable axes first', () => {
  const a = SymArray([x, y]);
  expect(str(evaluate(pow(x, 2), m))).toBe('Matrix([[2*x, 0], [0, 0]])');
  expect(str(evaluate(pow(x, 2), a))).toBe('[2*x, 0]');
  expect(str(evaluate(SymArray([pow(x, 2), sin(x)]), x))).toBe('[2*x, cos(x)]');
  expect(str(evaluate(m, x))).toBe('Matrix([[1, 0], [0, 0]])');
  expect(str(evaluate(a, a))).toBe('[[1, 0], [0, 1]]');
  expect(str(evaluate(a, m))).toBe('[[[1, 0], [0, 1]], [[0, 0], [0, 0]]]');
  expect(str(evaluate(x, y))).toBe('0');
  expect(str(evaluate(pow(x, 3), x, 2))).toBe('6*x');
  expect(str(evaluate(pow(x, 3), x, x))).toBe('6*x');
  expect(str(evaluate(D(pow(x, 3), x), x))).toBe('6*x');
  expect(str(evaluate(pow(x, 3)))).toBe('3*x**2');
  expect(D(x, [x, 0])).toBe(x);
});
it('differentiates symbolic matrices and retains unsupported mixed derivatives', () => {
  expect(evaluate(x, M).key).toBe(ZeroMatrix(3, 2).key);
  expect(evaluate(M, x).key).toBe(ZeroMatrix(3, 2).key);
  const A = MatrixSymbol('A', 2, 2);
  expect(str(explicitArray(evaluate(A, A)))).toBe('[[[[1, 0], [0, 0]], [[0, 1], [0, 0]]], [[[0, 0], [1, 0]], [[0, 0], [0, 1]]]]');
  expect(str(explicitArray(evaluate(Transpose(A), A)))).toContain('1');
  // d tr(A)/d A is the identity, including when A has symbolic entries.
  expect(str(explicitArray(evaluate(Trace(A), A)))).toBe('[[1, 0], [0, 1]]');
  expect(getShape(evaluate(MatMul(x, A), x)).map(String)).toEqual(['2', '2']);
  expect(evaluate(SymArray([x]), A)).toBeInstanceOf(D);
  expect(evaluate(A, SymArray([x]))).toBeInstanceOf(D);
  expect(evaluate(A, x, SymArray([y]))).toBeInstanceOf(D);
  expect(str(explicitArray(evaluate(x, new ArraySymbol('Q', [2]))))).toBe('[0, 0]');
  for (const dims of [[3, 1], [1, 3], [1, 1]] as const) {
    const vector = MatrixSymbol('v', dims[0], dims[1]);
    expect(str(evaluate(vector, vector))).toBe(dims[0] === 1 && dims[1] === 1 ? '1' : 'I');
  }
});
it('validates counts and variables', () => {
  expect(() => D(x, 2)).toThrow(TypeError);
  expect(D(S.One)).toBe(S.Zero);
  expect(() => D(x, x.add(y))).toThrow(RangeError);
  expect(() => evaluate(x, SymArray([1, x]))).toThrow(RangeError);
  expect(() => D(x.add(y))).toThrow(RangeError);
  for (const n of [-1, 0.5, Infinity]) expect(() => D(x, [x, n])).toThrow(RangeError);
  expect(() => D(x, S.One)).toThrow(RangeError);
  expect(str(D(x, x, {}))).toBe('Derivative(x, x)');
  expect(cast(D(x, ImmutableMatrix(m)), D).shape.map(String)).toEqual(['2', '2']);
});


class NonScalarVariable extends ExtensionExpr {
  constructor() { super('NonScalarVariable', []); }
  override get isScalar(): boolean { return false; }
  withArgs(): Expr { return this; }
}
it('retains unknown derivatives, remaining variables and extension hooks', () => {
  const custom = new NonScalarVariable(), A = new ArraySymbol('A', [2]);
  expect(evaluate(custom, x)).toBeInstanceOf(D);
  expect(evaluate(x, custom)).toBeInstanceOf(D);
  expect(evaluate(A, x)).toBeInstanceOf(D);
  expect(evaluate(DiagonalMatrix(MatrixSymbol('v', 2, 1)), x)).toBeInstanceOf(D);
  const remaining = cast(evaluate(M, N, x), D);
  expect(remaining.variableCount.map(([v, n]) => [String(v), n])).toEqual([['N', 1], ['x', 1]]);
  // Keep a scalar matrix-entry function unevaluated if its matrix formula is unavailable.
  expect(evaluate(sin(M.at(0, 0)), M)).toBeInstanceOf(D);
  const idx = new IndexedBase('a').at(0), f = SymFunction('f')(x);
  expect(evaluate(idx, idx).key).toBe(S.One.key);
  expect(evaluate(f, f).key).toBe(S.One.key);
  expect(evaluate(A.at(0), A.at(0)).key).toBe(S.One.key);
  expect(evaluate(M.at(0, 0), M.at(0, 0)).key).toBe(S.One.key);
  expect(D(x, Derivative(f, x))).toBeInstanceOf(D);
  expect(() => D(x, new IndexedBase('invalid'))).toThrow(RangeError);
  const hook = vi.spyOn(symbolicDerivatives, 'arrayDerive').mockImplementation(() => { throw new RangeError('invalid derivative dimensions'); });
  try { expect(() => evaluate(M, M)).toThrow('invalid derivative dimensions'); }
  finally { hook.mockRestore(); }
});

it('forms Jacobians of explicit vectors of matrix and array entries', () => {
  const array = new ArraySymbol('a', [2]);
  for (const entries of [[array.at(0), array.at(1)], [M.at(0, 0), M.at(1, 0)]]) {
    const vector = SymArray(entries);
    expect(str(evaluate(vector, vector))).toBe('[[1, 0], [0, 1]]');
  }
  expect(() => evaluate(SymArray([x]), SymArray([array]))).toThrow('cannot derive by this array');
});

it('reduces singleton axes in vector Jacobians and scalar matrix gradients', async () => {
  const { diff, MatPow, Rational, Identity } = await import('../../../src');
  const v = MatrixSymbol('v', 3, 1), w = MatrixSymbol('w', 3, 1), A = MatrixSymbol('A', 3, 3);
  expect(str(diff(MatMul(A, v), v))).toBe('A.T');
  expect(str(diff(MatMul(Transpose(v), w), v))).toBe('w');
  expect(str(diff(MatMul(Transpose(v), v), v))).toBe('2*v');
  expect(str(diff(MatMul(A, v), A))).toContain('ArrayTensorProduct');
  const root = MatPow(MatMul(Transpose(v), w), Rational.of(1, 2));
  expect(str(diff(root, v))).toBe('(1/2)*w*(v.T*w)**(-1/2)');
  expect(str(diff(MatMul(Identity(3), v), v))).toBe('I');
});

it('retains factors in scalar differentials and contracts elementwise vector Jacobians', async () => {
  const { diff, MatAdd, MatPow, HadamardProduct, HadamardPower } = await import('../../../src');
  const v = MatrixSymbol('v', 3, 1), w = MatrixSymbol('w', 3, 1);
  const A = MatrixSymbol('A', 3, 3), X = MatrixSymbol('X', 3, 3);
  expect(str(diff(HadamardProduct(w, v), v))).toBe('DiagMatrix(w)');
  expect(str(diff(HadamardPower(v, 2), v))).toBe('2*DiagMatrix(v)');
  expect(str(diff(MatMul(w.T, HadamardProduct(A, X), v), X))).toBe('HadamardProduct(w*v.T, A)');
  expect(str(diff(HadamardPower(MatMul(w.T, X, v), 2), X))).toBe('2*w*w.T*X*v*v.T');
  expect(str(diff(MatPow(MatMul(w.T, X, v), S.Half), X))).toBe('(1/2)*w*(w.T*X*v)**(-1/2)*v.T');
  expect(str(diff(MatMul(w.T, MatAdd(X, A), v), X))).toBe('w*v.T');
  expect(str(diff(Trace(MatMul(X, A)), X))).toBe('A.T');
});

it('keeps the axes of a column-vector product separate through a transpose', async () => {
  const { diff, MatAdd, MatPow } = await import('../../../src');
  const v = MatrixSymbol('v', 3, 1), A = MatrixSymbol('A', 3, 3), B = MatrixSymbol('B', 3, 3);
  expect(str(diff(MatMul(v, v.T, v), v))).toBe('KroneckerProduct(I, v.T*v) + 2*v*v.T');
  expect(str(diff(MatPow(MatMul(v.T, A, v), S.Half), v))).toContain('**(-1/2)');
  expect(str(diff(MatMul(v.T, MatMul(3, MatAdd(A, B), A), v), A))).toContain('v.T');
  expect(str(diff(MatAdd(v, MatMul(A, v)), v))).toBe('I + A.T');
  expect(str(diff(Trace(MatMul(Trace(A), A)), A))).toBe('(2*Trace(A))*I');
  expect(str(diff(Trace(MatPow(A, 2)), A))).toBe('2*A.T');
  expect(str(diff(v.T, v))).toBe('I');
});

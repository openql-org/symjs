// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * Coverage of sympy.matrices.expressions.kronecker with the expected values
 * of SymPy 1.14.
 */

import { describe, expect, it } from 'vitest';
import { Matrix, conjugate, adjoint, expand, sstr, symbols } from '../src';
import type { Expr } from '../src';
import {
  Adjoint,
  Determinant,
  Identity,
  ImmutableMatrix,
  Inverse,
  KroneckerProduct,
  MatMul,
  MatPow,
  MatrixSymbol,
  Trace,
  Transpose,
  ZeroMatrix,
  combineKronecker,
  det,
  kroneckerProduct,
  matrixKroneckerProduct,
} from '../src/matrices/expressions';
import type { MatrixExpr } from '../src/matrices/expressions';

const s = (e: unknown): string => sstr(e as Expr);
const M = (e: Expr): MatrixExpr => e as MatrixExpr;
const [n, i, j] = symbols('n i j', { integer: true });
const A = MatrixSymbol('A', 2, 2);
const B = MatrixSymbol('B', 3, 3);
const C = MatrixSymbol('C', 2, 3);
const D = MatrixSymbol('D', 3, 2);
const X = MatrixSymbol('X', n, n);
const Y = MatrixSymbol('Y', 6, 6);
const KAB = (): MatrixExpr => M(KroneckerProduct(A, B));

describe('KroneckerProduct', () => {
  it('identities and validation', () => {
    expect(s(KroneckerProduct(ImmutableMatrix(Matrix.eye(2)), ImmutableMatrix(Matrix.eye(2))))).toBe(
      'Matrix([[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]])',
    );
    expect(s(KroneckerProduct(Identity(2), Identity(n)))).toBe('I');
    expect(() => KroneckerProduct(A, 2)).toThrow('Mix of Matrix and Scalar symbols');
  });
  it('substitution and entries', () => {
    expect(s(KAB().subs(A, C.mul(D)))).toBe('KroneckerProduct(C*D, B)');
    expect(s(KAB().at(i, j))).toBe('A[Mod(floor(i/3), 2), Mod(floor(j/3), 2)]*B[Mod(i, 3), Mod(j, 3)]');
    expect(s(M(KroneckerProduct(A, X)).at(0, 1))).toBe('A[0, Mod(floor(1/n), 2)]*X[0, Mod(1, n)]');
  });
  it('adjoint, conjugate, determinant and inverse', () => {
    expect(s(adjoint(KAB()))).toBe('KroneckerProduct(Adjoint(A), Adjoint(B))');
    expect(s(M(Adjoint(KAB())).doit())).toBe('KroneckerProduct(Adjoint(A), Adjoint(B))');
    expect(s(conjugate(KAB()))).toBe('KroneckerProduct(Adjoint(A.T), Adjoint(B.T))');
    expect(s(det(KroneckerProduct(C, D)))).toBe('Determinant(KroneckerProduct(C, D))');
    expect(s(M(Determinant(KroneckerProduct(C, D))).doit())).toBe('Determinant(KroneckerProduct(C, D))');
    expect(s(M(Inverse(KroneckerProduct(C, D))).doit())).toBe('(KroneckerProduct(C, D))**(-1)');
    expect(s(M(Inverse(KAB())).doit())).toBe('KroneckerProduct(A**(-1), B**(-1))');
    expect(() => M(Inverse(KroneckerProduct(ZeroMatrix(2, 2), B))).doit()).toThrow('Matrix det == 0; not invertible.');
  });
  it('expand(kroneckerproduct=True)', () => {
    const k = M(KroneckerProduct(A.add(A.T), B));
    expect(s(expand(k, { kroneckerproduct: true }))).toBe('KroneckerProduct(A, B) + KroneckerProduct(A.T, B)');
    expect(s(expand(KAB(), { kroneckerproduct: true }))).toBe('KroneckerProduct(A, B)');
    expect(s(expand(k))).toBe('KroneckerProduct(A + A.T, B)');
    expect(s(expand(k, { other: true }))).toBe('KroneckerProduct(A + A.T, B)');
  });
  it('_kronecker_add and _kronecker_mul without matching shapes', () => {
    const kab = KAB() as KroneckerProduct;
    expect(s(kab.kroneckerAdd(KroneckerProduct(B, A)))).toBe('KroneckerProduct(A, B) + KroneckerProduct(B, A)');
    expect(s(kab.kroneckerMul(Y))).toBe('(KroneckerProduct(A, B))*Y');
  });
  it('doit and canonicalization', () => {
    expect(s(M(KroneckerProduct(Transpose(A.add(A)), B)).doit({ deep: false }))).toBe('KroneckerProduct((2*A).T, B)');
    expect(s(M(KroneckerProduct(A)).doit())).toBe('A');
    expect(s(M(KroneckerProduct(KAB(), A)).doit())).toBe('KroneckerProduct(A, B, A)');
    expect(s(M(KroneckerProduct(MatMul(2, A), MatMul(3, B))).doit())).toBe('6*(KroneckerProduct(A, B))');
    // SymPy raises AttributeError ('Mul' object has no attribute 'is_Identity')
    expect(s(M(KroneckerProduct(MatMul(2, A, A.T), B)).doit())).toBe('2*(KroneckerProduct(A*A.T, B))');
  });
  it('kronecker_product and matrix_kronecker_product errors', () => {
    expect(() => kroneckerProduct()).toThrow('Empty Kronecker product is undefined');
    // SymPy raises IndexError for no arguments
    expect(() => matrixKroneckerProduct()).toThrow(TypeError);
    expect(() => matrixKroneckerProduct(Matrix.of([[1]]), A as unknown as Matrix)).toThrow('Sequence of Matrices expected');
  });
});

describe('combine_kronecker', () => {
  it('sums', () => {
    // SymPy raises TypeError (unsupported operand type(s) for +: 'MatAdd' and 'list')
    expect(s(combineKronecker(KAB().add(Y)))).toBe('KroneckerProduct(A, B) + Y');
    expect(s(combineKronecker(M(KAB().add(KAB())).add(KroneckerProduct(B, A))))).toBe('2*(KroneckerProduct(A, B)) + KroneckerProduct(B, A)');
    expect(s(combineKronecker(Y.add(Y.T.mul(KAB()))))).toBe('Y + Y.T*(KroneckerProduct(A, B))');
  });
  it('products and powers', () => {
    expect(s(combineKronecker(MatMul(Y, KAB(), KAB())))).toBe('Y*(KroneckerProduct(A**2, B**2))');
    expect(s(combineKronecker(MatPow(KroneckerProduct(C, D), 2)))).toBe('(KroneckerProduct(C, D))**2');
    // SymPy raises TypeError (unsupported operand type(s) for +: 'MatAdd' and 'list')
    expect(s(combineKronecker(MatPow(Y.add(KAB()), 2)))).toBe('(KroneckerProduct(A, B) + Y)**2');
  });
  it('inside scalar and transposed expressions', () => {
    expect(s(combineKronecker(Trace(KAB().mul(KAB())).add(1)))).toBe('Trace(A**2)*Trace(B**2) + 1');
    expect(s(combineKronecker(Transpose(KAB().mul(KAB()))))).toBe('KroneckerProduct(A.T**2, B.T**2)');
  });
});

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/matrices/expressions/kronecker.ts.
//
// KroneckerProduct and the Kronecker product rules. Expected values are SymPy 1.14 results (explicit
// matrices printed on one line).

import { describe, expect, it } from 'vitest';
import * as sj from '../../../src';
import { adjoint, conjugate, expand, type Expr, Lambda, latex, Matrix, sin, sstr, symbol, symbols } from '../../../src';
import { Adjoint, combineKronecker, det, Determinant, ElementwiseApplyFunction, FunctionMatrix, HadamardPower, hadamardPower, Identity, ImmutableMatrix, Inverse, KroneckerProduct, kroneckerProduct, MatMul, MatPow, type MatrixExpr, matrixKroneckerProduct, MatrixSymbol, Trace, trace, Transpose, ZeroMatrix } from '../../../src/matrices/expressions';

const s = (e: unknown): string => sstr(e as Expr);
const L = (e: unknown): string => latex(e as Expr);
const M = (e: Expr): MatrixExpr => e as MatrixExpr;
const mats3 = (r: Expr | number, c: Expr | number): [MatrixExpr, MatrixExpr, MatrixExpr] => [MatrixSymbol('A', r, c), MatrixSymbol('B', r, c), MatrixSymbol('C', r, c)];
const [n, i, j] = symbols('n i j', { integer: true });
const A = MatrixSymbol('A', 2, 2);
const B = MatrixSymbol('B', 3, 3);
const C = MatrixSymbol('C', 2, 3);
const D = MatrixSymbol('D', 3, 2);
const X = MatrixSymbol('X', n, n);
const Y = MatrixSymbol('Y', 6, 6);
const KAB = (): MatrixExpr => M(KroneckerProduct(A, B));

describe('kronecker', () => {
  const [m, n] = symbols('m n', { integer: true });
  it('KroneckerProduct', () => {
    const A = MatrixSymbol('A', 5, 5);
    const B = MatrixSymbol('B', 5, 5);
    expect(KroneckerProduct(A, B)).toBeInstanceOf(KroneckerProduct);
  });
  it('has_matching_shape and structurally_equal', () => {
    const A = MatrixSymbol('A', m, n);
    const B = MatrixSymbol('B', n, m);
    const kab = KroneckerProduct(A, B) as KroneckerProduct;
    expect(kab.hasMatchingShape(KroneckerProduct(B, A))).toBe(true);
    expect(kab.hasMatchingShape(KroneckerProduct(A, B))).toBe(false);
    expect(kab.hasMatchingShape(A)).toBe(false);
    const A2 = MatrixSymbol('A', m, m);
    const B2 = MatrixSymbol('B', n, n);
    const C2 = MatrixSymbol('C', m, m);
    const D2 = MatrixSymbol('D', n, n);
    const k2 = KroneckerProduct(A2, B2) as KroneckerProduct;
    expect(k2.structurallyEqual(KroneckerProduct(C2, D2))).toBe(true);
    expect(k2.structurallyEqual(KroneckerProduct(D2, C2))).toBe(false);
    expect(k2.structurallyEqual(C2)).toBe(false);
  });
  it('combine_kronecker', () => {
    const A = MatrixSymbol('A', m, n);
    const B = MatrixSymbol('B', n, m);
    expect(s(combineKronecker(M(KroneckerProduct(A, B)).mul(KroneckerProduct(B, A))))).toBe('KroneckerProduct(A*B, B*A)');
    expect(s(combineKronecker(M(KroneckerProduct(A, B)).add(KroneckerProduct(B.T, A.T))))).toBe('KroneckerProduct(A + B.T, B + A.T)');
    const C = MatrixSymbol('C', n, n);
    const D = MatrixSymbol('D', m, m);
    expect(s(combineKronecker(M(KroneckerProduct(C, D)).pow(m)))).toBe('KroneckerProduct(C**m, D**m)');
  });
  it('kronecker_product', () => {
    const A = MatrixSymbol('A', 2, 2);
    const B = MatrixSymbol('B', 2, 2);
    expect(s(kroneckerProduct(A))).toBe('A');
    expect(s(kroneckerProduct(A, B))).toBe('KroneckerProduct(A, B)');
    expect(s(M(kroneckerProduct(A, B)).at(0, 1))).toBe('A[0, 0]*B[0, 1]');
    expect(String(M(kroneckerProduct(A, B)).asExplicit())).toBe(
      'Matrix([[A[0, 0]*B[0, 0], A[0, 0]*B[0, 1], A[0, 1]*B[0, 0], A[0, 1]*B[0, 1]], [A[0, 0]*B[1, 0], A[0, 0]*B[1, 1], A[0, 1]*B[1, 0], A[0, 1]*B[1, 1]], [A[1, 0]*B[0, 0], A[1, 0]*B[0, 1], A[1, 1]*B[0, 0], A[1, 1]*B[0, 1]], [A[1, 0]*B[1, 0], A[1, 0]*B[1, 1], A[1, 1]*B[1, 0], A[1, 1]*B[1, 1]]])',
    );
    const sigmaX = Matrix.of([
      [0, 1],
      [1, 0],
    ]);
    const isigmaY = Matrix.of([
      [0, 1],
      [-1, 0],
    ]);
    expect(s(kroneckerProduct(sigmaX, isigmaY))).toBe('Matrix([[0, 0, 0, 1], [0, 0, -1, 0], [0, 1, 0, 0], [-1, 0, 0, 0]])');
  });
  it('matrix_kronecker_product', () => {
    const m1 = Matrix.of([
      [1, 2],
      [3, 4],
    ]);
    const m2 = Matrix.of([
      [1, 0],
      [0, 1],
    ]);
    expect(String(matrixKroneckerProduct(m1, m2))).toBe('Matrix([[1, 0, 2, 0], [0, 1, 0, 2], [3, 0, 4, 0], [0, 3, 0, 4]])');
    expect(String(matrixKroneckerProduct(m2, m1))).toBe('Matrix([[1, 2, 0, 0], [3, 4, 0, 0], [0, 0, 1, 2], [0, 0, 3, 4]])');
  });
  it('printing and evaluation', () => {
    const k = symbol('k');
    const [A, B, C] = mats3(k, k);
    expect(L(KroneckerProduct(A, B))).toBe('A \\otimes B');
    expect(L(KroneckerProduct(A.add(B), C))).toBe('\\left(A + B\\right) \\otimes C');
    expect(s(KroneckerProduct(A, B).mul(C))).toBe('(KroneckerProduct(A, B))*C');
    expect(s(M(KroneckerProduct(A, B)).neg())).toBe('-(KroneckerProduct(A, B))');
    expect(L(M(KroneckerProduct(A, B)).neg())).toBe('- A \\otimes B');
    expect(s(kroneckerProduct(Identity(2), Identity(3)))).toBe('I');
    expect(s(M(KroneckerProduct(A, B)).T)).toBe('KroneckerProduct(A.T, B.T)');
    expect(s(trace(KroneckerProduct(A, B)))).toBe('Trace(A)*Trace(B)');
    expect(s(kroneckerProduct(MatMul(2, A), B))).toBe('2*(KroneckerProduct(A, B))');
    expect(s(M(KroneckerProduct(A, B)).I)).toBe('KroneckerProduct(A**(-1), B**(-1))');
  });
});

describe('more SymPy cases', () => {
  const [, , k] = symbols('n m k');
  const [P, Q, R] = [MatrixSymbol('P', k, k), MatrixSymbol('Q', k, k), MatrixSymbol('R', k, k)];
  it('kronecker, hadamard and applyfunc details', () => {
    expect(s(det(KroneckerProduct(P, Q)))).toBe('Determinant(P)**k*Determinant(Q)**k');
    expect(s(kroneckerProduct(P, Matrix.of([[1, 2]])))).toBe('KroneckerProduct(P, Matrix([[1, 2]]))');
    expect(s(combineKronecker(M(KroneckerProduct(P, Q)).add(R)))).toBe('KroneckerProduct(P, Q) + R');
    expect(s(HadamardPower(2, 3))).toBe('8');
    expect(s(hadamardPower(P, 2))).toBe('HadamardPower(P, 2)');
    expect(s(M(HadamardPower(P, 2)).T)).toBe('HadamardPower(P.T, 2)');
    expect(s(ElementwiseApplyFunction(sin, MatrixSymbol('Y', 1, 1)))).toBe('Lambda(_d, sin(_d)).(Y)');
    expect(s(M(ElementwiseApplyFunction(sin, Matrix.of([[1, 2]]))).doit())).toBe('Matrix([[sin(1), sin(2)]])');
    const [i, j] = symbols('i j');
    expect(String(FunctionMatrix(2, 2, Lambda([i, j], i.mul(2))).asExplicit())).toBe('Matrix([[0, 0], [2, 2]])');
  });
});

describe('matrix error classes (SymPy sympy.matrices.exceptions)', () => {
  it('keeps an inverse of a Kronecker product of non-square factors unevaluated', () => {
    const A = sj.MatrixSymbol('A', 2, 3);
    const B = sj.MatrixSymbol('B', 3, 2);
    expect(String(sj.Inverse(sj.KroneckerProduct(A, B)))).toBe('(KroneckerProduct(A, B))**(-1)');
  });
});

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

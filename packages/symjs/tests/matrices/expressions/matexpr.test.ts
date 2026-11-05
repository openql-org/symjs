// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/matrices/expressions/matexpr.ts.
//
// The core matrix expressions: MatrixSymbol, indexing, MatrixElement, the special matrices, MatAdd,
// MatMul, MatPow, Inverse, Transpose, Adjoint, MatrixSlice, Trace, Determinant, Permanent and
// ElementwiseApplyFunction. Doctest examples of SymPy 1.14, printing (str and LaTeX) and evaluation
// cases; expected values are SymPy 1.14 results (explicit matrices printed on one line).

import { describe, expect, it } from 'vitest';
import * as sj from '../../../src';
import { adjoint, conjugate, cos, diff, Dummy, Eq, exp, type Expr, I as ImagUnit, Lambda, latex, Matrix, matrixExp, mul, Rational, S, sin, sstr, symbol, symbols, SymFunction as UFunction, transpose } from '../../../src';
import { Adjoint, det, Determinant, ElementwiseApplyFunction, GenericIdentity, GenericZeroMatrix, HadamardProduct, Identity, ImmutableMatrix, Inverse, isMataddValid, isMatmulValid, isSquare, MatAdd, MatMul, MatPow, MatrixElement, MatrixExpr, MatrixSlice, MatrixSymbol, matrixSymbols, MatScalar, mergeExplicitMatAdd, mergeExplicitMatMul, OneMatrix, per, Permanent, PermutationMatrix, ShapeError, Str, Trace, trace, Transpose, ZeroMatrix } from '../../../src/matrices/expressions';
import { doit } from '../../../src/calculus/doit';
import { MatMulNode, MatrixElementNode, MatrixSliceNode, negate, TraceNode, transposeOf } from '../../../src/matrices/expressions/matexpr';
import { rebuild } from '../../../src/core/traverse';
import { cast } from '../../../src/core/guard';

const s = (e: unknown): string => sstr(e as Expr);
const L = (e: unknown): string => latex(e as Expr);
const M = (e: Expr): MatrixExpr => e as MatrixExpr;
const eye = (n: number): Matrix => Matrix.eye(n);
const ones = (r: number, c = r): Matrix => Matrix.fromFunction(r, c, () => 1);
const [x, y, n, m, k, i] = symbols('x y n m k i');
const X = MatrixSymbol('X', 2, 2);
const Y = MatrixSymbol('Y', 2, 2);
const Z = MatrixSymbol('Z', 2, 2);
const A = MatrixSymbol('A', 2, 3);
const B = MatrixSymbol('B', 3, 2);
const W = MatrixSymbol('W', n, n);
const X3 = MatrixSymbol('X', 3, 3);
const Mi = ImmutableMatrix([
  [1, 2],
  [3, 4],
]);
const Yn = MatrixSymbol('Y', n, n);

describe('_shape', () => {
  const [m, n, p, q] = symbols('m n p q');
  const A = MatrixSymbol('A', m, n);
  const B = MatrixSymbol('B', p, q);
  it('is_matadd_valid, is_matmul_valid, is_square', () => {
    expect(s(isMataddValid(A, B))).toBe('Eq(m, p) & Eq(n, q)');
    expect(s(isMatmulValid(A, B))).toBe('Eq(n, p)');
    expect(s(isSquare(A))).toBe('Eq(m, n)');
  });
  it('validates integer shapes like SymPy', () => {
    const A3 = MatrixSymbol('A', 3, 4);
    const C = MatrixSymbol('C', 4, 3);
    expect(s(MatAdd(A3, MatrixSymbol('B', 3, 4)))).toBe('A + B');
    expect(() => MatAdd(A3, C)).toThrow(ShapeError);
    expect(() => MatAdd(A3, C)).toThrow('Matrices have mismatching shape: (3, 4)');
    expect(() => A3.mul(A3)).toThrow('Matrices are not aligned');
    expect(() => MatPow(A3, 2)).toThrow('Power of non-square matrix A');
    expect(() => Trace(A3)).toThrow('Trace of a non-square matrix');
    expect(() => A3.I).toThrow('Inverse of non-square matrix');
    expect(() => HadamardProduct(A3, C)).toThrow('Matrices have mismatching shape: (3, 4)');
    expect(() => MatAdd(A3, 2)).toThrow('Mix of Matrix and Scalar symbols');
    expect(() => MatrixSymbol('A', -1, 2)).toThrow('should be a nonnegative integer');
    expect(() => MatrixSymbol('A', Rational.of(1, 2), 2)).toThrow(RangeError);
  });
});

describe('adjoint', () => {
  it('Adjoint and adjoint', () => {
    const A = MatrixSymbol('A', 3, 5);
    const B = MatrixSymbol('B', 5, 3);
    const AB = A.mul(B);
    expect(s(Adjoint(AB))).toBe('Adjoint(A*B)');
    expect(s(adjoint(AB))).toBe('Adjoint(B)*Adjoint(A)');
    expect(adjoint(AB).equals(Adjoint(AB))).toBe(false);
    expect(adjoint(AB).equals(M(Adjoint(AB)).doit())).toBe(true);
    expect(M(adjoint(AB)).equalsExplicit(Adjoint(AB))).toBe(true);
    expect(s(M(Adjoint(AB)).doit())).toBe('Adjoint(B)*Adjoint(A)');
    expect(L(Adjoint(A))).toBe('A^{\\dagger}');
    expect(L(Adjoint(AB))).toBe('\\left(A B\\right)^{\\dagger}');
    expect(s(A.H)).toBe('Adjoint(A)');
  });
});

describe('applyfunc', () => {
  it('ElementwiseApplyFunction', () => {
    const X = MatrixSymbol('X', 3, 3);
    expect(s(X.applyfunc(exp))).toBe('Lambda(_d, exp(_d)).(X)');
    const expr = ElementwiseApplyFunction(exp, eye(3));
    expect(s(expr)).toBe('Lambda(_d, exp(_d)).(Matrix([[1, 0, 0], [0, 1, 0], [0, 0, 1]]))');
    expect(s(M(expr).doit())).toBe('Matrix([[E, 1, 1], [1, E, 1], [1, 1, E]])');
    expect(String(matrixExp(eye(3)))).toBe('Matrix([[E, 0, 0], [0, E, 0], [0, 0, E]])');
    expect(s(M(X.applyfunc(exp)).T)).toBe('Lambda(_d, exp(_d)).(X.T)');
    expect(s(M(X.applyfunc(exp)).at(0, 1))).toBe('exp(X[0, 1])');
    expect(s(M(M(X.applyfunc(sin)).applyfunc(exp)).doit())).toBe('Lambda(_d, exp(sin(_d))).(X)');
    expect(L(X.applyfunc(exp))).toBe('{\\left( d \\mapsto e^{d} \\right)}_{\\circ}\\left({X}\\right)');
  });
});

describe('determinant', () => {
  const A = MatrixSymbol('A', 3, 3);
  it('Determinant and det', () => {
    expect(s(Determinant(A))).toBe('Determinant(A)');
    expect(s(Determinant(eye(3)).doit())).toBe('1');
    expect(s(det(A))).toBe('Determinant(A)');
    expect(s(det(eye(3)))).toBe('1');
    expect(L(Determinant(A))).toBe('\\left|{A}\\right|');
  });
  it('Permanent and per', () => {
    expect(s(Permanent(A))).toBe('Permanent(A)');
    expect(s(Permanent(ones(3, 3)).doit())).toBe('6');
    expect(s(per(A))).toBe('Permanent(A)');
    expect(s(per(ones(5, 5)))).toBe('120');
    expect(s(per(Matrix.col(1, 2, 5)))).toBe('8');
    expect(L(Permanent(A))).toBe('\\operatorname{Permanent}\\left(A\\right)');
  });
});

describe('inverse', () => {
  it('Inverse', () => {
    const A = MatrixSymbol('A', 3, 3);
    const B = MatrixSymbol('B', 3, 3);
    expect(s(Inverse(A))).toBe('A**(-1)');
    expect(A.inverse().equals(Inverse(A))).toBe(true);
    expect(s(M(A.mul(B)).inverse())).toBe('B**(-1)*A**(-1)');
    expect(s(Inverse(A.mul(B)))).toBe('(A*B)**(-1)');
    expect(s(M(Inverse(A.mul(B))).doit())).toBe('B**(-1)*A**(-1)');
    expect(s(M(Inverse(A.mul(B))).doit({ invExpand: false }))).toBe('(A*B)**(-1)');
  });
});

describe('matadd', () => {
  it('MatAdd', () => {
    const [A, B, C] = ['A', 'B', 'C'].map((x) => MatrixSymbol(x, 5, 5));
    expect(s(MatAdd(A!, B!, C!))).toBe('A + B + C');
  });
  it('merge_explicit', () => {
    const A = MatrixSymbol('A', 2, 2);
    const B = eye(2);
    const C = Matrix.of([
      [1, 2],
      [3, 4],
    ]);
    const X = MatAdd(A, B, C);
    expect(s(X)).toBe('Matrix([[1, 0], [0, 1]]) + Matrix([[1, 2], [3, 4]]) + A');
    expect(s(mergeExplicitMatAdd(X))).toBe('Matrix([[2, 2], [3, 5]]) + A');
    expect(s(M(X).doit())).toBe('Matrix([[2, 2], [3, 5]]) + A');
    expect(s(A.add(B))).toBe('Matrix([[1, 0], [0, 1]]) + A');
    expect(s(MatAdd(Identity(2), C))).toBe('I + Matrix([[1, 2], [3, 4]])');
    expect(s(M(M(A.add(C)).add(A)))).toBe('Matrix([[1, 2], [3, 4]]) + 2*A');
  });
});

describe('matexpr', () => {
  it('MatrixExpr', () => {
    const A = MatrixSymbol('A', 3, 3);
    const y = MatrixSymbol('y', 3, 1);
    const x = M(M(M(M(A.T).mul(A)).I).mul(A)).mul(y);
    expect(s(x)).toBe('A**(-1)*A.T**(-1)*A*y');
    expect(L(x)).toBe('A^{-1} \\left(A^{T}\\right)^{-1} A y');
  });
  it('as_explicit, as_mutable, equals', () => {
    const I3 = Identity(3);
    expect(s(I3)).toBe('I');
    expect(String(I3.asExplicit())).toBe('Matrix([[1, 0, 0], [0, 1, 0], [0, 0, 1]])');
    expect(I3.shape.map(s)).toEqual(['3', '3']);
    expect(String(I3.asMutable())).toBe('Matrix([[1, 0, 0], [0, 1, 0], [0, 0, 1]])');
    expect(Identity(3).equalsExplicit(eye(3))).toBe(true);
    expect(Identity(3).equals(ImmutableMatrix(eye(3)))).toBe(false);
    expect(MatrixSymbol('A', 2, 2).equalsExplicit(MatrixSymbol('Z', 2, 2))).toBe(false);
    expect(() => Identity(symbol('n')).asExplicit()).toThrow('Matrix with symbolic shape cannot be represented explicitly.');
  });
  it('MatrixSymbol', () => {
    const A = MatrixSymbol('A', 3, 4);
    const B = MatrixSymbol('B', 4, 3);
    expect(A.shape.map(s)).toEqual(['3', '4']);
    expect(s(M(MatMul(2, A).mul(B)).add(Identity(3)))).toBe('I + 2*A*B');
    expect(s(M(A.rmul(2)).mul(B))).toBe('2*A*B');
    expect(new MatrixSymbol('A', 3, 4).symbolName).toBe('A');
    expect(L(MatrixSymbol('alpha', 2, 2))).toBe('\\alpha');
  });
  it('matrix_symbols', () => {
    const n = symbol('n');
    const A = MatrixSymbol('A', n, n);
    const B = MatrixSymbol('B', n, n);
    expect(matrixSymbols(MatMul(Trace(B), A)).map(s)).toEqual(['B', 'A']);
  });
  it('MatrixElement', () => {
    const n = symbol('n');
    const A = MatrixSymbol('A', n, n);
    expect(s(MatrixElement(A, 0, 1))).toBe('A[0, 1]');
    expect(s(MatrixElement(Matrix.of([[1, 2]]), 0, 1))).toBe('2');
    expect(L(MatrixElement(A.T, 0, 1))).toBe('{\\left(A^{T}\\right)}_{0,1}');
    expect(s(MatrixElement(A.mul(MatrixSymbol('B', n, n)), 0, 1))).toBe('(A*B)[0, 1]');
  });
});

describe('matmul', () => {
  it('MatMul', () => {
    const A = MatrixSymbol('A', 5, 4);
    const B = MatrixSymbol('B', 4, 3);
    const C = MatrixSymbol('C', 3, 6);
    expect(s(MatMul(A, B, C))).toBe('A*B*C');
  });
  it('merge_explicit', () => {
    const A = MatrixSymbol('A', 2, 2);
    const B = Matrix.of([
      [1, 1],
      [1, 1],
    ]);
    const C = Matrix.of([
      [1, 2],
      [3, 4],
    ]);
    let X = MatMul(A, B, C);
    expect(s(X)).toBe('A*Matrix([[1, 1], [1, 1]])*Matrix([[1, 2], [3, 4]])');
    expect(s(mergeExplicitMatMul(X))).toBe('A*Matrix([[4, 6], [4, 6]])');
    X = MatMul(B, A, C);
    expect(s(X)).toBe('Matrix([[1, 1], [1, 1]])*A*Matrix([[1, 2], [3, 4]])');
    expect(s(mergeExplicitMatMul(X))).toBe('Matrix([[1, 1], [1, 1]])*A*Matrix([[1, 2], [3, 4]])');
    expect(L(MatMul(A, B))).toBe('A \\left[\\begin{matrix}1 & 1\\\\1 & 1\\end{matrix}\\right]');
    expect(s(M(MatMul(2, A)).mul(C))).toBe('2*A*Matrix([[1, 2], [3, 4]])');
    expect(s(M(MatMul(2, C, A)).doit())).toBe('Matrix([[2, 4], [6, 8]])*A');
    expect(s(MatMul(C, 2, A))).toBe('Matrix([[1, 2], [3, 4]])*2*A');
    expect(s(A.mul(eye(2)))).toBe('A');
  });
  it('entries', () => {
    const A = MatrixSymbol('A', 2, 2);
    const Z = MatrixSymbol('Z', 2, 2);
    const C = Matrix.of([
      [1, 2],
      [3, 4],
    ]);
    expect(s(M(A.mul(Z)).at(0, 1))).toBe('A[0, 0]*Z[0, 1] + A[0, 1]*Z[1, 1]');
    expect(s(M(A.mul(C)).at(0, 1))).toBe('2*A[0, 0] + 4*A[0, 1]');
    expect(s(M(A.add(C)).at(0, 1))).toBe('A[0, 1] + 2');
    expect(s(M(MatMul(2, A)).at(0, 1))).toBe('2*A[0, 1]');
    expect(s(M(A.pow(2)).at(0, 1))).toBe('A[0, 0]*A[0, 1] + A[0, 1]*A[1, 1]');
    expect(s(M(A.I).at(0, 1))).toBe('-A[0, 1]/(A[0, 0]*A[1, 1] - A[0, 1]*A[1, 0])');
  });
});

describe('slice', () => {
  it('MatrixSlice', () => {
    const Mx = ImmutableMatrix(4, 4, Array.from({ length: 16 }, (_, k) => k));
    expect(s(Mx)).toBe('Matrix([[0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12, 13, 14, 15]])');
    const B = MatrixSlice(Mx, [0, 2], [2, 4]);
    expect(String(M(B).asExplicit())).toBe('Matrix([[2, 3], [6, 7]])');
  });
  it('mat_slice_of_slice', () => {
    const X = MatrixSymbol('X', 10, 10);
    expect(s(M(X.slice([null, null], [1, 5])).slice([5, 8], [null, null]))).toBe('X[5:8, 1:5]');
    expect(s(M(X.slice([1, 9, 2], [2, 6])).slice([1, 3], 2))).toBe('X[3:7:2, 4:5]');
  });
  it('printing', () => {
    const n = symbol('n');
    const A = MatrixSymbol('A', n, n);
    expect(s(A.slice([1, 3], 2))).toBe('A[1:3, 2:3]');
    expect(L(A.slice([1, 3], 2))).toBe('A\\left[1:3, 2:3\\right]');
    expect(s(M(A.mul(MatrixSymbol('B', n, n))).slice([null, null], 1))).toBe('(A*B)[:, 1:2]');
    expect(M(A.slice([0, 2], [0, 3])).shape.map(s)).toEqual(['2', '3']);
  });
});

describe('special', () => {
  it('Identity', () => {
    const A = MatrixSymbol('A', 3, 5);
    expect(s(Identity(3).mul(A))).toBe('A');
    expect(L(Identity(3))).toBe('\\mathbb{I}');
    expect(s(Identity(3).at(1, 1))).toBe('1');
    const [i, j] = symbols('i j');
    // SymPy: KroneckerDelta(i, j, (0, 2)); the base module's KroneckerDelta has no range argument
    expect(s(Identity(3).at(i, j))).toBe('KroneckerDelta(i, j)');
  });
  it('ZeroMatrix', () => {
    const A = MatrixSymbol('A', 3, 5);
    const Z = ZeroMatrix(3, 5);
    expect(s(A.add(Z))).toBe('A');
    expect(s(Z.mul(A.T))).toBe('0');
    expect(() => ZeroMatrix(2, 2).I).toThrow('Matrix det == 0; not invertible.');
  });
  it('OneMatrix', () => {
    const [n, m] = symbols('n m');
    expect(s(OneMatrix(n, m))).toBe('1');
    expect(s(M(OneMatrix(1, 1)).doit())).toBe('I');
    expect(s(M(OneMatrix(n, n)).pow(3))).toBe('n**2*1');
    expect(s(M(OneMatrix(n, m)).mul(OneMatrix(m, n)))).toBe('m*1');
    expect(s(trace(OneMatrix(n, n)))).toBe('n');
    expect(s(det(OneMatrix(2, 2)))).toBe('0');
  });
});

describe('trace', () => {
  it('Trace', () => {
    const A = MatrixSymbol('A', 3, 3);
    expect(s(Trace(A))).toBe('Trace(A)');
    expect(s(Trace(eye(3)))).toBe('Trace(Matrix([[1, 0, 0], [0, 1, 0], [0, 0, 1]]))');
    expect(s(Trace(eye(3)).simplify())).toBe('3');
    expect(L(Trace(A))).toBe('\\operatorname{tr}\\left(A \\right)');
  });
  it('trace', () => {
    const n = symbol('n');
    const X = MatrixSymbol('X', n, n);
    expect(s(trace(MatMul(2, X)))).toBe('2*Trace(X)');
    expect(s(trace(eye(3)))).toBe('3');
    expect(s(trace(X.T))).toBe('Trace(X)');
    expect(s(trace(Identity(n)))).toBe('n');
    expect(s(trace(M(X.add(X)).add(MatrixSymbol('Y', n, n))))).toBe('2*Trace(X) + Trace(Y)');
    expect(s(trace(Adjoint(X)))).toBe('conjugate(Trace(X))');
    expect(s(Trace(X.add(X)).simplify())).toBe('2*Trace(X)');
  });
});

describe('transpose', () => {
  it('Transpose and transpose', () => {
    const A = MatrixSymbol('A', 3, 5);
    const B = MatrixSymbol('B', 5, 3);
    expect(s(Transpose(A))).toBe('A.T');
    expect(A.T.equals(transpose(A))).toBe(true);
    expect(transpose(A).equals(Transpose(A))).toBe(true);
    expect(s(Transpose(A.mul(B)))).toBe('(A*B).T');
    expect(s(transpose(A.mul(B)))).toBe('B.T*A.T');
  });
});

describe('printing like SymPy', () => {
  const [n, x] = symbols('n x');
  const A = MatrixSymbol('A', n, n);
  const B = MatrixSymbol('B', n, n);
  const C = MatrixSymbol('C', n, n);
  const cases: [() => unknown, string, string][] = [
    [() => A.add(B), 'A + B', 'A + B'],
    [() => B.add(A), 'A + B', 'A + B'],
    [() => M(A.T).add(B), 'B + A.T', 'B + A^{T}'],
    [() => M(MatMul(2, A)).add(B), '2*A + B', '2 A + B'],
    [() => B.sub(A), '-A + B', '- A + B'],
    [() => A.sub(B), 'A - B', 'A - B'],
    [() => M(A.neg()).sub(B), '-A - B', '- A - B'],
    [() => M(A.mul(B)).add(C), 'A*B + C', 'A B + C'],
    [() => Identity(n).add(A), 'I + A', '\\mathbb{I} + A'],
    [() => A.add(ZeroMatrix(n, n)), 'A', 'A'],
    [() => M(A.pow(2)).add(A), 'A**2 + A', 'A^{2} + A'],
    [() => M(A.I).add(B), 'A**(-1) + B', 'A^{-1} + B'],
    [() => M(MatMul(Trace(A), B)).add(A), 'Trace(A)*B + A', '\\operatorname{tr}\\left(A \\right) B + A'],
    [() => M(A.mul(B)).sub(B.mul(A)), 'A*B - B*A', 'A B - B A'],
    [() => M(A.mul(x)).add(B), 'x*A + B', 'x A + B'],
    [() => MatMul(x.add(1), A), '(x + 1)*A', '\\left(x + 1\\right) A'],
    [() => MatMul(-2, A, B), '-2*A*B', '- 2 A B'],
    [() => MatMul(S.I, A), 'I*A', 'i A'],
    [() => MatMul(S.I.neg(), A), '-I*A', '- i A'],
    [() => M(A.T).mul(B), 'A.T*B', 'A^{T} B'],
    [() => M(A.mul(B)).T, 'B.T*A.T', 'B^{T} A^{T}'],
    [() => Transpose(A.mul(B)), '(A*B).T', '\\left(A B\\right)^{T}'],
    [() => Inverse(A.mul(B)), '(A*B)**(-1)', '\\left(A B\\right)^{-1}'],
    [() => M(A.add(B)).T, 'A.T + B.T', 'A^{T} + B^{T}'],
    [() => Transpose(A.add(B)), '(A + B).T', '\\left(A + B\\right)^{T}'],
    [() => Transpose(MatMul(2, A)), '(2*A).T', '\\left(2 A\\right)^{T}'],
    [() => MatPow(A, 2), 'A**2', 'A^{2}'],
    [() => MatPow(A.T, 2), 'A.T**2', '\\left(A^{T}\\right)^{2}'],
    [() => MatPow(A.mul(B), 2), '(A*B)**2', '\\left(A B\\right)^{2}'],
    [() => MatPow(A, x.add(1)), 'A**(x + 1)', 'A^{x + 1}'],
    [() => MatPow(A, -2), 'A**(-2)', 'A^{-2}'],
    [() => Adjoint(A.T), 'Adjoint(A.T)', '\\left(A^{T}\\right)^{\\dagger}'],
    [() => A.conjugate(), 'Adjoint(A.T)', '\\left(A^{T}\\right)^{\\dagger}'],
    [() => M(A.mul(B)).conjugate(), 'Adjoint((A*B).T)', '\\left(\\left(A B\\right)^{T}\\right)^{\\dagger}'],
    [() => A.at(0, 1), 'A[0, 1]', '{A}_{0,1}'],
    [() => M(A.mul(B)).at(0, 1), 'Sum(A[0, _i_1]*B[_i_1, 1], (_i_1, 0, n - 1))', ''],
    [() => M(A.add(B)).at(0, 1), 'A[0, 1] + B[0, 1]', '{A}_{0,1} + {B}_{0,1}'],
    [() => M(A.T).at(0, 1), 'A[1, 0]', '{A}_{1,0}'],
    [() => A.slice([0, 2], [1, 3]), 'A[:2, 1:3]', 'A\\left[:2, 1:3\\right]'],
    [() => M(A.I).T, 'A.T**(-1)', '\\left(A^{T}\\right)^{-1}'],
    [() => M(A.T).I, 'A.T**(-1)', '\\left(A^{T}\\right)^{-1}'],
    [() => Trace(A.mul(B)), 'Trace(A*B)', '\\operatorname{tr}\\left(A B \\right)'],
    [() => trace(A.add(B)), 'Trace(A) + Trace(B)', '\\operatorname{tr}\\left(A \\right) + \\operatorname{tr}\\left(B \\right)'],
    [() => trace(A.mul(B)), 'Trace(A*B)', '\\operatorname{tr}\\left(A B \\right)'],
    [() => det(A.mul(B)), 'Determinant(A)*Determinant(B)', '\\left|{A}\\right| \\left|{B}\\right|'],
    [() => det(MatMul(2, A)), '2**n*Determinant(A)', '2^{n} \\left|{A}\\right|'],
    [() => A.mul(Identity(n)), 'A', 'A'],
    [() => ZeroMatrix(n, n).mul(A), '0', '0'],
    [() => MatMul(x.neg(), A), '(-x)*A', '- x A'],
    [() => MatMul(mul(-2, x), A), '(-2*x)*A', '- 2 x A'],
    [() => MatMul(mul(x, symbol('y')), A), '(x*y)*A', 'x y A'],
    [() => A.div(2), '(1/2)*A', '\\left(\\frac{1}{2}\\right) A'],
    [() => M(A.neg()).div(2), '-(1/2)*A', '- \\frac{1}{2} A'],
    [() => MatMul(Rational.of(-3, 2), A, B), '-(3/2)*A*B', '- \\frac{3}{2} A B'],
    [() => MatMul(A, 2, B), 'A*2*B', 'A 2 B'],
    [() => MatMul(A, x, B, 3), 'A*x*B*3', 'A x B 3'],
    [() => M(MatMul(A, x, B, 3)).doit(), '(3*x)*A*B', '3 x A B'],
    [() => MatMul(S.I.add(1), A), '(1 + I)*A', '\\left(1 + i\\right) A'],
    [() => MatMul(S.I.add(1).neg(), A), '(-1 - I)*A', '\\left(-1 - i\\right) A'],
    [() => A.sub(MatMul(2, B)), 'A - 2*B', 'A - 2 B'],
    [() => A.sub(MatMul(x, B)), '(-x)*B + A', '- x B + A'],
    [() => M(MatMul(x, A)).sub(B), 'x*A - B', 'x A - B'],
    [() => A.sub(B.mul(C)), 'A - B*C', 'A - B C'],
    [() => M(M(A.mul(B)).neg()).sub(C), '-A*B - C', '- A B - C'],
    [() => MatMul(A, -1), '-A', 'A \\left(-1\\right)'],
    [() => M(MatMul(A, -1)).doit(), '-A', '- A'],
    [() => M(A.pow(-1)).mul(B), 'A**(-1)*B', 'A^{-1} B'],
    [() => M(A.T).neg(), '-A.T', '- A^{T}'],
    [() => M(A.pow(2)).neg(), '-A**2', '- A^{2}'],
    [() => M(MatMul(mul(-1, Trace(A)), B)), '(-Trace(A))*B', '- \\operatorname{tr}\\left(A \\right) B'],
    [() => M(MatMul(Trace(A), B)).sub(A), 'Trace(A)*B - A', '\\operatorname{tr}\\left(A \\right) B - A'],
    [() => M(A.add(B)).neg(), '-A - B', '- A - B'],
    [() => MatMul(-1, A.add(B)), '-(A + B)', '- \\left(A + B\\right)'],
    [() => M(MatMul(2, A.add(B))).doit(), '2*A + 2*B', '2 A + 2 B'],
    [() => M(MatMul(x, A.add(B))).doit(), 'x*(A + B)', 'x \\left(A + B\\right)'],
    [() => M(MatMul(Rational.of(1, 2), A.add(B))).doit(), '(1/2)*A + (1/2)*B', '\\left(\\frac{1}{2}\\right) A + \\left(\\frac{1}{2}\\right) B'],
    [() => MatAdd(MatrixSymbol('P', 2, 2), eye(2), Matrix.of([[1, 2], [3, 4]])), 'Matrix([[1, 0], [0, 1]]) + Matrix([[1, 2], [3, 4]]) + P', '\\left[\\begin{matrix}1 & 0\\\\0 & 1\\end{matrix}\\right] + \\left[\\begin{matrix}1 & 2\\\\3 & 4\\end{matrix}\\right] + P'],
    [() => Trace(eye(2)), 'Trace(Matrix([[1, 0], [0, 1]]))', '\\operatorname{tr}\\left(\\left[\\begin{matrix}1 & 0\\\\0 & 1\\end{matrix}\\right] \\right)'],
    [() => Determinant(eye(2)), 'Determinant(Matrix([[1, 0], [0, 1]]))', '\\left|{\\begin{matrix}1 & 0\\\\0 & 1\\end{matrix}}\\right|'],
    [() => Adjoint(A.add(B)), 'Adjoint(A + B)', '\\left(A + B\\right)^{\\dagger}'],
    [() => MatrixElement(A.mul(B), 0, 1), '(A*B)[0, 1]', '{\\left(A B\\right)}_{0,1}'],
    [() => OneMatrix(n, n), '1', '1'],
  ];
  it.each(cases.map((c, k) => [k, ...c] as const))('case %i', (_k, f, str0, tex) => {
    const e = f();
    expect(s(e)).toBe(str0);
    if (tex) expect(L(e)).toBe(tex);
  });
});

describe('evaluation like SymPy', () => {
  const [n, x] = symbols('n x');
  const A = MatrixSymbol('A', n, n);
  const B = MatrixSymbol('B', n, n);
  it('canonical products and powers', () => {
    expect(s(A.mul(A))).toBe('A**2');
    expect(s(M(A.mul(A)).mul(A))).toBe('A**3');
    expect(s(M(A.I).mul(A))).toBe('I');
    expect(s(A.mul(A.I))).toBe('I');
    expect(s(M(A.mul(B)).mul(Inverse(A.mul(B))))).toBe('I');
    expect(s(M(MatPow(A, 2)).pow(3))).toBe('A**6');
    expect(s(M(MatPow(A, 0)).doit())).toBe('I');
    expect(s(M(A.I).I)).toBe('A');
    expect(s(M(A.T).T)).toBe('A');
    expect(s(MatMul(0, A))).toBe('0*A');
    expect(s(M(MatMul(0, A)).doit())).toBe('0');
    expect(s(M(A.mul(2)).mul(3))).toBe('6*A');
    expect(s(M(MatAdd(A, A)).doit())).toBe('2*A');
    expect(s(M(A.add(B)).sub(A))).toBe('B');
  });
  it('expand, simplify and diff', () => {
    expect(s(M(MatMul(A.add(B), A)).expand())).toBe('A**2 + B*A');
    expect(s(M(MatMul(A.add(B), A.sub(B))).expand())).toBe('A**2 - B**2 - A*B + B*A');
    expect(s(M(MatMul(x, A.add(B))).expand())).toBe('x*A + x*B');
    expect(s(M(MatAdd(A, A)).simplify())).toBe('A + A');
    expect(s(M(MatMul(x, A)).diff(x))).toBe('A');
    expect(s(M(MatMul(x.pow(2), A)).diff(x))).toBe('(2*x)*A');
    expect(s(M(MatMul(x, A, B)).diff(x))).toBe('A*B');
    expect(s(A.diff(x))).toBe('0');
    expect(s(Trace(MatMul(x, A)).diff(x))).toBe('Trace(A)');
    expect(s(M(M(MatMul(x, A)).add(B)).diff(x))).toBe('A');
    expect(s(M(MatMul(x, A)).T.diff(x))).toBe('A.T');
    expect(s(mul(x, A.at(0, 1)).diff(A.at(0, 1) as never))).toBe('x');
    expect(s(A.at(0, 1).diff(A.at(1, 1) as never))).toBe('0');
    expect(s(A.at(0, 1).diff(A.at(0, 1) as never))).toBe('1');
  });
  it('substitution and dimensions', () => {
    const k = new Dummy('k');
    expect(s(A.subs(n, 3))).toBe('A');
    expect(M(A.subs(n, 3)).shape.map(s)).toEqual(['3', '3']);
    expect(M(Identity(n).subs(n, 2)).asExplicit().toString()).toBe('Matrix([[1, 0], [0, 1]])');
    expect(s(Eq(k, k))).toBe('True');
  });
});

describe('more SymPy cases', () => {
  const [n, m] = symbols('n m k');
  const A = MatrixSymbol('A', n, n);
  it('special matrices', () => {
    expect([OneMatrix(n, n).I, OneMatrix(2, 2).T, OneMatrix(n, m).T, ZeroMatrix(n, m).T, Identity(n).T, Identity(n).I, M(ZeroMatrix(n, n)).pow(2), Identity(n).pow(5)].map(s)).toEqual(['1**(-1)', '1', '1', '0', 'I', 'I', '0', 'I']);
    expect([Inverse(Identity(n)), Transpose(Identity(n)), MatPow(Identity(n), 2)].map(L)).toEqual(['\\left(\\mathbb{I}\\right)^{-1}', '\\left(\\mathbb{I}\\right)^{T}', '\\left(\\mathbb{I}\\right)^{2}']);
  });
  it('powers, inverses, transposes and adjoints', () => {
    expect(s(A.pow(Rational.of(1, 2)))).toBe('A**(1/2)');
    expect(L(A.pow(Rational.of(1, 2)))).toBe('A^{\\frac{1}{2}}');
    expect([MatPow(A, 2).T, MatPow(A, 2).I, Adjoint(MatPow(A, 2)).doit(), MatPow(A, 2).conjugate()].map(s)).toEqual(['A.T**2', 'A**(-2)', 'Adjoint(A)**2', 'Adjoint(A.T)**2']);
    expect([Inverse(A).T, Inverse(A).conjugate(), Adjoint(Inverse(A)).doit(), det(Inverse(A)), det(A.T), Transpose(A).conjugate(), Adjoint(A.T).doit(), trace(Inverse(A))].map(s)).toEqual([
      'A.T**(-1)',
      'Adjoint(A.T)**(-1)',
      'Adjoint(A)**(-1)',
      '1/Determinant(A)',
      'Determinant(A)',
      'Adjoint(A)',
      'Adjoint(A.T)',
      'Trace(A**(-1))',
    ]);
    expect(s(Trace(A).rewriteAsSum())).toBe('Sum(A[i, i], (i, 0, n - 1))');
  });
});

describe('matrix symbols', () => {
  it('transpose and adjoint like SymPy', async () => {
    const { MatrixSymbol, transpose, adjoint, mul, add } = await import('../../../src');
    const A = new MatrixSymbol('A', 3, 3);
    const B = new MatrixSymbol('B', 3, 3);
    expect(sstr(transpose(A))).toBe('A.T');
    expect(sstr(adjoint(A))).toBe('Adjoint(A)');
    expect(sstr(transpose(mul(A, B)))).toBe('B.T*A.T');
    expect(sstr(adjoint(mul(A, B)))).toBe('Adjoint(B)*Adjoint(A)');
    expect(sstr(transpose(transpose(A)))).toBe('A');
    expect(sstr(transpose(add(A, B)))).toBe('A.T + B.T');
    expect(latex(transpose(A))).toBe('A^{T}');
  });
});

describe('construction', () => {
  it('validates dimensions and arguments', () => {
    expect(() => MatrixSymbol('A', symbol('q', { negative: true }), 2)).toThrow('The dimension specification q should be a nonnegative integer.');
    expect(() => MatrixSymbol('A', 1.5, 2)).toThrow('should be a nonnegative integer');
    expect(() => Transpose(2)).toThrow('2 is not a matrix');
    expect(() => MatAdd(A, MatrixSymbol('C', 2, 4))).toThrow('Matrices have mismatching shape: (3, 4)');
    expect(() => MatPow(2, 2)).toThrow('MatPow base should be a matrix');
    expect(() => Inverse(2)).toThrow('mat should be a matrix');
    expect(() => Inverse(A)).toThrow('Inverse of non-square matrix A');
    expect(() => Trace(2)).toThrow('input to Trace, 2, is not a matrix');
    expect(() => Determinant(2)).toThrow('Input to Determinant, 2, not a matrix');
    expect(() => Determinant(A)).toThrow('Det of a non-square matrix');
    expect(() => Permanent(2)).toThrow('Input to Permanent, 2, not a matrix');
    expect(() => ElementwiseApplyFunction(sin, 2)).toThrow('2 must be a matrix instance.');
    expect(() => ElementwiseApplyFunction(Lambda([x, y], x.add(y)), X)).toThrow('should be able to accept 1 arguments.');
    // SymPy only raises in as_coeff_matrices
    expect(() => MatMul(symbol('a', { commutative: false }), X)).toThrow('noncommutative scalars in MatMul are not supported.');
  });
  it('ImmutableMatrix from entries, a function or a matrix expression', () => {
    expect(s(ImmutableMatrix(2, 2, [1, 2, 3, 4]))).toBe('Matrix([[1, 2], [3, 4]])');
    expect(s(ImmutableMatrix(2, 2, (a, b) => a + b))).toBe('Matrix([[0, 1], [1, 2]])');
    expect(s(ImmutableMatrix(OneMatrix(2, 2)))).toBe('Matrix([[1, 1], [1, 1]])');
    expect(s(ImmutableMatrix(Matrix.zeros(0, 2)))).toBe('Matrix(0, 2, [])');
    expect(s(ImmutableMatrix(0))).toBe('Matrix(0, 0, [])');
    expect(latex(ImmutableMatrix(1, 11, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]))).toBe('\\left[\\begin{array}{ccccccccccc}0 & 1 & 2 & 3 & 4 & 5 & 6 & 7 & 8 & 9 & 10\\end{array}\\right]');
    expect(s(ImmutableMatrix([[x]]).subs(x, 2))).toBe('Matrix([[2]])');
    expect(s(Mi.at(-1, -1))).toBe('4');
    expect(Mi.isMatrixExpr).toBe(false);
    expect(X.isMatrixExpr).toBe(true);
    expect(X.isScalar).toBe(false);
    expect(s(Mi.doit({ deep: false }))).toBe('Matrix([[1, 2], [3, 4]])');
  });
  it('Str', () => {
    const a = new Str('a');
    expect(latex(a)).toBe('a');
    expect(a.withArgs()).toBe(a);
  });
});

describe('MatAdd', () => {
  it('special sums, adjoint and printing', () => {
    expect(s(MatAdd())).toBe('0');
    expect(s(M(Adjoint(MatAdd(X, Y))).doit())).toBe('Adjoint(X) + Adjoint(Y)');
    // SymPy MatrixExpr.canonicalize returns the expression itself
    expect(s(M(MatAdd(X, X, Y)).canonicalize())).toBe('X + X + Y');
    const nested = MatAdd(X, MatAdd(Y, Z));
    expect(s(nested)).toBe('(Y + Z) + X');
    expect(latex(nested)).toBe('\\left(Y + Z\\right) + X');
    expect(s(mergeExplicitMatAdd(X))).toBe('X');
    expect(s(mergeExplicitMatMul(X))).toBe('X');
    expect(s(transposeOf(x))).toBe('x');
    expect(s(negate(x))).toBe('-x');
  });
  it('orders the terms like SymPy', () => {
    expect(s(M(MatAdd(MatMul(x, X, Y), Z)).doit())).toBe('x*X*Y + Z');
    expect(s(MatAdd(MatMul(x.pow(2), X), Y))).toBe('x**2*X + Y');
    expect(s(MatAdd(MatMul(x, X), MatMul(y, Y)))).toBe('x*X + y*Y');
    expect(s(MatAdd(MatMul(ImagUnit, X), Y))).toBe('I*X + Y');
    expect(s(MatAdd(MatMul(y, X), MatMul(x, Y), MatMul(x.mul(y), Z)))).toBe('x*Y + y*X + (x*y)*Z');
    expect(s(MatAdd(X3.slice([null, 1]), MatrixSymbol('Y', 3, 3).slice([null, 1])))).toBe('X[:1, :] + Y[:1, :]');
  });
});

describe('MatMul', () => {
  it('special products', () => {
    expect(s(MatMul())).toBe('I');
    expect(s(MatMul(2, 3))).toBe('6');
    // SymPy MatrixExpr.canonicalize returns the expression itself
    expect(s(M(MatMul(X, Identity(2), X)).canonicalize())).toBe('X*I*X');
    expect(s(MatMul(UFunction('f')(), X))).toBe('f()*X');
    expect(s(M(MatMul(x, X)).subs(x, y))).toBe('y*X');
    expect(s(M(MatMul(X, MatAdd(Y, Y))).doit({ deep: false }))).toBe('X*(Y + Y)');
    expect(s(X.div(Y))).toBe('X*Y**(-1)');
    // the product rule of an expression free of x
    expect(s(M(MatMul(2, X)).diffSelf(x, diff))).toBe('0');
  });
  it('determinants of products', () => {
    const P = MatrixSymbol('P', n, m);
    const Q = MatrixSymbol('Q', m, k);
    expect(() => Determinant(P.mul(Q)).doit()).toThrow('Invalid matrices being multiplied');
    expect(s(Determinant(A.mul(B)).doit())).toBe('Determinant(A*B)');
    expect(s(Determinant(MatMul(X, Y)).doit({ deep: false }))).toBe('Determinant(X)*Determinant(Y)');
  });
  it('canonicalization rules', () => {
    expect(s(M(MatMul(MatAdd(X, Y), 2)).doit())).toBe('2*X + 2*Y');
    expect(s(M(MatMul(X, Y, Inverse(MatMul(X, Y)))).doit())).toBe('I');
    expect(s(M(MatMul(Inverse(MatMul(X, Y)), X, Y)).doit())).toBe('I');
    expect(s(M(MatMul(X, OneMatrix(2, 2))).doit())).toBe('X*1');
    expect(s(M(MatMul(Mi, 2)).doit())).toBe('Matrix([[2, 4], [6, 8]])');
    expect(s(M(MatMul(2, 3, Mi)).doit())).toBe('Matrix([[6, 12], [18, 24]])');
    expect(s(M(MatMul(2, Mi)).doit())).toBe('Matrix([[2, 4], [6, 8]])');
    expect(s(M(MatMul(PermutationMatrix([1, 0, 2]), PermutationMatrix([0, 2, 1]))).doit())).toBe('PermutationMatrix((0 2 1))');
  });
});

describe('MatPow and Inverse', () => {
  it('entries', () => {
    expect(s(Inverse(X).at(0, 0))).toBe('X[1, 1]/(X[0, 0]*X[1, 1] - X[0, 1]*X[1, 0])');
    expect(s(MatPow(W, k).at(0, 0))).toBe('(W**k)[0, 0]');
    expect(s(MatPow(X, 2).at(0, 1))).toBe('X[0, 0]*X[0, 1] + X[0, 1]*X[1, 1]');
    // SymPy writes the entry of X**k out with the eigenvalues of X; it is left unevaluated here
    expect(s(MatPow(X, k).at(0, 0))).toBe('(X**k)[0, 0]');
    const e = MatPow(X, -2).at(0, 1);
    const ref = X.at(0, 0).mul(X.at(0, 1)).add(X.at(0, 1).mul(X.at(1, 1))).neg().div(X.at(0, 0).mul(X.at(1, 1)).sub(X.at(0, 1).mul(X.at(1, 0))).pow(2));
    expect(s(e.sub(ref).simplify())).toBe('0');
  });
  it('doit, subs and printing', () => {
    expect(s(M(MatPow(X, n)).subs(n, 2))).toBe('X**2');
    expect(s(M(MatPow(MatPow(Mi, 2), 3)).doit({ deep: false }))).toBe('Matrix([[5743, 8370], [12555, 18298]])');
    expect(latex(MatPow(ImmutableMatrix([[x.pow(2)]]), 2))).toBe('\\left(\\left[\\begin{matrix}x^{2}\\end{matrix}\\right]\\right)^{2}');
  });
  it('derivatives', () => {
    // SymPy 1.14 raises TypeError (Mix of Matrix and Scalar symbols) for these derivatives
    expect(s(diff(MatPow(MatMul(x, X), 2), x))).toBe('(2*x)*X**2');
    expect(s(diff(MatPow(MatMul(x, X), -2), x))).toBe('(-2/x**3)*X**(-2)');
    expect(s(M(MatPow(MatAdd(MatMul(x, X), Y), -2)).diffSelf(x, diff))).toBe('-(x*X + Y)**(-1)*X*(x*X + Y)**(-2) - (x*X + Y)**(-2)*X*(x*X + Y)**(-1)');
    expect(s(diff(Inverse(MatMul(x, X)), x))).toBe('(-1/x**2)*X**(-1)');
    expect(s((Inverse(MatAdd(MatMul(x, X), Y)) as MatrixExpr).diffSelf(x, diff))).toBe('-(x*X + Y)**(-1)*X*(x*X + Y)**(-1)');
    // SymPy raises as well
    expect(() => diff(MatPow(MatMul(x, X), k), x)).toThrow('diff: MatPow does not define a derivative');
    expect(() => diff(MatPow(X, x), x)).toThrow('diff: MatPow does not define a derivative');
  });
});

describe('Transpose and Adjoint', () => {
  it('Transpose', () => {
    expect(s(M(Transpose(W)).subs(n, 2))).toBe('W.T');
    expect(s(M(Transpose(MatMul(X, Y))).doit({ deep: false }))).toBe('Y.T*X.T');
    expect(s(M(Transpose(X)).doit({ deep: false }))).toBe('X.T');
    // SymPy 1.14 gives X; the derivative of (x*X).T is X.T
    expect(s(diff(Transpose(MatMul(x, X)), x))).toBe('X.T');
    expect(latex(Transpose(ImmutableMatrix([[x.pow(2), 1]])))).toBe('\\left(\\left[\\begin{matrix}x^{2} & 1\\end{matrix}\\right]\\right)^{T}');
  });
  it('Adjoint', () => {
    expect(s(M(Adjoint(W)).subs(n, 2))).toBe('Adjoint(W)');
    expect(s(M(Adjoint(MatMul(X, Y))).doit({ deep: false }))).toBe('Adjoint(Y)*Adjoint(X)');
    expect(s(M(Adjoint(Adjoint(X))).doit())).toBe('X');
    expect(s(M(Transpose(Adjoint(X))).doit())).toBe('Adjoint(X.T)');
    expect(s(M(Adjoint(X)).conjugate())).toBe('X.T');
    expect(s(conjugate(Adjoint(X)))).toBe('X.T');
    expect(latex(Adjoint(MatMul(X, Y)))).toBe('\\left(X Y\\right)^{\\dagger}');
    expect(latex(MatMul(X, Adjoint(Y)))).toBe('X Y^{\\dagger}');
    // SymPy 1.14 raises AttributeError; for a real x the derivative of Adjoint(x*X) is Adjoint(X)
    const xr = symbol('xr', { real: true });
    expect(s(diff(Adjoint(MatMul(xr, X)), xr))).toBe('Adjoint(X)');
  });
});

describe('MatrixSlice', () => {
  it('normalizes and validates slices', () => {
    expect(s(X3.slice(-1))).toBe('X[2:, :]');
    expect(s(X3.slice([-2, -1]))).toBe('X[1:2, :]');
    expect(() => X3.slice([1, 1])).toThrow('Invalid slice');
    expect(() => X3.slice([0, 5])).toThrow('Invalid slice');
    const V = MatrixSymbol('V', symbol('p', { positive: true, integer: true }), symbol('p', { positive: true, integer: true }));
    const p = symbol('p', { positive: true, integer: true });
    expect(() => M(V.slice([0, p, 2])).slice([0, p])).toThrow('Invalid slice');
    expect(latex(X3.slice([0, 2, 2], [1, null]))).toBe('X\\left[:2:2, 1:\\right]');
    expect(s(X3.slice([1, 3, 2], [null, 2]))).toBe('X[1::2, :2]');
    expect(s(M(W.slice([0, k])).subs(k, 1))).toBe('W[:1, :]');
    expect(M(X3.slice([0, 2], [0, 2])) instanceof MatrixSliceNode).toBe(true);
  });
});

describe('Trace, Determinant and Permanent', () => {
  it('Trace', () => {
    const t = Trace(W).subs(n, 2) as TraceNode;
    expect(s(t)).toBe('Trace(W)');
    expect(t.arg.shape.map(s)).toEqual(['2', '2']);
    expect(s(Trace(Mi).doit({ deep: false }))).toBe('5');
    expect(s(Trace(X).doit({ deep: false }))).toBe('Trace(X)');
    expect(s(Trace(X).asExplicit())).toBe('X[0, 0] + X[1, 1]');
    expect(s(Trace(X).rewrite('Sum'))).toBe('X[0, 0] + X[1, 1]');
    expect(s(Trace(X).rewrite('sin'))).toBe('Trace(X)');
    expect(s(transpose(Trace(X)))).toBe('Trace(X)');
    // SymPy: Trace(X).diff(X[0, 0]) = 1. diff() replaces the element by a dummy
    // before differentiating, which misses it inside Trace(X); the handler is right
    expect(s((Trace(X) as TraceNode).diffSelf(X.at(0, 0), diff))).toBe('1');
    expect(s(Trace(MatrixSymbol('V', i, i)).rewrite('Sum'))).toBe('Sum(V[i0, i0], (i0, 0, i - 1))');
    expect(s(Trace(X).simplify())).toBe('Trace(X)');
    expect(s(Trace(X.mul(MatAdd(Y, Z))).expand())).toBe('Trace(X*Y + X*Z)');
    expect(s(M(MatMul(Trace(X).add(1), Y)).simplify())).toBe('(Trace(X) + 1)*Y');
    expect(s(diff(Trace(W), n))).toBe('0');
  });
  it('Determinant and Permanent', () => {
    expect(s(Determinant(W).subs(n, 2))).toBe('Determinant(W)');
    expect(s(Permanent(W).subs(n, 2))).toBe('Permanent(W)');
  });
});

describe('MatrixElement and derivatives of special matrices', () => {
  it('derivatives with respect to a dimension', () => {
    expect(s(diff(W, n))).toBe('0');
    // SymPy 1.14 raises AttributeError for these
    expect(s(diff(Identity(n), n))).toBe('0');
    expect(s(diff(ZeroMatrix(n, n), n))).toBe('0');
    expect(s(diff(W.at(0, 0), n))).toBe('0');
  });
  it('subs of the special matrices', () => {
    expect(s(ZeroMatrix(n, 2).subs(n, 3))).toBe('0');
    expect(M(ZeroMatrix(n, 2).subs(n, 3)).shape.map(s)).toEqual(['3', '2']);
    expect(M(OneMatrix(n, 2).subs(n, 3)).shape.map(s)).toEqual(['3', '2']);
  });
  it('MatrixElement doit', () => {
    expect(s((MatrixElement(X, 0, 1) as MatrixElementNode).doit({ deep: false }))).toBe('X[0, 1]');
    const e = X.at(0, 1) as MatrixElementNode;
    expect(s(e.diffSelf(X.at(0, 1), diff))).toBe('1');
    expect(s(e.diffSelf(X.at(1, 1), diff))).toBe('0');
    expect(s(e.diffSelf(MatrixSymbol('B', 2, 2).at(0, 0), diff))).toBe('0');
    expect(new MatrixElementNode(MatMul(X, A), S.Zero, S.Zero).diffSelf(X.at(0, 0), diff)).toBe(undefined);
    expect(s(new MatrixElementNode(MatMul(x, W), S.Zero, S.Zero).diffSelf(x, diff))).toBe('W[0, 0]');
    expect(new MatrixElementNode(MatPow(X, x), S.Zero, S.Zero).diffSelf(x, () => x)).toBe(undefined);
    const bad = new MatrixElementNode(x, S.Zero, S.Zero);
    expect(bad.doit()).toBe(bad);
    expect(bad.diffSelf(x, diff)).toBe(undefined);
  });
});

describe('ElementwiseApplyFunction', () => {
  it('construction and doit', () => {
    expect(s(X.applyfunc(Lambda(x, x.pow(2))))).toBe('Lambda(x, x**2).(X)');
    expect(s(MatrixSymbol('V', 1, 1).applyfunc(Lambda(x, x)))).toBe('V');
    // SymPy prints Lambda(_x, _x).(X): its IdentityFunction reports is_identity False
    expect(s(M(ElementwiseApplyFunction(Lambda(x, x), X)).doit())).toBe('X');
    expect(M(ElementwiseApplyFunction(sin, W).subs(n, 2)).shape.map(s)).toEqual(['2', '2']);
    expect(s(M(ElementwiseApplyFunction(sin, MatMul(X, Y))).doit({ deep: false }))).toBe('Lambda(_d, sin(_d)).(X*Y)');
    expect(s(M(ElementwiseApplyFunction(sin, X)).doit())).toBe('Lambda(_d, sin(_d)).(X)');
    expect(s(M(ElementwiseApplyFunction(sin, ElementwiseApplyFunction(cos, X))).doit())).toBe('Lambda(_d, sin(cos(_d))).(X)');
  });
});

describe('defaults and remaining paths', () => {
  /** A matrix expression with only the required members (the defaults of MatrixExpr). */
  class Bare extends MatrixExpr {
    constructor(args: readonly Expr[] = []) {
      super('Bare', args);
    }
    get shape(): [Expr, Expr] {
      return [S.One, S.One];
    }
    withArgs(args: readonly Expr[]): Expr {
      return new Bare(args);
    }
  }
  /** A matrix scalar with only the required members (the defaults of MatScalar). */
  class BareScalar extends MatScalar {
    constructor(a: Expr) {
      super('BareScalar', [a]);
    }
    withArgs(args: readonly Expr[]): Expr {
      return new BareScalar(args[0] ?? S.Zero);
    }
  }
  it('the base class defaults', () => {
    const b = new Bare();
    expect(() => b.at(0, 0)).toThrow('Indexing not implemented for Bare');
    expect(b.diffSelf(x, diff)).toBe(undefined);
    expect(b.doit({ deep: false })).toBe(b);
    expect(doit(b)).toBe(b);
    expect(s(new Bare([MatAdd(X, X)]).doit())).toBe('Bare(2*X)');
    const bs = new BareScalar(Trace(MatAdd(X, X)));
    expect(bs.doit({ deep: false })).toBe(bs);
    expect(s(bs.doit())).toBe('BareScalar(2*Trace(X))');
    // SymPy: doit is deep, so the trace of 2*X is 2*Trace(X) (f(Trace(2*X)).doit() = f(2*Trace(X)))
    expect(s(doit(bs))).toBe('BareScalar(2*Trace(X))');
    const bx = new BareScalar(x);
    expect(bx.doit()).toBe(bx);
    expect(M(X.applyfunc(sin)).diffSelf(x, diff)).toBe(undefined);
  });
  it('doit of MatrixSymbol and equalsExplicit with a symbolic shape', () => {
    expect(X.doit({ deep: false })).toBe(X);
    expect(s(doit(X))).toBe('X');
    expect(X.equalsExplicit(W)).toBe(false);
  });
  it('sort keys of products with several scalar factors', () => {
    expect(s(M(MatAdd(MatMul(x, y, X), Z)).doit({ deep: false }))).toBe('(x*y)*X + Z');
    expect(s(MatAdd(new MatMulNode([X, new MatMulNode([x, y, Y])]), Z))).toBe('X*(x*y*Y) + Z');
    expect(s(M(MatMul(Trace(X).add(1), Y)).expand())).toBe('(Trace(X) + 1)*Y');
  });
  it('MatPow with explicit and special bases', () => {
    expect(s(MatPow(X, 1).at(0, 0))).toBe('X[0, 0]');
    // SymPy diagonalizes the matrix; the power with a symbolic exponent is kept unevaluated
    expect(s(M(MatPow(Mi, x)).doit())).toBe('Matrix([[1, 2], [3, 4]])**x');
    expect(() => M(MatPow(OneMatrix(2, 2), -2)).doit()).toThrow('Matrix det == 0; not invertible');
    expect(() => M(MatPow(ZeroMatrix(2, 2), -2)).doit()).toThrow('Matrix det == 0; not invertible');
    expect(s(Determinant(OneMatrix(1, 1)).doit({ deep: false }))).toBe('1');
    expect(s(Inverse(OneMatrix(1, 1)).doit({ deep: false }))).toBe('I');
    expect(s(M(MatPow(OneMatrix(1, 1), 5)).doit({ deep: false }))).toBe('I');
    expect(s(OneMatrix(2, 2).doit({ deep: false }))).toBe('1');
    expect(s(diff(OneMatrix(n, n), n))).toBe('0');
  });
  it('products with inverses of products', () => {
    expect(s(M(MatMul(X, Y, Inverse(MatMul(X, Y)))).doit({ deep: false }))).toBe('I');
    expect(s(M(MatMul(Inverse(MatMul(X, Y)), X, Y)).doit({ deep: false }))).toBe('I');
  });
  it('merge_explicit of a product', () => {
    expect(s(mergeExplicitMatMul(MatMul(Mi, 2)))).toBe('Matrix([[2, 4], [6, 8]])');
    expect(s(mergeExplicitMatMul(MatMul(2, 3, Mi)))).toBe('Matrix([[6, 12], [18, 24]])');
  });
  it('generic identity and zero', () => {
    expect(GenericIdentity().key).toBe('GenericIdentity()');
    expect(GenericZeroMatrix().key).toBe('GenericZeroMatrix()');
    expect(GenericIdentity().withArgs()).toEqual(GenericIdentity());
    expect(GenericZeroMatrix().withArgs()).toEqual(GenericZeroMatrix());
  });
  it('substituting a scalar for the matrix', () => {
    expect(s(M(Transpose(X).subs(X, x)).doit())).toBe('x');
  });
  it('Trace.rewrite with a used name and ElementwiseApplyFunction.doit', () => {
    const [i0] = symbols('i0');
    expect(s(Trace(MatrixSymbol('V', i.add(i0), i.add(i0))).rewrite('Sum'))).toBe('Sum(V[i1, i1], (i1, 0, i + i0 - 1))');
    expect(s(M(ElementwiseApplyFunction(sin, MatAdd(X, X))).doit())).toBe('Lambda(_d, sin(_d)).(2*X)');
  });
  it('ImmutableMatrix with missing entries', () => {
    expect(s(ImmutableMatrix(2, 2))).toBe('Matrix([[0, 0], [0, 0]])');
    expect(s(ImmutableMatrix(2, 2, [1]))).toBe('Matrix([[1, 0], [0, 0]])');
    expect(s(ImmutableMatrix(2))).toBe('Matrix(2, 0, [])');
  });
});

describe('MatrixExpr indexing', () => {
  it('det and single indices', () => {
    expect(s(X.det())).toBe('Determinant(X)');
    expect(s(X.at(1))).toBe('X[0, 1]');
    expect(s(X.at(-1))).toBe('X[-1, 1]');
    expect(() => X.at(5)).toThrow('Invalid index 5');
    expect(() => Yn.at(1)).toThrow('Single indexing is only supported when the number of columns is known.');
    expect(() => X.at(x)).toThrow('Only integers may be used');
    expect(() => X.at(3, 0)).toThrow('Invalid indices (3, 0)');
  });
  it('equalsExplicit', () => {
    expect(X.equalsExplicit(X)).toBe(true);
    expect(X.equalsExplicit(1)).toBe(false);
    expect(X.equalsExplicit(A)).toBe(false);
    expect(ImmutableMatrix([[1, 2]]).equalsExplicit(ImmutableMatrix([[1], [2]]))).toBe(false);
  });
});

describe('ImmutableMatrix', () => {
  const Mx = ImmutableMatrix([
    [1, x],
    [ImagUnit, 2],
  ]);
  it('adjoint, conjugate, inverse and powers', () => {
    expect(s(Mx.adjoint())).toBe('Matrix([[1, -I], [conjugate(x), 2]])');
    expect(s(Mx.conjugate())).toBe('Matrix([[1, conjugate(x)], [-I, 2]])');
    // SymPy prints Matrix([[2*I/(x + 2*I), -I*x/(x + 2*I)], [1/(x + 2*I), I/(x + 2*I)]]), the same entries
    const inv = ImmutableMatrix([
      [ImagUnit.mul(2).div(x.add(ImagUnit.mul(2))), ImagUnit.mul(x).neg().div(x.add(ImagUnit.mul(2)))],
      [x.add(ImagUnit.mul(2)).pow(-1), ImagUnit.div(x.add(ImagUnit.mul(2)))],
    ]);
    expect(M(Mx.inv()).equalsExplicit(inv)).toBe(true);
    expect(M(Mx.pow(-1)).equalsExplicit(inv)).toBe(true);
    // SymPy: Matrix([[(-I*x - 4)/(x**2 + 4*I*x - 4), 3*x/(x**2 + 4*I*x - 4)], [3*I/(x**2 + 4*I*x - 4), (-I*x - 1)/(x**2 + 4*I*x - 4)]])
    const d = x.pow(2).add(ImagUnit.mul(4).mul(x)).sub(4);
    const inv2 = ImmutableMatrix([
      [ImagUnit.mul(x).neg().sub(4).div(d), x.mul(3).div(d)],
      [ImagUnit.mul(3).div(d), ImagUnit.mul(x).neg().sub(1).div(d)],
    ]);
    expect(M(M(MatPow(Mx, -2)).doit()).equalsExplicit(inv2)).toBe(true);
  });
  it('simplify, expand and diff', () => {
    expect(s(ImmutableMatrix([[sin(x).pow(2).add(cos(x).pow(2))]]).simplify())).toBe('Matrix([[1]])');
    expect(s(ImmutableMatrix([[x.add(1).pow(2)]]).expand())).toBe('Matrix([[x**2 + 2*x + 1]])');
    expect(s(diff(ImmutableMatrix([[x.pow(2), x]]), x))).toBe('Matrix([[2*x, 1]])');
  });
});

describe('MatrixElement', () => {
  it('indices, doit and diff', () => {
    const e = MatrixElement(X, 0, 1);
    expect((e as never as { indices: Expr[] }).indices.map(s)).toEqual(['0', '1']);
    expect(s(M(X).at(0, 1))).toBe('X[0, 1]');
    expect(s(diff(MatrixElement(X, x, y), x))).toBe('0');
    expect(s(diff(X.at(0, 1), MatrixSymbol('B', 2, 2).at(0, 0) as never))).toBe('0');
    expect(s(diff(M(X.mul(A)).at(0, 1), X.at(0, 0) as never))).toBe('A[0, 1]');
    expect(() => MatrixElement(1, 0, 0)).toThrow('First argument of MatrixElement should be a matrix');
    expect(() => MatrixElement(X, 5, 0)).toThrow('indices out of range');
  });
});

describe('special matrices', () => {
  it('Identity, GenericIdentity and GenericZeroMatrix', () => {
    const I3 = Identity(3);
    expect(s(I3.conjugate())).toBe('I');
    expect(s(diff(I3, x))).toBe('0');
    expect(s(I3.adjoint())).toBe('I');
    expect(s(GenericIdentity())).toBe('I');
    expect(s(GenericZeroMatrix())).toBe('0');
    expect(latex(GenericIdentity())).toBe('\\mathbb{I}');
    expect(() => GenericIdentity().shape).toThrow('GenericIdentity does not have a specified shape');
    expect(() => GenericZeroMatrix().shape).toThrow('GenericZeroMatrix does not have a specified shape');
  });
  it('ZeroMatrix', () => {
    const Z = ZeroMatrix(2, 3);
    expect(s(Z.adjoint())).toBe('0');
    expect(s(Trace(ZeroMatrix(2, 2)).doit())).toBe('0');
    expect(s(Determinant(ZeroMatrix(2, 2)).doit())).toBe('0');
    expect(s(Z.conjugate())).toBe('0');
    expect(s(Z.at(0, 1))).toBe('0');
    expect(s(diff(Z, x))).toBe('0');
    expect(s(M(MatPow(ZeroMatrix(2, 2), 2)).doit())).toBe('0');
    expect(() => M(MatPow(ZeroMatrix(2, 2), -1)).doit()).toThrow('Matrix det == 0; not invertible');
  });
  it('OneMatrix', () => {
    const O = OneMatrix(2, 3);
    const O2 = OneMatrix(2, 2);
    expect(String(O.asExplicit())).toBe('Matrix([[1, 1, 1], [1, 1, 1]])');
    expect(s(O.adjoint())).toBe('1');
    expect(s(O.conjugate())).toBe('1');
    expect(s(O.at(0, 0))).toBe('1');
    expect(s(diff(O, x))).toBe('0');
    expect(s(M(MatPow(O2, 3)).doit())).toBe('4*1');
    expect(s(M(MatPow(O2, x)).doit())).toBe('1**x');
    expect(s(Determinant(O2).doit())).toBe('0');
    expect(s(Determinant(OneMatrix(n, n)).doit())).toBe('Determinant(1)');
    expect(s(Inverse(OneMatrix(n, n)).doit())).toBe('1**(-1)');
    expect(s(M(MatPow(OneMatrix(1, 1), 5)).doit())).toBe('I');
    expect(s(OneMatrix(1, n).T)).toBe('1');
    expect(() => OneMatrix(n, 2).asExplicit()).toThrow(RangeError);
    expect(() => M(MatPow(O2, -1)).doit()).toThrow('Matrix det == 0; not invertible');
    expect(() => O2.inverse()).toThrow('Matrix det == 0; not invertible');
  });
});

describe('matrix expressions', () => {

  it('nodes rebuilt from their arguments are equal (SymPy e.func(*e.args) == e)', () => {
    const [n] = sj.symbols('n');
    const X = sj.MatrixSymbol('X', n, n);
    const sl = cast(X.slice([0, n], [0, 2]), MatrixExpr);
    for (const t of sl.sortArgs()) expect(rebuild(t, t.args).key).toBe(t.key);
    const B = cast(sj.BlockMatrix([[X, X], [X, X]]), MatrixExpr);
    for (const t of B.sortArgs()) expect(rebuild(t, t.args).key).toBe(t.key);
    const P = sj.PermutationMatrix([1, 0, 2]);
    expect(rebuild(P, P.args).key).toBe(P.key);
    const p = P.args[0];
    if (p === undefined) throw new Error('no argument');
    expect(rebuild(p, p.args).key).toBe(p.key);
  });
});

describe('evalf of a matrix element', () => {
  it('evaluates the element of an explicit matrix expression (SymPy MatPow(M, 2)[0, 1].evalf() = 10.0)', () => {
    const M = ImmutableMatrix([[1, 2], [3, 4]]);
    expect(String(sj.evalf(MatrixElement(MatPow(M, 2), 0, 1)))).toBe('10.0000000000000');
    const [i] = symbols('i', { integer: true });
    // an element with a symbolic index stays an element (SymPy keeps the integer entries: Matrix([[1, 2], [3, 4]])[i, 0])
    expect(String(sj.evalf(MatrixElement(M, i as sj.Expr, 0)))).toBe('Matrix([[1.0, 2.0], [3.0, 4.0]])[i, 0]');
  });
});

describe('Expr methods of matrix expressions (SymPy MatrixExpr derives from Expr)', () => {
  const A = MatrixSymbol('A', 2, 2);
  const B = MatrixSymbol('B', 2, 2);
  const C = MatrixSymbol('C', 2, 2);
  const [x, n] = symbols('x n');
  const show = (r: unknown): string => (Array.isArray(r) ? `[${r.map(show).join(', ')}]` : r instanceof Map ? `{${[...r].map(([k, v]) => `${show(k)}: ${show(v)}`).join(', ')}}` : String(r));
  it('core arithmetic builds MatAdd, MatMul and MatPow (SymPy constructor postprocessors)', () => {
    expect(sj.add(A, B)).toBeInstanceOf(MatrixExpr);
    expect(s(sj.add(A, B))).toBe('A + B');
    expect(s(sj.mul(2, x, A, B))).toBe('(2*x)*A*B');
    expect(sj.mul(2, x, A, B)).toBeInstanceOf(MatMulNode);
    expect(s(sj.sub(A, B))).toBe('A - B');
    expect(s(sj.pow(A, 2))).toBe('A**2');
    // a sum of a scalar and a matrix stays an Add (SymPy Add(x, A) is x + A)
    expect(s(sj.add(x, A))).toBe('x + A');
    expect(sj.add(x, A)).not.toBeInstanceOf(MatrixExpr);
    expect(s(sj.sub(x, A))).toBe('x - A');
    expect(s(sj.pow(2, A))).toBe('2**A');
  });
  it('fromiter', () => {
    // SymPy MatAdd.fromiter([A, B]) and MatMul.fromiter([2, A])
    expect(s(sj.Expr.fromiter.call(cast(MatAdd(A, B), MatrixExpr).constructor as typeof MatrixExpr, [A, B]))).toBe('A + B');
    expect(s(MatMulNode.fromiter([2, A]))).toBe('2*A');
    expect(() => MatrixExpr.fromiter([A])).toThrow(sj.NotImplementedError);
  });
  it('structural methods treat MatAdd as a sum and MatMul as a product', () => {
    // SymPy 1.14 values
    expect(show(sj.argsCnc(sj.mul(2, x, A, B)))).toBe('[2*x]');
    expect(show(sj.asCoeffAdd(A.add(B)))).toBe('[0, [A, B]]');
    expect(show(sj.asCoeffMul(A.mul(2)))).toBe('[2, [A]]');
    expect(show(sj.asCoeffMul(sj.mul(2, x, A, B)))).toBe('[1, [2*x, A, B]]');
    expect(s(sj.asCoefficient(sj.mul(2, x, A), x))).toBe('2*A');
    // SymPy (2*x*A).as_coefficient(A) raises NotImplementedError; 2*x is the coefficient
    expect(s(sj.asCoefficient(sj.mul(2, x, A), A))).toBe('2*x');
    expect(show(sj.asCoefficientsDict(sj.add(sj.mul(2, A), sj.mul(3, B))))).toBe('{2*A: 1, 3*B: 1}');
    expect(show(sj.asContentPrimitive(sj.mul(2, A)))).toBe('[2, A]');
    expect(show(sj.primitive(sj.mul(2, A)))).toBe('[1, 2*A]');
    expect(show(sj.asIndependent(sj.mul(x, A, B), [x]))).toBe('[1, x*A*B]');
    expect(show(sj.asIndependent(sj.add(A, sj.mul(x, B)), [x]))).toBe('[0, x*B + A]');
    expect(show(sj.asNumerDenom(A.mul(B)))).toBe('[A*B, 1]');
    // SymPy (1*A, x): MatMul(1, A) is A
    expect(show(sj.asNumerDenom(A.div(x)))).toBe('[A, x]');
    expect(show(sj.asPowersDict(A.mul(B)))).toBe('{A: 1, B: 1}');
    expect(show(sj.asPowersDict(A.pow(2)))).toBe('{A**2: 1}');
    expect(show(sj.asTerms(A.add(B)))).toBe('[[[A, [[1, 0], [], [A]]], [B, [[1, 0], [], [B]]]], []]');
    expect(s(sj.coeff(sj.add(sj.mul(2, A), sj.mul(3, B)), A))).toBe('2');
    expect([sj.couldExtractMinusSign(A.neg()), sj.couldExtractMinusSign(A), sj.couldExtractMinusSign(A.neg().mul(B))]).toEqual([true, false, true]);
    expect(s(sj.extractMultiplicatively(A.mul(2), 2))).toBe('A');
    // SymPy (A + B).extract_additively(A) exceeds the recursion depth
    expect(s(sj.extractAdditively(A.add(B), A))).toBe('B');
    expect([sj.isPolynomial(A.mul(B)), sj.isPolynomial(x.mul(A), [x]), sj.isRationalFunction(A.div(x), [x]), sj.isAlgebraicExpr(A.mul(B))]).toEqual([true, true, true, true]);
    expect(sj.isMeromorphic(x.mul(A), x, 0)).toBe(true);
  });
  it('count_ops', () => {
    expect([A.add(B), A.mul(B), sj.add(sj.mul(2, A, B), C), A.pow(2), A.T, Inverse(A), A.neg(), A.sub(B)].map((e) => sj.countOps(e))).toEqual([1, 1, 3, 0, 0, 1, 1, 1]);
    expect(s(sj.countOps(sj.add(sj.mul(2, A, B), C), { visual: true }))).toBe('ADD + 2*MATMUL');
    expect(s(sj.countOps(A.neg().mul(B), { visual: true }))).toBe('MATMUL + NEG');
    expect(s(sj.countOps(A.div(x), { visual: true }))).toBe('DIV');
  });
  it('as_real_imag, evalf and the methods without structure', () => {
    expect(show(sj.asRealImag(A))).toBe('[(1/2)*Adjoint(A.T) + (1/2)*A, -(I/2)*(-Adjoint(A.T) + A)]');
    expect(s(A.evalf())).toBe('A');
    expect(s(sj.asDummy(A.mul(B)))).toBe('A*B');
    expect(s(sj.asExpr(A.mul(B)))).toBe('A*B');
    expect(s(sj.copy(A.mul(B)))).toBe('A*B');
    expect(s(sj.normal(A.mul(B)))).toBe('A*B');
    expect(s(sj.removeO(A.mul(B)))).toBe('A*B');
    expect(sj.getO(A.mul(B))).toBe(sj.NoMatch);
    expect(s(sj.rcall(A.mul(B), x))).toBe('A*B');
    expect([sj.compare(A, B), sj.compare(B, A), sj.compare(A.mul(B), A)]).toEqual([-1, 1, -1]);
    expect(sj.asPoly(A.add(B))).toBe(sj.NoMatch);
    // SymPy A.invert(B) raises PolynomialError (non-commutative expressions)
    expect(() => sj.invert(A, B)).toThrow(sj.PolynomialError);
    expect(sj.isHypergeometric(A, n)).toBe(true);
  });
});

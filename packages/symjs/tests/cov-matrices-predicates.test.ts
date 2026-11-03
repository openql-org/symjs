// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * Coverage of the matrix predicates (askMatrix, askInvertible,
 * refineMatrix) with the expected values of SymPy 1.14 ask and refine.
 * SymPy's None is 'unknown'.
 */

import { describe, expect, it } from 'vitest';
import { sstr, symbol } from '../src';
import type { Expr } from '../src';
import {
  Adjoint,
  BlockDiagMatrix,
  Determinant as Det,
  DiagMatrix,
  DiagonalMatrix,
  Identity,
  ImmutableMatrix,
  MatAdd,
  MatMul,
  MatPow,
  MatrixQ,
  MatrixSymbol,
  OneMatrix,
  Transpose,
  ZeroMatrix,
  askMatrix,
  refineMatrix,
} from '../src/matrices/expressions';
import { askInvertible } from '../src/matrices/expressions/predicates';

const s = (e: Expr): string => sstr(e);
const X = MatrixSymbol('X', 3, 3);
const Y = MatrixSymbol('Y', 3, 3);
const A = MatrixSymbol('A', 2, 3);
const I3 = Identity(3);
const Z = ZeroMatrix(3, 3);
const k = symbol('k');
const m = symbol('m', { integer: true, negative: true });

describe('askMatrix', () => {
  it('prints a predicate like SymPy', () => {
    expect(String(MatrixQ.orthogonal(X))).toBe('Q.orthogonal(X)');
  });
  it('is false for a non-matrix', () => {
    expect(askMatrix(MatrixQ.symmetric(2))).toBe(false);
  });
  it('orthogonal and unitary', () => {
    expect(askMatrix(MatrixQ.orthogonal(I3))).toBe(true);
    expect(askMatrix(MatrixQ.orthogonal(Z))).toBe(false);
    expect(askMatrix(MatrixQ.unitary(X), MatrixQ.orthogonal(X))).toBe(true);
    expect(askMatrix(MatrixQ.orthogonal(X.T), MatrixQ.orthogonal(X))).toBe(true);
    expect(askMatrix(MatrixQ.orthogonal(X.I), MatrixQ.orthogonal(X))).toBe(true);
    // SymPy gives None; the adjoint of a unitary matrix is unitary
    expect(askMatrix(MatrixQ.unitary(Adjoint(X)), MatrixQ.unitary(X))).toBe(true);
    const both = [MatrixQ.orthogonal(X), MatrixQ.orthogonal(Y)];
    expect(askMatrix(MatrixQ.orthogonal(X.mul(Y)), both)).toBe(true);
    expect(askMatrix(MatrixQ.orthogonal(MatMul(2, X, Y)), both)).toBe('unknown');
    expect(askMatrix(MatrixQ.orthogonal(MatPow(X, 2)), MatrixQ.orthogonal(X))).toBe(true);
    expect(askMatrix(MatrixQ.orthogonal(MatAdd(X, Y)), both)).toBe('unknown');
    expect(askMatrix(MatrixQ.orthogonal(X.mul(Y)), MatrixQ.orthogonal(X))).toBe('unknown');
  });
  it('symmetric', () => {
    expect(askMatrix(MatrixQ.symmetric(A))).toBe(false);
    expect(askMatrix(MatrixQ.symmetric(I3))).toBe(true);
    expect(askMatrix(MatrixQ.symmetric(Z))).toBe(true);
    expect(askMatrix(MatrixQ.symmetric(X), MatrixQ.diagonal(X))).toBe(true);
    expect(askMatrix(MatrixQ.symmetric(X.T), MatrixQ.symmetric(X))).toBe(true);
    expect(askMatrix(MatrixQ.symmetric(X.I), MatrixQ.symmetric(X))).toBe(true);
    const both = [MatrixQ.symmetric(X), MatrixQ.symmetric(Y)];
    expect(askMatrix(MatrixQ.symmetric(MatAdd(X, Y)), both)).toBe(true);
    // SymPy gives False; X + Y may be symmetric (Y symmetric) or not, so it is unknown
    expect(askMatrix(MatrixQ.symmetric(MatAdd(X, Y)), MatrixQ.symmetric(X))).toBe('unknown');
    expect(askMatrix(MatrixQ.symmetric(MatMul(X, Y, X)), both)).toBe(true);
    // SymPy gives True; (X*Y).T = Y*X, which differs from X*Y for symmetric X, Y that do not commute
    expect(askMatrix(MatrixQ.symmetric(X.mul(Y)), both)).toBe('unknown');
    expect(askMatrix(MatrixQ.symmetric(MatPow(X, 2)), MatrixQ.symmetric(X))).toBe(true);
    expect(askMatrix(MatrixQ.symmetric(MatPow(X, k)), MatrixQ.symmetric(X))).toBe('unknown');
  });
  it('diagonal and triangular', () => {
    expect(askMatrix(MatrixQ.diagonal(I3))).toBe(true);
    expect(askMatrix(MatrixQ.diagonal(Z))).toBe(true);
    expect(askMatrix(MatrixQ.diagonal(X.T), MatrixQ.diagonal(X))).toBe(true);
    expect(askMatrix(MatrixQ.diagonal(X.I), MatrixQ.diagonal(X))).toBe(true);
    expect(askMatrix(MatrixQ.diagonal(DiagMatrix(MatrixSymbol('v', 3, 1))))).toBe(true);
    expect(askMatrix(MatrixQ.diagonal(DiagonalMatrix(X)))).toBe(true);
    expect(askMatrix(MatrixQ.diagonal(X))).toBe('unknown');
    expect(askMatrix(MatrixQ.upper_triangular(I3))).toBe(true);
    expect(askMatrix(MatrixQ.upper_triangular(X), MatrixQ.diagonal(X))).toBe(true);
    expect(askMatrix(MatrixQ.lower_triangular(X))).toBe('unknown');
    expect(askMatrix(MatrixQ.lower_triangular(Z))).toBe(true);
    // SymPy gives None; the identity is unit triangular
    expect(askMatrix(MatrixQ.unit_triangular(I3))).toBe(true);
    expect(askMatrix(MatrixQ.unit_triangular(X))).toBe('unknown');
    expect(askMatrix(MatrixQ.positive_definite(I3))).toBe(true);
    expect(askMatrix(MatrixQ.positive_definite(X))).toBe('unknown');
    // SymPy gives None for both; a diagonal matrix is symmetric and triangular
    expect(askMatrix(MatrixQ.symmetric(DiagonalMatrix(X)))).toBe(true);
    expect(askMatrix(MatrixQ.lower_triangular(DiagMatrix(MatrixSymbol('v', 3, 1))))).toBe(true);
    expect(askMatrix(MatrixQ.unitary(X.T), MatrixQ.orthogonal(X))).toBe(true);
    expect(askMatrix(MatrixQ.singular(X), MatrixQ.square(X))).toBe('unknown');
    expect(askMatrix(MatrixQ.symmetric(X.mul(X.T)))).toBe(true);
  });
  it('square, fullrank and singular', () => {
    expect(askMatrix(MatrixQ.square(A))).toBe(false);
    expect(askMatrix(MatrixQ.square(X))).toBe(true);
    expect(askMatrix(MatrixQ.fullrank(X), MatrixQ.orthogonal(X))).toBe(true);
    expect(askMatrix(MatrixQ.fullrank(X.I))).toBe(true);
    expect(askMatrix(MatrixQ.fullrank(X))).toBe('unknown');
    expect(askMatrix(MatrixQ.singular(X), MatrixQ.invertible(X))).toBe(false);
    expect(askMatrix(MatrixQ.singular(X), MatrixQ.orthogonal(X))).toBe(false);
    expect(askMatrix(MatrixQ.invertible(X), MatrixQ.singular(X))).toBe(false);
    expect(askMatrix(MatrixQ.invertible(X), MatrixQ.symmetric(Y))).toBe('unknown');
    expect(askMatrix(MatrixQ.singular(X))).toBe('unknown');
    // SymPy gives None; the zero matrix is singular
    expect(askMatrix(MatrixQ.singular(Z))).toBe(true);
  });
});

describe('askInvertible', () => {
  const inv = (e: Expr, ...as: Parameters<typeof MatrixQ.invertible>[0][]): unknown => askMatrix(MatrixQ.invertible(e), as.map((a) => MatrixQ.invertible(a)));
  it('follows the SymPy handlers', () => {
    expect(askInvertible(k)).toBe('unknown');
    expect(inv(MatMul(0, X))).toBe(false);
    expect(inv(X.mul(Y), X, Y)).toBe(true);
    expect(inv(X.mul(Y), X)).toBe('unknown');
    expect(inv(X.mul(Y), X.mul(Y))).toBe(true);
    expect(inv(X.I)).toBe(true);
    expect(inv(MatPow(X, k), X)).toBe('unknown');
    expect(inv(MatPow(X, 2), X)).toBe(true);
    expect(inv(MatPow(X, m), X)).toBe('unknown');
    expect(inv(MatPow(X, 2))).toBe('unknown');
    expect(inv(MatAdd(X, Y), MatAdd(X, Y))).toBe(true);
    expect(inv(MatAdd(X, Y))).toBe('unknown');
    expect(inv(OneMatrix(1, 1))).toBe(true);
    expect(inv(OneMatrix(3, 3))).toBe(false);
    expect(inv(Transpose(X), X)).toBe(true);
    // SymPy gives None; the adjoint of an invertible matrix is invertible
    expect(inv(Adjoint(X), X)).toBe(true);
    expect(inv(X.slice([null, null], [null, null]), X)).toBe(true);
    // SymPy gives True: a leading principal submatrix of an invertible matrix
    // may be singular (X = [[0, 1], [1, 0]]), so it is unknown
    expect(inv(X.slice([0, 2], [0, 2]), X)).toBe('unknown');
    expect(inv(X.slice([0, 2], [1, 3]), X)).toBe('unknown');
    expect(inv(X.slice([0, 2], [1, 3]), X.slice([0, 2], [1, 3]))).toBe(true);
    expect(inv(A)).toBe(false);
    expect(inv(X)).toBe('unknown');
    expect(inv(ImmutableMatrix([[1, 2], [3, 4]]))).toBe(true);
    expect(inv(ImmutableMatrix([[1, 2], [2, 4]]))).toBe(false);
    // SymPy gives True; the determinant k - 1 is zero for k = 1
    expect(inv(ImmutableMatrix([[k, 1], [1, 1]]))).toBe('unknown');
    expect(inv(BlockDiagMatrix(X, Y), X, Y)).toBe(true);
    expect(inv(BlockDiagMatrix(X, Y), X)).toBe('unknown');
    expect(inv(DiagonalMatrix(X))).toBe('unknown');
    expect(inv(BlockDiagMatrix(X, ZeroMatrix(2, 2)))).toBe(false);
  });
});

describe('refineMatrix', () => {
  it('follows the SymPy refine handlers', () => {
    expect(s(refineMatrix(MatMul(2, X, X.T, Y), MatrixQ.orthogonal(X)))).toBe('2*I*Y');
    expect(s(refineMatrix(MatMul(X, Y, X.T), MatrixQ.orthogonal(X)))).toBe('X*Y*X.T');
    expect(s(refineMatrix(X.T.mul(X), MatrixQ.orthogonal(X)))).toBe('I');
    expect(s(refineMatrix(Det(X), MatrixQ.unit_triangular(X)))).toBe('1');
    expect(s(refineMatrix(Det(X)))).toBe('Determinant(X)');
    expect(s(refineMatrix(X.I))).toBe('X**(-1)');
    expect(s(refineMatrix(X.I, MatrixQ.singular(X)))).toBe('X**(-1)');
    expect(() => refineMatrix(X.I, MatrixQ.singular(X.I))).toThrow('Inverse of singular matrix X');
    expect(s(refineMatrix(MatAdd(X.T, Y), MatrixQ.symmetric(X)))).toBe('X + Y');
    expect(s(refineMatrix(Transpose(X.mul(Y)), MatrixQ.symmetric(X.mul(Y))))).toBe('X*Y');
    expect(s(refineMatrix(k))).toBe('k');
    expect(s(refineMatrix(Det(X).add(1), MatrixQ.orthogonal(X)))).toBe('2');
  });
});

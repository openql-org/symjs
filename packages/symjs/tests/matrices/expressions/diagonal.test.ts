// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/matrices/expressions/diagonal.ts.
//
// DiagonalMatrix, DiagonalOf, DiagMatrix and diagonalize_vector. Expected values are SymPy 1.14
// results (explicit matrices printed on one line).

import { describe, expect, it } from 'vitest';
import { type Expr, Matrix, sstr, symbol, symbols } from '../../../src';
import { DiagMatrix, diagonalizeVector, DiagonalMatrix, DiagonalOf, MatMul, MatrixSymbol, Transpose } from '../../../src/matrices/expressions';

const s = (e: unknown): string => sstr(e as Expr);
const [n, i] = symbols('n i j k', { integer: true });
const x = symbol('x');
const A = MatrixSymbol('A', 3, 1);
const B = MatrixSymbol('B', 1, 3);
const C = MatrixSymbol('C', 2, 2);
const X = MatrixSymbol('X', 2, 2);
const Y = MatrixSymbol('Y', 2, 2);

describe('diagonal', () => {
  const n = symbol('n', { integer: true });
  const m = symbol('m', { integer: true });
  it('DiagonalMatrix', () => {
    const D = DiagonalMatrix(MatrixSymbol('x', 2, 3));
    expect(s(D.at(1, 2))).toBe('0');
    expect(s(D.at(1, 1))).toBe('x[1, 1]');
    expect(s(D.diagonalLength)).toBe('2');
    expect(s(DiagonalMatrix(MatrixSymbol('x', n.add(1), n)).diagonalLength)).toBe('n');
    const tall = DiagonalMatrix(MatrixSymbol('x', n, 3));
    expect(s(tall.diagonalLength)).toBe('3');
    expect(s(tall.at(10, 1))).toBe('0');
    // SymPy gives None; the length is Min(n, m)
    expect(s(DiagonalMatrix(MatrixSymbol('x', n, m)).diagonalLength)).toBe('Min(m, n)');
    const [i, j] = symbols('i j');
    const Xs = MatrixSymbol('X', n, n);
    expect(s(DiagonalMatrix(Xs).at(0, 0))).toBe('X[0, 0]');
    expect(s(DiagonalMatrix(Xs).at(i, j))).toBe('KroneckerDelta(i, j)*X[i, j]');
  });
  it('DiagonalOf', () => {
    const x = MatrixSymbol('x', 2, 3);
    const diag = DiagonalOf(x);
    expect(diag.shape.map(s)).toEqual(['2', '1']);
    expect(s(diag.at(1, 0))).toBe('x[1, 1]');
    expect(s(diag.at(1))).toBe('x[1, 1]');
    expect(s(diag.diagonalLength)).toBe('2');
    expect(s(DiagonalOf(MatrixSymbol('x', n.add(1), n)).diagonalLength)).toBe('n');
    expect(s(DiagonalOf(MatrixSymbol('x', n, 3)).diagonalLength)).toBe('3');
    expect(s(DiagonalOf(MatrixSymbol('x', n, m)).diagonalLength)).toBe('Min(m, n)');
    expect(s(DiagonalOf(MatrixSymbol('X', n, n)).at(symbol('i'), 0))).toBe('X[i, i]');
  });
  it('DiagMatrix and diagonalize_vector', () => {
    const k = symbol('k');
    const v = MatrixSymbol('v', k, 1);
    const w = MatrixSymbol('w', 1, k);
    expect(s(DiagMatrix(v).doit())).toBe('DiagMatrix(v)');
    expect(s(DiagMatrix(MatMul(2, v)).doit())).toBe('2*DiagMatrix(v)');
    expect(s(DiagMatrix(v.T).doit())).toBe('DiagMatrix(v)');
    expect(s(DiagMatrix(Matrix.col(1, 2)).doit())).toBe('Matrix([[1, 0], [0, 2]])');
    expect(s(diagonalizeVector(v))).toBe('DiagMatrix(v)');
    expect(s(DiagMatrix(v).at(0, 1))).toBe('0');
    expect(s(DiagMatrix(w).at(1, 1))).toBe('w[0, 1]');
    expect(String(DiagMatrix(Matrix.col(1, 2)).asExplicit())).toBe('Matrix([[1, 0], [0, 2]])');
    expect(s(DiagMatrix(v).T)).toBe('DiagMatrix(v)');
  });
});

describe('diagonal matrices', () => {
  it('diagonal_length', () => {
    expect(s(DiagonalMatrix(MatrixSymbol('Z', 3, n)).diagonalLength)).toBe('3');
    expect(s(DiagonalMatrix(MatrixSymbol('Z', n, 3)).diagonalLength)).toBe('3');
    expect(s(DiagonalMatrix(MatrixSymbol('Z', n, n)).diagonalLength)).toBe('n');
    const nn = symbol('nn', { integer: true, positive: true });
    expect(s(DiagonalMatrix(MatrixSymbol('Z', nn, nn.add(1))).diagonalLength)).toBe('nn');
    expect(s(DiagonalMatrix(MatrixSymbol('Z', nn.add(1), nn)).diagonalLength)).toBe('nn');
  });
  it('entries and subs', () => {
    expect(s(DiagonalMatrix(X).at(0, 1))).toBe('0');
    expect(s(DiagonalMatrix(X).at(i, i.add(1)))).toBe('0');
    expect(s(DiagonalMatrix(X).subs(X, Y))).toBe('DiagonalMatrix(Y)');
    expect(s(DiagonalOf(X).subs(X, Y))).toBe('DiagonalOf(Y)');
    expect(s(DiagMatrix(A).subs(A, MatrixSymbol('E', 3, 1)))).toBe('DiagMatrix(E)');
  });
  it('DiagMatrix doit', () => {
    const v = MatrixSymbol('v', 2, 1);
    expect(s(DiagMatrix(MatrixSymbol('u', 1, 1)).doit())).toBe('u');
    expect(s(DiagMatrix(Transpose(B)).doit({ deep: false }))).toBe('DiagMatrix(B)');
    expect(s(DiagMatrix(MatMul(2, A)).doit())).toBe('2*DiagMatrix(A)');
    expect(s(DiagMatrix(C.mul(v)).doit())).toBe('DiagMatrix(C*v)');
    expect(s(DiagMatrix(MatMul(x, C, v)).doit())).toBe('x*DiagMatrix(C*v)');
    expect(s(DiagMatrix(B.T).doit())).toBe('DiagMatrix(B)');
    expect(s(DiagMatrix(A).doit())).toBe('DiagMatrix(A)');
  });
});

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/assumptions/handlers/matrices.ts.
// ask with the matrix predicates. Expected values are those of SymPy 1.14 unless a comment says otherwise.

import { describe, expect, it } from 'vitest';
import * as sj from '../../../src';
import '../../../src/assumptions/handlers/matrices';

const { Q, ask } = sj;
const X = sj.MatrixSymbol('X', 3, 3);
const Y = sj.MatrixSymbol('Y', 2, 3);
const Z = sj.MatrixSymbol('Z', 3, 3);
const I3 = sj.Identity(3);
const Z3 = sj.ZeroMatrix(3, 3);
const mm = (...a: sj.MatrixExpr[]): sj.Expr => sj.MatMul(...a);

describe('matrix predicates in ask', () => {
  it('square, symmetric, invertible, singular', () => {
    expect(ask(Q.square(X))).toBe(true);
    expect(ask(Q.square(Y))).toBe(false);
    expect(ask(Q.square(Z3))).toBe(true);
    expect(ask(Q.symmetric(Y))).toBe(false);
    expect(ask(Q.symmetric(sj.MatAdd(X, Z)), sj.And(Q.symmetric(X), Q.symmetric(Z)))).toBe(true);
    // (SymPy answers True; a product of symmetric matrices need not be symmetric)
    expect(ask(Q.symmetric(mm(X, Z)), sj.And(Q.symmetric(X), Q.symmetric(Z)))).toBe('unknown');
    expect(ask(Q.invertible(mm(X, sj.MatrixSymbol('W', 3, 2))), Q.invertible(X))).toBe(false);
    expect(ask(Q.invertible(mm(X, Z)), sj.And(Q.invertible(X), Q.invertible(Z)))).toBe(true);
    expect(ask(Q.invertible(X), sj.And(Q.fullrank(X), Q.square(X)))).toBe(true);
    expect(ask(Q.singular(X), sj.And(Q.fullrank(X), Q.square(X)))).toBe(false);
    expect(ask(Q.singular(X), sj.Not(Q.invertible(X)))).toBe(true);
    expect(ask(Q.invertible(X))).toBe('unknown');
    expect(ask(Q.square(X), sj.Not(Q.symmetric(X)))).toBe(true);
    expect(ask(Q.invertible(sj.symbol('x')))).toBe('unknown');
  });
  it('orthogonal, unitary, positive definite, full rank, triangular, diagonal', () => {
    expect(ask(Q.orthogonal(Y))).toBe(false);
    expect(ask(Q.unitary(Y))).toBe(false);
    expect(ask(Q.positive_definite(Y))).toBe(false);
    expect(ask(Q.orthogonal(I3))).toBe(true);
    expect(ask(Q.orthogonal(mm(X, Z, X)), sj.And(Q.orthogonal(X), Q.orthogonal(Z)))).toBe(true);
    expect(ask(Q.positive_definite(sj.MatAdd(X, Z)), sj.And(Q.positive_definite(X), Q.positive_definite(Z)))).toBe(true);
    expect(ask(Q.positive_definite(sj.MatAdd(X, Z)), Q.positive_definite(X))).toBe('unknown');
    expect(ask(Q.fullrank(sj.Transpose(X)), Q.fullrank(X))).toBe(true);
    expect(ask(Q.fullrank(sj.Inverse(X)), Q.fullrank(X))).toBe(true);
    expect(ask(Q.fullrank(Z3))).toBe(false);
    expect(ask(Q.fullrank(I3))).toBe(true);
    expect(ask(Q.fullrank(mm(X, Z)), sj.And(Q.fullrank(X), Q.fullrank(Z)))).toBe(true);
    expect(ask(Q.fullrank(mm(X, Z)), Q.fullrank(X))).toBe('unknown');
    expect(ask(Q.fullrank(X))).toBe('unknown');
    expect(ask(Q.diagonal(X), sj.And(Q.lower_triangular(X), Q.upper_triangular(X)))).toBe(true);
    expect(ask(Q.diagonal(X), Q.lower_triangular(X))).toBe('unknown');
    expect(ask(Q.upper_triangular(Z3))).toBe(true);
  });
  it('the elements of a matrix', () => {
    const e = sj.MatrixElement(X, 1, 2);
    expect(ask(Q.integer(e), Q.integer_elements(X))).toBe(true);
    expect(ask(Q.real(e), Q.real_elements(X))).toBe(true);
    expect(ask(Q.complex(e), Q.complex_elements(X))).toBe(true);
    expect(ask(Q.integer(e))).toBe('unknown');
  });
});

it('propagates structural matrix and entry-set facts without inferring principal invertibility', () => {
  const slice = sj.MatrixSlice(X, [0, 2], [0, 2]);
  const off = sj.MatrixSlice(X, [0, 2], [1, 3]);
  for (const p of [Q.symmetric, Q.diagonal, Q.upper_triangular, Q.lower_triangular, Q.positive_definite]) {
    expect(ask(p(slice), p(X))).toBe(true);
    expect(ask(p(slice))).toBe('unknown');
  }
  expect(ask(Q.invertible(slice), Q.invertible(X))).toBe('unknown');
  expect(ask(Q.orthogonal(slice), Q.orthogonal(X))).toBe('unknown');
  expect(ask(Q.symmetric(off), Q.symmetric(X))).toBe('unknown');
  for (const p of [Q.symmetric, Q.diagonal, Q.upper_triangular, Q.lower_triangular]) {
    expect(ask(p(sj.MatrixSymbol('tiny', 1, 1)))).toBe(true);
    expect(ask(p(sj.MatrixSymbol('empty', 0, 0)))).toBe(true);
  }
  for (const p of [Q.diagonal, Q.upper_triangular, Q.lower_triangular, Q.fullrank, Q.positive_definite]) {
    expect(ask(p(sj.OneMatrix(3, 3)))).toBe(false);
    expect(ask(p(sj.OneMatrix(1, 1)))).toBe(true);
  }
  expect(ask(Q.symmetric(sj.OneMatrix(3, 3)))).toBe(true);
  expect(ask(Q.symmetric(sj.OneMatrix(2, 3)))).toBe(false);
  expect(ask(Q.positive_definite(Z3))).toBe(false);
  expect(ask(Q.invertible(sj.BlockMatrix([I3])))).toBe(true);
  expect(ask(Q.invertible(sj.BlockMatrix([Z3])))).toBe(false);
  expect(ask(Q.invertible(sj.BlockMatrix([[X, Z]])))).toBe(false);
  const explicit = sj.ImmutableMatrix([[1, 0], [0, 1]]);
  expect(ask(Q.invertible(sj.BlockMatrix([[explicit, explicit], [explicit, sj.ImmutableMatrix([[2, 0], [0, 2]])]])))).toBe(true);
  for (const p of [Q.diagonal, Q.upper_triangular, Q.lower_triangular, Q.fullrank]) {
    expect(ask(p(sj.MatPow(X, 3)), p(X))).toBe(true);
    expect(ask(p(sj.MatPow(X, 3)))).toBe('unknown');
  }
  expect(ask(Q.diagonal(sj.MatPow(X, sj.symbol('alpha')))), 'noninteger power').toBe('unknown');
  const V = sj.MatrixSymbol('V', 3, 2);
  expect(ask(Q.symmetric(sj.MatMul(sj.Transpose(V), X, V)), Q.symmetric(X))).toBe(true);
  expect(ask(Q.symmetric(sj.MatMul(sj.Transpose(V), X, V)))).toBe('unknown');
  for (const [p, t] of [[Q.upper_triangular, Q.lower_triangular], [Q.lower_triangular, Q.upper_triangular], [Q.diagonal, Q.diagonal]] as const) {
    expect(ask(p(sj.Transpose(X)), t(X))).toBe(true);
    expect(ask(p(sj.Inverse(X)), p(X))).toBe(true);
    expect(ask(p(sj.MatAdd(X, Z)), sj.And(p(X), p(Z)))).toBe(true);
    expect(ask(p(sj.MatAdd(X, Z)), p(X))).toBe('unknown');
    expect(ask(p(sj.MatMul(X, Z)), sj.And(p(X), p(Z)))).toBe(true);
    expect(ask(p(sj.MatMul(X, Z)), p(X))).toBe('unknown');
  }
  for (const m of [sj.Transpose(X), sj.Inverse(X)]) expect(ask(Q.positive_definite(m), Q.positive_definite(X))).toBe(true);
  expect(ask(Q.positive(sj.MatrixElement(X, 1, 1)), Q.positive_definite(X))).toBe(true);
  expect(ask(Q.positive(sj.MatrixElement(X, 1, 2)), Q.positive_definite(X))).toBe('unknown');
  for (const [p, scalar] of [[Q.integer_elements, Q.integer], [Q.real_elements, Q.real], [Q.complex_elements, Q.complex]] as const) {
    for (const m of [I3, Z3, sj.OneMatrix(3, 3)]) expect(ask(p(m))).toBe(true);
    for (const m of [slice, sj.Transpose(X), sj.Trace(X), sj.Determinant(X), sj.MatPow(X, 2)]) expect(ask(p(m), p(X))).toBe(true);
    for (const m of [sj.MatAdd(X, Z), sj.MatMul(X, Z), sj.HadamardProduct(X, Z), sj.BlockMatrix([[X], [Z]])]) {
      expect(ask(p(m), sj.And(p(X), p(Z)))).toBe(true);
      expect(ask(p(m), p(X))).toBe('unknown');
    }
    for (const m of [sj.Trace(X), sj.Determinant(X)]) expect(ask(scalar(m), p(X))).toBe(true);
    expect(ask(p(sj.Inverse(X)), sj.And(p(X), Q.invertible(X)))).toBe(p === Q.integer_elements ? 'unknown' : true);
    expect(ask(p(sj.Inverse(X)), p(X))).toBe('unknown');
    expect(ask(p(sj.MatPow(X, -2)), sj.And(p(X), Q.invertible(X)))).toBe(p === Q.integer_elements ? 'unknown' : true);
    expect(ask(p(sj.MatPow(X, -2)), p(X))).toBe('unknown');
    expect(ask(p(sj.MatPow(X, sj.symbol('a'))), p(X))).toBe('unknown');
    const a = sj.symbol('alpha');
    expect(ask(p(sj.MatMul(a, X)), sj.And(p(X), scalar(a)))).toBe(true);
    expect(ask(p(sj.MatMul(a, X)), p(X))).toBe('unknown');
    expect(ask(p(sj.MatMul(a, X)), scalar(a))).toBe('unknown');
  }
  expect(ask(Q.real_elements(X), Q.integer_elements(X))).toBe(true);
  expect(ask(Q.complex_elements(X), Q.integer_elements(X))).toBe(true);
  expect(ask(Q.complex_elements(X), Q.real_elements(X))).toBe(true);
  expect(ask(Q.real_elements(sj.LofLU(X)), Q.real_elements(X))).toBe(true);
  expect(ask(Q.integer_elements(sj.LofLU(X)), Q.integer_elements(X))).toBe('unknown');
  expect(ask(Q.complex_elements(sj.DFT(3)))).toBe(true);
  expect(ask(Q.complex_elements(sj.IDFT(3)))).toBe(true);
  expect(ask(Q.real_elements(sj.DFT(3)))).toBe('unknown');
  expect(ask(Q.real_elements(sj.IDFT(3)))).toBe('unknown');
  for (const m of [sj.Trace(X), sj.Determinant(X)]) {
    expect(ask(Q.positive(m), Q.positive_definite(X))).toBe(true);
    expect(ask(Q.positive(m))).toBe('unknown');
  }
});
it('queries recursive structural facts through inverses and transposes', () => {
  const sum = sj.MatAdd(X, Z);
  const a = sj.And(Q.diagonal(X), Q.diagonal(Z));
  expect(ask(Q.diagonal(sj.Transpose(sum)), a)).toBe(true);
  expect(ask(Q.diagonal(sj.Inverse(sum)), a)).toBe(true);
});
it('leaves an inverse with unknown structure undecided', () => {
  expect(ask(Q.diagonal(sj.Inverse(X)))).toBe('unknown');
});

it('queries the adjoint symmetry of explicit matrices', () => {
  const m = (rows: sj.ExprLike[][]): sj.Expr => sj.sympifyMatrix(sj.Matrix.of(rows));
  expect(ask(Q.hermitian(m([[2, sj.S.I], [sj.mul(-1, sj.S.I), 3]])))).toBe(true);
  expect(ask(Q.hermitian(m([[sj.S.I]])))).toBe(false);
  expect(ask(Q.hermitian(m([[sj.symbol('unknown')]])))).toBe('unknown');
  expect(ask(Q.antihermitian(m([[sj.S.I]])))).toBe(true);
  expect(ask(Q.antihermitian(m([[1]])))).toBe(false);
  expect(ask(Q.antihermitian(m([[sj.symbol('unknown')]])))).toBe('unknown');
  expect(ask(Q.antihermitian(X))).toBe('unknown');
});

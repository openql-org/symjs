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

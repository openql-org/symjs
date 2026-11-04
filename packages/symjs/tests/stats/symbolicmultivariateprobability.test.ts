// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/stats/symbolicmultivariateprobability.ts (SymPy
// sympy/stats/symbolic_multivariate_probability.py and
// sympy/stats/tests/test_symbolic_multivariate.py). Expected values are
// those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { ImmutableMatrix, Matrix, MatrixSymbol, ShapeError, Sym, ZeroMatrix, mul, str, transpose } from '../../src';
import type { Expr, MatrixExpr } from '../../src';
import {
  Covariance,
  CrossCovarianceMatrix,
  CrossCovarianceMatrixNode,
  Expectation,
  ExpectationMatrix,
  ExpectationMatrixNode,
  Normal,
  RandomMatrixSymbol,
  Variance,
  VarianceMatrix,
  VarianceMatrixNode,
  variance,
} from '../../src/stats';

const [j, k] = [new Sym('j'), new Sym('k')];
const MS = (n: string, r: Expr | number, c: Expr | number): MatrixExpr => MatrixSymbol(n, r, c) as MatrixExpr;
const [A, B, C, D] = ['A', 'B', 'C', 'D'].map((n) => MS(n, k, k)) as [MatrixExpr, MatrixExpr, MatrixExpr, MatrixExpr];
const [a, b] = [MS('a', k, 1), MS('b', k, 1)];
const [A2, B2] = [MS('A2', 2, 2), MS('B2', 2, 2)];
const [X, Y, Z, W] = ['X', 'Y', 'Z', 'W'].map((n) => new RandomMatrixSymbol(n, k, 1)) as [RandomMatrixSymbol, RandomMatrixSymbol, RandomMatrixSymbol, RandomMatrixSymbol];
const X2 = new RandomMatrixSymbol('X2', 2, 1);
const normal = Normal('normal', 0, 1);
const m1 = ImmutableMatrix(Matrix.of([[1, mul(j, Normal('normal2', 2, 1))], [normal, 0]]));
const T = (e: Expr): MatrixExpr => transpose(e) as MatrixExpr;
const s = (e: unknown): string => str(e as Expr);
const ex = (e: unknown): Expr => (e as { expand(): Expr }).expand();

describe('ExpectationMatrix (SymPy test_multivariate_expectation)', () => {
  it('constructs and expands', () => {
    expect(s(Expectation(a))).toBe('a');
    expect(s(ExpectationMatrix(a))).toBe('a');
    const e = Expectation(X);
    expect(e).toBeInstanceOf(ExpectationMatrixNode);
    expect(e.key).toBe(ExpectationMatrix(X).key);
    expect((e as MatrixExpr).shape.map(s)).toEqual(['k', '1']);
    expect(s((e as MatrixExpr).rows)).toBe('k');
    expect(s(ex(Expectation(A.mul(X).add(b))))).toBe('A*ExpectationMatrix(X) + b');
    const e1 = Expectation(m1.mul(X2));
    expect(ex(e1).key).toBe(e1.key);
    const e4 = Expectation(A2.mul(m1).mul(B2).mul(X2));
    expect((e4.args[0] as Expr).args.map(s)).toEqual(['A2', 'Matrix([[1, j*normal2], [normal, 0]])', 'B2', 'X2']);
    expect(s(ex(e4))).toBe('A2*ExpectationMatrix(Matrix([[1, j*normal2], [normal, 0]])*B2*X2)');
    expect(s(ex(Expectation(X.add(Y).mul(T(X.sub(Y))))))).toBe('ExpectationMatrix(X*X.T) - ExpectationMatrix(X*Y.T) + ExpectationMatrix(Y*X.T) - ExpectationMatrix(Y*Y.T)');
    expect(s(ex(Expectation(A.mul(X).add(B.mul(Y)))))).toBe('A*ExpectationMatrix(X) + B*ExpectationMatrix(Y)');
    // a sum of non-random terms
    expect(s(ex(ExpectationMatrix(X, a)))).toBe('ExpectationMatrix(X, a)');
    expect(s(ex(new ExpectationMatrixNode([a])))).toBe('a');
    expect(s(new ExpectationMatrixNode([X]).withArgs([Y]))).toBe('ExpectationMatrix(Y)');
    expect(new ExpectationMatrixNode([X, a]).condition?.key).toBe(a.key);
    // a product whose first factor is random
    expect(s(ex(Expectation(X.mul(T(a)))))).toBe('ExpectationMatrix(X*a.T)');
    // the transpose of a random symbol is neither a sum nor a product
    expect(s(ex(Expectation(T(X))))).toBe('ExpectationMatrix(X.T)');
  });
  it('evaluates explicit matrices entry by entry', () => {
    expect(s((Expectation(m1) as ExpectationMatrixNode).doit())).toBe('Matrix([[1, 2*j], [0, 0]])');
    const N = (n: string, m: number): Expr => Normal(n, m, 1);
    const x1 = ImmutableMatrix(Matrix.of([[N('N11', 11), N('N12', 12)], [N('N21', 21), N('N22', 22)]]));
    const x2 = ImmutableMatrix(Matrix.of([[N('M11', 1), N('M12', 2)], [N('M21', 3), N('M22', 4)]]));
    const sum = x1.add(x2);
    const outer = Expectation(Expectation(sum)) as ExpectationMatrixNode;
    expect(outer.doit({ deep: false }).key).toBe(ExpectationMatrix(sum).key);
    expect(s(outer.doit())).toBe('Matrix([[12, 14], [24, 26]])');
    // a random matrix symbol of the empty space stays unevaluated; a non-random one is its value
    expect(s((Expectation(X) as ExpectationMatrixNode).doit())).toBe('ExpectationMatrix(X)');
    expect(s(new ExpectationMatrixNode([a]).doit())).toBe('a');
  });
});

describe('VarianceMatrix (SymPy test_multivariate_variance)', () => {
  it('constructs and expands', () => {
    expect(() => Variance(A)).toThrow(ShapeError);
    expect(s(ex(Variance(a)))).toBe(s(ZeroMatrix(k, k)));
    expect(Variance(a).key).toBe(VarianceMatrix(a).key);
    expect(s(ex(Variance(T(a))))).toBe('0');
    expect((Variance(T(a)) as MatrixExpr).shape.map(s)).toEqual(['k', 'k']);
    const e = Variance(X);
    expect(e).toBeInstanceOf(VarianceMatrixNode);
    expect((e as MatrixExpr).shape.map(s)).toEqual(['k', 'k']);
    expect(s(ex(e))).toBe('VarianceMatrix(X)');
    expect(s(ex(Variance(A.mul(X))))).toBe('A*VarianceMatrix(X)*A.T');
    expect(s(ex(Variance(A.mul(B).mul(X))))).toBe('A*B*VarianceMatrix(X)*B.T*A.T');
    const v1 = Variance(m1.mul(X2));
    expect(ex(v1).key).toBe(v1.key);
    const v4 = Variance(A2.mul(m1).mul(B2).mul(X2));
    expect((v4.args[0] as Expr).args.map(s)).toEqual(['A2', 'Matrix([[1, j*normal2], [normal, 0]])', 'B2', 'X2']);
    expect(ex(v4).key).toBe(v4.key);
    expect(s(ex(Variance(A.mul(X).add(B.mul(Y)))))).toBe('2*A*CrossCovarianceMatrix(X, Y)*B.T + A*VarianceMatrix(X)*A.T + B*VarianceMatrix(Y)*B.T');
    // the transpose of a random symbol is neither a sum nor a product
    expect(s(ex(VarianceMatrix(T(X))))).toBe('VarianceMatrix(X.T)');
    expect(s(VarianceMatrix(X, a))).toBe('VarianceMatrix(X, a)');
    expect(new VarianceMatrixNode([X, a]).condition?.key).toBe(a.key);
    expect(s(new VarianceMatrixNode([X]).withArgs([Y]))).toBe('VarianceMatrix(Y)');
    // rv_interface variance of a random matrix symbol of the empty space
    expect(s(variance(X))).toBe('VarianceMatrix(X)');
  });
});

describe('CrossCovarianceMatrix (SymPy test_multivariate_crosscovariance)', () => {
  it('constructs and expands', () => {
    expect(() => Covariance(X, T(Y))).toThrow(ShapeError);
    expect(() => Covariance(X, A)).toThrow(ShapeError);
    expect(() => Covariance(A, X)).toThrow(ShapeError);
    const e0 = Covariance(T(a), T(b));
    expect((e0 as MatrixExpr).shape.map(s)).toEqual(['1', '1']);
    expect(s(ex(e0))).toBe('0');
    const e = Covariance(a, b);
    expect(e).toBeInstanceOf(CrossCovarianceMatrixNode);
    expect(e.key).toBe(CrossCovarianceMatrix(a, b).key);
    expect((e as MatrixExpr).shape.map(s)).toEqual(['k', 'k']);
    expect(s(ex(Covariance(A.mul(X).add(a), b)))).toBe('0');
    const cxy = Covariance(X, Y);
    expect(ex(cxy).key).toBe(cxy.key);
    expect(s(ex(Covariance(X, X)))).toBe('VarianceMatrix(X)');
    expect(s(ex(Covariance(X.add(Y), Z)))).toBe('CrossCovarianceMatrix(X, Z) + CrossCovarianceMatrix(Y, Z)');
    expect(s(ex(Covariance(A.mul(X), Y)))).toBe('A*CrossCovarianceMatrix(X, Y)');
    expect(s(ex(Covariance(X, B.mul(Y))))).toBe('CrossCovarianceMatrix(X, Y)*B.T');
    expect(s(ex(Covariance(A.mul(X).add(a), T(B).mul(Y).add(b))))).toBe('A*CrossCovarianceMatrix(X, Y)*B');
    expect(s(ex(Covariance(A.mul(X).add(B.mul(Y)).add(a), T(C).mul(Z).add(T(D).mul(W)).add(b))))).toBe(
      'A*CrossCovarianceMatrix(X, W)*D + A*CrossCovarianceMatrix(X, Z)*C + B*CrossCovarianceMatrix(Y, W)*D + B*CrossCovarianceMatrix(Y, Z)*C',
    );
    // a random term that is neither a symbol nor a product, and a sum with one
    expect(s(ex(Covariance(T(T(X).add(T(a))), Y)))).toBe('CrossCovarianceMatrix(X, Y)');
    expect(s(ex(CrossCovarianceMatrix(X.add(a), T(T(Y)).add(Z))))).toBe('CrossCovarianceMatrix(X, Y) + CrossCovarianceMatrix(X, Z)');
    // random terms that are neither symbols, sums nor products
    expect(s(ex(CrossCovarianceMatrix(T(X), T(Y))))).toBe('CrossCovarianceMatrix(X.T, Y.T)');
    expect(s(CrossCovarianceMatrix(X, Y, a))).toBe('CrossCovarianceMatrix(X, Y, a)');
    expect(new CrossCovarianceMatrixNode([X, Y, a]).condition?.key).toBe(a.key);
    expect(s(new CrossCovarianceMatrixNode([X, Y]).withArgs([X, Z]))).toBe('CrossCovarianceMatrix(X, Z)');
  });
});

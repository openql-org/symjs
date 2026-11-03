// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * Coverage of sympy.matrices.expressions.permutation (PermutationMatrix,
 * MatrixPermute) with the expected values of SymPy 1.14.
 */

import { describe, expect, it } from 'vitest';
import { latex, sstr, symbols } from '../src';
import type { Expr } from '../src';
import { Adjoint, Identity, MatMul, MatPow, MatrixPermute, MatrixSymbol, OneMatrix, PermutationMatrix, PermutationNode, Transpose } from '../src/matrices/expressions';
import type { MatrixExpr } from '../src/matrices/expressions';

const s = (e: unknown): string => sstr(e as Expr);
const M = (e: Expr): MatrixExpr => e as MatrixExpr;
const [i, j, k] = symbols('i j k', { integer: true });
const p = PermutationNode.from([1, 2, 0]);
const q = PermutationNode.from([1, 0, 2]);
const P = PermutationMatrix(p);
const X = MatrixSymbol('X', 3, 3);

describe('Permutation argument', () => {
  it('validation, the empty permutation and resize', () => {
    expect(() => PermutationNode.from([0, 0, 1])).toThrow(RangeError);
    expect(s(PermutationNode.from([]))).toBe('()');
    expect(s(p.resize(5))).toBe('(4)(0 1 2)');
    expect(s(PermutationNode.from([1, 0, 2, 3]).resize(2))).toBe('(0 1)');
    expect(s(PermutationNode.from({ arrayForm: [1, 0, 2] }))).toBe('(2)(0 1)');
    expect(s(PermutationNode.from([1, 0]).compose(PermutationNode.from([0, 2, 1])))).toBe('(0 2 1)');
    expect(() => p.resize(2)).toThrow('The permutation cannot be resized to 2 because the cycle (0, 1, 2) may break.');
  });
});

describe('PermutationMatrix', () => {
  it('entries', () => {
    // SymPy gives 0, from KroneckerDelta(AppliedPermutation((0 1 2), i), j), which is wrong for i = 0, j = 1
    expect(s(P.at(i, j))).toBe('PermutationMatrix((0 1 2))[i, j]');
    expect(s(P.at(1, j))).toBe('KroneckerDelta(2, j)');
  });
  it('powers, adjoints and products', () => {
    // SymPy raises TypeError (Cannot convert symbols to int)
    expect(s(P.pow(k))).toBe('PermutationMatrix((0 1 2))**k');
    expect(s(M(MatPow(P, -2)).doit())).toBe('PermutationMatrix((0 1 2))');
    expect(latex(PermutationMatrix([]))).toBe('P_{\\left( \\right)}');
    expect(s(P.adjoint())).toBe('PermutationMatrix((0 2 1))');
    expect(s(M(Adjoint(P)).doit())).toBe('PermutationMatrix((0 2 1))');
    expect(s(M(MatMul(P, PermutationMatrix(q))).doit())).toBe('PermutationMatrix((1 2))');
  });
  it('rewrite(BlockDiagMatrix)', () => {
    const bd = (a: number[]): string => s(PermutationMatrix(a).rewriteAsBlockDiagMatrix());
    expect(bd([2, 0, 1, 3])).toBe('Matrix([[PermutationMatrix((0 2 1)), 0], [0, PermutationMatrix((0))]])');
    expect(bd([3, 2, 1, 0])).toBe('Matrix([[PermutationMatrix((0 3)(1 2))]])');
    expect(bd([1, 2, 3, 0, 4])).toBe('Matrix([[PermutationMatrix((0 1 2 3)), 0], [0, PermutationMatrix((0))]])');
    expect(bd([0, 3, 1, 2])).toBe('Matrix([[PermutationMatrix((0)), 0], [0, PermutationMatrix((0 2 1))]])');
    expect(bd([4, 1, 2, 3, 0, 5])).toBe('Matrix([[PermutationMatrix((0 4)), 0], [0, PermutationMatrix((0))]])');
    expect(bd([2, 3, 0, 1])).toBe('Matrix([[PermutationMatrix((0 2)(1 3))]])');
    expect(bd([1, 3, 0, 2, 5, 4])).toBe('Matrix([[PermutationMatrix((0 1 3 2)), 0], [0, PermutationMatrix((0 1))]])');
    expect(bd([3, 0, 1, 2, 5, 4, 6])).toBe('Matrix([[PermutationMatrix((0 3 2 1)), 0, 0], [0, PermutationMatrix((0 1)), 0], [0, 0, PermutationMatrix((0))]])');
    expect(bd([5, 0, 1, 2, 3, 4])).toBe('Matrix([[PermutationMatrix((0 5 4 3 2 1))]])');
    expect(bd([1, 0, 4, 2, 3, 6, 5, 7])).toBe(
      'Matrix([[PermutationMatrix((0 1)), 0, 0, 0], [0, PermutationMatrix((0 2 1)), 0, 0], [0, 0, PermutationMatrix((0 1)), 0], [0, 0, 0, PermutationMatrix((0))]])',
    );
    expect(bd([2, 1, 0, 4, 3])).toBe('Matrix([[PermutationMatrix((0 2)), 0], [0, PermutationMatrix((0 1))]])');
    expect(s(P.rewrite('BlockDiagMatrix'))).toBe('Matrix([[PermutationMatrix((0 1 2))]])');
    expect(s(P.rewrite('MatMul'))).toBe('PermutationMatrix((0 1 2))');
    expect(bd([3, 5, 2, 0, 4, 1])).toBe('Matrix([[PermutationMatrix((0 3)(1 5))]])');
  });
});

describe('MatrixPermute', () => {
  it('construction', () => {
    expect(s(MatrixPermute(X, PermutationMatrix(q)))).toBe('MatrixPermute(X, (2)(0 1), 0)');
    expect(() => MatrixPermute(X, p, 2)).toThrow('The axis must be 0 or 1.');
    expect(s(MatrixPermute(MatrixSymbol('Y', 4, 4), p, 0))).toBe('MatrixPermute(Y, (3)(0 1 2), 0)');
    expect(() => MatrixPermute(2, p)).toThrow('must be a SymPy matrix instance.');
  });
  it('doit', () => {
    expect(s(MatrixPermute(X, [0, 1, 2]).doit())).toBe('X');
    expect(s(MatrixPermute(Identity(3), p, 1).doit())).toBe('PermutationMatrix((0 2 1))');
    expect(s(MatrixPermute(OneMatrix(3, 3), p).doit())).toBe('1');
    expect(s(MatrixPermute(MatrixPermute(X, p, 0), p, 1).doit())).toBe('MatrixPermute(MatrixPermute(X, (0 1 2), 0), (0 1 2), 1)');
    const tx = Transpose(X.add(X));
    expect(s(MatrixPermute(tx, p).doit({ deep: false }))).toBe('MatrixPermute((2*X).T, (0 1 2), 0)');
    // SymPy evaluates the matrix but returns the unevaluated self: MatrixPermute((2*X).T, (0 1 2), 0)
    expect(s(MatrixPermute(tx, p).doit())).toBe('MatrixPermute(2*X.T, (0 1 2), 0)');
    expect(s(MatrixPermute(X, p).doit())).toBe('MatrixPermute(X, (0 1 2), 0)');
  });
  it('entries, subs and rewrite', () => {
    // SymPy gives X[AppliedPermutation((0 1 2), i), j] and X[i, AppliedPermutation((0 1 2), j)]
    expect(s(MatrixPermute(X, p, 0).at(i, j))).toBe('MatrixPermute(X, (0 1 2), 0)[i, j]');
    expect(s(MatrixPermute(X, p, 1).at(i, j))).toBe('MatrixPermute(X, (0 1 2), 1)[i, j]');
    expect(s(MatrixPermute(X, p, 1).at(i, 1))).toBe('X[i, 2]');
    expect(s(MatrixPermute(X, p, 1).subs(X, MatrixSymbol('Z', 3, 3)))).toBe('MatrixPermute(Z, (0 1 2), 1)');
    expect(s(MatrixPermute(X, p, 1).rewrite('BlockDiagMatrix'))).toBe('MatrixPermute(X, (0 1 2), 1)');
    expect(s(MatrixPermute(X, p, 1).rewrite('MatMul'))).toBe('X*PermutationMatrix((0 2 1))');
  });
});

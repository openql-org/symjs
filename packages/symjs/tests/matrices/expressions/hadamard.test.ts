// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/matrices/expressions/hadamard.ts.
//
// HadamardProduct and HadamardPower. Expected values are SymPy 1.14 results (explicit matrices printed
// on one line).

import { describe, expect, it } from 'vitest';
import { type Expr, Integral, latex, Matrix, sstr, Sum, symbol, symbols, SymFunction as UFunction } from '../../../src';
import { canonicalize, DiagonalMatrix, HadamardPower, hadamardPower, HadamardProduct, hadamardProduct, MatMul, MatPow, type MatrixExpr, MatrixSymbol, OneMatrix, Transpose, ZeroMatrix } from '../../../src/matrices/expressions';

const s = (e: unknown): string => sstr(e as Expr);
const L = (e: unknown): string => latex(e as Expr);
const M = (e: Expr): MatrixExpr => e as MatrixExpr;
const mats3 = (r: Expr | number, c: Expr | number): [MatrixExpr, MatrixExpr, MatrixExpr] => [MatrixSymbol('A', r, c), MatrixSymbol('B', r, c), MatrixSymbol('C', r, c)];
const [n, , , k] = symbols('n i j k', { integer: true });
const x = symbol('x');
const C = MatrixSymbol('C', 2, 2);
const X = MatrixSymbol('X', 2, 2);
const Y = MatrixSymbol('Y', 2, 2);

describe('hadamard', () => {
  it('HadamardProduct and hadamard_product', () => {
    const A = MatrixSymbol('A', 5, 5);
    const B = MatrixSymbol('B', 5, 5);
    expect(hadamardProduct(A, B)).toBeInstanceOf(HadamardProduct);
    const A2 = MatrixSymbol('A', 2, 3);
    const B2 = MatrixSymbol('B', 2, 3);
    expect(s(hadamardProduct(A2))).toBe('A');
    expect(s(hadamardProduct(A2, B2))).toBe('HadamardProduct(A, B)');
    expect(s(M(hadamardProduct(A2, B2)).at(0, 1))).toBe('A[0, 1]*B[0, 1]');
    expect(() => hadamardProduct()).toThrow('Empty Hadamard product is undefined');
  });
  it('canonicalize', () => {
    const [A, B, C] = mats3(2, 2);
    let X = HadamardProduct(A, HadamardProduct(B, C));
    expect(s(X)).toBe('HadamardProduct(A, HadamardProduct(B, C))');
    expect(s(canonicalize(X))).toBe('HadamardProduct(A, B, C)');
    X = HadamardProduct(A, B);
    const Y = HadamardProduct(B, A);
    expect(s(X)).toBe('HadamardProduct(A, B)');
    expect(s(Y)).toBe('HadamardProduct(B, A)');
    expect(s(canonicalize(X))).toBe('HadamardProduct(A, B)');
    expect(s(canonicalize(Y))).toBe('HadamardProduct(A, B)');
    X = HadamardProduct(A, OneMatrix(2, 2));
    expect(s(X)).toBe('HadamardProduct(A, 1)');
    expect(s(canonicalize(X))).toBe('A');
    X = HadamardProduct(A, ZeroMatrix(2, 2));
    expect(s(X)).toBe('HadamardProduct(A, 0)');
    expect(s(canonicalize(X))).toBe('0');
    X = HadamardProduct(A, A, A);
    expect(s(X)).toBe('HadamardProduct(A, A, A)');
    expect(s(canonicalize(X))).toBe('HadamardPower(A, 3)');
  });
  it('printing and powers', () => {
    const n = symbol('n');
    const x = symbol('x');
    const [A, B, C] = mats3(n, n);
    expect(L(HadamardProduct(A, B))).toBe('A \\circ B');
    expect(L(HadamardProduct(A, HadamardProduct(B, C)))).toBe('A \\circ \\left(B \\circ C\\right)');
    expect(s(HadamardPower(A, 3))).toBe('HadamardPower(A, 3)');
    expect(L(HadamardPower(A, 3))).toBe('A^{\\circ {3}}');
    expect(L(HadamardPower(A, x.add(1)))).toBe('A^{\\circ \\left({x + 1}\\right)}');
    expect(s(HadamardProduct(A, B).mul(C))).toBe('(HadamardProduct(A, B))*C');
    expect(L(HadamardProduct(A, B).mul(C))).toBe('\\left(A \\circ B\\right) C');
    expect(s(MatMul(2, HadamardProduct(A, B)))).toBe('2*(HadamardProduct(A, B))');
    expect(s(MatPow(HadamardProduct(A, B), 2))).toBe('(HadamardProduct(A, B))**2');
    expect(s(hadamardPower(A, 1))).toBe('A');
    expect(s(M(HadamardPower(MatrixSymbol('P', 2, 2), 2)).at(0, 1))).toBe('P[0, 1]**2');
    expect(s(M(hadamardProduct(Matrix.of([[1, 2], [3, 4]]), Matrix.of([[5, 6], [7, 8]]))))).toBe('Matrix([[5, 12], [21, 32]])');
  });
});

describe('Hadamard', () => {
  it('HadamardProduct', () => {
    expect(() => HadamardProduct()).toThrow('HadamardProduct needs at least one argument');
    expect(() => HadamardProduct(X, 2)).toThrow('Mix of Matrix and Scalar symbols');
    expect(s(HadamardProduct.create([X, X], true))).toBe('HadamardPower(X, 2)');
    expect(s(HadamardProduct(X, Y).subs(X, C))).toBe('HadamardProduct(C, Y)');
    expect(s(M(HadamardProduct(X, Y)).T)).toBe('HadamardProduct(X.T, Y.T)');
    expect(s(M(Transpose(HadamardProduct(X, Y))).doit())).toBe('HadamardProduct(X.T, Y.T)');
    expect(s(M(HadamardProduct(Transpose(X.add(X)), Y.T)).doit({ deep: false }))).toBe('HadamardProduct(2*X.T, Y.T)');
    expect(s(M(HadamardProduct(OneMatrix(2, 2), OneMatrix(2, 2))).doit())).toBe('1');
    expect(s(M(HadamardProduct(HadamardProduct(X, Y), X)).doit())).toBe('HadamardProduct(HadamardPower(X, 2), Y)');
  });
  it('HadamardPower', () => {
    expect(s(HadamardPower(X, Y))).toBe('HadamardPower(X, Y)');
    expect(s(HadamardPower(2, X))).toBe('HadamardPower(2, X)');
    expect(M(HadamardPower(2, X)).shape.map(s)).toEqual(['2', '2']);
    expect(s(M(HadamardPower(2, X)).at(0, 1))).toBe('2**X[0, 1]');
    expect(s(M(HadamardPower(X, Y)).at(0, 1))).toBe('X[0, 1]**Y[0, 1]');
    expect(s(HadamardPower(X, 2).subs(X, Y))).toBe('HadamardPower(Y, 2)');
    expect(s(M(HadamardPower(X, 2)).mul(Y))).toBe('HadamardPower(X, 2)*Y');
    expect(s(HadamardPower(X.add(Y), 2))).toBe('HadamardPower(X + Y, 2)');
    expect(s(M(HadamardPower(X, 2)).T)).toBe('HadamardPower(X.T, 2)');
    expect(s(hadamardPower(x, 2))).toBe('x**2');
    expect(() => hadamardPower(X, Y)).toThrow('cannot raise expression to a matrix');
    expect(s(hadamardPower(X, 1))).toBe('X');
  });
});

describe('remaining branches (SymPy 1.14)', () => {
  it('canonicalize of a non-Hadamard expression and diagonal lengths', () => {
    expect(s(canonicalize(X))).toBe('X');
    expect(s(DiagonalMatrix(MatrixSymbol('Z', 3, 2)).diagonalLength)).toBe('2');
  });
  it('LaTeX precedence of scalar exponents', () => {
    const f = UFunction('f');
    expect(latex(HadamardPower(X, new Integral([f(x), x])))).toBe('X^{\\circ {\\int f{\\left(x \\right)}\\, dx}}');
    expect(latex(HadamardPower(X, Sum(f(k), [k, 0, n])))).toBe('X^{\\circ {\\sum_{k=0}^{n} f{\\left(k \\right)}}}');
    expect(latex(HadamardPower(X, x.add(1)))).toBe('X^{\\circ \\left({x + 1}\\right)}');
    expect(latex(HadamardPower(X, x.mul(2)))).toBe('X^{\\circ {2 x}}');
  });
});

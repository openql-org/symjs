// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/matrices/expressions/misc.ts.
//
// The smaller matrix expression modules (DotProduct, CompanionMatrix, MatrixSet, factorizations, DFT).
// Expected values are SymPy 1.14 results (explicit matrices printed on one line).

import { describe, expect, it } from 'vitest';
import { type Expr, I, Interval, latex, Matrix, Poly, Rational, Reals, S, sqrt, sstr, symbol, symbols } from '../../../src';
import { CompanionMatrix, DotProduct, eig, HadamardPower, LofLU, lu, MatrixSet, MatrixSymbol, qr, svd } from '../../../src/matrices/expressions';

const s = (e: unknown): string => sstr(e as Expr);
const L = (e: unknown): string => latex(e as Expr);
const [n, i, j, k] = symbols('n i j k', { integer: true });
const x = symbol('x');
const A = MatrixSymbol('A', 3, 1);
const B = MatrixSymbol('B', 1, 3);
const C = MatrixSymbol('C', 2, 2);
const X = MatrixSymbol('X', 2, 2);
const Y = MatrixSymbol('Y', 2, 2);

describe('companion', () => {
  it('CompanionMatrix', () => {
    const x = symbol('x');
    const c = symbols('c0 c1 c2 c3 c4');
    const p = Poly.from(c[0]!.add(c[1]!.mul(x)).add(c[2]!.mul(x.pow(2))).add(c[3]!.mul(x.pow(3))).add(c[4]!.mul(x.pow(4))).add(x.pow(5)), [x]);
    expect(s(CompanionMatrix(p))).toBe("CompanionMatrix(Poly(x**5 + c4*x**4 + c3*x**3 + c2*x**2 + c1*x + c0, x, domain='ZZ[c0,c1,c2,c3,c4]'))");
    const C = CompanionMatrix(Poly.from(x.pow(2).add(x.mul(2)).add(3), [x]));
    expect(String(C.asExplicit())).toBe('Matrix([[0, -3], [1, -2]])');
    expect(s(C.at(0, 1))).toBe('-3');
    expect(s(C.at(1, 0))).toBe('1');
  });
});

describe('dotproduct', () => {
  it('DotProduct', () => {
    const A = MatrixSymbol('A', 1, 3);
    const B = MatrixSymbol('B', 1, 3);
    expect(s(DotProduct(A, B))).toBe('DotProduct(A, B)');
    expect(s(DotProduct(A, B).doit())).toBe('A[0, 0]*B[0, 0] + A[0, 1]*B[0, 1] + A[0, 2]*B[0, 2]');
    expect(s(DotProduct(MatrixSymbol('a', 3, 1), MatrixSymbol('b', 3, 1)).doit())).toBe('a[0, 0]*b[0, 0] + a[1, 0]*b[1, 0] + a[2, 0]*b[2, 0]');
    expect(s(DotProduct(MatrixSymbol('a', 1, 3), MatrixSymbol('b', 3, 1)).doit())).toBe('a[0, 0]*b[0, 0] + a[0, 1]*b[1, 0] + a[0, 2]*b[2, 0]');
    expect(s(DotProduct(Matrix.col(1, 2, 3), Matrix.col(4, 5, 6)).doit())).toBe('32');
    expect(L(DotProduct(MatrixSymbol('a', 1, 3), MatrixSymbol('b', 1, 3)))).toBe('a \\cdot b');
    expect(() => DotProduct(MatrixSymbol('a', 2, 3), B)).toThrow('Argument 1 of DotProduct is not a vector');
  });
});

describe('sets', () => {
  it('MatrixSet', () => {
    const Ms = MatrixSet(2, 2, Reals);
    expect(Ms.contains(Matrix.of([[1, 2], [3, 4]]))).toBe(true);
    expect(Ms.contains(Matrix.of([[1, 2], [S.I, 4]]))).toBe(false);
    expect(s(Ms)).toBe('MatrixSet(2, 2, Reals)');
    expect(MatrixSet(symbol('n'), 2, Reals).contains(Matrix.of([[1, 2]]))).toBe('unknown');
    expect(Ms.contains(MatrixSymbol('Y', 2, 2))).toBe('unknown');
  });
});

describe('factorizations', () => {
  it('lu, qr, eig, svd', () => {
    const n = symbol('n');
    const X = MatrixSymbol('X', n, n);
    expect(lu(X).map(s)).toEqual(['LofLU(X)', 'UofLU(X)']);
    expect(qr(X).map(s)).toEqual(['QofQR(X)', 'RofQR(X)']);
    expect(eig(X).map(s)).toEqual(['EigenValues(X)', 'EigenVectors(X)']);
    expect(svd(X).map(s)).toEqual(['UofSVD(X)', 'SofSVD(X)', 'VofSVD(X)']);
    expect(lu(X)[0].predicates).toEqual(['lower_triangular']);
    expect(lu(X)[0].shape.map(s)).toEqual(['n', 'n']);
  });
});

describe('DotProduct', () => {
  it('validation', () => {
    expect(() => DotProduct(1, A)).toThrow('Argument 1 of DotProduct is not a matrix');
    expect(() => DotProduct(A, 1)).toThrow('Argument 2 of DotProduct is not a matrix');
    expect(() => DotProduct(A, C)).toThrow('Argument 2 of DotProduct is not a vector');
    expect(() => DotProduct(A, MatrixSymbol('D', 2, 1))).toThrow('DotProduct arguments are not the same length');
  });
  it('subs, doit and LaTeX', () => {
    expect(s(DotProduct(A, A).subs(A, MatrixSymbol('E', 3, 1)))).toBe('DotProduct(E, E)');
    expect(s(DotProduct(A, A).doit({ deep: false }))).toBe('A[0, 0]**2 + A[1, 0]**2 + A[2, 0]**2');
    expect(s(DotProduct(A, B).doit())).toBe('A[0, 0]*B[0, 0] + A[1, 0]*B[0, 1] + A[2, 0]*B[0, 2]');
    expect(s(DotProduct(B, A).doit())).toBe('A[0, 0]*B[0, 0] + A[1, 0]*B[0, 1] + A[2, 0]*B[0, 2]');
    expect(s(DotProduct(B, B).doit())).toBe('B[0, 0]**2 + B[0, 1]**2 + B[0, 2]**2');
    expect(latex(HadamardPower(X, DotProduct(A, A)))).toBe('X^{\\circ \\left({A \\cdot A}\\right)}');
  });
});

describe('CompanionMatrix', () => {
  const cm = CompanionMatrix(Poly.from(x.pow(3).add(x.mul(2)).add(5), [x]));
  it('validation', () => {
    expect(() => CompanionMatrix(x.pow(2).add(1) as unknown as Poly)).toThrow('x**2 + 1 must be a Poly instance.');
    expect(() => CompanionMatrix(Poly.from(x.pow(2).add(k.mul(x)), [x, k]))).toThrow('must be a univariate polynomial.');
    expect(() => CompanionMatrix(Poly.from(x.pow(2).mul(2).add(1), [x]))).toThrow('must be a monic polynomial.');
    expect(() => CompanionMatrix(Poly.from(1, [x]))).toThrow('must have degree not less than 1.');
  });
  it('subs, entries and LaTeX', () => {
    const y = symbol('y');
    expect(s(cm.subs(x, y))).toBe("CompanionMatrix(Poly(y**3 + 2*y + 5, y, domain='ZZ'))");
    const entries: string[] = [];
    for (let r = 0; r < 3; r++) for (let c = 0; c < 3; c++) entries.push(s(cm.at(r, c)));
    expect(entries.join(', ')).toBe('0, 0, -5, 1, 0, -2, 0, 1, 0');
    // SymPy gives 0 for cm[i, j], which is wrong for the last column and the subdiagonal
    expect(() => cm.at(i, j)).toThrow(TypeError);
    expect(latex(cm)).toBe('\\operatorname{CompanionMatrix}\\left(\\operatorname{Poly}{\\left( x^{3} + 2 x + 5, x, domain=\\mathbb{Z} \\right)}\\right)');
    expect(latex(CompanionMatrix(Poly.from(x.pow(2).add(Rational.of(1, 2)), [x])))).toBe(
      '\\operatorname{CompanionMatrix}\\left(\\operatorname{Poly}{\\left( x^{2} + \\frac{1}{2}, x, domain=\\mathbb{Q} \\right)}\\right)',
    );
  });
});

describe('MatrixSet and factorizations', () => {
  it('MatrixSet', () => {
    expect(() => MatrixSet(2.5, 2, Reals)).toThrow('should be a nonnegative integer.');
    expect(() => MatrixSet(-1, 2, Reals)).toThrow('The dimension specification -1 should be a nonnegative integer.');
    expect(MatrixSet(1, 1, Reals).contains(Matrix.of([[1]]))).toBe(true);
    expect(() => MatrixSet(1, 1, Reals).contains(1)).toThrow('1 should be an instance of MatrixExpr.');
    // SymPy leaves Contains(C, MatrixSet(n, n, Reals)) unevaluated
    expect(MatrixSet(n, n, Reals).contains(C)).toBe('unknown');
    expect(MatrixSet(2, 2, Reals).contains(MatrixSymbol('Z', n, n))).toBe('unknown');
    expect(MatrixSet(3, 3, Reals).contains(C)).toBe(false);
    expect(s(MatrixSet(n, 2, Reals).subs(n, 3))).toBe('MatrixSet(3, 2, Reals)');
    // SymPy: \operatorname{MatrixSet}\left(n, 2, \left[0, 1\right]\right); the LaTeX printer has no rule for sets yet,
    // so only the part printed by MatrixSet is compared
    expect(latex(MatrixSet(n, 2, Interval.of(0, 1)))).toMatch(/^\\operatorname\{MatrixSet\}\\left\(n, 2, .*\\right\)$/);
  });
  it('factorizations', () => {
    expect(s(LofLU(X).subs(X, Y))).toBe('LofLU(Y)');
  });
});

describe('remaining branches (SymPy 1.14)', () => {
  it('CompanionMatrix LaTeX of polynomial domains', () => {
    const q = symbol('k');
    expect(latex(CompanionMatrix(Poly.from(x.pow(2).add(q), [x])))).toBe(
      '\\operatorname{CompanionMatrix}\\left(\\operatorname{Poly}{\\left( x^{2} + k, x, domain=\\mathbb{Z}\\left[k\\right] \\right)}\\right)',
    );
    expect(latex(CompanionMatrix(Poly.from(x.pow(2).add(q.mul(q.add(1).pow(-1))), [x])))).toBe(
      '\\operatorname{CompanionMatrix}\\left(\\operatorname{Poly}{\\left( x^{2} + \\frac{k}{k + 1}, x, domain=\\mathbb{Z}\\left(k\\right) \\right)}\\right)',
    );
    expect(latex(CompanionMatrix(Poly.from(x.pow(3).add(q.add(1).mul(x.pow(2))).sub(x).add(q).add(2), [x])))).toBe(
      '\\operatorname{CompanionMatrix}\\left(\\operatorname{Poly}{\\left( x^{3} + \\left(k + 1\\right) x^{2} - x + k + 2, x, domain=\\mathbb{Z}\\left[k\\right] \\right)}\\right)',
    );
    expect(latex(CompanionMatrix(Poly.from(x.pow(3).sub(x.mul(2)).sub(3), [x])))).toBe(
      '\\operatorname{CompanionMatrix}\\left(\\operatorname{Poly}{\\left( x^{3} - 2 x - 3, x, domain=\\mathbb{Z} \\right)}\\right)',
    );
    expect(latex(CompanionMatrix(Poly.from(x.pow(2).add(sqrt(2)), [x])))).toBe(
      '\\operatorname{CompanionMatrix}\\left(\\operatorname{Poly}{\\left( x^{2} + \\sqrt{2}, x, domain=\\mathtt{\\text{EX}} \\right)}\\right)',
    );
    expect(latex(CompanionMatrix(Poly.from(x.pow(2).add(I), [x])))).toBe(
      '\\operatorname{CompanionMatrix}\\left(\\operatorname{Poly}{\\left( x^{2} + i, x, domain=\\mathtt{\\text{ZZ\\_I}} \\right)}\\right)',
    );
    expect(latex(CompanionMatrix(Poly.from(x, [x])))).toBe('\\operatorname{CompanionMatrix}\\left(\\operatorname{Poly}{\\left( x, x, domain=\\mathbb{Z} \\right)}\\right)');
  });
});

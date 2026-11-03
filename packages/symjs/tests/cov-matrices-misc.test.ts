// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * Coverage of the smaller matrix expression modules (DotProduct,
 * CompanionMatrix, MatrixSet, factorizations, Hadamard products and powers,
 * diagonal matrices, FunctionMatrix, DFT and from_index_summation), with the
 * expected values of SymPy 1.14.
 */

import { describe, expect, it } from 'vitest';
import { I, Integral, Interval, Lambda, Matrix, Poly, Rational, Reals, Sum, SymFunction as UFunction, latex, mul, sstr, sqrt, symbol, symbols } from '../src';
import { relTruth } from '../src/matrices/expressions/util';
import type { Expr } from '../src';
import {
  CompanionMatrix,
  DFT,
  DiagMatrix,
  DiagonalMatrix,
  DiagonalOf,
  DotProduct,
  FunctionMatrix,
  HadamardPower,
  HadamardProduct,
  IDFT,
  Inverse,
  LofLU,
  MatMul,
  MatrixSet,
  MatrixSymbol,
  OneMatrix,
  Transpose,
  canonicalize,
  fromIndexSummation,
  hadamardPower,
} from '../src/matrices/expressions';
import type { MatrixExpr } from '../src/matrices/expressions';

const s = (e: unknown): string => sstr(e as Expr);
const M = (e: Expr): MatrixExpr => e as MatrixExpr;
const [n, i, j, k] = symbols('n i j k', { integer: true });
const x = symbol('x');
const A = MatrixSymbol('A', 3, 1);
const B = MatrixSymbol('B', 1, 3);
const C = MatrixSymbol('C', 2, 2);
const X = MatrixSymbol('X', 2, 2);
const Y = MatrixSymbol('Y', 2, 2);

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

describe('FunctionMatrix and DFT', () => {
  it('FunctionMatrix', () => {
    expect(() => FunctionMatrix(2, 2, Lambda([i], i))).toThrow('should be able to accept 2 arguments.');
    expect(() => FunctionMatrix(2, 2, 'foo')).toThrow('foo should be compatible with SymPy function classes.');
    expect(s(FunctionMatrix(n, 2, Lambda([i, j], i.add(j))).subs(n, 3))).toBe('FunctionMatrix(3, 2, Lambda((i, j), i + j))');
  });
  it('DFT and IDFT', () => {
    expect(s(DFT(n).at(i, j))).toBe('exp(-2*I*pi*i*j/n)/sqrt(n)');
    expect(s(DFT(n).subs(n, 3))).toBe('DFT(3)');
    expect(s(IDFT(n).subs(n, 3))).toBe('IDFT(3)');
    expect(s(IDFT(3).at(1, 2))).toBe('sqrt(3)*exp(-2*I*pi/3)/3');
    expect(s(IDFT(n).I)).toBe('DFT(n)');
    expect(s(M(Inverse(IDFT(n))).doit())).toBe('DFT(n)');
  });
});

describe('from_index_summation', () => {
  const N = symbol('N', { integer: true });
  const [l] = symbols('l', { integer: true });
  const An = MatrixSymbol('A', N, N);
  const Bn = MatrixSymbol('B', N, N);
  const Cn = MatrixSymbol('C', N, N);
  const Nm1 = N.sub(1);
  const ab = mul(An.at(i, j), Bn.at(j, k));
  it('errors', () => {
    // SymPy gives j*A*B, which drops the dependence of the coefficient on the summation index
    expect(() => fromIndexSummation(Sum(mul(j, ab), [j, 0, Nm1]))).toThrow('cannot convert j');
    expect(() => fromIndexSummation(Sum(ab, [j, 0, N.sub(2)]))).toThrow('summation index and array dimension mismatch: j');
    expect(() => fromIndexSummation(Sum(ab, [j, 1, Nm1]))).toThrow('summation index and array dimension mismatch: j');
    // SymPy gives the array expressions ArrayDiagonal(ArrayTensorProduct(A, B), (1, 2)) and ArrayTensorProduct(A, B)
    expect(() => fromIndexSummation(ab)).toThrow('an index appears twice without summation');
    expect(() => fromIndexSummation(mul(An.at(i, j), Bn.at(k, l)))).toThrow('unsupported index structure');
  });
  it('first and last indices', () => {
    // SymPy gives A*B for last_index=i and B.T*A.T for last_index=k, the transposes of
    // the matrices whose row index is the other free index
    expect(s(fromIndexSummation(Sum(ab, [j, 0, Nm1]), undefined, i))).toBe('B.T*A.T');
    expect(s(fromIndexSummation(Sum(ab, [j, 0, Nm1]), undefined, k))).toBe('A*B');
    expect(s(fromIndexSummation(Sum(ab, [j, 0, Nm1]), k, i))).toBe('B.T*A.T');
    expect(s(fromIndexSummation(Sum(ab, [j, 0, Nm1]), k))).toBe('B.T*A.T');
  });
  it('sums', () => {
    // SymPy raises TypeError (Mix of Matrix and Scalar symbols)
    expect(s(fromIndexSummation(Sum(An.at(i, i).add(Bn.at(i, i)), [i, 0, Nm1])))).toBe('Trace(A) + Trace(B)');
    // SymPy raises IndexError; the constant is summed N times
    expect(s(fromIndexSummation(Sum(An.at(i, i).add(2), [i, 0, Nm1])))).toBe('2*N + Trace(A)');
    // SymPy gives A*B + C; C[i, k] does not depend on j and is summed N times
    expect(s(fromIndexSummation(Sum(ab.add(Cn.at(i, k)), [j, 0, Nm1])))).toBe('N*C + A*B');
    expect(s(fromIndexSummation(Sum(mul(3, An.at(i, i)), [i, 0, Nm1])))).toBe('3*Trace(A)');
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
  it('canonicalize of a non-Hadamard expression and diagonal lengths', () => {
    expect(s(canonicalize(X))).toBe('X');
    expect(s(DiagonalMatrix(MatrixSymbol('Z', 3, 2)).diagonalLength)).toBe('2');
  });
  it('DFT entries with non-integer indices', () => {
    const [a, b] = symbols('a b');
    expect(s(DFT(n).at(a, b))).toBe('exp(-2*I*pi/n)**(a*b)/sqrt(n)');
  });
  it('from_index_summation of an open chain of indices', () => {
    const N = symbol('N', { integer: true });
    const An = MatrixSymbol('A', N, N);
    const Bn = MatrixSymbol('B', N, N);
    // SymPy raises IndexError
    expect(() => fromIndexSummation(Sum(mul(An.at(i, j), Bn.at(j, j)), [i, 0, N.sub(1)], [j, 0, N.sub(1)]))).toThrow('unsupported index structure');
  });
  it('relational truth from the sign of the difference', () => {
    const ip = symbol('i', { integer: true, positive: true });
    const jn = symbol('j', { integer: true, nonnegative: true });
    expect(relTruth('Gt', n.add(ip), n)).toBe(true);
    expect(relTruth('Le', n.add(ip), n)).toBe(false);
    expect(relTruth('Ge', n.add(jn), n)).toBe(true);
    expect(relTruth('Lt', n.add(jn), n)).toBe(false);
    expect(relTruth('Ge', n.add(ip), n.add(ip.mul(2)))).toBe(false);
    expect(relTruth('Lt', n, k)).toBe('unknown');
    expect(relTruth('Eq', n, k)).toBe('unknown');
  });
  it('LaTeX precedence of scalar exponents', () => {
    const f = UFunction('f');
    expect(latex(HadamardPower(X, new Integral([f(x), x])))).toBe('X^{\\circ {\\int f{\\left(x \\right)}\\, dx}}');
    expect(latex(HadamardPower(X, Sum(f(k), [k, 0, n])))).toBe('X^{\\circ {\\sum_{k=0}^{n} f{\\left(k \\right)}}}');
    expect(latex(HadamardPower(X, x.add(1)))).toBe('X^{\\circ \\left({x + 1}\\right)}');
    expect(latex(HadamardPower(X, x.mul(2)))).toBe('X^{\\circ {2 x}}');
  });
});

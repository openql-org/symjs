// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/matrices/matrix.ts.
//
// The Matrix class: construction, arithmetic, indexing, slicing and the dense matrix methods. Expected
// values are SymPy 1.14 results.

import { describe, expect, it } from 'vitest';
import { type Expr, I, Matrix, mul, MutableMatrix, pi, Rational, sqrt, symbols } from '../../src';
import { inspect } from 'node:util';

const [a, b, c, d] = symbols('a b c d');
const [x, lam] = symbols('x lambda');
const s = (v: unknown): string => String(v);
const M = Matrix.of([[1, 2], [3, 4]]);

describe('Matrix', () => {
  it('basic algebra', () => {
    const m = Matrix.of([[a, b], [c, d]]);
    expect(m.det().toString()).toBe('a*d - b*c');
    expect(m.trace().toString()).toBe('a + d');
    expect(m.transpose().toString()).toBe('Matrix([[a, c], [b, d]])');
    expect(m.mul(Matrix.eye(2)).equals(m)).toBe(true);
    expect(m.inv().mul(m).simplify().equals(Matrix.eye(2))).toBe(true);
  });

  it('determinant of 3x3 via Berkowitz', () => {
    const m = Matrix.of([[2, 0, 1], [1, 3, 2], [1, 1, 2]]);
    expect(m.det().toString()).toBe('6');
    expect(Matrix.of([[a, b, 0], [c, d, 0], [0, 0, 1]]).det().toString()).toBe('a*d - b*c');
    expect(() => Matrix.of([[1, 2], [2, 4]]).inv()).toThrow(/singular/);
    expect(m.mul(m.inv()).equals(Matrix.eye(3))).toBe(true);
  });

  it('kronecker product', () => {
    const k = Matrix.kron(Matrix.of([[0, 1], [1, 0]]), Matrix.eye(2));
    expect(k.rows).toBe(4);
    expect(k.get(0, 2).toString()).toBe('1');
  });

  it('eigenvalues', () => {
    expect(Matrix.of([[0, 1], [1, 0]]).eigenvals().map(String)).toEqual(['-1', '1']);
    expect(Matrix.of([[0, mul(-1, I)], [I, 0]]).eigenvals().map(String)).toEqual(['-1', '1']);
    expect(Matrix.of([[2, 1], [1, 2]]).eigenvals().map(String)).toEqual(['1', '3']);
  });
});

describe('construction', () => {
  it('blocks, scalars and empty input', () => {
    // SymPy Matrix([[M, Matrix([5, 6])]])
    expect(s(Matrix.of([[M, Matrix.col(5, 6)]]))).toBe('Matrix([[1, 2, 5], [3, 4, 6]])');
    // SymPy Matrix([[Matrix([[1, 2]])], [Matrix([[3, 4]])]])
    expect(s(Matrix.of([[Matrix.row(1, 2)], [Matrix.row(3, 4)]]))).toBe('Matrix([[1, 2], [3, 4]])');
    // scalars next to blocks are 1x1 blocks: Matrix([[1, 2], [Matrix([[3, 4]])]]) has rows [1, 2] and [3, 4]
    expect(s(Matrix.of([[1, 2], [Matrix.row(3, 4)]]))).toBe('Matrix([[1, 2], [3, 4]])');
    // SymPy Matrix([[M], []]) raises (ZeroDivisionError)
    expect(() => Matrix.of([[M], []])).toThrow(RangeError);
    // SymPy Matrix([[1, 2], [3]]): ValueError mismatched dimensions
    expect(() => Matrix.of([[1, 2], [3]])).toThrow(RangeError);
    expect(s(Matrix.of([]))).toBe('Matrix(0, 0, [])');
    expect(s(Matrix.zeros(0, 3))).toBe('Matrix(0, 3, [])');
    expect(s(Matrix.zeros(2, 0))).toBe('Matrix(2, 0, [])');
    expect(s(Matrix.diag(1, 2))).toBe('Matrix([[1, 0], [0, 2]])');
    expect(s(Matrix.kron())).toBe('Matrix([[1]])');
  });

  it('index errors', () => {
    // SymPy: IndexError
    expect(() => M.get(2, 0)).toThrow(RangeError);
    expect(() => M.get(0, -1)).toThrow(RangeError);
    expect(() => M.with(0, 2, 1)).toThrow(RangeError);
  });
});

describe('arithmetic', () => {
  const X = Matrix.of([[0, 1], [1, 0]]);

  it('negation, scalar product and anticommutator', () => {
    expect(s(M.neg())).toBe('Matrix([[-1, -2], [-3, -4]])');
    expect(s(M.mul(x))).toBe('Matrix([[x, 2*x], [3*x, 4*x]])');
    expect(s(M.anticommutator(X))).toBe('Matrix([[5, 5], [5, 5]])');
  });

  it('shape errors', () => {
    // SymPy: ShapeError Matrix size mismatch
    expect(() => M.mul(Matrix.row(1, 2, 3))).toThrow(RangeError);
    expect(() => M.add(Matrix.row(1, 2, 3))).toThrow(RangeError);
    expect(() => M.hstack(Matrix.of([[1]]))).toThrow(RangeError);
    expect(() => M.vstack(Matrix.row(1, 2, 3))).toThrow(RangeError);
  });

  it('powers', () => {
    expect(s(M.pow(-1))).toBe('Matrix([[-2, 1], [3/2, -1/2]])');
    expect(s(M.pow(0))).toBe('Matrix([[1, 0], [0, 1]])');
    expect(s(M.pow(3))).toBe('Matrix([[37, 54], [81, 118]])');
    // SymPy: NonSquareMatrixError
    expect(() => Matrix.row(1, 2, 3).pow(2)).toThrow(RangeError);
    // non-integer powers are not supported (SymPy computes them from the Jordan form)
    expect(() => M.pow(0.5)).toThrow(RangeError);
  });
});

describe('linear algebra', () => {
  it('square-matrix errors', () => {
    const r = Matrix.row(1, 2, 3);
    // SymPy: NonSquareMatrixError for each
    expect(() => r.trace()).toThrow(RangeError);
    expect(() => r.det()).toThrow(RangeError);
    expect(() => r.adjugate()).toThrow(RangeError);
    expect(() => r.inv()).toThrow(RangeError);
    expect(() => r.charpolyCoeffs()).toThrow(RangeError);
  });

  it('small and empty matrices', () => {
    expect(s(Matrix.of([[x]]).det())).toBe('x');
    expect(s(Matrix.zeros(0).det())).toBe('1');
    expect(Matrix.zeros(0).charpolyCoeffs().map(s)).toEqual(['1']);
    expect(s(Matrix.zeros(0).charpoly(lam))).toBe('1');
    expect(s(Matrix.of([[x]]).adjugate())).toBe('Matrix([[1]])');
    expect(s(Matrix.of([[5]]).adjugate())).toBe('Matrix([[1]])');
  });

  it('dagger', () => {
    expect(s(Matrix.row(1, I).dagger())).toBe('Matrix([[1], [-I]])');
  });
});

describe('transformation', () => {
  it('subs, expand, evalf, toComplex', () => {
    expect(s(Matrix.of([[x]]).subs(x, 2))).toBe('Matrix([[2]])');
    expect(s(Matrix.of([[x]]).subs([[x, 2]]))).toBe('Matrix([[2]])');
    expect(s(Matrix.of([[mul(x, x.add(1))]]).expand())).toBe('Matrix([[x**2 + x]])');
    expect(s(Matrix.row(sqrt(2), pi).evalf(5))).toBe('Matrix([[1.4142, 3.1416]])');
    const c = Matrix.row(x, I).toComplex({ x: 2 });
    expect(c.map((r) => r.map((v) => [v.re, v.im]))).toEqual([[[2, 0], [0, 1]]]);
  });
});

describe('predicates and printing', () => {
  it('isSame', () => {
    expect(M.isSame(Matrix.of([[1, 2], [3, 4]]))).toBe(true);
    expect(M.isSame(MutableMatrix.of([[1, 2], [3, 4]]))).toBe(false);
    expect(M.isSame(Matrix.of([[1, 2]]))).toBe(false);
    expect(M.isSame('M')).toBe(false);
    const approx = (a: Expr, b: Expr): boolean => Math.abs(a.toComplex().re - b.toComplex().re) < 0.1;
    expect(Matrix.row(1, x).isSame(Matrix.row(Rational.of(21n, 20n), x), approx)).toBe(true);
    expect(Matrix.row(1, x).isSame(Matrix.row(Rational.of(3n, 2n), x), approx)).toBe(false);
  });

  it('LaTeX as SymPy latex(Matrix)', () => {
    expect(Matrix.of([[1, x], [x.pow(2), Rational.of(1n, 2n)]]).toLatex()).toBe(
      '\\left[\\begin{matrix}1 & x\\\\x^{2} & \\frac{1}{2}\\end{matrix}\\right]',
    );
    expect(Matrix.col(1, 2).toLatex()).toBe('\\left[\\begin{matrix}1\\\\2\\end{matrix}\\right]');
    expect(Matrix.zeros(0, 0).toLatex()).toBe('\\left[\\begin{matrix}\\end{matrix}\\right]');
    expect(Matrix.zeros(2, 0).toLatex()).toBe('\\left[\\begin{matrix}\\\\\\end{matrix}\\right]');
    expect(Matrix.fromFunction(1, 11, () => 1).toLatex()).toBe(
      '\\left[\\begin{array}{ccccccccccc}1 & 1 & 1 & 1 & 1 & 1 & 1 & 1 & 1 & 1 & 1\\end{array}\\right]',
    );
  });

  it('isUnitary, isHermitian and equalsSimplified on other shapes', () => {
    expect(Matrix.row(1, 2).isUnitary()).toBe(false);
    expect(Matrix.row(1, 2).isHermitian()).toBe(false);
    expect(M.equalsSimplified(Matrix.row(1, 2))).toBe(false);
  });

  it('inspect', () => {
    expect(inspect(M)).toBe('Matrix([[1, 2], [3, 4]])');
  });
});

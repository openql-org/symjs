// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/matrices/matrix.ts.
//
// The Matrix class: construction, arithmetic, indexing, slicing and the dense matrix methods. Expected
// values are SymPy 1.14 results.

import { describe, expect, it } from 'vitest';
import { type Expr, type ExprLike, fn, type FnName, I, Matrix, mul, MutableMatrix, NonInvertibleMatrixError, NonSquareMatrixError, parse, pi, Rational, ShapeError, sqrt, symbols } from '../../src';
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
    // SymPy: NonInvertibleMatrixError('Matrix det == 0; not invertible.')
    expect(() => Matrix.of([[1, 2], [2, 4]]).inv()).toThrow(NonInvertibleMatrixError);
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

  it('products keep their entries unexpanded, powers expand them (SymPy dotprodsimp)', () => {
    const A = Matrix.of([[x.add(1), b], [2, x]]);
    // SymPy: Matrix([[x + 1]])*Matrix([[x - 1]]) -> Matrix([[(x - 1)*(x + 1)]])
    expect(s(Matrix.of([[x.add(1)]]).mul(Matrix.of([[x.sub(1)]])))).toBe('Matrix([[(x - 1)*(x + 1)]])');
    expect(s(A.mul(A))).toBe('Matrix([[2*b + (x + 1)**2, b*x + b*(x + 1)], [4*x + 2, 2*b + x**2]])');
    expect(s(A.pow(2))).toBe('Matrix([[2*b + x**2 + 2*x + 1, 2*b*x + b], [4*x + 2, 2*b + x**2]])');
    // 1x1 and diagonal matrices are raised entrywise
    expect(s(Matrix.of([[x.add(1)]]).pow(2))).toBe('Matrix([[(x + 1)**2]])');
    expect(s(Matrix.of([[x.add(1), 0], [0, a]]).pow(3))).toBe('Matrix([[(x + 1)**3, 0], [0, a**3]])');
  });
});

describe('linear algebra', () => {
  it('square-matrix errors', () => {
    const r = Matrix.row(1, 2, 3);
    // SymPy: NonSquareMatrixError for each
    expect(() => r.trace()).toThrow(NonSquareMatrixError);
    expect(() => r.det()).toThrow(NonSquareMatrixError);
    expect(() => r.adjugate()).toThrow(NonSquareMatrixError);
    expect(() => r.inv()).toThrow(NonSquareMatrixError);
    expect(() => r.charpolyCoeffs()).toThrow(NonSquareMatrixError);
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

describe('eigenvals of a triangular matrix', () => {
  it('are the diagonal entries in order (SymPy eigenvals(multiple=True))', () => {
    expect(Matrix.of([[3, 1], [0, 1]]).eigenvals().map(String)).toEqual(['3', '1']);
    expect(Matrix.of([[1, 0], [2, 3]]).eigenvals().map(String)).toEqual(['1', '3']);
  });
});

describe('Matrix methods of SymPy MatrixBase', () => {
  const [y, z] = symbols('y z');
  const N = Matrix.of([[x, 1], [y, 2]]);
  const R9 = Matrix.fromFunction(3, 3, (i, j) => 3 * i + j);
  const R19 = Matrix.fromFunction(3, 3, (i, j) => 3 * i + j + 1);
  it('ones and from_dok', () => {
    expect(s(Matrix.ones(2, 3))).toBe('Matrix([[1, 1, 1], [1, 1, 1]])');
    expect(s(Matrix.ones(2))).toBe('Matrix([[1, 1], [1, 1]])');
    expect(s(Matrix.fromDok(2, 2, new Map<readonly [number, number], ExprLike>([[[0, 0], x], [[1, 1], 2]])))).toBe('Matrix([[x, 0], [0, 2]])');
  });
  it('copy, flat, tolist, values, todok, todod', () => {
    const c = N.copy();
    expect(c).not.toBe(N);
    expect(c.isSame(N)).toBe(true);
    expect(N.flat().map(s)).toEqual(['x', '1', 'y', '2']);
    expect(N.tolist().map((r) => r.map(s))).toEqual([['x', '1'], ['y', '2']]);
    const Z = Matrix.of([[0, 1], [2, 0]]);
    expect(Z.values().map(s)).toEqual(['1', '2']);
    expect([...Z.todok()].map(([k, v]) => [k, s(v)])).toEqual([[[0, 1], '1'], [[1, 0], '2']]);
    expect([...Z.todod()].map(([i, row]) => [i, [...row].map(([j, v]) => [j, s(v)])])).toEqual([[0, [[1, '1']]], [1, [[0, '2']]]]);
  });
  it('minors and cofactors', () => {
    expect(s(N.minorEntry(0, 1))).toBe('y');
    expect(s(N.minorMatrix(0, 1))).toBe('Matrix([[y]])');
    expect(s(R9.minorSubmatrix(1, -1))).toBe('Matrix([[0, 1], [6, 7]])');
    expect(s(R9.minorSubmatrix(-1, 0))).toBe('Matrix([[1, 2], [4, 5]])');
    expect(s(N.cofactor(0, 1))).toBe('-y');
    expect(s(N.cofactor(1, 1))).toBe('x');
    expect(() => Matrix.of([[1, 2, 3]]).cofactor(0, 1)).toThrow(NonSquareMatrixError);
  });
  it('triangular parts, diagonals, extract, reshape, rot90, vec, vech', () => {
    expect(s(R19.lowerTriangular())).toBe('Matrix([[1, 0, 0], [4, 5, 0], [7, 8, 9]])');
    expect(s(R19.lowerTriangular(1))).toBe('Matrix([[1, 2, 0], [4, 5, 6], [7, 8, 9]])');
    expect(s(R19.lowerTriangular(-1))).toBe('Matrix([[0, 0, 0], [4, 0, 0], [7, 8, 0]])');
    expect(s(R19.upperTriangular())).toBe('Matrix([[1, 2, 3], [0, 5, 6], [0, 0, 9]])');
    expect(s(R19.upperTriangular(1))).toBe('Matrix([[0, 2, 3], [0, 0, 6], [0, 0, 0]])');
    const R23 = Matrix.of([[1, 2, 3], [4, 5, 6]]);
    expect(s(R23.upperTriangular(-1))).toBe('Matrix([[1, 2, 3], [4, 5, 6]])');
    expect(s(R23.diagonal())).toBe('Matrix([[1, 5]])');
    expect(s(R23.diagonal(1))).toBe('Matrix([[2, 6]])');
    expect(s(R23.diagonal(-1))).toBe('Matrix([[4]])');
    expect(() => R23.diagonal(3)).toThrow('The 3 diagonal is out of range [-1, 2]');
    expect(() => R23.diagonal(-2)).toThrow(RangeError);
    expect(s(R9.extract([0, 2], [1, -1]))).toBe('Matrix([[1, 2], [7, 8]])');
    expect(s(R9.extract([true, false, true], [false, true, false]))).toBe('Matrix([[1], [7]])');
    expect(s(R9.extract([0, true], [-3]))).toBe('Matrix([[0], [3]])');
    expect(s(Matrix.fromFunction(2, 3, (i, j) => 3 * i + j).reshape(3, 2))).toBe('Matrix([[0, 1], [2, 3], [4, 5]])');
    expect(() => R23.reshape(4, 2)).toThrow('Invalid reshape parameters 4 2');
    expect(s(M.rot90())).toBe('Matrix([[3, 1], [4, 2]])');
    expect(s(M.rot90(2))).toBe('Matrix([[4, 3], [2, 1]])');
    expect(s(M.rot90(-1))).toBe('Matrix([[2, 4], [1, 3]])');
    expect(s(Matrix.of([[1, 2, 5], [3, 4, 6]]).rot90(3))).toBe('Matrix([[5, 6], [2, 4], [1, 3]])');
    expect(s(Matrix.of([[1, 3], [2, 4]]).vec())).toBe('Matrix([[1], [2], [3], [4]])');
    const Sy = Matrix.of([[1, 2], [2, 3]]);
    expect(s(Sy.vech())).toBe('Matrix([[1], [2], [3]])');
    expect(s(Sy.vech({ diagonal: false }))).toBe('Matrix([[2]])');
    expect(() => Matrix.of([[1, 2], [5, 3]]).vech()).toThrow('The matrix is not symmetric.');
    expect(s(Matrix.of([[1, 2], [5, 3]]).vech({ checkSymmetry: false }))).toBe('Matrix([[1], [5], [3]])');
    expect(() => Matrix.of([[1, 2, 3]]).vech()).toThrow(NonSquareMatrixError);
  });
  it('row_insert, col_insert', () => {
    expect(s(N.rowInsert(1, Matrix.of([[7, 8]])))).toBe('Matrix([[x, 1], [7, 8], [y, 2]])');
    expect(s(N.colInsert(1, Matrix.col(7, 8)))).toBe('Matrix([[x, 7, 1], [y, 8, 2]])');
    expect(s(N.colInsert(0, Matrix.col(7, 8)))).toBe('Matrix([[7, x, 1], [8, y, 2]])');
    // SymPy clamps the position and counts a negative one from the end
    expect(s(N.rowInsert(10, Matrix.of([[7, 8]])))).toBe('Matrix([[x, 1], [y, 2], [7, 8]])');
    expect(s(N.rowInsert(-1, Matrix.of([[7, 8]])))).toBe('Matrix([[x, 1], [7, 8], [y, 2]])');
    expect(s(N.rowInsert(-10, Matrix.of([[7, 8]])))).toBe('Matrix([[7, 8], [x, 1], [y, 2]])');
    expect(s(Matrix.zeros(0, 0).rowInsert(0, N))).toBe(s(N));
    expect(s(Matrix.zeros(0, 0).colInsert(0, N))).toBe(s(N));
    expect(() => N.rowInsert(0, Matrix.of([[1, 2, 3]]))).toThrow(ShapeError);
    expect(() => N.colInsert(0, Matrix.col(1, 2, 3))).toThrow(ShapeError);
  });
  it('permute', () => {
    expect(s(Matrix.eye(3).permute([[0, 2]]))).toBe('Matrix([[0, 0, 1], [0, 1, 0], [1, 0, 0]])');
    expect(s(R9.permute([[0, 1], [1, 2]], { orientation: 'cols' }))).toBe('Matrix([[1, 2, 0], [4, 5, 3], [7, 8, 6]])');
    expect(s(R9.permute([[0, 1], [1, 2]], { direction: 'backward' }))).toBe('Matrix([[6, 7, 8], [0, 1, 2], [3, 4, 5]])');
    expect(s(R9.permute([[0, 1], [1, 2]], { orientation: 'cols', direction: 'backward' }))).toBe('Matrix([[2, 0, 1], [5, 3, 4], [8, 6, 7]])');
    expect(s(R9.permute([2, 0, 1]))).toBe('Matrix([[6, 7, 8], [0, 1, 2], [3, 4, 5]])');
    expect(s(R9.permute([1, 2, 0], { direction: 'backward' }))).toBe('Matrix([[3, 4, 5], [6, 7, 8], [0, 1, 2]])');
    expect(s(R9.permute([]))).toBe(s(R9));
  });
  it('multiply, rmultiply, multiply_elementwise, project, hat, vee', () => {
    expect(s(N.multiply(N))).toBe('Matrix([[x**2 + y, x + 2], [x*y + 2*y, y + 4]])');
    expect(s(N.multiply(2))).toBe('Matrix([[2*x, 2], [2*y, 4]])');
    expect(() => N.multiply(Matrix.of([[1, 2, 3]]))).toThrow('Matrix size mismatch: (2, 2) * (1, 3).');
    expect(() => N.multiply(Matrix.of([[1, 2, 3]]))).toThrow(ShapeError);
    expect(s(N.rmultiply(Matrix.of([[1, 2]])))).toBe('Matrix([[x + 2*y, 5]])');
    expect(s(N.rmultiply(3))).toBe('Matrix([[3*x, 3], [3*y, 6]])');
    expect(s(Matrix.of([[1, 2]]).multiplyElementwise(Matrix.of([[3, 4]])))).toBe('Matrix([[3, 8]])');
    expect(() => Matrix.of([[1, 2]]).multiplyElementwise(Matrix.of([[3, 4, 5]]))).toThrow('Matrix shapes must agree (1, 2) != (1, 3)');
    expect(() => Matrix.of([[1, 2]]).multiplyElementwise(Matrix.of([[3], [4]]))).toThrow(ShapeError);
    expect(s(Matrix.of([[1, 1]]).project(Matrix.of([[1, 0]])))).toBe('Matrix([[1, 0]])');
    expect(s(Matrix.col(1, 2, 3).project(Matrix.col(0, 1, 1)))).toBe('Matrix([[0], [5/2], [5/2]])');
    expect(s(Matrix.col(1, 2, 3).hat())).toBe('Matrix([[0, -3, 2], [3, 0, -1], [-2, 1, 0]])');
    expect(() => Matrix.col(1, 2).hat()).toThrow('Dimensions incorrect, expected (3, 1), got (2, 1)');
    expect(() => Matrix.row(1, 2, 3).hat()).toThrow(ShapeError);
    expect(s(Matrix.of([[0, -3, 2], [3, 0, -1], [-2, 1, 0]]).vee())).toBe('Matrix([[1], [2], [3]])');
    expect(() => Matrix.of([[0, -3, 2], [3, 0, -1], [-2, 2, 0]]).vee()).toThrow('Matrix is not skew-symmetric');
    expect(() => Matrix.of([[0, 1], [2, 3]]).vee()).toThrow('Dimensions incorrect, expected (3, 3), got (2, 2)');
    expect(() => Matrix.zeros(3, 2).vee()).toThrow(ShapeError);
  });
  it('predicates', () => {
    expect(Matrix.of([[1, x], [x, 2]]).isSymmetric()).toBe(true);
    expect(Matrix.of([[1, x], [y, 2]]).isSymmetric()).toBe(false);
    const P = Matrix.of([[0, parse('x**2 + 2*x + 1')], [parse('(x + 1)**2'), 0]]);
    expect(P.isSymmetric()).toBe(true);
    expect(P.isSymmetric(false)).toBe(false);
    expect(Matrix.of([[1, 2, 3]]).isSymmetric()).toBe(false);
    expect(Matrix.of([[0, 1], [-1, 0]]).isAntiSymmetric()).toBe(true);
    expect(Matrix.of([[0, 1], [1, 0]]).isAntiSymmetric()).toBe(false);
    const Q = Matrix.of([[0, parse('x**2 + 2*x + 1')], [parse('-(x + 1)**2'), 0]]);
    expect(Q.isAntiSymmetric()).toBe(true);
    // SymPy is_anti_symmetric(simplify=False) is None here
    expect(Q.isAntiSymmetric(false)).toBe('unknown');
    expect(Matrix.of([[0, 1], [-1, 0]]).isAntiSymmetric(false)).toBe(true);
    expect(Matrix.of([[0, 1], [1, 0]]).isAntiSymmetric(false)).toBe(false);
    expect(Matrix.of([[0, 1, 2]]).isAntiSymmetric()).toBe(false);
    expect(Matrix.of([[1, 0], [0, 2]]).isDiagonal()).toBe(true);
    expect(Matrix.of([[1, 1], [0, 2]]).isDiagonal()).toBe(false);
    expect(Matrix.of([[1, 0, 0], [0, 2, 0]]).isDiagonal()).toBe(true);
    expect(Matrix.of([[1, 1], [0, 2]]).isUpper()).toBe(true);
    expect(Matrix.of([[1, 1], [0, 2]]).isLower()).toBe(false);
    expect(Matrix.of([[0, 1], [0, 0]]).isNilpotent()).toBe(true);
    expect(Matrix.of([[1, 1], [0, 0]]).isNilpotent()).toBe(false);
    expect(() => Matrix.of([[1, 1, 0]]).isNilpotent()).toThrow('Nilpotency is valid only for square matrices');
    expect(N.isSymbolic()).toBe(true);
    expect(Matrix.of([[1, 2]]).isSymbolic()).toBe(false);
    expect(N.has(x)).toBe(true);
    expect(N.has(z)).toBe(false);
    expect(N.has(x, z)).toBe(true);
    expect(N.atoms().map(s).sort()).toEqual(['1', '2', 'x', 'y']);
    expect(N.atoms((e) => e.isNumber === false).map(s).sort()).toEqual(['x', 'y']);
  });
  it('entrywise operations', () => {
    expect(s(Matrix.of([[pi, 1]]).n())).toBe('Matrix([[3.14159265358979, 1.00000000000000]])');
    expect(s(Matrix.of([[pi, 1]]).n(3))).toBe('Matrix([[3.14, 1.00]])');
    const [re, im] = N.asRealImag();
    expect(s(re)).toBe('Matrix([[re(x), 1], [re(y), 2]])');
    expect(s(im)).toBe('Matrix([[im(x), 0], [im(y), 0]])');
    expect(s(Matrix.of([[x.pow(2), y]]).diff(x))).toBe('Matrix([[2*x, 0]])');
    expect(s(Matrix.of([[x.pow(2), y]]).diff(x, 2))).toBe('Matrix([[2, 0]])');
    expect(s(Matrix.of([[x, y]]).integrate(x))).toBe('Matrix([[x**2/2, x*y]])');
    expect(s(Matrix.of([[x, y]]).integrate(x, [0, 1]))).toBe('Matrix([[1/2, y]])');
    expect(s(Matrix.of([[parse('sin(x)/x'), x]]).limit(x, 0))).toBe('Matrix([[1, 0]])');
    expect(s(Matrix.of([[x, y]]).xreplace([[x, z]]))).toBe('Matrix([[z, y]])');
    expect(s(Matrix.of([[x, y]]).replace(x, z))).toBe('Matrix([[z, y]])');
    expect(s(Matrix.of([[parse('sin(x)'), y]]).replace({ fn: 'sin' }, { fn: 'cos' }, { apply: (name, args) => fn(name as FnName, args) }))).toBe('Matrix([[cos(x), y]])');
  });
});

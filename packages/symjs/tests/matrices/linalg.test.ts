// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/matrices/linalg.ts.
//
// Matrix functions (exp, log, sqrt and analytic functions of a matrix), decompositions, eigenvalues
// and the other linear algebra routines. Expected values are SymPy 1.14 results.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { analyticFunc, I, log, Matrix, matrixLog, mul, oo, parse, parseExpr, Rational, S, simplify, sstr, symbols } from '../../src';
import * as L from '../../src/matrices/linalg';
import { isDiagonalizable, jordanForm } from '../../src/matrices/linalg';
import { MatrixError, NonInvertibleMatrixError, NonPositiveDefiniteMatrixError, NonSquareMatrixError, NotLoadedError } from '../../src/core/errors';

const q = (n: number) => Rational.of(n, 4);
const [x] = symbols('x');
const [y, a, b, c, d, t, n] = symbols('y a b c d t n');
const s = (v: unknown): string => String(v);
const M = (rows: Parameters<typeof Matrix.of>[0]): Matrix => Matrix.of(rows);
const tuple = (vs: readonly unknown[]): string => vs.map(s).join(' | ');

describe('matrix functions (SymPy Matrix.log / analytic_func)', () => {
  it('log of a non-diagonalizable matrix', () => {
    expect(String(matrixLog(Matrix.of([[1, 1], [0, 1]])))).toBe('Matrix([[0, 1], [0, 0]])');
  });
  it('log of a symmetric matrix', () => {
    expect(String(matrixLog(Matrix.of([[q(5), q(3)], [q(3), q(5)]])))).toBe('Matrix([[0, log(2)], [log(2), 0]])');
    expect(String(matrixLog(Matrix.of([[q(3), q(5)], [q(5), q(3)]])))).toBe('Matrix([[I*pi/2, log(2) - I*pi/2], [log(2) - I*pi/2, I*pi/2]])');
  });
  it('analytic_func with an explicit function', () => {
    expect(String(analyticFunc(Matrix.of([[q(5), q(3)], [q(3), q(5)]]), log(x), x))).toBe('Matrix([[0, log(2)], [log(2), 0]])');
  });
});

describe('matrix solving and constructions', () => {
  it('match SymPy', async () => {
    const { Matrix, matrixSolve, gaussJordanSolve, solveLeastSquares, GramSchmidt, hessian, wronskian, casoratian, normalized } = await import('../../src');
    const [x, y, n] = symbols('x y n');
    const A = Matrix.of([[2, 1], [1, 3]]);
    expect(String(matrixSolve(A, Matrix.col(1, 2)))).toBe('Matrix([[1/5], [3/5]])');
    const [sol, params] = gaussJordanSolve(Matrix.of([[1, 2], [2, 4]]), Matrix.col(3, 6));
    expect([String(sol), String(params)]).toEqual(['Matrix([[3 - 2*tau0], [tau0]])', 'Matrix([[tau0]])']);
    expect(String(solveLeastSquares(Matrix.of([[1, 2], [3, 4], [5, 6]]), Matrix.col(1, 2, 4)))).toBe('Matrix([[2/3], [1/12]])');
    expect(GramSchmidt([Matrix.col(3, 1), Matrix.col(2, 2)]).map(String)).toEqual(['Matrix([[3], [1]])', 'Matrix([[-2/5], [6/5]])']);
    expect(String(hessian(parse('x**2*y'), [x, y]))).toBe('Matrix([[2*y, 2*x], [2*x, 0]])');
    expect(sstr(wronskian([parse('sin(x)'), parse('cos(x)')], x))).toBe('-sin(x)**2 - cos(x)**2');
    expect(sstr(casoratian([1, parse('2**n')], n))).toBe('1');
    expect(String(normalized(Matrix.col(3, 4)))).toBe('Matrix([[3/5], [4/5]])');
  });
});

describe('jordan_form', () => {
  it('gives A = P*J*P**-1 with Jordan blocks', async () => {
    const { Matrix, jordanForm, simplify: simp } = await import('../../src');
    const cases = [
      [[5, 4, 2, 1], [0, 1, -1, -1], [-1, -1, 3, 0], [1, 1, -1, 2]],
      [[2, 1], [0, 2]],
      [[1, 2], [3, 4]],
      [[2, 0, 0], [0, 2, 0], [0, 0, 3]],
      [[0, 1, 0], [0, 0, 1], [0, 0, 0]],
    ];
    const Js: string[] = [];
    for (const rows of cases) {
      const A = Matrix.of(rows);
      const [P, J] = jordanForm(A);
      const back = P.mul(J).mul(P.inv()).map((e) => simp(e));
      expect(String(back)).toBe(String(A));
      Js.push(String(J));
    }
    expect(Js[0]).toBe('Matrix([[1, 0, 0, 0], [0, 2, 0, 0], [0, 0, 4, 1], [0, 0, 0, 4]])');
    expect(Js[4]).toBe('Matrix([[0, 1, 0], [0, 0, 1], [0, 0, 0]])');
  });
});

describe('row reduction and spaces', () => {
  it('echelon_form', () => {
    expect(s(L.echelonForm(M([[1, 2, 3], [2, 4, 6], [1, 0, 1]])))).toBe('Matrix([[1, 2, 3], [0, -2, -2], [0, 0, 0]])');
    expect(s(L.echelonForm(M([[0, 1], [2, 3], [4, 5]])))).toBe('Matrix([[2, 3], [0, 1], [0, 0]])');
    expect(s(L.echelonForm(M([[a, b], [c, d]])))).toBe('Matrix([[a, b], [0, a*d - b*c]])');
    expect(s(L.echelonForm(Matrix.zeros(0, 3)))).toBe('Matrix(0, 3, [])');
  });

  it('rref of an empty matrix', () => {
    const [R, p] = L.rref(Matrix.zeros(0, 3));
    expect(s(R)).toBe('Matrix(0, 3, [])');
    expect(p).toEqual([]);
  });

  it('columnspace and rowspace', () => {
    const m = M([[1, 2, 3], [2, 4, 6], [1, 0, 1]]);
    expect(tuple(L.columnspace(m))).toBe('Matrix([[1], [2], [1]]) | Matrix([[2], [4], [0]])');
    expect(tuple(L.rowspace(m))).toBe('Matrix([[1, 2, 3]]) | Matrix([[0, -2, -2]])');
    expect(tuple(L.rowspace(M([[0, 0], [1, 2]])))).toBe('Matrix([[1, 2]])');
  });
});

describe('eigen decomposition', () => {
  it('is_diagonalizable', () => {
    expect(L.isDiagonalizable(M([[1, 1], [0, 1]]))).toBe(false);
    expect(L.isDiagonalizable(M([[0, -1], [1, 0]]), true)).toBe(false);
    expect(L.isDiagonalizable(M([[0, -1], [1, 0]]))).toBe(true);
    expect(L.isDiagonalizable(M([[2, 1], [1, 2]]), true)).toBe(true);
    expect(L.isDiagonalizable(M([[1, 2, 3], [4, 5, 6]]))).toBe(false);
  });

  it('diagonalize of a defective matrix raises MatrixError', () => {
    expect(() => L.diagonalize(M([[1, 1], [0, 1]]))).toThrow(MatrixError);
  });

  it('analytic_func needs a square matrix', () => {
    expect(() => L.analyticFunc(M([[1, 2]]), x, x)).toThrow(NonSquareMatrixError);
  });
});

describe('decompositions', () => {
  const A = M([[4, 2], [2, 3]]);
  const A3 = M([[25, 15, -5], [15, 18, 0], [-5, 0, 11]]);
  const H = M([[2, I], [mul(-1, I), 2]]);

  it('cholesky', () => {
    expect(s(L.cholesky(A))).toBe('Matrix([[2, 0], [1, sqrt(2)]])');
    expect(s(L.cholesky(A, false))).toBe('Matrix([[2, 0], [1, sqrt(2)]])');
    expect(s(L.cholesky(A3))).toBe('Matrix([[5, 0, 0], [3, 3, 0], [-1, 1, 3]])');
    expect(s(L.cholesky(H))).toBe('Matrix([[sqrt(2), 0], [-sqrt(2)*I/2, sqrt(6)/2]])');
    expect(() => L.cholesky(M([[1, 2, 3], [4, 5, 6]]))).toThrow(NonSquareMatrixError);
  });

  it('cholesky raises like SymPy', () => {
    // SymPy: NonPositiveDefiniteMatrixError('Matrix must be positive-definite')
    expect(() => L.cholesky(M([[1, 2], [2, 1]]))).toThrow(NonPositiveDefiniteMatrixError);
    expect(() => L.cholesky(M([[0]]))).toThrow(NonPositiveDefiniteMatrixError);
    expect(() => L.cholesky(M([[new sj.Sym('w', { negative: true })]]))).toThrow(NonPositiveDefiniteMatrixError);
    // without the Hermitian requirement there is no positivity check
    expect(s(L.cholesky(M([[1, 2], [2, 1]]), false))).toBe('Matrix([[1, 0], [2, sqrt(3)*I]])');
    expect(s(L.cholesky(M([[-1]]), false))).toBe('Matrix([[I]])');
    // SymPy raises ValueError for these
    expect(() => L.cholesky(M([[1, 2], [3, 1]]))).toThrow('Matrix must be Hermitian.');
    expect(() => L.cholesky(M([[1, 2], [3, 1]]), false)).toThrow('Matrix must be symmetric.');
    expect(() => L.cholesky(M([[I]]))).toThrow('Matrix must be Hermitian.');
    // a value that cannot be evaluated numerically is decided by the assumptions
    expect(s(L.cholesky(M([[parse('Abs(f(1))')]])))).toBe('Matrix([[sqrt(Abs(f(1)))]])');
  });

  it('LDLdecomposition', () => {
    expect(tuple(L.ldl(A))).toBe('Matrix([[1, 0], [1/2, 1]]) | Matrix([[4, 0], [0, 2]])');
    expect(tuple(L.ldl(A, false))).toBe('Matrix([[1, 0], [1/2, 1]]) | Matrix([[4, 0], [0, 2]])');
    expect(tuple(L.ldl(H))).toBe('Matrix([[1, 0], [-I/2, 1]]) | Matrix([[2, 0], [0, 3/2]])');
    expect(tuple(L.ldl(A3))).toBe('Matrix([[1, 0, 0], [3/5, 1, 0], [-1/5, 1/3, 1]]) | Matrix([[25, 0, 0], [0, 9, 0], [0, 0, 9]])');
  });

  it('LUdecomposition with row swaps', () => {
    const lu = (m: Matrix) => {
      const [l, u, p] = L.luDecomposition(m);
      return `${s(l)} | ${s(u)} | ${JSON.stringify(p)}`;
    };
    expect(lu(M([[0, 1], [1, 1]]))).toBe('Matrix([[1, 0], [0, 1]]) | Matrix([[1, 1], [0, 1]]) | [[0,1]]');
    expect(lu(M([[0, 0, 1], [0, 2, 3], [4, 5, 6]]))).toBe(
      'Matrix([[1, 0, 0], [0, 1, 0], [0, 0, 1]]) | Matrix([[4, 5, 6], [0, 2, 3], [0, 0, 1]]) | [[0,2]]',
    );
    expect(lu(M([[1, 2, 3], [2, 4, 5], [3, 7, 1]]))).toBe(
      'Matrix([[1, 0, 0], [3, 1, 0], [2, 0, 1]]) | Matrix([[1, 2, 3], [0, 1, -8], [0, 0, -1]]) | [[1,2]]',
    );
    expect(lu(M([[1, 2, 3], [4, 5, 6]]))).toBe('Matrix([[1, 0], [4, 1]]) | Matrix([[1, 2, 3], [0, -3, -6]]) | []');
    expect(lu(M([[1, 2], [3, 4], [5, 6]]))).toBe('Matrix([[1, 0, 0], [3, 1, 0], [5, 2, 1]]) | Matrix([[1, 2], [0, -2], [0, 0]]) | []');
  });

  it('LUdecomposition of rank-deficient and tall matrices (rankcheck=False)', () => {
    const lu = (m: Matrix) => {
      const [l, u, p] = L.luDecomposition(m);
      return `${s(l)} | ${s(u)} | ${JSON.stringify(p)}`;
    };
    expect(lu(M([[0, 1], [0, 2]]))).toBe('Matrix([[1, 0], [2, 1]]) | Matrix([[0, 1], [0, 0]]) | []');
    expect(lu(M([[1, 2, 3], [2, 4, 7], [3, 6, 1]]))).toBe('Matrix([[1, 0, 0], [2, 1, 0], [3, -8, 1]]) | Matrix([[1, 2, 3], [0, 0, 1], [0, 0, 0]]) | []');
    expect(lu(M([[1, 2], [3, 4], [5, 6], [7, 9]]))).toBe(
      'Matrix([[1, 0, 0, 0], [3, 1, 0, 0], [5, 2, 1, 0], [7, 5/2, 0, 1]]) | Matrix([[1, 2], [0, -2], [0, 0], [0, 0]]) | []',
    );
    expect(lu(M([[0, 0], [0, 0]]))).toBe('Matrix([[1, 0], [0, 1]]) | Matrix([[0, 0], [0, 0]]) | []');
    expect(lu(M([[0, 1, 2], [1, 2, 3], [0, 0, 1]]))).toBe('Matrix([[1, 0, 0], [0, 1, 0], [0, 0, 1]]) | Matrix([[1, 2, 3], [0, 1, 2], [0, 0, 1]]) | [[0,1]]');
    expect(lu(M([[1, 2, 3, 4], [2, 4, 6, 9], [1, 1, 1, 1]]))).toBe(
      'Matrix([[1, 0, 0], [1, 1, 0], [2, 0, 1]]) | Matrix([[1, 2, 3, 4], [0, -1, -2, -3], [0, 0, 0, 1]]) | [[1,2]]',
    );
    expect(lu(M([[1, 2, 3], [2, 4, 6], [3, 6, 10]]))).toBe('Matrix([[1, 0, 0], [3, 1, 0], [2, 0, 1]]) | Matrix([[1, 2, 3], [0, 0, 1], [0, 0, 0]]) | [[1,2]]');
    expect(lu(M([[1, 2, 3], [2, 4, 6], [3, 6, 9]]))).toBe('Matrix([[1, 0, 0], [2, 1, 0], [3, 0, 1]]) | Matrix([[1, 2, 3], [0, 0, 0], [0, 0, 0]]) | []');
    expect(lu(Matrix.zeros(0, 2))).toBe('Matrix(0, 0, []) | Matrix(0, 2, []) | []');
  });

  it('QRdecomposition skips dependent columns', () => {
    expect(tuple(L.qrDecomposition(M([[1, 1, 2], [1, 0, 1], [0, 1, 1]])))).toBe(
      'Matrix([[sqrt(2)/2, sqrt(6)/6], [sqrt(2)/2, -sqrt(6)/6], [0, sqrt(6)/3]]) | Matrix([[sqrt(2), sqrt(2)/2, 3*sqrt(2)/2], [0, sqrt(6)/2, sqrt(6)/2]])',
    );
    expect(tuple(L.qrDecomposition(M([[1, 2, 0], [1, 2, 1], [0, 0, 1]])))).toBe(
      'Matrix([[sqrt(2)/2, -sqrt(6)/6], [sqrt(2)/2, sqrt(6)/6], [0, sqrt(6)/3]]) | Matrix([[sqrt(2), 2*sqrt(2), sqrt(2)/2], [0, 0, sqrt(6)/2]])',
    );
  });
});

describe('vector operations and norms', () => {
  it('dot', () => {
    const u = Matrix.col(1, I);
    const v = Matrix.col(I, 2);
    expect(s(L.dot(u, v))).toBe('3*I');
    expect(s(L.dot(u, v, true))).toBe('-I');
    expect(s(L.dot(u, v, true, 'physics'))).toBe('I');
    expect(() => L.dot(u, Matrix.col(1, 2, 3))).toThrow(RangeError);
  });

  it('cross', () => {
    expect(s(L.cross(Matrix.row(1, 2, 3), Matrix.row(4, 5, 6)))).toBe('Matrix([[-3, 6, -3]])');
    expect(s(L.cross(Matrix.col(1, 2, 3), Matrix.col(4, 5, 6)))).toBe('Matrix([[-3], [6], [-3]])');
    expect(() => L.cross(Matrix.col(1, 2), Matrix.col(1, 2))).toThrow(RangeError);
    // with vectors of @symjs/symjs/vector: sympy.vector.cross and dot
    const C = sj.CoordSys3D('C');
    expect(s(L.cross(C.i, C.j))).toBe('C.k');
    expect(s(L.dot(C.i, C.i))).toBe('1');
    expect(() => L.dot(Matrix.col(1, 2, 3), C.i)).toThrow('dot: a matrix and a vector');
    const saved = L.vectorProducts.cross;
    delete L.vectorProducts.cross;
    try {
      expect(() => L.cross(C.i, C.j)).toThrow(NotLoadedError);
    } finally {
      L.vectorProducts.cross = saved;
    }
  });

  it('singular_values', () => {
    expect(L.singularValues(M([[1, 2], [2, 1]])).map(s)).toEqual(['3', '1']);
    expect(L.singularValues(M([[1, 0, 0], [0, 2, 0]])).map(s)).toEqual(['2', '1', '0']);
  });

  it('vector norms', () => {
    const v = Matrix.col(3, -4);
    expect(s(L.norm(v))).toBe('5');
    expect(s(L.norm(v, 2))).toBe('5');
    expect(s(L.norm(v, oo))).toBe('4');
    expect(s(L.norm(v, S.NegativeInfinity))).toBe('3');
    expect(s(L.norm(v, 1))).toBe('7');
    expect(s(L.norm(v, 3))).toBe('91**(1/3)');
    expect(s(L.norm(v, x))).toBe('(3**x + 4**x)**(1/x)');
    // SymPy: ValueError (Expected order to be Number, Symbol, oo)
    expect(() => L.norm(v, 'fro')).toThrow(RangeError);
  });

  it('matrix norms', () => {
    const m = M([[1, -2], [3, 4]]);
    expect(s(L.norm(m))).toBe('sqrt(30)');
    expect(s(L.norm(m, 'fro'))).toBe('sqrt(30)');
    expect(s(L.norm(m, 'f'))).toBe('sqrt(30)');
    expect(s(L.norm(m, 1))).toBe('6');
    expect(s(L.norm(m, oo))).toBe('7');
    expect(s(simplify(L.norm(m, 2).sub(parseExpr('sqrt(5*sqrt(5) + 15)'))))).toBe('0');
    expect(s(simplify(L.norm(m, -2).sub(parseExpr('sqrt(15 - 5*sqrt(5))'))))).toBe('0');
    // SymPy: NotImplementedError (Matrix Norms under development)
    expect(() => L.norm(m, 3)).toThrow(RangeError);
  });

  it('pinv and jacobian', () => {
    expect(s(L.pinv(M([[1, 2], [3, 4], [5, 6]])))).toBe('Matrix([[-4/3, -1/3, 2/3], [13/12, 1/3, -5/12]])');
    expect(s(L.pinv(M([[1, 2, 3], [4, 5, 6]])))).toBe('Matrix([[-17/18, 4/9], [-1/9, 1/9], [13/18, -2/9]])');
    expect(s(L.jacobian(Matrix.col(x.mul(y), x.add(y)), [x, y]))).toBe('Matrix([[y, x], [1, 1]])');
    expect(s(L.jacobian(Matrix.col(x.mul(y), x.add(y)), Matrix.row(x, y)))).toBe('Matrix([[y, x], [1, 1]])');
  });
});

describe('structural helpers', () => {
  const m = M([[1, 2, 3], [4, 5, 6], [7, 8, 9]]);

  it('triangular parts and diagonals', () => {
    expect(s(L.upperTriangular(m))).toBe('Matrix([[1, 2, 3], [0, 5, 6], [0, 0, 9]])');
    expect(s(L.upperTriangular(m, 1))).toBe('Matrix([[0, 2, 3], [0, 0, 6], [0, 0, 0]])');
    expect(s(L.lowerTriangular(m))).toBe('Matrix([[1, 0, 0], [4, 5, 0], [7, 8, 9]])');
    expect(s(L.lowerTriangular(m, -1))).toBe('Matrix([[0, 0, 0], [4, 0, 0], [7, 8, 0]])');
    expect(s(L.diagonal(m))).toBe('Matrix([[1, 5, 9]])');
    expect(s(L.diagonal(m, 1))).toBe('Matrix([[2, 6]])');
    expect(s(L.diagonal(m, -2))).toBe('Matrix([[7]])');
  });

  it('extract, reshape, rot90, vech, vec', () => {
    expect(s(L.extract(m, [0, -1], [1, 2]))).toBe('Matrix([[2, 3], [8, 9]])');
    expect(s(L.extract(m, [true, false, true], [0, 2]))).toBe('Matrix([[1, 3], [7, 9]])');
    expect(s(L.extract(m, [0, true], [2]))).toBe('Matrix([[3], [6]])');
    expect(s(L.reshape(M([[1, 2, 3], [4, 5, 6]]), 3, 2))).toBe('Matrix([[1, 2], [3, 4], [5, 6]])');
    expect(() => L.reshape(m, 2, 2)).toThrow(RangeError);
    const q = M([[1, 2], [3, 4]]);
    expect(s(L.rot90(q))).toBe('Matrix([[3, 1], [4, 2]])');
    expect(s(L.rot90(q, 2))).toBe('Matrix([[4, 3], [2, 1]])');
    expect(s(L.rot90(q, -1))).toBe('Matrix([[2, 4], [1, 3]])');
    expect(s(L.rot90(q, 0))).toBe('Matrix([[1, 2], [3, 4]])');
    const sym = M([[1, 2], [2, 3]]);
    expect(s(L.vech(sym))).toBe('Matrix([[1], [2], [3]])');
    expect(s(L.vech(sym, false))).toBe('Matrix([[2]])');
    expect(s(L.vec(m))).toBe('Matrix([[1], [4], [7], [2], [5], [8], [3], [6], [9]])');
  });

  it('predicates', () => {
    expect(L.isSymmetric(m)).toBe(false);
    expect(L.isSymmetric(M([[1, 2], [2, 3]]))).toBe(true);
    expect(L.isSymmetric(M([[1, 2, 3]]))).toBe(false);
    expect(L.isAntiSymmetric(M([[0, 1], [-1, 0]]))).toBe(true);
    expect(L.isAntiSymmetric(m)).toBe(false);
    expect(L.isAntiSymmetric(M([[1, 2, 3]]))).toBe(false);
    expect(L.isDiagonal(M([[1, 0], [0, 2]]))).toBe(true);
    expect(L.isDiagonal(m)).toBe(false);
    expect(L.isUpper(M([[1, 2], [0, 3]]))).toBe(true);
    expect(L.isUpper(m)).toBe(false);
    expect(L.isLower(M([[1, 0], [2, 3]]))).toBe(true);
    expect(L.isLower(m)).toBe(false);
    expect(L.isNilpotent(M([[0, 1], [0, 0]]))).toBe(true);
    expect(L.isNilpotent(m)).toBe(false);
    // SymPy: NonSquareMatrixError (Nilpotency is valid only for square matrices)
    expect(() => L.isNilpotent(M([[0, 1, 0]]))).toThrow(NonSquareMatrixError);
  });

  it('elementwise product, projection, Givens rotation, Jordan block, permanent', () => {
    expect(s(L.multiplyElementwise(M([[1, 2], [3, 4]]), M([[a, b], [c, d]])))).toBe('Matrix([[a, 2*b], [3*c, 4*d]])');
    expect(s(L.project(M([[1, 1]]), M([[1, 0]])))).toBe('Matrix([[1, 0]])');
    expect(s(L.project(Matrix.col(1, 2), Matrix.col(3, 4)))).toBe('Matrix([[33/25], [44/25]])');
    expect(s(L.rotGivens(0, 2, t))).toBe('Matrix([[cos(t), 0, sin(t)], [0, 1, 0], [-sin(t), 0, cos(t)]])');
    expect(s(L.rotGivens(1, 0, t, 2))).toBe('Matrix([[cos(t), -sin(t)], [sin(t), cos(t)]])');
    expect(s(L.jordanBlock(3, x, 'lower'))).toBe('Matrix([[x, 0, 0], [1, x, 0], [0, 1, x]])');
    expect(s(L.permanent(M([[1, 2], [3, 4], [5, 6]])))).toBe('64');
    expect(s(L.permanent(M([[a, b, c]])))).toBe('a + b + c');
    expect(s(L.permanent(Matrix.zeros(0, 0)))).toBe('1');
  });
});

describe('solving and constructions', () => {
  it('pinv_solve', () => {
    expect(s(L.pinvSolve(M([[1, 0], [0, 1], [1, 1]]), Matrix.col(1, 2, 3)))).toBe('Matrix([[1], [2]])');
    expect(s(L.pinvSolve(M([[1, 0], [0, 1], [1, 1]]), Matrix.col(1, 2, 3), Matrix.col(a, b)))).toBe('Matrix([[1], [2]])');
  });

  it('inconsistent and underdetermined systems', () => {
    expect(() => L.gaussJordanSolve(M([[1, 1], [1, 1]]), Matrix.col(1, 2))).toThrow(/no solution/);
    expect(() => L.matrixSolve(M([[1, 1], [1, 1]]), Matrix.col(1, 1))).toThrow(NonInvertibleMatrixError);
  });

  it('GramSchmidt', () => {
    expect(() => L.gramSchmidt([Matrix.col(1, 2), Matrix.col(2, 4)])).toThrow(RangeError);
    expect(tuple(L.gramSchmidt([Matrix.col(1, 1), Matrix.col(1, 0)], true))).toBe(
      'Matrix([[sqrt(2)/2], [sqrt(2)/2]]) | Matrix([[sqrt(2)/2], [-sqrt(2)/2]])',
    );
  });

  it('wronskian and casoratian', () => {
    expect(s(L.wronskian([], x))).toBe('1');
    expect(s(simplify(L.casoratian([parseExpr('2**n'), parseExpr('3**n')], n, false)))).toBe('6**n');
  });

  it('inv_mod errors', () => {
    expect(() => L.invMod(M([[1, 2], [3, 4]]), 2)).toThrow(NonInvertibleMatrixError);
    expect(() => L.invMod(M([[S.Half, 2], [3, 4]]), 5)).toThrow(TypeError);
  });

  it('permute_cols', () => {
    expect(s(L.permuteCols(M([[1, 2, 3], [4, 5, 6]]), [2, 0, 1]))).toBe('Matrix([[3, 1, 2], [6, 4, 5]])');
  });

  it('jordan_form needs a square matrix', () => {
    expect(() => L.jordanForm(M([[1, 2, 3]]))).toThrow(NonSquareMatrixError);
  });

  it('liupc and row_structure_symbolic_cholesky', () => {
    const sp = M([[1, 0, 3, 2], [0, 0, 1, 0], [4, 0, 0, 5], [0, 6, 7, 0]]);
    // SymPy SparseMatrix.liupc(): ([[0], [], [0], [1, 2]], [4, 3, 4, 4])
    const [R, parent] = L.liupc(sp);
    expect(R).toEqual([[0], [], [0], [1, 2]]);
    expect(parent).toEqual([4, 3, 4, 4]);
    expect(L.rowStructureSymbolicCholesky(sp)).toEqual([[0], [], [0], [1, 2]]);
  });

  it('irregular that does not fill the space', () => {
    expect(() => L.irregular(2, Matrix.of([[1], [1]]), Matrix.of([[2, 2]]), Matrix.of([[3]]))).toThrow(/fill the space/);
  });
});

describe('zero tests and helpers', () => {
  it('rref with an entry that expands to zero and with an unevaluated number', () => {
    const [R0, p0] = L.rref(M([[parseExpr('x*(x + 1) - x**2 - x'), 1]]));
    expect(s(R0)).toBe('Matrix([[0, 1]])');
    expect(p0).toEqual([1]);
    const [R1, p1] = L.rref(M([[parseExpr('f(1)'), 1]]));
    expect(s(R1)).toBe('Matrix([[1, 1/f(1)]])');
    expect(p1).toEqual([0]);
  });

  it('is_diagonalizable(reals_only) with an eigenvalue of unknown reality', () => {
    expect(L.isDiagonalizable(M([[parseExpr('f(1)'), 0], [0, 1]]), true)).toBe(false);
  });

  it('minors, cofactors and insertion', () => {
    const m = M([[1, 2, 3], [4, 5, 6], [7, 8, 10]]);
    expect(s(L.minorSubmatrix(m, 1, 1))).toBe('Matrix([[1, 3], [7, 10]])');
    expect(s(L.minorDet(m, 1, 1))).toBe('-11');
    expect(s(L.cofactor(m, 0, 1))).toBe('2');
    expect(s(L.cofactor(m, 1, 1))).toBe('-11');
    expect(s(L.rowInsert(m, 1, M([[0, 0, 0]])))).toBe('Matrix([[1, 2, 3], [0, 0, 0], [4, 5, 6], [7, 8, 10]])');
    expect(s(L.colInsert(m, 1, Matrix.col(0, 0, 0)))).toBe('Matrix([[1, 0, 2, 3], [4, 0, 5, 6], [7, 0, 8, 10]])');
  });

  it('rotation matrices', () => {
    expect(s(L.rotAxis1(t))).toBe('Matrix([[1, 0, 0], [0, cos(t), sin(t)], [0, -sin(t), cos(t)]])');
    expect(s(L.rotAxis2(t))).toBe('Matrix([[cos(t), 0, -sin(t)], [0, 1, 0], [sin(t), 0, cos(t)]])');
    expect(s(L.rotAxis3(t))).toBe('Matrix([[cos(t), sin(t), 0], [-sin(t), cos(t), 0], [0, 0, 1]])');
    expect(s(L.rotCcwAxis1(t))).toBe('Matrix([[1, 0, 0], [0, cos(t), -sin(t)], [0, sin(t), cos(t)]])');
    expect(s(L.rotCcwAxis2(t))).toBe('Matrix([[cos(t), 0, sin(t)], [0, 1, 0], [-sin(t), 0, cos(t)]])');
    expect(s(L.rotCcwAxis3(t))).toBe('Matrix([[cos(t), -sin(t), 0], [sin(t), cos(t), 0], [0, 0, 1]])');
  });

  it('liupc elimination trees with path compression', () => {
    const A = M([[1, 0, 0, 1], [0, 1, 0, 1], [0, 0, 1, 1], [1, 1, 1, 1]]);
    expect(L.liupc(A)).toEqual([[[0], [1], [2], [0, 1, 2, 3]], [3, 3, 3, 4]]);
    expect(L.rowStructureSymbolicCholesky(A)).toEqual([[0], [1], [2], [0, 1, 2, 3]]);
    const B = M([[1, 1, 0, 0, 1], [1, 1, 1, 0, 0], [0, 1, 1, 1, 0], [0, 0, 1, 1, 1], [1, 0, 0, 1, 1]]);
    expect(L.liupc(B)).toEqual([[[0], [0, 1], [1, 2], [2, 3], [0, 3, 4]], [1, 2, 3, 4, 5]]);
    expect(L.rowStructureSymbolicCholesky(B)).toEqual([[0], [0, 1], [1, 2], [2, 3], [0, 1, 2, 3, 4]]);
  });

  it('permute_rows with a partial list keeps the remaining rows', () => {
    // SymPy permute_rows([1, 0]) on three rows: Matrix([[4, 5, 6], [1, 2, 3], [7, 8, 10]])
    expect(s(L.permuteRows(M([[1, 2, 3], [4, 5, 6], [7, 8, 10]]), [1, 0]))).toBe('Matrix([[4, 5, 6], [1, 2, 3], [7, 8, 10]])');
    expect(s(L.permuteCols(M([[1, 2, 3]]), [1, 0]))).toBe('Matrix([[2, 1, 3]])');
  });
});

describe('matrices/linalg, linsys, domainmatrix, mutable', () => {
  it('is_diagonalizable with reals_only', () => {
    const r = sj.symbol('r', { real: true });
    const f = sj.SymFunction('f');
    // SymPy: False/True, True/True, False/True, False/True, True/True
    const cases: [Matrix, boolean, boolean][] = [
      [M([[x, 1], [0, 1]]), false, true],
      [M([[r, 1], [0, 1]]), true, true],
      [M([[f(1)]]), false, true],
      [M([[0, -1], [1, 0]]), false, true],
      [M([[1, 1], [0, 2]]), true, true],
    ];
    for (const [A, real, any] of cases) expect([isDiagonalizable(A, true), isDiagonalizable(A)]).toEqual([real, any]);
  });

  it('jordan_form of a float matrix', () => {
    // SymPy converts the Floats to Rationals (nsimplify) and evaluates the result at their precision:
    // P = Matrix([[-1.45442676678536, 0.427399739758336], [1.0, 1.0]]) (1.0 printed as 1.00000000000000 here)
    const [P, J] = jordanForm(M([[new sj.Float(1.1), new sj.Float(2.3)], [new sj.Float(3.7), new sj.Float(4.9)]]));
    expect(s(P)).toBe('Matrix([[-1.45442676678536, 0.427399739758336], [1.00000000000000, 1.00000000000000]])');
    expect(s(J)).toBe('Matrix([[-0.481379037105842, 0], [0, 6.48137903710584]])');
  });

  it('companion matrices of irreducible cubics (eigenvectors over the number field)', () => {
    const residual = (A: Matrix, P: Matrix, J: Matrix) => Math.max(...A.mul(P).sub(P.mul(J)).toComplex().flat().map((z) => Math.hypot(z.re, z.im)));
    // x**3 - 3*x + 1 (casus irreducibilis) and x**3 - x - 1; SymPy: is_diagonalizable() is True
    for (const A of [M([[0, 0, -1], [1, 0, 3], [0, 1, 0]]), M([[0, 0, 1], [1, 0, 1], [0, 1, 0]])]) {
      expect(isDiagonalizable(A)).toBe(true);
      const [P, J] = jordanForm(A);
      expect(residual(A, P, J)).toBeLessThan(1e-12);
      expect(Math.abs(P.det().toComplex().re) + Math.abs(P.det().toComplex().im)).toBeGreaterThan(1e-6);
    }
    // SymPy eigenvects: eigenvalues 0.347296355334, 1.53208888624, -1.87938524157 with the
    // eigenvectors [-2.87938524157, 0.347296355334, 1], [-0.652703644666, 1.53208888624, 1], [0.532088886238, -1.87938524157, 1]
    const ev = L.eigenvects(M([[0, 0, -1], [1, 0, 3], [0, 1, 0]])).map(([v, k, vs]) => `${s(sj.evalf(v, 12))} ${k} ${vs.map((u) => s(u.evalf(12))).join(' ')}`);
    expect(ev).toEqual([
      '0.347296355334 1 Matrix([[-2.87938524157], [0.347296355334], [1.00000000000]])',
      '1.53208888624 1 Matrix([[-0.652703644666], [1.53208888624], [1.00000000000]])',
      '-1.87938524157 1 Matrix([[0.532088886238], [-1.87938524157], [1.00000000000]])',
    ]);
    // a repeated irreducible cubic factor: the eigenspaces of the companion blocks over the number field
    const C = M([[0, 0, -1], [1, 0, 3], [0, 1, 0]]);
    const Z = Matrix.zeros(3);
    const D = Matrix.of([[C, Z], [Z, C]]);
    expect(isDiagonalizable(D)).toBe(true);
    expect(L.eigenvects(D).map(([, k, vs]) => [k, vs.length])).toEqual([[2, 2], [2, 2], [2, 2]]);
  });

  it('eigenvalues of a triangular matrix with an applied function (SymPy is_diagonalizable: True)', () => {
    const A = M([[parse('f(1)'), 1], [0, 2]]);
    expect(isDiagonalizable(A)).toBe(true);
    // SymPy: [(2, 1, [Matrix([[-1/(f(1) - 2)], [1]])]), (f(1), 1, [Matrix([[1], [0]])])]
    expect(L.eigenvects(A).map(([v, k, vs]) => `${s(v)} ${k} ${vs.map(s).join(' ')}`)).toEqual(['2 1 Matrix([[-1/(f(1) - 2)], [1]])', 'f(1) 1 Matrix([[1], [0]])']);
  });
});

describe('definiteness (SymPy is_positive_definite, is_positive_semidefinite, is_negative_definite, is_negative_semidefinite)', () => {
  const x = new sj.Sym('x');
  const p = new sj.Sym('p', { positive: true });
  const r = new sj.Sym('r', { real: true });
  // [matrix, positive definite, positive semidefinite, negative definite, negative semidefinite] from SymPy 1.14
  const cases: [string, sj.Matrix, sj.Truth, sj.Truth, sj.Truth, sj.Truth][] = [
    ['identity', Matrix.of([[1, 0], [0, 1]]), true, true, false, false],
    ['indefinite', Matrix.of([[1, 1], [1, -1]]), false, false, false, false],
    ['dominated', Matrix.of([[1, 2], [2, 1]]), false, false, false, false],
    ['tridiagonal', Matrix.of([[2, -1, 0], [-1, 2, -1], [0, -1, 2]]), true, true, false, false],
    ['zero', Matrix.of([[0, 0], [0, 0]]), false, true, false, true],
    ['symbolic', Matrix.of([[x, 0], [0, 1]]), 'unknown', 'unknown', false, false],
    ['not square', Matrix.of([[1, 2, 3], [4, 5, 6]]), false, false, false, false],
    ['not hermitian', Matrix.of([[1, 2], [0, 3]]), true, true, false, false],
    ['singular', Matrix.of([[0, 0], [0, 1]]), false, true, false, false],
    ['antidiagonal', Matrix.of([[0, 1], [1, 0]]), false, false, false, false],
    ['positive corner', Matrix.of([[p, 0], [0, 0]]), false, true, false, false],
    ['ones', Matrix.of([[1, 1], [1, 1]]), false, true, false, false],
    ['positive', Matrix.of([[2, 3], [3, 5]]), true, true, false, false],
    ['real corner', Matrix.of([[r, 0], [0, 0]]), false, 'unknown', false, 'unknown'],
    ['symbolic corner', Matrix.of([[0, 0], [0, x]]), false, 'unknown', false, 'unknown'],
    ['symbolic below', Matrix.of([[0, 0], [x, 0]]), false, 'unknown', false, 'unknown'],
    ['negative', Matrix.of([[-1, 0], [0, -2]]), false, false, true, true],
    ['signs', Matrix.of([[1, 0, 0], [0, 0, 0], [0, 0, -1]]), false, false, false, false],
    ['positive symbol', Matrix.of([[p, 1], [1, p]]), 'unknown', 'unknown', false, false],
    ['pivoting', Matrix.of([[4, 2, 2], [2, 1, 1], [2, 1, 3]]), false, true, false, false],
    ['rank one block', Matrix.of([[1, 2, 0], [2, 4, 0], [0, 0, 0]]), false, true, false, false],
  ];
  it.each(cases)('%s', (_name, m, pd, psd, nd, nsd) => {
    expect(L.isPositiveDefinite(m)).toBe(pd);
    expect(L.isPositiveSemidefinite(m)).toBe(psd);
    expect(L.isNegativeDefinite(m)).toBe(nd);
    expect(L.isNegativeSemidefinite(m)).toBe(nsd);
  });
});

describe('solving by decompositions and the inverse methods (SymPy matrices/solvers.py, inverse.py)', () => {
  const A = M([[2, 1], [1, 3]]);
  const singular = M([[1, 2], [2, 4]]);
  const nonsym = M([[1, 2], [3, 4]]);
  it('diagonal_solve, lower_triangular_solve, upper_triangular_solve', () => {
    expect(s(sj.diagonalSolve(M([[2, 0], [0, 3]]), M([[1], [2]])))).toBe('Matrix([[1/2], [2/3]])');
    expect(s(sj.diagonalSolve(M([[2, 0], [0, 0]]), M([[1], [2]])))).toBe('Matrix([[1/2], [zoo]])');
    expect(() => sj.diagonalSolve(M([[2, 1], [0, 3]]), M([[1], [2]]))).toThrow(new TypeError('Matrix should be diagonal'));
    expect(() => sj.diagonalSolve(M([[2, 0], [0, 3]]), M([[1], [2], [3]]))).toThrow(new TypeError('Size mismatch'));
    expect(s(sj.lowerTriangularSolve(M([[2, 0], [1, 3]]), M([[2], [7]])))).toBe('Matrix([[1], [2]])');
    expect(() => sj.lowerTriangularSolve(M([[2, 1], [1, 3]]), M([[2], [7]]))).toThrow('Matrix must be lower triangular.');
    expect(() => sj.lowerTriangularSolve(M([[2, 0, 0], [1, 3, 0]]), M([[2], [7]]))).toThrow(NonSquareMatrixError);
    expect(() => sj.lowerTriangularSolve(M([[2, 0], [1, 3]]), M([[2], [7], [1]]))).toThrow(sj.ShapeError);
    expect(() => sj.lowerTriangularSolve(M([[0, 0], [1, 3]]), M([[2], [7]]))).toThrow(new TypeError('Matrix must be non-singular.'));
    expect(s(sj.upperTriangularSolve(M([[2, 1], [0, 3]]), M([[4], [6]])))).toBe('Matrix([[1], [2]])');
    expect(s(sj.upperTriangularSolve(M([[2, 1], [0, 3]]), M([[4, 1], [6, 3]])))).toBe('Matrix([[1, 0], [2, 1]])');
    expect(() => sj.upperTriangularSolve(M([[2, 1], [1, 3]]), M([[4], [6]]))).toThrow(new TypeError('Matrix is not upper triangular.'));
    expect(() => sj.upperTriangularSolve(M([[2, 1], [0, 0]]), M([[4], [6]]))).toThrow('Matrix must be non-singular.');
    expect(() => sj.upperTriangularSolve(M([[2, 1, 1]]), M([[4]]))).toThrow(NonSquareMatrixError);
    expect(() => sj.upperTriangularSolve(M([[2, 1], [0, 3]]), M([[4]]))).toThrow(sj.ShapeError);
  });
  it('cholesky_solve', () => {
    expect(s(sj.choleskySolve(M([[4, 2], [2, 3]]), M([[1], [2]])))).toBe('Matrix([[-1/8], [3/4]])');
    // neither symmetric nor Hermitian: solved through A^H A
    expect(s(sj.choleskySolve(M([[4, 1], [2, 3]]), M([[1], [2]])))).toBe('Matrix([[1/10], [3/5]])');
    // Hermitian (SymPy: Matrix([[2/3], [I/3]]))
    expect(s(sj.choleskySolve(M([[2, I], [mul(-1, I), 2]]), M([[1], [0]])))).toBe('Matrix([[2/3], [I/3]])');
    // symmetric but not positive definite (SymPy: Matrix([[-1/3], [2/3]]))
    expect(s(sj.choleskySolve(M([[1, 2], [2, 1]]), M([[1], [0]])))).toBe('Matrix([[-1/3], [2/3]])');
    expect(() => sj.choleskySolve(M([[4, 2, 1], [2, 3, 1]]), M([[1], [2]]))).toThrow('Under-determined System. Try M.gauss_jordan_solve(rhs)');
  });
  it('cramer_solve', () => {
    expect(s(sj.cramerSolve(nonsym, M([[5], [6]])))).toBe('Matrix([[-4], [9/2]])');
    expect(s(sj.cramerSolve(M([[x, 1], [1, y]]), M([[1], [0]])))).toBe('Matrix([[y/(x*y - 1)], [-1/(x*y - 1)]])');
    expect(s(sj.cramerSolve(singular, M([[5], [6]])))).toBe('Matrix([[zoo], [zoo]])');
  });
  it('inverse_ADJ, inverse_BLOCK, inverse_CH, inverse_GE, inverse_LDL, inverse_LU, inverse_QR', () => {
    const methods = [sj.inverseADJ, sj.inverseBLOCK, sj.inverseCH, sj.inverseGE, sj.inverseLDL, sj.inverseLU, sj.inverseQR];
    for (const inv of methods) {
      expect(s(inv(A))).toBe('Matrix([[3/5, -1/5], [-1/5, 2/5]])');
      expect(s(inv(nonsym))).toBe('Matrix([[-2, 1], [3/2, -1/2]])');
      expect(() => inv(singular)).toThrow(new NonInvertibleMatrixError('Matrix det == 0; not invertible.'));
      expect(() => inv(M([[1, 2, 3]]))).toThrow(new NonSquareMatrixError('A Matrix must be square to invert.'));
    }
    // symbolic entries: SymPy prints inverse_ADJ alike; the other methods give equivalent forms
    // (SymPy inverse_GE: Matrix([[-y/(-x*y + 1), 1/(-x*y + 1)], [1/(-x*y + 1), -x/(-x*y + 1)]]))
    const S2 = M([[x, 1], [1, y]]);
    expect(s(sj.inverseADJ(S2))).toBe('Matrix([[y/(x*y - 1), -1/(x*y - 1)], [-1/(x*y - 1), x/(x*y - 1)]])');
    for (const inv of [sj.inverseGE, sj.inverseLU, sj.inverseLDL]) expect(inv(S2).equalsSimplified(sj.inverseADJ(S2))).toBe(true);
    // the block partition, reached with a small threshold (SymPy partitions above 20 rows)
    expect(s(sj.inverseBLOCK(M([[1, 2, 0], [3, 4, 1], [0, 1, 5]]), 1))).toBe('Matrix([[-19/11, 10/11, -2/11], [15/11, -5/11, 1/11], [-3/11, 1/11, 2/11]])');
    // a singular lower block: the LU inverse (SymPy: Matrix([[0, -1, 1], [-1, 0, 1], [1, 1, -1]]))
    expect(s(sj.inverseBLOCK(M([[1, 0, 1], [0, 1, 1], [1, 1, 1]]), 1))).toBe('Matrix([[0, -1, 1], [-1, 0, 1], [1, 1, -1]])');
    // an invertible lower block with a singular Schur complement: the matrix is singular
    expect(() => sj.inverseBLOCK(M([[1, 1, 0], [1, 1, 0], [0, 0, 1]]), 1)).toThrow(NonInvertibleMatrixError);
    expect(() => sj.inverseBLOCK(M([[1, 2, 3], [4, 5, 6]]), 1)).toThrow(NonSquareMatrixError);
  });
  it('condition_number, left_eigenvects', () => {
    expect(s(sj.conditionNumber(M([[1, 0], [0, 2]])))).toBe('2');
    expect(s(sj.conditionNumber(nonsym))).toBe('sqrt(sqrt(221) + 15)/sqrt(15 - sqrt(221))');
    expect(s(sj.conditionNumber(Matrix.zeros(0, 0)))).toBe('0');
    expect(tuple(sj.leftEigenvects(M([[2, 1], [0, 2]])).map(([v, k, vs]) => `${s(v)} ${k} ${vs.map(s).join()}`))).toBe('2 2 Matrix([[0, 1]])');
    // SymPy: [(5/2 - sqrt(33)/2, 1, [Matrix([[-sqrt(33)/4 - 3/4, 1]])]), (5/2 + sqrt(33)/2, 1, [Matrix([[-3/4 + sqrt(33)/4, 1]])])]
    const left = sj.leftEigenvects(nonsym);
    expect(left.map(([v, k]) => `${s(v)} ${k}`)).toEqual(['5/2 - sqrt(33)/2 1', '5/2 + sqrt(33)/2 1']);
    for (const [v, , [w]] of left) expect(w!.mul(nonsym).equalsSimplified(w!.scale(v))).toBe(true);
    expect(s(simplify(left[0]![2][0]!.get(0, 0)))).toBe('-sqrt(33)/4 - 3/4');
  });
  it('companion of a monic Poly', () => {
    expect(s(sj.companion(sj.Poly.from(parse('x**2 + 2*x + 3'), [x])))).toBe('Matrix([[0, -3], [1, -2]])');
    expect(s(sj.companion(sj.Poly.from(parse('x + 5'), [x])))).toBe('Matrix([[-5]])');
    expect(() => sj.companion(sj.Poly.from(parse('2*x**2 + 1'), [x]))).toThrow("Poly(2*x**2 + 1, x, domain='ZZ') must be a monic polynomial.");
    expect(() => sj.companion(sj.Poly.from(parse('3'), [x]))).toThrow(RangeError);
  });
  it('matrix_multiply_elementwise and the structural functions', () => {
    expect(s(sj.matrixMultiplyElementwise(M([[1, 2]]), M([[3, 4]])))).toBe('Matrix([[3, 8]])');
    expect(() => sj.matrixMultiplyElementwise(M([[1, 2]]), M([[3, 4, 5]]))).toThrow('Matrix shapes must agree (1, 2) != (1, 3)');
    expect(s(L.lowerTriangular(nonsym))).toBe('Matrix([[1, 0], [3, 4]])');
    expect(s(L.diagonal(nonsym, 1))).toBe('Matrix([[2]])');
    expect(s(L.extract(nonsym, [1], [0]))).toBe('Matrix([[3]])');
    expect(s(L.reshape(nonsym, 1, 4))).toBe('Matrix([[1, 2, 3, 4]])');
    expect(s(L.rot90(nonsym))).toBe('Matrix([[3, 1], [4, 2]])');
    expect(s(L.vec(nonsym))).toBe('Matrix([[1], [3], [2], [4]])');
    expect(s(L.vech(nonsym, true, false))).toBe('Matrix([[1], [3], [4]])');
    expect(s(L.minorSubmatrix(nonsym, 0, 0))).toBe('Matrix([[4]])');
    expect(s(L.minorDet(nonsym, 0, 1))).toBe('3');
    expect(L.isSymmetric(M([[0, parse('x**2 + 2*x + 1')], [parse('(x + 1)**2'), 0]]), false)).toBe(false);
    expect(L.isAntiSymmetric(M([[0, x], [parse('-x'), 0]]), false)).toBe(true);
    expect(L.isDiagonal(nonsym)).toBe(false);
    expect(L.isUpper(nonsym)).toBe(false);
    expect(L.isLower(M([[1, 0], [3, 4]]))).toBe(true);
    expect(L.isNilpotent(M([[0, 1], [0, 0]]))).toBe(true);
    expect(s(L.multiplyElementwise(nonsym, nonsym))).toBe('Matrix([[1, 4], [9, 16]])');
    expect(s(L.project(M([[1, 1]]), M([[1, 0]])))).toBe('Matrix([[1, 0]])');
    expect(s(L.colInsert(nonsym, 1, M([[0], [0]])))).toBe('Matrix([[1, 0, 2], [3, 0, 4]])');
  });
});

describe('LU pivoting', () => {
  it('prefers an entry known to be nonzero, else the first undecided one (SymPy _find_reasonable_pivot_naive)', () => {
    const [a, b, x] = symbols('a b x');
    const show = ([l, u, p]: [Matrix, Matrix, [number, number][]]) => `${String(l)} ${String(u)} ${JSON.stringify(p)}`;
    expect(show(L.luDecomposition(Matrix.of([[a, 1], [1, b]])))).toBe('Matrix([[1, 0], [a, 1]]) Matrix([[1, b], [0, -a*b + 1]]) [[0,1]]');
    // SymPy writes the entry 2 - b/a
    expect(show(L.luDecomposition(Matrix.of([[a, 1], [b, 2]])))).toBe('Matrix([[1, 0], [b/a, 1]]) Matrix([[a, 1], [0, (2*a - b)/a]]) []');
    expect(show(L.luDecomposition(Matrix.of([[0, 1], [x, 2]])))).toBe('Matrix([[1, 0], [0, 1]]) Matrix([[x, 2], [0, 1]]) [[0,1]]');
  });
});

describe('luSolve and the LDL solution of a Hermitian matrix', () => {
  it('luSolve (SymPy LUsolve) rejects singular and mismatched systems', () => {
    expect(() => L.luSolve(Matrix.of([[1, 2], [2, 4]]), Matrix.col(1, 2))).toThrow(NonInvertibleMatrixError);
    expect(() => L.luSolve(Matrix.of([[1, 2], [3, 4]]), Matrix.col(1, 2, 3))).toThrow('``M`` and ``rhs`` must have the same number of rows.');
    expect(() => L.luSolve(Matrix.of([[1, 2, 3], [4, 5, 6]]), Matrix.col(1, 2))).toThrow(sj.NotImplementedError);
  });
  it('inverseLDL of a Hermitian matrix (SymPy)', () => {
    expect(String(L.inverseLDL(Matrix.of([[2, I], [mul(-1, I), 2]])))).toBe('Matrix([[2/3, -I/3], [I/3, 2/3]])');
  });
});

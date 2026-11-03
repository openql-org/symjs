// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Coverage of matrices/*.ts and matrices/expressions/*.ts; expected values are those of SymPy 1.14.
import { describe, expect, it } from 'vitest';
import * as sj from '../src';
import { Matrix } from '../src/matrices/matrix';
import * as more from '../src/matrices/more';
import { isDiagonalizable, jordanForm } from '../src/matrices/linalg';
import { linearEqToMatrix, linsolve } from '../src/matrices/linsys';
import { toDM } from '../src/matrices/domainmatrix';
import { MutableDenseMatrix } from '../src/matrices/mutable';
import { rebuild } from '../src/core/traverse';
import { cast } from '../src/core/guard';
import { MatrixExpr } from '../src/matrices/expressions/matexpr';
import { NonInvertibleMatrixError, NonlinearError } from '../src/core/errors';

const M = (rows: sj.ExprLike[][]): Matrix => Matrix.of(rows);
const s = (e: unknown): string => String(e);
const [x, y] = sj.symbols('x y');

describe('matrices/more', () => {
  it('berkowitz', () => {
    expect(more.berkowitz(M([[1, 2, 3], [4, 5, 6], [7, 8, 10]])).map((r) => r.map(s))).toEqual([['1'], ['1', '-1'], ['1', '-6', '-3'], ['1', '-16', '-12', '3']]);
    // SymPy: NonSquareMatrixError
    expect(() => more.berkowitz(M([[1, 2, 3], [4, 5, 6]]))).toThrow(RangeError);
  });

  it('upper_hessenberg_decomposition', () => {
    const cases: [sj.ExprLike[][], string, string][] = [
      [[[1, 0, 0], [0, 2, 0], [0, 0, 3]], 'Matrix([[1, 0, 0], [0, 2, 0], [0, 0, 3]])', 'Matrix([[1, 0, 0], [0, 1, 0], [0, 0, 1]])'],
      [[[1, 2, 3], [4, 5, 6], [0, 8, 9]], 'Matrix([[1, 2, 3], [4, 5, 6], [0, 8, 9]])', 'Matrix([[1, 0, 0], [0, 1, 0], [0, 0, 1]])'],
      [[[1, 2, 3], [0, 4, 5], [6, 7, 8]], 'Matrix([[1, -3, -2], [-6, 8, 7], [0, 5, 4]])', 'Matrix([[1, 0, 0], [0, 0, -1], [0, -1, 0]])'],
    ];
    for (const [a, h, p] of cases) {
      const [H, P] = more.upperHessenbergDecomposition(M(a));
      expect([s(H), s(P)]).toEqual([h, p]);
    }
    expect(() => more.upperHessenbergDecomposition(M([[1, 2]]))).toThrow('Matrix must be square.');
  });

  it('bidiagonal forms', () => {
    const D = M([[1, 0, 0], [0, 2, 0], [0, 0, 3]]);
    expect(more.bidiagonalDecomposition(D).map(s)).toEqual(['Matrix([[1, 0, 0], [0, 1, 0], [0, 0, 1]])', s(D), 'Matrix([[1, 0, 0], [0, 1, 0], [0, 0, 1]])']);
    expect(s(more.bidiagonalize(D))).toBe(s(D));
    // SymPy fails here (TypeError: Invalid NaN comparison, from 0/|0|): the decomposition is still A = U B V
    const A = M([[0, 1], [1, 0]]);
    const [U, B, V] = more.bidiagonalDecomposition(A);
    expect(s(U.mul(B).mul(V).map((e) => sj.simplify(e)))).toBe(s(A));
    expect(s(B.get(1, 0))).toBe('0');
  });

  it('LUdecomposition_Simple', () => {
    const cases: [sj.ExprLike[][], string][] = [
      [[[0, 1], [0, 2]], 'Matrix([[0, 1], [2, 0]])'],
      [[[1, 2], [2, 4], [3, 6]], 'Matrix([[1, 2], [2, 0], [3, 0]])'],
      [[[0, 1, 2], [0, 3, 4], [0, 5, 6]], 'Matrix([[0, 1, 2], [3, 0, -2], [5, 2, 0]])'],
      [[[1, 2], [3, 4], [5, 6]], 'Matrix([[1, 2], [3, -2], [5, 2]])'],
    ];
    for (const [a, lu] of cases) {
      const [LU, swaps] = more.luDecompositionSimple(M(a));
      expect([s(LU), swaps]).toEqual([lu, []]);
    }
    const [E, sw] = more.luDecompositionSimple(Matrix.zeros(0, 2));
    expect([E.rows, E.cols, sw]).toEqual([0, 2, []]);
  });

  it('LUdecompositionFF', () => {
    // SymPy: ValueError Matrix is not full rank
    expect(() => more.luDecompositionFF(M([[0, 1], [0, 2]]))).toThrow('Matrix is not full rank');
    expect(more.luDecompositionFF(M([[1, 1, 1], [1, 1, 2], [1, 2, 3]])).map(s)).toEqual([
      'Matrix([[1, 0, 0], [0, 0, 1], [0, 1, 0]])',
      'Matrix([[1, 0, 0], [1, 1, 0], [1, 0, 1]])',
      'Matrix([[1, 0, 0], [0, 1, 0], [0, 0, 1]])',
      'Matrix([[1, 1, 1], [0, 1, 2], [0, 0, 1]])',
    ]);
  });

  it('lll', () => {
    expect(s(more.lll(M([[1, -2, 3], [-4, 5, 6]])))).toBe('Matrix([[1, -2, 3], [-4, 5, 6]])');
    // mu = 1/2 exactly: size-reduced
    expect(s(more.lll(M([[2, 0], [1, 1]])))).toBe('Matrix([[1, 1], [1, -1]])');
    expect(more.lllTransform(M([[-3, 1, 0], [5, -2, 1]])).map(s)).toEqual(['Matrix([[-1, 0, 1], [-1, 1, -2]])', 'Matrix([[2, 1], [-3, -2]])']);
    // SymPy: DMRankError input matrix contains linearly dependent rows
    expect(() => more.lll(M([[1, 2], [2, 4]]))).toThrow('input matrix contains linearly dependent rows');
    // SymPy: CoercionFailed (1/2 is not in ZZ)
    expect(() => more.lll(M([[sj.Rational.of(1n, 2n), 1], [0, 1]]))).toThrow('input matrix domain must be ZZ');
    // SymPy converts the float 0.75 to QQ; symjs requires a rational
    expect(() => more.lll(M([[1, 0], [0, 1]]), new sj.Float(0.75))).toThrow('delta must be a rational number');
  });

  it('elementary operations', () => {
    const A = M([[1, 2], [3, 4], [5, 6]]);
    expect(s(more.elementaryRowOp(A, { op: 'n<->m', index1: 0, index2: 2 }))).toBe('Matrix([[5, 6], [3, 4], [1, 2]])');
    expect(s(more.elementaryRowOp(A, { op: 'n<->m', index: 0, index2: 2 }))).toBe('Matrix([[5, 6], [3, 4], [1, 2]])');
    expect(s(more.elementaryRowOp(A, { op: 'n->n+km', index: 0, k: 3, index2: 1 }))).toBe('Matrix([[10, 14], [3, 4], [5, 6]])');
    expect(s(more.elementaryRowOp(A, { op: 'n->kn', index1: 1, k: 5 }))).toBe('Matrix([[1, 2], [15, 20], [5, 6]])');
    expect(s(more.elementaryColOp(A, { op: 'n->n+km', index: 1, k: 2, index2: 0 }))).toBe('Matrix([[1, 4], [3, 10], [5, 16]])');
    // k defaults to 1 (SymPy requires it)
    expect(s(more.elementaryRowOp(A, { op: 'n->n+km', index1: 0, index2: 1 }))).toBe('Matrix([[4, 6], [3, 4], [5, 6]])');
    expect(s(more.elementaryRowOp(A, { index: 2 }))).toBe(s(A));
    // SymPy: ValueError This matrix does not have a row '-1' / '3'; `row` and `row2` must be different
    expect(() => more.elementaryRowOp(A, { op: 'n->kn', index: -1, k: 2 })).toThrow("This matrix does not have a row '-1'");
    expect(() => more.elementaryColOp(A, { op: 'n->kn', index: 2, k: 2 })).toThrow("This matrix does not have a col '2'");
    expect(() => more.elementaryRowOp(A, { op: 'n->n+km', index: 0, k: 3, index2: 0 })).toThrow("For a row operation 'n->n+km' `row` and `row2` must be different.");
    expect(() => more.elementaryRowOp(A, { op: 'n<->m', index1: 1, index2: 1 })).toThrow(RangeError);
  });

  it('permutations of rows by an index list, deletion', () => {
    const A = M([[1, 2], [3, 4], [5, 6]]);
    // JavaScript only: an index list shorter than the rows leaves the remaining rows in place
    expect(s(more.permuteFwd(A, [1, 0]))).toBe('Matrix([[3, 4], [1, 2], [5, 6]])');
    // SymPy row_del(-1) and col_del(-1) (in place)
    expect(s(more.rowDel(A, -1))).toBe('Matrix([[1, 2], [3, 4]])');
    expect(s(more.colDel(A, -1))).toBe('Matrix([[1], [3], [5]])');
    // SymPy: IndexError Row 5 is out of range. / Column -3 is out of range.
    expect(() => more.rowDel(A, 5)).toThrow('Row 5 is out of range.');
    expect(() => more.colDel(A, -3)).toThrow('Column -3 is out of range.');
  });

  it('key2ij and key2bounds', () => {
    const A = M([[1, 2], [3, 4], [5, 6]]);
    expect(more.key2ij(A, [{ start: -2 }, 1])).toEqual([{ start: -2 }, 1]);
    expect(more.key2ij(A, { start: -2, step: -1 })).toEqual([4, -1]);
    expect(more.key2ij(A, { start: -10, stop: 10 })).toEqual([0, 6]);
    expect(more.key2ij(A, { step: -1 })).toEqual([5, -1]);
    expect(more.key2ij(A, { start: 10, stop: -10, step: -1 })).toEqual([5, -1]);
    expect(more.key2ij(A, [0, {}])).toEqual([0, {}]);
    expect(more.key2bounds(A, [{ start: 0, stop: 2 }, -1])).toEqual([0, 2, 1, 2]);
    expect(more.key2bounds(Matrix.zeros(0, 2), [{}, 0])).toEqual([0, 0, 0, 1]);
    expect(more.key2bounds(Matrix.zeros(2, 0), [0, {}])).toEqual([0, 1, 0, 0]);
  });

  it('table, matrix2numpy, list2numpy', () => {
    expect(more.table(M([[1, 22, 333], [4444, 5, 6]]), { align: 'center' })).toBe('[ 1  , 22, 333]\n[4444, 5 ,  6 ]');
    expect(more.table(M([[333], [22]]), { align: 'center' })).toBe('[333]\n[ 22]');
    expect(more.matrix2numpy(M([[1, sj.Rational.of(1n, 2n)]]), 'float')).toEqual([[1, 0.5]]);
    expect(more.matrix2numpy(M([[1, x]])).flat().map(s)).toEqual(['1', 'x']);
    expect(more.list2numpy([1, [2n, x]]).flat().map(s)).toEqual(['1', '2', 'x']);
    expect(more.list2numpy([1, [2]], 'float')).toEqual([1, [2]]);
    // SymPy sympify('a') would give a Symbol; symjs's list2numpy takes no strings
    expect(() => more.list2numpy(['a'])).toThrow(sj.SympifyError);
  });
});

it('randMatrix with zeros, not symmetric', () => {
  const R = more.randMatrix(3, 3, { seed: 7, percent: 50 });
  expect(R.data.filter((e) => s(e) === '0').length).toBeGreaterThanOrEqual(5);
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
    // SymPy converts floats to rationals first and gives J = diag(-0.481379037105842, 6.48137903710584);
    // symjs finds no eigenvectors of the float eigenvalues
    expect(() => jordanForm(M([[new sj.Float(1.1), new sj.Float(2.3)], [new sj.Float(3.7), new sj.Float(4.9)]]))).toThrow(sj.NotImplementedError);
  });

  it('linear_eq_to_matrix and linsolve', () => {
    // SymPy: NonlinearError for 1/x and for x*y; a relation other than Eq is an expression
    expect(linearEqToMatrix([sj.pow(x, -1)], [x])).toBe(undefined);
    expect(() => linsolve([sj.mul(x, y)], [x, y])).toThrow(NonlinearError);
    const r = linearEqToMatrix([sj.Eq(sj.add(x, y), 2), sj.sub(x, y)], [x, y]);
    expect(r?.map(s)).toEqual(['Matrix([[1, 1], [1, -1]])', 'Matrix([[2], [0]])']);
    expect(() => linsolve([sj.Lt(x, 1)], [x])).toThrow(NonlinearError);
  });

  it('to_DM domains', () => {
    const cases: [Matrix, string, string][] = [
      [M([[1, sj.I]]), 'QQ_I', 'ZZ_I'],
      [M([[sj.Rational.of(1n, 2n)]]), 'QQ', 'QQ'],
      [M([[new sj.Float(1.5)]]), 'RR', 'RR'],
      [M([[x, new sj.Float(1.5)]]), 'RR(x)', 'RR[x]'],
      [M([[x, 2]]), 'ZZ(x)', 'ZZ[x]'],
    ];
    for (const [A, f, d] of cases) expect([toDM(A, { field: true }).domain, toDM(A).domain]).toEqual([f, d]);
  });

  it('MutableDenseMatrix.of', () => {
    const A = MutableDenseMatrix.of([[1, 2], [3, 4]]);
    expect(A).toBeInstanceOf(MutableDenseMatrix);
    expect(s(A)).toBe('Matrix([[1, 2], [3, 4]])');
  });
});

describe('matrix expressions', () => {
  it('a singular explicit block in a product: no inverse to cancel', () => {
    const X = sj.MatrixSymbol('X', 4, 4);
    const Y = sj.MatrixSymbol('Y', 2, 2);
    const B = sj.BlockDiagMatrix(sj.ImmutableMatrix([[1, 1], [1, 1]]), Y);
    expect(s(cast(sj.MatMul(X, B), MatrixExpr).doit())).toBe('X*Matrix([[Matrix([[1, 1], [1, 1]]), 0], [0, Y]])');
    // SymPy: NonInvertibleMatrixError Matrix det == 0; not invertible.
    expect(() => sj.ImmutableMatrix([[1, 1], [1, 1]]).inverse()).toThrow(NonInvertibleMatrixError);
    expect(() => B.inverse()).toThrow(NonInvertibleMatrixError);
  });

  it('nodes rebuilt from their arguments are equal (SymPy e.func(*e.args) == e)', () => {
    const [n] = sj.symbols('n');
    const X = sj.MatrixSymbol('X', n, n);
    const sl = cast(X.slice([0, n], [0, 2]), MatrixExpr);
    for (const t of sl.sortArgs()) expect(rebuild(t, t.args).key).toBe(t.key);
    const B = cast(sj.BlockMatrix([[X, X], [X, X]]), MatrixExpr);
    for (const t of B.sortArgs()) expect(rebuild(t, t.args).key).toBe(t.key);
    const P = sj.PermutationMatrix([1, 0, 2]);
    expect(rebuild(P, P.args).key).toBe(P.key);
    const p = P.args[0];
    if (p === undefined) throw new Error('no argument');
    expect(rebuild(p, p.args).key).toBe(p.key);
  });
});

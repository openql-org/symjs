// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * Linear algebra on symbolic matrices, including
 * row reduction, rank, null/column/row spaces, eigenvectors,
 * diagonalization, LU/QR/Cholesky/LDL decompositions, norms, singular
 * values, pseudo-inverse, matrix exponential and structural helpers.
 * @module
 */

import { at, defined, expectType, first, last } from '../core/guard';
import { UPoly } from '../polys/poly';
import { isNegative, isPositive, isReal, isZero } from '../core/assumptions';
import { toTruth, truthAnd, truthNot } from '../core/truth';
import type { Truth } from '../core/truth';
import { MatrixError, NonInvertibleMatrixError, NonPositiveDefiniteMatrixError, NonSquareMatrixError, NotImplementedError, NotLoadedError, ShapeError } from '../core/errors';
import type { ExprLike } from '../core/nodes';
import { Dummy, Expr, Float, Rational, S, Special, Sym, impl } from '../core/nodes';
import { nsimplify } from '../numeric/nfloat';
import { precToDps } from '../numeric/mpf';
import { add, mul, pow, sqrt, sympify } from '../core/ops';
import { diff } from '../calculus/diff';
import { abs, conjugate, cos, log, sin } from '../functions/elementary/elementary';
import { Max, Min } from '../functions/special/special';
import { compareKeys, sortKey } from '../printing/sortkey';
import { expandMul } from '../simplify/expand';
import { cancel } from '../simplify/rational';
import { exp } from '../core/ops';
import { Matrix } from './matrix';
import { uniquelyNamedSymbol } from '../core/symbol';
import { lcm } from '../core/numbers';

/** SymPy simplify, late-bound as in matrix.ts (the matrices entry loads it). */
const simplify = (e: Expr): Expr => impl.simplify(e);

const isZeroE = (e: Expr): boolean => {
  if (e instanceof Rational) return e.isZero;
  const x = expandMul(e);
  if (x instanceof Rational) return x.isZero;
  if (x.freeSymbols().size === 0) {
    try {
      const v = x.toComplex();
      if (Math.hypot(v.re, v.im) > 1e-9) return false;
    } catch {
      return false;
    }
  }
  const s = simplify(x);
  return s instanceof Rational && s.isZero;
};

/** Tidy an entry produced by elimination. */
const tidy = (e: Expr): Expr => {
  if (e.freeSymbols().size === 0 && !(e instanceof Rational)) return expandMul(e);
  // cancel keeps what it cannot treat as a polynomial (it catches its own polynomial failures)
  return cancel(e);
};

type Rows = Expr[][];
const rowsOf = (m: Matrix): Rows => m.toArray();
/** The entry (i, j) of a row array; throws when out of range. */
const ent = (A: readonly (readonly Expr[])[], i: number, j: number): Expr => at(at(A, i), j);
/** The zero test used for structural (exact zero) checks. */
const isExactZero = (e: Expr): boolean => e instanceof Rational && e.isZero;
const range = (a: number, b: number): number[] => Array.from({ length: Math.max(0, b - a) }, (_, i) => a + i);
const fromRows = (r: Rows, cols: number): Matrix => (r.length === 0 ? Matrix.zeros(0, cols) : Matrix.of(r));

// ---------------------------------------------------------------------------
// row reduction
// ---------------------------------------------------------------------------

/**
 * Reduces the matrix to reduced row echelon form and identifies the pivot columns.
 * @param m - The input matrix.
 * @param opts - An optional `iszerofunc` predicate for choosing pivots.
 * @returns The reduced matrix and zero-based pivot columns.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.rref`
 * @example
 * ```ts
 * import { Matrix, rref } from '@symjs/symjs';
 * rref(Matrix.of([[1, 2], [2, 4]]))[1]; // => [0]
 * ```
 */
export function rref(m: Matrix, opts: { iszerofunc?: (e: Expr) => boolean } = {}): [Matrix, number[]] {
  const zero = opts.iszerofunc ?? isZeroE;
  const A = rowsOf(m);
  const pivots: number[] = [];
  let r = 0;
  for (let c = 0; c < m.cols && r < m.rows; c++) {
    let p = -1;
    for (let i = r; i < m.rows; i++) {
      if (!zero(ent(A, i, c))) {
        p = i;
        break;
      }
      at(A, i)[c] = S.Zero;
    }
    if (p < 0) continue;
    const rowP = at(A, p);
    A[p] = at(A, r);
    const pivot = at(rowP, c);
    const reciprocal = pow(pivot, -1);
    const inv = pivot.freeSymbols().size === 0 && impl.radsimp ? impl.radsimp(reciprocal) : reciprocal;
    const pivotRow = rowP.map((v) => tidy(mul(v, inv)));
    pivotRow[c] = S.One;
    A[r] = pivotRow;
    for (let i = 0; i < m.rows; i++) {
      if (i === r) continue;
      const Ai = at(A, i);
      const f = at(Ai, c);
      if (zero(f)) continue;
      A[i] = Ai.map((v, j) => tidy(add(v, mul(-1, f, at(pivotRow, j)))));
    }
    pivots.push(c);
    r++;
  }
  return [fromRows(A, m.cols), pivots];
}

/**
 * Tests whether the leading entries move strictly to the right and all zero rows are last.
 * @param m - The input matrix.
 * @returns Whether the matrix is echelon.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.is_echelon`
 * @example
 * ```ts
 * import { Matrix, isEchelon } from '@symjs/symjs';
 * isEchelon(Matrix.of([[1]])); // => True
 * ```
 */
export function isEchelon(m: Matrix): boolean {
  let pivotRow = 0;
  for (let col = 0; col < m.cols && pivotRow < m.rows; col++) {
    for (let row = pivotRow + 1; row < m.rows; row++) {
      if (isZero(m.get(row, col)) !== true) return false;
    }
    if (isZero(m.get(pivotRow, col)) !== true) pivotRow++;
  }
  return true;
}

/**
 * Echelon form by fraction-free cross-multiplication.
 * @param m - The input matrix.
 * @returns The resulting matrix.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.echelon_form`
 * @remarks SymPy prints this result as `Matrix([[1, 2], [0, -2]])`.
 * @example
 * ```ts
 * import { Matrix, echelonForm } from '@symjs/symjs';
 * echelonForm(Matrix.of([[1, 2], [3, 4]])); // => Matrix([
 * //   [1,  2],
 * //   [0, -2]])
 * ```
 */
export function echelonForm(m: Matrix): Matrix {
  const A = rowsOf(m);
  let r = 0;
  for (let c = 0; c < m.cols && r < m.rows; c++) {
    let p = -1;
    for (let i = r; i < m.rows; i++) {
      if (!isZeroE(ent(A, i, c))) {
        p = i;
        break;
      }
    }
    if (p < 0) continue;
    const pivotRow = at(A, p);
    A[p] = at(A, r);
    A[r] = pivotRow;
    const piv = at(pivotRow, c);
    for (let i = r + 1; i < m.rows; i++) {
      const Ai = at(A, i);
      const f = at(Ai, c);
      if (isZeroE(f)) continue;
      A[i] = Ai.map((v, j) => tidy(add(mul(piv, v), mul(-1, f, at(pivotRow, j)))));
    }
    r++;
  }
  return fromRows(A, m.cols);
}

/**
 * Computes the number of linearly independent rows or columns.
 * @param m - The input matrix.
 * @param opts - An optional `iszerofunc` predicate for deciding which entries are zero.
 * @returns The dimension of the column space.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.rank`
 * @example
 * ```ts
 * import { Matrix, rank } from '@symjs/symjs';
 * rank(Matrix.of([[1, 2, 3], [4, 5, 6], [7, 8, 9]]), {}); // => 2
 * ```
 */
export function rank(m: Matrix, opts: { iszerofunc?: (e: Expr) => boolean } = {}): number {
  if (opts.iszerofunc && m.rows === 2 && m.cols === 2) {
    if (m.data.every(opts.iszerofunc)) return 0;
    return opts.iszerofunc(m.det()) ? 1 : 2;
  }
  return rref(m, opts)[1].length;
}

/**
 * Finds a basis for the solutions of the homogeneous matrix equation.
 * @param m - The input matrix.
 * @returns A basis for the kernel.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.nullspace`
 * @example
 * ```ts
 * import { Matrix, nullspace } from '@symjs/symjs';
 *
 * const M = Matrix.of([[1, 3, 0], [-2, -6, 0], [3, 9, 6]]);
 * nullspace(M).map(v => v.toArray()); // => [[[-3], [1], [0]]]
 * ```
 */
export function nullspace(m: Matrix): Matrix[] {
  const [R, pivots] = rref(m);
  const free = [...Array(m.cols).keys()].filter((c) => !pivots.includes(c));
  return free.map((f) => {
    const v: Expr[] = Array.from({ length: m.cols }, () => S.Zero);
    v[f] = S.One;
    pivots.forEach((pc, i) => {
      v[pc] = tidy(mul(-1, R.get(i, f)));
    });
    return Matrix.col(...v);
  });
}

/**
 * Finds a basis for the space spanned by the columns.
 * @param m - The input matrix.
 * @returns A basis of column vectors.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.columnspace`
 * @example
 * ```ts
 * import { Matrix, columnspace } from '@symjs/symjs';
 *
 * const M = Matrix.of([[1, 3, 0], [-2, -6, 0], [3, 9, 6]]);
 * columnspace(M).map(v => v.toArray()); // => [[[1], [-2], [3]], [[0], [0], [6]]]
 * ```
 */
export function columnspace(m: Matrix): Matrix[] {
  return rref(m)[1].map((c) => m.col(c));
}

/**
 * Finds a basis for the space spanned by the rows.
 * @param m - The input matrix.
 * @returns A basis of row vectors.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.rowspace`
 * @example
 * ```ts
 * import { Matrix, rowspace } from '@symjs/symjs';
 *
 * const M = Matrix.of([[1, 3, 0], [-2, -6, 0], [3, 9, 6]]);
 * rowspace(M).map(v => v.toArray()); // => [[[1, 3, 0]], [[0, 0, 6]]]
 * ```
 */
export function rowspace(m: Matrix): Matrix[] {
  const E = echelonForm(m);
  const out: Matrix[] = [];
  for (let i = 0; i < E.rows; i++) {
    const r = E.row(i);
    if (r.data.some((e) => !isZeroE(e))) out.push(r);
  }
  return out;
}

// ---------------------------------------------------------------------------
// eigen decomposition
// ---------------------------------------------------------------------------

function eigenvalueMultiplicities(m: Matrix): [Expr, number][] {
  const vals = m.eigenvals();
  const out = new Map<string, [Expr, number]>();
  for (const v of vals) {
    const e = out.get(v.key);
    if (e) e[1]++;
    else out.set(v.key, [v, 1]);
  }
  return [...out.values()].sort((a, b) => compareKeys(sortKey(a[0]), sortKey(b[0])));
}

/**
 * Computes the eigenvalues and a basis for each eigenspace.
 * @param m - The input matrix.
 * @returns Triples of eigenvalue, algebraic multiplicity and eigenspace basis.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.eigenvects`
 * @example
 * ```ts
 * import { Matrix, eigenvects } from '@symjs/symjs';
 * eigenvects(Matrix.diag(1, 2)).map(([value, multiplicity]) => [value, multiplicity]); // => [[1, 1], [2, 1]]
 * ```
 */
export function eigenvects(m: Matrix): [Expr, number, Matrix[]][] {
  const fields = rationalEigenspaces(m);
  return eigenvalueMultiplicities(m).map(([v, k]) => {
    // an eigenvalue that is a root of an irreducible factor of degree >= 3 of the characteristic
    // polynomial: the eigenspace over Q[t]/(f) at t = v (SymPy eigenvects over QQ<theta>)
    const field = fields.find(([f]) => isRootOf(f, v));
    if (field) return [v, k, field[1].map((vec) => Matrix.col(...vec.map((c) => expandMul(c.toExpr(v)))))];
    const shifted = m.sub(Matrix.eye(m.rows).scale(v));
    return [v, k, nullspace(shifted)];
  });
}

const isRat = (e: unknown): e is Rational => e instanceof Rational;

/** Whether v is (numerically) a root of f. */
function isRootOf(f: UPoly, v: Expr): boolean {
  // (the eigenvalues of a rational matrix are numbers)
  const z = f.toExpr(v).toComplex();
  return Math.hypot(z.re, z.im) < 1e-8;
}

/**
 * For a rational matrix, the irreducible factors f of degree >= 3 of the
 * characteristic polynomial with a basis of the null space of A - t*I over the
 * field Q[t]/(f): exact elimination with the eigenvalue as an algebraic number,
 * where the radical expressions of the roots of a cubic defeat the zero tests.
 */
function rationalEigenspaces(m: Matrix): [UPoly, UPoly[][]][] {
  if (!m.isSquare || !m.data.every((e) => e instanceof Rational)) return [];
  const cs = m.charpolyCoeffs().map((c) => expectType(c, isRat, 'characteristic polynomial coefficient')).reverse();
  return new UPoly(cs).factor().factors.filter(([f]) => f.degree >= 3).map(([f]) => [f, fieldNullspace(m, f)]);
}

/** Q[t]/(f) for an irreducible f: reduction and inverses (extended Euclid). */
function fieldOps(f: UPoly): { red: (a: UPoly) => UPoly; inv: (a: UPoly) => UPoly } {
  const red = (a: UPoly): UPoly => a.divmod(f)[1];
  const inv = (a: UPoly): UPoly => {
    let [r0, r1] = [f, a];
    let [s0, s1] = [new UPoly([]), new UPoly([S.One])];
    while (!r1.isZero) {
      const [q, r] = r0.divmod(r1);
      [r0, r1] = [r1, r];
      [s0, s1] = [s1, s0.sub(q.mul(s1))];
    }
    // r0 is a nonzero constant: f is irreducible and a is not a multiple of f
    return red(s0.scale(Rational.of(r0.lc.q, r0.lc.p)));
  };
  return { red, inv };
}

/** Basis of the null space of A - t*I over Q[t]/(f), as coefficient polynomials in t. */
function fieldNullspace(m: Matrix, f: UPoly): UPoly[][] {
  const { red, inv } = fieldOps(f);
  const n = m.rows;
  const t = new UPoly([S.Zero, S.One]);
  const A: UPoly[][] = Array.from({ length: n }, (_, i) =>
    Array.from({ length: n }, (_, j) => {
      const c = new UPoly([expectType(m.get(i, j), isRat, 'rational entry')]);
      return i === j ? c.sub(t) : c;
    }),
  );
  const pivots: number[] = [];
  let r = 0;
  for (let c = 0; c < n && r < n; c++) {
    const p = A.findIndex((row, i) => i >= r && !at(row, c).isZero);
    if (p < 0) continue;
    [A[p], A[r]] = [at(A, r), at(A, p)];
    const ip = inv(at(at(A, r), c));
    A[r] = at(A, r).map((e) => red(e.mul(ip)));
    const pr = at(A, r);
    for (let i = 0; i < n; i++) {
      const fac = at(at(A, i), c);
      if (i === r || fac.isZero) continue;
      A[i] = at(A, i).map((e, j) => red(e.sub(fac.mul(at(pr, j)))));
    }
    pivots.push(c);
    r++;
  }
  const free = [...Array(n).keys()].filter((c) => !pivots.includes(c));
  return free.map((fc) => {
    const v: UPoly[] = Array.from({ length: n }, (_, i) => new UPoly(i === fc ? [S.One] : []));
    pivots.forEach((pc, i) => {
      v[pc] = at(at(A, i), fc).scale(Rational.of(-1n));
    });
    return v;
  });
}

/** SymPy val.is_real for an eigenvalue: a number by its numeric value, anything else by the assumptions. */
function isRealEigenvalue(v: Expr): boolean {
  if (v.freeSymbols().size === 0) {
    try {
      return Math.abs(v.toComplex().im) <= 1e-12;
    } catch {
      // not numerically evaluable (f(1)): decided by the assumptions
    }
  }
  return isReal(v) === true;
}

/**
 * Returns `True` if a matrix is diagonalizable.
 * @param m - The input matrix.
 * @param realsOnly - Whether to require a real eigenbasis.
 * @returns Whether the matrix is diagonalizable.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.is_diagonalizable`
 * @example
 * ```ts
 * import { Matrix, isDiagonalizable } from '@symjs/symjs';
 * isDiagonalizable(Matrix.of([[0, 1], [0, 0]]), false); // => False
 * ```
 */
export function isDiagonalizable(m: Matrix, realsOnly = false): boolean {
  if (!m.isSquare) return false;
  for (const [v, k, vecs] of eigenvects(m)) {
    if (vecs.length !== k) return false;
    if (realsOnly && !isRealEigenvalue(v)) return false;
  }
  return true;
}

/**
 * Finds a basis in which a square matrix is diagonal.
 * @param m - The input matrix.
 * @param realsOnly - Whether to require a real eigenbasis.
 * @returns The basis matrix and diagonal matrix, in matching column order.
 * @throws MatrixError when the matrix has no eigenbasis over the requested field.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.diagonalize`
 * @example
 * ```ts
 * import { Matrix, diagonalize } from '@symjs/symjs';
 * diagonalize(Matrix.of([[1, 2, 0], [0, 3, 0], [2, -4, 2]]))[1].toArray(); // => [[1, 0, 0], [0, 2, 0], [0, 0, 3]]
 * ```
 */
export function diagonalize(m: Matrix, realsOnly = false): [Matrix, Matrix] {
  if (!isDiagonalizable(m, realsOnly)) throw new MatrixError('Matrix is not diagonalizable');
  const cols: Matrix[] = [];
  const vals: Expr[] = [];
  for (const [v, , vecs] of eigenvects(m)) {
    for (const vec of vecs) {
      // diagonalize uses simplified primitive columns; eigenvects retains
      // the nullspace convention with a free entry of 1.
      cols.push(vec.data.every(isRat) ? vec.scale(Rational.of(vec.data.reduce((d, e) => lcm(d, e.q), 1n))) : vec);
      vals.push(v);
    }
  }
  const P = first(cols).hstack(...cols.slice(1));
  return [P, Matrix.diag(...vals)];
}

/**
 * Computes the exponential of a square matrix, including matrices without an eigenbasis.
 * @param m - The input matrix.
 * @returns The exponential of a square matrix, including matrices without an eigenbasis.
 * @throws NonSquareMatrixError when the matrix is not square.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.exp`
 * @remarks SymPy prints this result as `Matrix([[E, 0, 0], [0, E, 0], [0, 0, E]])`.
 * @example
 * ```ts
 * import { Matrix, matrixExp } from '@symjs/symjs';
 * matrixExp(Matrix.of([[1, 0, 0], [0, 1, 0], [0, 0, 1]])); // => Matrix([
 * //   [E, 0, 0],
 * //   [0, E, 0],
 * //   [0, 0, E]])
 * ```
 */
export function matrixExp(m: Matrix): Matrix {
  if (!m.isSquare) throw new NonSquareMatrixError('Matrix exponential requires a square matrix');
  if (!isDiagonalizable(m)) {
    const x = new Dummy('x');
    return analyticFunc(m, exp(x), x);
  }
  const [P, D] = diagonalize(m);
  const E = Matrix.diag(...Array.from({ length: D.rows }, (_, i) => exp(D.get(i, i))));
  return P.mul(E).mul(P.inv()).map((e) => expandMul(e));
}

/**
 * Evaluates an analytic scalar function at a square matrix by interpolation at its eigenvalues.
 * @param m - The input matrix.
 * @param fIn - The scalar function to evaluate or differentiate.
 * @param x - The differentiation variable.
 * @returns The resulting matrix.
 * @throws NonSquareMatrixError when the matrix is not square.
 * @throws RangeError when the function variable is not independent of the matrix or the function is not analytic at an eigenvalue.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.analytic_func`
 * @remarks SymPy prints this result as `Matrix([[0, log(2)], [log(2), 0]])`.
 * @example
 * ```ts
 * import { Matrix, analyticFunc, ex, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * analyticFunc(Matrix.of([[ex`5/4`, ex`3/4`], [ex`3/4`, ex`5/4`]]), ex`log(x)`, x); // => Matrix([
 * //   [     0, log(2)],
 * //   [log(2),      0]])
 * ```
 */
export function analyticFunc(m: Matrix, fIn: ExprLike, x: Sym): Matrix {
  if (!m.isSquare) throw new NonSquareMatrixError('analytic_func: square matrix expected');
  const f = sympify(fIn);
  const dependsOnX = (e: Expr): boolean => [...e.freeSymbols()].some((v) => v.key === x.key);
  if (!dependsOnX(f) || m.data.some(dependsOnX)) throw new RangeError('analyticFunc requires an independent function parameter');
  const n = m.rows;
  const eig = new Map<string, [Expr, number]>();
  for (const v of m.eigenvals()) {
    const e = eig.get(v.key);
    eig.set(v.key, [v, (e?.[1] ?? 0) + 1]);
  }
  const maxMul = Math.max(...[...eig.values()].map(([, k]) => k));
  const derivs: Expr[] = [f];
  for (let i = 1; i < maxMul; i++) derivs.push(diff(at(derivs, i - 1), x));
  const r: Expr[][] = [];
  const fv: Expr[][] = [];
  for (const [lam, k] of eig.values()) {
    for (let d = 0; d < k; d++) {
      // d-th derivative of x**a at lam: a!/(a-d)! lam**(a-d)
      const row: Expr[] = [];
      for (let a = 0; a < n; a++) {
        if (a < d) {
          row.push(S.Zero);
          continue;
        }
        let c = 1;
        for (let t = 0; t < d; t++) c *= a - t;
        row.push(mul(c, pow(lam, a - d)));
      }
      r.push(row);
      const value = subsValue(at(derivs, d), x, lam);
      if ([S.NaN, S.Infinity, S.NegativeInfinity, S.ComplexInfinity].some((pole) => value.has(pole))) {
        throw new RangeError(`Function is not analytic at eigenvalue ${String(lam)}`);
      }
      fv.push([value]);
    }
  }
  const c = Matrix.of(r).inv().mul(Matrix.of(fv));
  let ans = Matrix.zeros(n);
  let pre = Matrix.eye(n);
  for (let i = 0; i < n; i++) {
    ans = ans.add(pre.scale(c.get(i, 0)));
    pre = pre.mul(m);
  }
  return ans.map((e) => cancel(expandMul(e)));
}

function subsValue(e: Expr, x: Sym, v: Expr): Expr {
  return impl.subs(e, [[x, v]]);
}

/**
 * Computes the logarithm of a square matrix.
 * @param m - The input matrix.
 * @returns The logarithm of a square matrix.
 * @throws MatrixError when the matrix has a zero eigenvalue.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.log`
 * @remarks SymPy prints this result as `Matrix([[0, 1], [0, 0]])`.
 * @example
 * ```ts
 * import { Matrix, matrixLog } from '@symjs/symjs';
 * matrixLog(Matrix.of([[1, 1], [0, 1]])); // => Matrix([
 * //   [0, 1],
 * //   [0, 0]])
 * ```
 */
export function matrixLog(m: Matrix): Matrix {
  const x = new Dummy('x');
  if (m.isSquare && m.eigenvals().some(isExactZero)) throw new MatrixError('Matrix logarithm requires nonzero eigenvalues');
  return analyticFunc(m, log(x), x);
}

// ---------------------------------------------------------------------------
// decompositions
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// Definiteness (SymPy sympy/matrices/eigen.py)
// ---------------------------------------------------------------------------

/** SymPy is_nonnegative: real and not negative. */
function isNonnegativeTri(e: Expr): boolean | undefined {
  const neg = isNegative(e);
  if (neg === true) return false;
  return neg === false && isReal(e) === true ? true : undefined;
}

/** SymPy fuzzy_and of three-valued answers. */
function fuzzyAnd(ts: readonly (boolean | undefined)[]): boolean | undefined {
  if (ts.includes(false)) return false;
  return ts.every((t) => t === true) ? true : undefined;
}

/** The diagonal entries satisfy a three-valued predicate (SymPy _has_positive_diagonals, _has_nonnegative_diagonals). */
const diagonalsAre = (m: Matrix, p: (e: Expr) => boolean | undefined): boolean | undefined => fuzzyAnd(Array.from({ length: m.rows }, (_, i) => p(m.get(i, i))));

/**
 * The matrix is row strictly (strong) or weakly diagonally dominant (SymPy
 * is_strongly_diagonally_dominant, is_weakly_diagonally_dominant).
 */
function diagonallyDominant(m: Matrix, strong: boolean): boolean | undefined {
  return fuzzyAnd(
    Array.from({ length: m.rows }, (_, i) => {
      const others = add(...Array.from({ length: m.cols }, (_, j) => (i === j ? S.Zero : abs(m.get(i, j)))));
      const d = add(abs(m.get(i, i)), mul(-1, others));
      return strong ? isPositive(d) : isNonnegativeTri(d);
    }),
  );
}

/** The hermitian part M + M^H of a square matrix that is not hermitian (SymPy _is_positive_definite). */
const hermitianPart = (m: Matrix): Matrix => (m.isHermitian() === true ? m : m.add(m.adjoint()));

/** SymPy _is_positive_definite_GE: division-free Gaussian elimination. */
function positiveDefiniteGE(m0: Matrix): boolean | undefined {
  const a = m0.toArray();
  const n = m0.rows;
  for (let i = 0; i < n; i++) {
    const row = at(a, i);
    const pos = isPositive(at(row, i));
    if (pos !== true) return pos;
    for (let j = i + 1; j < n; j++) {
      const rj = at(a, j);
      for (let c = i + 1; c < n; c++) rj[c] = add(mul(at(row, i), at(rj, c)), mul(-1, at(rj, i), at(row, c)));
    }
  }
  return true;
}

/** SymPy _is_positive_semidefinite_cholesky: Cholesky factorization with complete pivoting. */
function positiveSemidefiniteCholesky(m0: Matrix): boolean | undefined {
  const a = m0.toArray();
  const n = m0.rows;
  const isZeroE = (e: Expr): boolean | undefined => (isZero(e) === undefined ? isZero(simplify(e)) : isZero(e));
  for (let k = 0; k < n; k++) {
    // the first diagonal entry that is not zero (SymPy _find_reasonable_pivot without assumptions)
    let pivot = -1;
    let undecided = false;
    for (let i = k; i < n; i++) {
      const z = isZeroE(at(at(a, i), i));
      if (z === false) {
        pivot = i - k;
        break;
      }
      if (z === undefined) undecided = true;
    }
    if (pivot < 0 && undecided) return undefined;
    if (pivot < 0) {
      for (let i = k + 1; i < n; i++) {
        for (let j = k; j < n; j++) {
          const z = isZero(at(at(a, i), j));
          if (z !== true) return z === undefined ? undefined : false;
        }
      }
      return true;
    }
    const pivotVal = at(at(a, k + pivot), k + pivot);
    if (isNegative(at(at(a, k), k)) === true || isNegative(pivotVal) === true) return false;
    if (!(isNonnegativeTri(at(at(a, k), k)) === true && isNonnegativeTri(pivotVal) === true)) return undefined;
    if (pivot > 0) {
      const p = k + pivot;
      for (const row of a) [row[k], row[p]] = [at(row, p), at(row, k)];
      [a[k], a[p]] = [at(a, p), at(a, k)];
    }
    const rk = at(a, k);
    rk[k] = sqrt(at(rk, k));
    for (let j = k + 1; j < n; j++) rk[j] = mul(at(rk, j), pow(at(rk, k), -1));
    for (let i = k + 1; i < n; i++) {
      for (let j = k + 1; j < n; j++) at(a, i)[j] = add(at(at(a, i), j), mul(-1, conjugate(at(rk, i)), at(rk, j)));
    }
  }
  return isNonnegativeTri(at(at(a, n - 1), n - 1));
}

/**
 * Tests whether the matrix is positive definite.
 * @param m0 - The input matrix.
 * @returns Whether the property holds, or `'unknown'` if undecidable.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.is_positive_definite`
 * @example
 * ```ts
 * import { Matrix, isPositiveDefinite } from '@symjs/symjs';
 * isPositiveDefinite(Matrix.of([[1, 0], [0, 1]])); // => True
 * ```
 */
export function isPositiveDefinite(m0: Matrix): Truth {
  if (!m0.isSquare) return false;
  const m = hermitianPart(m0);
  const pd = diagonalsAre(m, isPositive);
  if (pd === false) return false;
  if (pd === true && diagonallyDominant(m, true) === true) return true;
  return toTruth(positiveDefiniteGE(m));
}

/**
 * Tests whether the matrix is positive semidefinite.
 * @param m0 - The input matrix.
 * @returns Whether the property holds, or `'unknown'` if undecidable.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.is_positive_semidefinite`
 * @example
 * ```ts
 * import { Matrix, isPositiveSemidefinite } from '@symjs/symjs';
 * isPositiveSemidefinite(Matrix.of([[1, 0], [0, 1]])); // => True
 * ```
 */
export function isPositiveSemidefinite(m0: Matrix): Truth {
  if (!m0.isSquare) return false;
  const m = hermitianPart(m0);
  const nd = diagonalsAre(m, isNonnegativeTri);
  if (nd === false) return false;
  if (nd === true && diagonallyDominant(m, false) === true) return true;
  return toTruth(positiveSemidefiniteCholesky(m));
}

/**
 * Tests whether the matrix is negative definite.
 * @param m - The input matrix.
 * @returns Whether the property holds, or `'unknown'` if undecidable.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.is_negative_definite`
 * @example
 * ```ts
 * import { Matrix, isNegativeDefinite } from '@symjs/symjs';
 * isNegativeDefinite(Matrix.of([[-1, 0], [0, -1]])); // => True
 * ```
 */
export function isNegativeDefinite(m: Matrix): Truth {
  return isPositiveDefinite(m.neg());
}

/**
 * Tests whether the matrix is negative semidefinite.
 * @param m - The input matrix.
 * @returns Whether the property holds, or `'unknown'` if undecidable.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.is_negative_semidefinite`
 * @example
 * ```ts
 * import { Matrix, isNegativeSemidefinite } from '@symjs/symjs';
 * isNegativeSemidefinite(Matrix.of([[-1, 0], [0, -1]])); // => True
 * ```
 */
export function isNegativeSemidefinite(m: Matrix): Truth {
  return isPositiveSemidefinite(m.neg());
}

/**
 * Tests whether the matrix is indefinite.
 * @param m - The input matrix.
 * @returns Whether the property holds, or `'unknown'` if undecidable.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.is_indefinite`
 * @example
 * ```ts
 * import { Matrix, isIndefinite } from '@symjs/symjs';
 * isIndefinite(Matrix.of([[1, 2], [2, -1]])); // => True
 * ```
 */
export function isIndefinite(m: Matrix): Truth {
  if (!m.isSquare) return false;
  return truthAnd(truthNot(isPositiveSemidefinite(m)), truthNot(isNegativeSemidefinite(m)));
}

/**
 * Tests whether each diagonal magnitude exceeds the sum of the other magnitudes in its row.
 * @param m - The input matrix.
 * @returns Whether the property holds, or `'unknown'` if undecidable.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.is_strongly_diagonally_dominant`
 * @example
 * ```ts
 * import { Matrix, isStronglyDiagonallyDominant } from '@symjs/symjs';
 * isStronglyDiagonallyDominant(Matrix.of([[-4, 2, 1], [1, 6, 2], [1, -2, 5]])); // => True
 * ```
 */
export function isStronglyDiagonallyDominant(m: Matrix): Truth {
  return m.isSquare ? toTruth(diagonallyDominant(m, true)) : false;
}

/**
 * Tests whether each diagonal magnitude is at least the sum of the other magnitudes in its row.
 * @param m - The input matrix.
 * @returns Whether the property holds, or `'unknown'` if undecidable.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.is_weakly_diagonally_dominant`
 * @example
 * ```ts
 * import { Matrix, isWeaklyDiagonallyDominant } from '@symjs/symjs';
 * isWeaklyDiagonallyDominant(Matrix.of([[-4, 2, 1], [1, 6, 2], [1, -2, 5]])); // => True
 * ```
 */
export function isWeaklyDiagonallyDominant(m: Matrix): Truth {
  return m.isSquare ? toTruth(diagonallyDominant(m, false)) : false;
}

/**
 * Cholesky: lower L with A = L L^H (hermitian) or A = L L^T.
 * @param m - The input matrix.
 * @param hermitian - Whether to use conjugate transposition.
 * @returns The resulting matrix.
 * @throws NonSquareMatrixError when the matrix is not square.
 * @throws MatrixError when the matrix is not Hermitian or the matrix is not symmetric.
 * @throws NonPositiveDefiniteMatrixError when the matrix is not positive definite.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.cholesky`
 * @remarks SymPy prints this result as `Matrix([[1, 0], [2, sqrt(3)*I]])`.
 * @example
 * ```ts
 * import { Matrix, cholesky } from '@symjs/symjs';
 * cholesky(Matrix.of([[1, 2], [2, 1]]), false); // => Matrix([
 * //   [1,         0],
 * //   [2, sqrt(3)*I]])
 * ```
 */
export function cholesky(m: Matrix, hermitian = true): Matrix {
  if (!m.isSquare) throw new NonSquareMatrixError('Matrix must be square');
  // SymPy raises ValueError for these two
  if (hermitian && m.isHermitian() !== true) throw new MatrixError('Matrix must be Hermitian.');
  if (!hermitian && !m.equalsSimplified(m.transpose())) throw new MatrixError('Matrix must be symmetric.');
  const n = m.rows;
  const L: Expr[][] = Array.from({ length: n }, () => Array.from({ length: n }, () => S.Zero as Expr));
  const cj = (e: Expr) => (hermitian ? conjugate(e) : e);
  for (let i = 0; i < n; i++) {
    const Li = at(L, i);
    for (let j = 0; j < i; j++) {
      const Lj = at(L, j);
      let s: Expr = m.get(i, j);
      for (let k = 0; k < j; k++) s = add(s, mul(-1, at(Li, k), cj(at(Lj, k))));
      Li[j] = tidy(mul(s, pow(at(Lj, j), -1)));
    }
    let d: Expr = m.get(i, i);
    for (let k = 0; k < i; k++) d = add(d, mul(-1, at(Li, k), cj(at(Li, k))));
    const d2 = tidy(d);
    // SymPy: Lii2.is_positive is False (the Hermitian case only)
    if (hermitian && isNotPositive(d2)) throw new NonPositiveDefiniteMatrixError('Matrix must be positive-definite');
    Li[i] = sqrt(d2);
  }
  return Matrix.of(L);
}

/** SymPy e.is_positive is False for a real value (a pivot of a Hermitian matrix): a number by its value, anything else by the assumptions. */
function isNotPositive(e: Expr): boolean {
  if (e.freeSymbols().size === 0) {
    try {
      return e.toComplex().re <= 0;
    } catch {
      // not numerically evaluable: decided by the assumptions
    }
  }
  return isPositive(e) === false;
}

/**
 * Factors a matrix into unit lower triangular, diagonal and transposed triangular factors.
 * @param m - The input matrix.
 * @param hermitian - Whether to use conjugate transposition.
 * @returns The unit lower triangular and diagonal factors.
 * @throws NonSquareMatrixError when the matrix is not square.
 * @throws MatrixError when the matrix is not Hermitian or the matrix is not symmetric.
 * @throws NonPositiveDefiniteMatrixError when the matrix is not positive definite.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.LDLdecomposition`
 * @example
 * ```ts
 * import { LDLdecomposition, Matrix } from '@symjs/symjs';
 * LDLdecomposition(Matrix.of([[25, 15, -5], [15, 18, 0], [-5, 0, 11]]))[1].toArray(); // => [[25, 0, 0], [0, 9, 0], [0, 0, 9]]
 * ```
 */
export function ldl(m: Matrix, hermitian = true): [Matrix, Matrix] {
  if (!m.isSquare) throw new NonSquareMatrixError('Matrix must be square.');
  if (hermitian && m.isHermitian() !== true) throw new MatrixError('Matrix must be Hermitian.');
  if (!hermitian && !m.equalsSimplified(m.transpose())) throw new MatrixError('Matrix must be symmetric.');
  const n = m.rows;
  const L: Expr[][] = Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, j) => (i === j ? S.One : S.Zero) as Expr));
  const D: Expr[] = [];
  const cj = (e: Expr) => (hermitian ? conjugate(e) : e);
  for (let i = 0; i < n; i++) {
    const Li = at(L, i);
    for (let j = 0; j < i; j++) {
      const Lj = at(L, j);
      let s: Expr = m.get(i, j);
      for (let k = 0; k < j; k++) s = add(s, mul(-1, at(Li, k), cj(at(Lj, k)), at(D, k)));
      Li[j] = tidy(mul(s, pow(at(D, j), -1)));
    }
    let d: Expr = m.get(i, i);
    for (let k = 0; k < i; k++) d = add(d, mul(-1, at(Li, k), cj(at(Li, k)), at(D, k)));
    const pivot = tidy(d);
    if (hermitian && isPositive(pivot) === false) throw new NonPositiveDefiniteMatrixError('Matrix must be positive-definite');
    D.push(pivot);
  }
  return [Matrix.of(L), Matrix.diag(...D)];
}

/**
 * Factors a matrix into lower and upper triangular factors with row swaps.
 * @param m - The input matrix.
 * @returns The lower factor, upper factor and row swaps.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.LUdecomposition`
 * @example
 * ```ts
 * import { LUdecomposition, Matrix } from '@symjs/symjs';
 * LUdecomposition(Matrix.of([[4, 3], [6, 3]]))[0].toArray(); // => [[1, 0], [3/2, 1]]
 * ```
 */
export function luDecomposition(m: Matrix): [Matrix, Matrix, [number, number][]] {
  const n = m.rows;
  // combined storage: U on and above the diagonal, the multipliers of L below
  const lu = rowsOf(m);
  const perm: [number, number][] = [];
  let pc = 0;
  for (let pr = 0; pr < n - 1 && pc < m.cols; pr++, pc++) {
    let p = -1;
    while (pc < m.cols) {
      // SymPy _find_reasonable_pivot_naive: the first entry known to be nonzero, else the first undecided one
      let undecided = -1;
      for (let i = pr; i < n && p < 0; i++) {
        const v = ent(lu, i, pc);
        if (isZeroE(v)) continue;
        if (isZero(v) === false) p = i;
        else if (undecided < 0) undecided = i;
      }
      if (p < 0) p = undecided;
      if (p >= 0) break;
      pc++;
    }
    if (p < 0) break;
    if (p !== pr) {
      perm.push([pr, p]);
      const rowR = at(lu, pr);
      const rowP = at(lu, p);
      for (let k = 0; k < m.cols; k++) {
        if (k >= pr && k < pc) continue;
        const tmp = at(rowR, k);
        rowR[k] = at(rowP, k);
        rowP[k] = tmp;
      }
    }
    const Ur = at(lu, pr);
    const pivInv = pow(at(Ur, pc), -1);
    for (let i = pr + 1; i < n; i++) {
      const Ui = at(lu, i);
      const f = tidy(mul(at(Ui, pc), pivInv));
      for (let j = pc + 1; j < m.cols; j++) Ui[j] = tidy(add(at(Ui, j), mul(-1, f, at(Ur, j))));
      if (pr !== pc) Ui[pc] = S.Zero;
      Ui[pr] = f;
    }
  }
  const Lm = Matrix.fromFunction(n, n, (i, j) => (i < j ? 0 : i === j ? 1 : j < m.cols ? ent(lu, i, j) : 0));
  const Um = Matrix.fromFunction(n, m.cols, (i, j) => (i > j ? 0 : ent(lu, i, j)));
  return [Lm, Um, perm];
}

/**
 * Factors a matrix into a matrix of orthonormal columns and an upper triangular matrix.
 * @param m - The input matrix.
 * @returns The orthogonal and triangular factors, in that order.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.QRdecomposition`
 * @example
 * ```ts
 * import { Matrix, QRdecomposition } from '@symjs/symjs';
 *
 * const A = Matrix.of([[12, -51, 4], [6, 167, -68], [-4, 24, -41]]);
 * const [Q, R] = QRdecomposition(A);
 * Q.mul(R).equals(A); // => True
 * ```
 */
export function qrDecomposition(m: Matrix): [Matrix, Matrix] {
  const qs: Matrix[] = [];
  const R: Expr[][] = [];
  for (let j = 0; j < m.cols; j++) {
    let v = m.col(j);
    const rcol: Expr[] = [];
    for (const q of qs) {
      const r = tidy(dot(q, m.col(j), true));
      rcol.push(r);
      v = v.sub(q.scale(r));
    }
    // a dependent column keeps its projections on the earlier q's as its R column
    R.push(rcol);
    const nv = sqrt(tidy(dot(v, v, true)));
    if (isZeroE(nv)) continue;
    rcol.push(nv);
    qs.push(v.map((e) => tidy(mul(e, pow(nv, -1)))));
  }
  const k = qs.length;
  const Rm = Matrix.fromFunction(k, m.cols, (i, j) => R[j]?.[i] ?? 0);
  return [k === 0 ? Matrix.zeros(m.rows, 0) : first(qs).hstack(...qs.slice(1)), Rm];
}

// ---------------------------------------------------------------------------
// vector operations and norms
// ---------------------------------------------------------------------------

/**
 * The dot and cross products of vectors of `@symjs/symjs/vector` (SymPy
 * sympy.vector.dot and cross), registered by vector/vector.ts: dot and
 * cross take matrices or vectors.
 */
export const vectorProducts: {
  dot?: (a: Expr, b: Expr) => Expr;
  cross?: (a: Expr, b: Expr) => Expr;
} = {};

/**
 * Computes a dot product of two vectors, optionally conjugating one operand.
 * @param a - The first operand.
 * @param b - The second operand.
 * @param hermitian - Whether to use conjugate transposition.
 * @param convention - Which argument is conjugated for a Hermitian dot product.
 * @returns A dot product of two vectors, optionally conjugating one operand.
 * @throws RangeError when the inner dimensions do not agree.
 * @see SymPy `sympy.vector.vector.dot`
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.dot`
 * @example
 * ```ts
 * import { Matrix, dot } from '@symjs/symjs';
 * dot(Matrix.of([[1, 2, 3]]), Matrix.col(3, 2, 1), false, 'maths'); // => 10
 * ```
 */
export function dot(a: Matrix | Expr, b: Matrix | Expr, hermitian = false, convention: 'maths' | 'physics' = 'maths'): Expr {
  if (!(a instanceof Matrix) || !(b instanceof Matrix)) return vectorProduct('dot', a, b);
  if (a.data.length !== b.data.length) throw new RangeError('dot: dimension mismatch');
  let x = a.data;
  let y = b.data;
  if (hermitian && convention === 'maths') x = x.map((e) => conjugate(e));
  if (hermitian && convention === 'physics') y = y.map((e) => conjugate(e));
  return add(...x.map((e, i) => mul(e, at(y, i))));
}

/** The vector product registered by vector/vector.ts. */
function vectorProduct(name: 'dot' | 'cross', a: Matrix | Expr, b: Matrix | Expr): Expr {
  const f = vectorProducts[name];
  if (f === undefined) throw new NotLoadedError(`${name} of vectors is not available: import '@symjs/symjs/vector' (or '@symjs/symjs')`);
  if (a instanceof Matrix || b instanceof Matrix) throw new TypeError(`${name}: a matrix and a vector`);
  return f(a, b);
}

/**
 * Computes the cross product of two three-dimensional vectors.
 * @param a - The first operand.
 * @param b - The second operand.
 * @returns The cross product of two three-dimensional vectors.
 * @see SymPy `sympy.vector.vector.cross`
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.cross`
 * @remarks SymPy prints this result as `Matrix([[-4], [8], [-4]])`.
 * @example
 * ```ts
 * import { Matrix, cross } from '@symjs/symjs';
 * cross(Matrix.of([[1], [2], [3]]), Matrix.of([[3], [2], [1]])); // => Matrix([
 * //   [-4],
 * //   [ 8],
 * //   [-4]])
 * ```
 */
export function cross(a: Matrix, b: Matrix): Matrix;
export function cross(a: Expr, b: Expr): Expr;
export function cross(a: Matrix | Expr, b: Matrix | Expr): Matrix | Expr {
  if (!(a instanceof Matrix) || !(b instanceof Matrix)) return vectorProduct('cross', a, b);
  const [a1, a2, a3] = threeEntries(a);
  const [b1, b2, b3] = threeEntries(b);
  const v = [
    add(mul(a2, b3), mul(-1, a3, b2)),
    add(mul(a3, b1), mul(-1, a1, b3)),
    add(mul(a1, b2), mul(-1, a2, b1)),
  ];
  return a.rows === 1 ? Matrix.row(...v) : Matrix.col(...v);
}

function threeEntries(v: Matrix): [Expr, Expr, Expr] {
  const [x, y, z] = v.data;
  if (x === undefined || y === undefined || z === undefined) throw new RangeError('cross: 3-vectors expected');
  return [x, y, z];
}

/**
 * Compute the singular values of a Matrix.
 * @param m - The input matrix.
 * @returns The singular values with their multiplicities.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.singular_values`
 * @example
 * ```ts
 * import { Matrix, singularValues } from '@symjs/symjs';
 * singularValues(Matrix.of([[0, 1], [-1, 0]])); // => [1, 1]
 * ```
 */
export function singularValues(m: Matrix): Expr[] {
  // eigenvals of the cols x cols matrix A^H A gives all cols values (or throws)
  const vals = m.adjoint().mul(m).eigenvals(false).map((v) => sqrt(v));
  return vals.sort((a, b) => {
    if (a.isNumber && b.isNumber) {
      try { return b.toNumber() - a.toNumber(); }
      catch { /* A symbolic function may have no numerical evaluator. */ }
    }
    return compareKeys(sortKey(b), sortKey(a));
  });
}

/**
 * Computes the specified vector or matrix norm.
 * @param m - The input matrix.
 * @param ord - The norm order.
 * @returns The specified vector or matrix norm.
 * @throws RangeError when the requested norm order is unsupported.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.norm`
 * @example
 * ```ts
 * import { Matrix, norm, oo } from '@symjs/symjs';
 * norm(Matrix.of([[1], [-2]]), oo); // => 2
 * ```
 */
export function norm(m: Matrix, ord?: ExprLike | string): Expr {
  const isVector = m.rows === 1 || m.cols === 1;
  const vals = m.data;
  const o = ord === undefined ? undefined : typeof ord === 'string' ? ord : sympify(ord);
  if (isVector) {
    if (o === undefined || (o instanceof Rational && o.p === 2n && o.q === 1n)) {
      return sqrt(add(...vals.map((v) => pow(abs(v), 2))));
    }
    if (o instanceof Special && o.name === 'oo') return Max(...vals.map((v) => abs(v)));
    if (o instanceof Special && o.name === '-oo') return Min(...vals.map((v) => abs(v)));
    if (o instanceof Rational && o.isOne) return add(...vals.map((v) => abs(v)));
    if (o instanceof Expr) return pow(add(...vals.map((v) => pow(abs(v), o))), pow(o, -1));
    throw new RangeError(`norm: unsupported order ${String(ord)}`);
  }
  if (o === undefined || o === 'fro' || o === 'f' || o === 'frobenius') return sqrt(add(...vals.map((v) => pow(abs(v), 2))));
  if (o instanceof Rational && o.isOne) {
    return Max(...Array.from({ length: m.cols }, (_, j) => add(...m.col(j).data.map((v) => abs(v)))));
  }
  if (o instanceof Special && o.name === 'oo') {
    return Max(...Array.from({ length: m.rows }, (_, i) => add(...m.row(i).data.map((v) => abs(v)))));
  }
  if (o instanceof Rational && o.p === 2n && o.q === 1n) return Max(...singularValues(m));
  if (o instanceof Rational && o.p === -2n && o.q === 1n) return Min(...singularValues(m));
  throw new RangeError(`norm: unsupported order ${String(ord)}`);
}

/**
 * Moore-Penrose pseudo-inverse via a full rank factorization.
 * @param m - The input matrix.
 * @returns The resulting matrix.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.pinv`
 * @remarks SymPy prints this result as `Matrix([[-17/18, 4/9], [-1/9, 1/9], [13/18, -2/9]])`.
 * @example
 * ```ts
 * import { Matrix, pinv } from '@symjs/symjs';
 * pinv(Matrix.of([[1, 2, 3], [4, 5, 6]])); // => Matrix([
 * //   [-17/18,  4/9],
 * //   [  -1/9,  1/9],
 * //   [ 13/18, -2/9]])
 * ```
 */
export function pinv(m: Matrix): Matrix {
  const [B, C] = rankDecomposition(m);
  if (B.cols === 0) return Matrix.zeros(m.cols, m.rows);
  const BH = B.adjoint(), CH = C.adjoint();
  return CH.mul(C.mul(CH).inv()).mul(BH.mul(B).inv()).mul(BH).map(tidy);
}

/**
 * Calculates the Jacobian matrix (derivative of a vector-valued function).
 * @param X - The functions to differentiate.
 * @param Y - The variables in column order.
 * @returns The derivatives of each function with respect to each variable.
 * @throws TypeError when a vector argument has more than one row and column.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.jacobian`
 * @remarks SymPy prints this result as `Matrix([[cos(phi), -rho*sin(phi)], [sin(phi), rho*cos(phi)]])`.
 * @example
 * ```ts
 * import { Matrix, ex, jacobian, symbols } from '@symjs/symjs';
 *
 * const [rho, phi] = symbols('rho phi');
 * jacobian(Matrix.of([[ex`rho*cos(phi)`], [ex`rho*sin(phi)`]]), Matrix.of([[rho], [phi]])); // => Matrix([
 * //   [cos(phi), -rho*sin(phi)],
 * //   [sin(phi),  rho*cos(phi)]])
 * ```
 */
export function jacobian(X: Matrix, Y: Matrix | readonly Expr[]): Matrix {
  if (X.rows !== 1 && X.cols !== 1) throw new TypeError('jacobian requires a row or column matrix');
  if (Y instanceof Matrix && Y.rows !== 1 && Y.cols !== 1) throw new TypeError('jacobian variables must be a row or column matrix');
  const ys = Y instanceof Matrix ? Y.data : Y;
  const xs = X.data;
  return Matrix.fromFunction(xs.length, ys.length, (i, j) => diff(at(xs, i), at(ys, j)));
}

// ---------------------------------------------------------------------------
// structural helpers
// ---------------------------------------------------------------------------

// SymPy Matrix methods, also as functions (the implementations are the Matrix methods)
export const upperTriangular = (m: Matrix, k = 0): Matrix => m.upperTriangular(k);
export const lowerTriangular = (m: Matrix, k = 0): Matrix => m.lowerTriangular(k);
export const diagonal = (m: Matrix, k = 0): Matrix => m.diagonal(k);
export const extract = (m: Matrix, rows: readonly (number | boolean)[], cols: readonly (number | boolean)[]): Matrix => m.extract(rows, cols);
export const reshape = (m: Matrix, r: number, c: number): Matrix => m.reshape(r, c);
export const rot90 = (m: Matrix, k = 1): Matrix => m.rot90(k);
export const vech = (m: Matrix, includeDiagonal = true, checkSymmetry = true): Matrix => m.vech({ diagonal: includeDiagonal, checkSymmetry });
export const vec = (m: Matrix): Matrix => m.vec();
export const minorSubmatrix = (m: Matrix, i: number, j: number): Matrix => m.minorSubmatrix(i, j);
export const minorDet = (m: Matrix, i: number, j: number): Expr => m.minorEntry(i, j);
export const cofactor = (m: Matrix, i: number, j: number): Expr => m.cofactor(i, j);
export const isSymmetric = (m: Matrix, simplifyEntries = true): boolean => m.isSymmetric(simplifyEntries);
export const isAntiSymmetric = (m: Matrix, simplifyEntries = true): Truth => m.isAntiSymmetric(simplifyEntries);
export const isDiagonal = (m: Matrix): boolean => m.isDiagonal();
export const isUpper = (m: Matrix): boolean => m.isUpper();
export const isLower = (m: Matrix): boolean => m.isLower();
export const isNilpotent = (m: Matrix): boolean => m.isNilpotent();
/**
 * Return the Hadamard product (elementwise product) of A and B.
 * @param a - The first operand.
 * @param b - The second operand.
 * @returns The Hadamard product (elementwise product) of A and B.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.multiply_elementwise`
 * @remarks SymPy prints this result as `Matrix([[0, 10, 200], [300, 40, 5]])`.
 * @example
 * ```ts
 * import { Matrix, multiplyElementwise } from '@symjs/symjs';
 * multiplyElementwise(Matrix.of([[0, 1, 2], [3, 4, 5]]), Matrix.of([[1, 10, 100], [100, 10, 1]])); // => Matrix([
 * //   [  0, 10, 200],
 * //   [300, 40,   5]])
 * ```
 */
export const multiplyElementwise = (a: Matrix, b: Matrix): Matrix => a.multiplyElementwise(b);
/**
 * The Hadamard product.
 * @param a - The first operand.
 * @param b - The second operand.
 * @returns The resulting matrix.
 * @see SymPy `sympy.matrices.dense.matrix_multiply_elementwise`
 * @example
 * ```ts
 * import { Matrix, matrixMultiplyElementwise } from '@symjs/symjs';
 * matrixMultiplyElementwise(Matrix.of([[0, 1, 2]]), Matrix.of([[1, 10, 100]])).toArray(); // => [[0, 10, 200]]
 * ```
 */
export const matrixMultiplyElementwise = (a: Matrix, b: Matrix): Matrix => a.multiplyElementwise(b);
export const project = (a: Matrix, b: Matrix): Matrix => a.project(b);
export const rowInsert = (m: Matrix, pos: number, o: Matrix): Matrix => m.rowInsert(pos, o);
export const colInsert = (m: Matrix, pos: number, o: Matrix): Matrix => m.colInsert(pos, o);

/**
 * Block-diagonal matrix from scalars and matrices.
 * @param blocks - The matrices or scalars to place along the diagonal.
 * @returns The assembled block-diagonal matrix.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.diag`
 * @example
 * ```ts
 * import { blockDiag } from '@symjs/symjs';
 * blockDiag(1, 2, 3).toArray(); // => [[1, 0, 0], [0, 2, 0], [0, 0, 3]]
 * ```
 */
export function blockDiag(...blocks: (Matrix | ExprLike)[]): Matrix {
  return blockDiagSized(blocks);
}

export interface BlockDiagOptions {
  readonly rows?: number;
  readonly cols?: number;
}

/**
 * Returns a matrix with the specified diagonal.
 * @param blocks - The matrices or scalars to place along the diagonal.
 * @param opts - The settings described by {@link BlockDiagOptions}.
 * @returns The block-diagonal matrix with any requested padding.
 * @throws RangeError when the specified dimensions cannot accommodate the entries.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.diag`
 * @remarks SymPy prints this result as `Matrix([[1], [2], [3]])`.
 * @example
 * ```ts
 * import { Matrix, blockDiagSized } from '@symjs/symjs';
 * blockDiagSized([Matrix.col(1, 2, 3)], {}); // => Matrix([
 * //   [1],
 * //   [2],
 * //   [3]])
 * ```
 */
export function blockDiagSized(blocks: readonly (Matrix | ExprLike)[], opts: BlockDiagOptions = {}): Matrix {
  const ms = blocks.map((b) => (b instanceof Matrix ? b : Matrix.of([[b]])));
  const minimumRows = ms.reduce((s, m) => s + m.rows, 0);
  const minimumCols = ms.reduce((s, m) => s + m.cols, 0);
  const rows = opts.rows ?? opts.cols ?? minimumRows;
  const cols = opts.cols ?? opts.rows ?? minimumCols;
  if (rows < minimumRows || cols < minimumCols) throw new RangeError(`The constructed matrix is ${minimumRows} x ${minimumCols} but a size of ${rows} x ${cols} was specified.`);
  const out = Matrix.zeros(rows, cols).toArray();
  let r0 = 0;
  let c0 = 0;
  for (const m of ms) {
    for (let i = 0; i < m.rows; i++) {
      const row = at(out, r0 + i);
      for (let j = 0; j < m.cols; j++) row[c0 + j] = m.get(i, j);
    }
    r0 += m.rows;
    c0 += m.cols;
  }
  return Matrix.of(out);
}

/**
 * Constructs the clockwise rotation matrix about the x-axis.
 * @param t - The rotation angle in radians.
 * @returns The clockwise rotation matrix about the x-axis.
 * @see SymPy `sympy.matrices.dense.rot_axis1`
 * @remarks SymPy prints this result as `Matrix([[1, 0, 0], [0, 0, 1], [0, -1, 0]])`.
 * @example
 * ```ts
 * import { ex, rotAxis1 } from '@symjs/symjs';
 * rotAxis1(ex`pi/2`); // => Matrix([
 * //   [1,  0, 0],
 * //   [0,  0, 1],
 * //   [0, -1, 0]])
 * ```
 */
export const rotAxis1 = (t: ExprLike): Matrix =>
  Matrix.of([[1, 0, 0], [0, cos(t), sin(t)], [0, mul(-1, sin(t)), cos(t)]]);
/**
 * Constructs the clockwise rotation matrix about the y-axis.
 * @param t - The rotation angle in radians.
 * @returns The clockwise rotation matrix about the y-axis.
 * @see SymPy `sympy.matrices.dense.rot_axis2`
 * @remarks SymPy prints this result as `Matrix([[0, 0, -1], [0, 1, 0], [1, 0, 0]])`.
 * @example
 * ```ts
 * import { ex, rotAxis2 } from '@symjs/symjs';
 * rotAxis2(ex`pi/2`); // => Matrix([
 * //   [0, 0, -1],
 * //   [0, 1,  0],
 * //   [1, 0,  0]])
 * ```
 */
export const rotAxis2 = (t: ExprLike): Matrix =>
  Matrix.of([[cos(t), 0, mul(-1, sin(t))], [0, 1, 0], [sin(t), 0, cos(t)]]);
/**
 * Constructs the clockwise rotation matrix about the z-axis.
 * @param t - The rotation angle in radians.
 * @returns The clockwise rotation matrix about the z-axis.
 * @see SymPy `sympy.matrices.dense.rot_axis3`
 * @remarks SymPy prints this result as `Matrix([[0, 1, 0], [-1, 0, 0], [0, 0, 1]])`.
 * @example
 * ```ts
 * import { ex, rotAxis3 } from '@symjs/symjs';
 * rotAxis3(ex`pi/2`); // => Matrix([
 * //   [ 0, 1, 0],
 * //   [-1, 0, 0],
 * //   [ 0, 0, 1]])
 * ```
 */
export const rotAxis3 = (t: ExprLike): Matrix =>
  Matrix.of([[cos(t), sin(t), 0], [mul(-1, sin(t)), cos(t), 0], [0, 0, 1]]);
/**
 * Constructs the counterclockwise rotation matrix about the x-axis.
 * @param t - The rotation angle in radians.
 * @returns The counterclockwise rotation matrix about the x-axis.
 * @see SymPy `sympy.matrices.dense.rot_ccw_axis1`
 * @remarks SymPy prints this result as `Matrix([[1, 0, 0], [0, 0, -1], [0, 1, 0]])`.
 * @example
 * ```ts
 * import { ex, rotCcwAxis1 } from '@symjs/symjs';
 * rotCcwAxis1(ex`pi/2`); // => Matrix([
 * //   [1, 0,  0],
 * //   [0, 0, -1],
 * //   [0, 1,  0]])
 * ```
 */
export const rotCcwAxis1 = (t: ExprLike): Matrix => rotAxis1(t).transpose();
/**
 * Constructs the counterclockwise rotation matrix about the y-axis.
 * @param t - The rotation angle in radians.
 * @returns The counterclockwise rotation matrix about the y-axis.
 * @see SymPy `sympy.matrices.dense.rot_ccw_axis2`
 * @remarks SymPy prints this result as `Matrix([[0, 0, 1], [0, 1, 0], [-1, 0, 0]])`.
 * @example
 * ```ts
 * import { ex, rotCcwAxis2 } from '@symjs/symjs';
 * rotCcwAxis2(ex`pi/2`); // => Matrix([
 * //   [ 0, 0, 1],
 * //   [ 0, 1, 0],
 * //   [-1, 0, 0]])
 * ```
 */
export const rotCcwAxis2 = (t: ExprLike): Matrix => rotAxis2(t).transpose();
/**
 * Constructs the counterclockwise rotation matrix about the z-axis.
 * @param t - The rotation angle in radians.
 * @returns The counterclockwise rotation matrix about the z-axis.
 * @see SymPy `sympy.matrices.dense.rot_ccw_axis3`
 * @remarks SymPy prints this result as `Matrix([[0, -1, 0], [1, 0, 0], [0, 0, 1]])`.
 * @example
 * ```ts
 * import { ex, rotCcwAxis3 } from '@symjs/symjs';
 * rotCcwAxis3(ex`pi/2`); // => Matrix([
 * //   [0, -1, 0],
 * //   [1,  0, 0],
 * //   [0,  0, 1]])
 * ```
 */
export const rotCcwAxis3 = (t: ExprLike): Matrix => rotAxis3(t).transpose();

/**
 * Givens rotation in the (i, j) plane of a dim x dim identity.
 * @param i - The zero-based row index.
 * @param j - The zero-based column index.
 * @param theta - The rotation angle in radians.
 * @param dim - The dimension of the rotation matrix.
 * @returns The resulting matrix.
 * @see SymPy `sympy.matrices.dense.rot_givens`
 * @remarks SymPy prints this result as `Matrix([[0, -1, 0], [1, 0, 0], [0, 0, 1]])`.
 * @example
 * ```ts
 * import { ex, rotGivens } from '@symjs/symjs';
 * rotGivens(1, 0, ex`pi/2`, 3); // => Matrix([
 * //   [0, -1, 0],
 * //   [1,  0, 0],
 * //   [0,  0, 1]])
 * ```
 */
export function rotGivens(i: number, j: number, theta: ExprLike, dim = 3): Matrix {
  const c = cos(theta);
  const s = sin(theta);
  return Matrix.fromFunction(dim, dim, (a, b) => {
    if (a === i && b === i) return c;
    if (a === j && b === j) return c;
    if (a === i && b === j) return s;
    if (a === j && b === i) return mul(-1, s);
    return a === b ? 1 : 0;
  });
}

/**
 * Returns a Jordan block.
 * @param size - The number of positions.
 * @param eigenvalue - The eigenvalue along the diagonal.
 * @param band - The side of the diagonal on which the ones appear.
 * @returns A Jordan block.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.jordan_block`
 * @remarks SymPy prints this result as `Matrix([[x, 1, 0, 0], [0, x, 1, 0], [0, 0, x, 1], [0, 0, 0, x]])`.
 * @example
 * ```ts
 * import { jordanBlock, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * jordanBlock(4, x); // => Matrix([
 * //   [x, 1, 0, 0],
 * //   [0, x, 1, 0],
 * //   [0, 0, x, 1],
 * //   [0, 0, 0, x]])
 * ```
 */
export function jordanBlock(size: number, eigenvalue: ExprLike, band: 'upper' | 'lower' = 'upper'): Matrix {
  return Matrix.fromFunction(size, size, (i, j) => (i === j ? eigenvalue : band === 'upper' ? (j === i + 1 ? 1 : 0) : i === j + 1 ? 1 : 0));
}

/**
 * Companion matrix of a monic polynomial (SymPy Matrix.companion(poly)),
 * given as a Poly or by its coefficients (highest first).
 * @param p - The monic polynomial or its coefficients in descending order.
 * @returns The resulting matrix.
 * @throws RangeError when the polynomial is not monic.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.companion`
 * @example
 * ```ts
 * import { Poly, ZZ, companion, ex } from '@symjs/symjs';
 *
 * const x = ex`x`;
 * companion(Poly.from(ex`c0 + x`, [x], { domain: 'ZZ[c0]', pure: false })); // => Matrix([[-c0]])
 * ```
 */
export function companion(p: readonly Expr[] | { allCoeffs(): Expr[]; toString(): string }): Matrix {
  const coeffs = 'allCoeffs' in p ? p.allCoeffs() : p;
  if (coeffs.length < 2 || !(first(coeffs) instanceof Rational && first(coeffs).equals(1))) throw new RangeError(`${String(p)} must be a monic polynomial.`);
  const n = coeffs.length - 1;
  return Matrix.fromFunction(n, n, (i, j) => (j === n - 1 ? mul(-1, at(coeffs, n - i)) : i === j + 1 ? 1 : 0));
}

/**
 * Rectangular permanent by subset dynamic programming of the Laplace recurrence.
 * @param mIn - The input matrix.
 * @returns The permanent of the explicit matrix.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.per`
 * @example
 * ```ts
 * import { Matrix, permanent } from '@symjs/symjs';
 * permanent(Matrix.of([[1], [5], [7]])); // => 13
 * ```
 */
export function permanent(mIn: Matrix): Expr {
  let m = mIn;
  let [r, c] = m.shape;
  if (r > c) {
    m = m.transpose();
    [r, c] = [c, r];
  }
  if (r === 0) return S.One;
  if (r === 1) return add(...m.row(0).data);
  const cache = new Map<bigint, Expr>();
  const visit = (row: number, used: bigint): Expr => {
    if (row === r) return S.One;
    const cached = cache.get(used);
    if (cached !== undefined) return cached;
    const terms: Expr[] = [];
    for (let col = 0; col < c; col++) {
      const bit = 1n << BigInt(col), entry = m.get(row, col);
      if ((used & bit) !== 0n || isExactZero(entry)) continue;
      terms.push(mul(entry, visit(row + 1, used | bit)));
    }
    const result = add(...terms);
    cache.set(used, result);
    return result;
  };
  return visit(0, 0n);
}

/**
 * Finds connected or strongly connected components of a graph or of the graph defined by a
 * matrix's nonzero entries.
 *
 * @see SymPy `sympy.utilities.iterables.connected_components`
 * @see SymPy `sympy.utilities.iterables.strongly_connected_components`
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.connected_components`
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.strongly_connected_components`
 */
export { connectedComponents, stronglyConnectedComponents } from '../utilities/iterables';

/**
 * Least-squares solution A^+ B plus the null-space part (I - A^+ A) W.
 * @param A - The input matrix.
 * @param B - The right-hand side of the linear system.
 * @param arbitrary - The matrix of free parameters in the solution.
 * @returns The resulting matrix.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.pinv_solve`
 * @remarks SymPy prints this result as `Matrix([[-55/18], [1/9], [59/18]])`.
 * @example
 * ```ts
 * import { Matrix, pinvSolve } from '@symjs/symjs';
 * pinvSolve(Matrix.of([[1, 2, 3], [4, 5, 6]]), Matrix.of([[7], [8]]), Matrix.of([[0], [0], [0]])); // => Matrix([
 * //   [-55/18],
 * //   [   1/9],
 * //   [ 59/18]])
 * ```
 */
export function pinvSolve(A: Matrix, B: Matrix, arbitrary?: Matrix): Matrix {
  const Ap = pinv(A);
  const n = A.shape[1];
  const W = arbitrary ?? Matrix.fromFunction(n, B.shape[1], (i, j) => new Dummy(`w${i}_${j}`));
  const proj = Matrix.eye(n).sub(Ap.mul(A));
  return Ap.mul(B).add(proj.mul(W)).map((e) => expandMul(e));
}

// ---- solving and constructions (SymPy Matrix.solve, GramSchmidt, hessian, wronskian, casoratian) ----

/**
 * Solves a linear system by Gauss–Jordan elimination, introducing parameters for free variables.
 * @param A - The input matrix.
 * @param b - The right-hand side of the linear system.
 * @param opts - Set `freevar` to include the free column indices.
 * @returns The solution, its parameters and, when requested, the free column indices.
 * @throws RangeError when the linear system is inconsistent.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.gauss_jordan_solve`
 * @example
 * ```ts
 * import { Matrix, gaussJordanSolve } from '@symjs/symjs';
 * gaussJordanSolve(Matrix.of([[1, 2], [2, 1]]), Matrix.col(5, 4))[0].toArray(); // => [[1], [2]]
 * ```
 */
export function gaussJordanSolve(A: Matrix, b: Matrix, opts: { freevar: true }): [Matrix, Matrix, number[]];
export function gaussJordanSolve(A: Matrix, b: Matrix, opts?: { freevar?: false }): [Matrix, Matrix];
export function gaussJordanSolve(A: Matrix, b: Matrix, opts: { freevar?: boolean } = {}): [Matrix, Matrix] | [Matrix, Matrix, number[]] {
  const n = A.cols;
  const [R, pivots] = rref(A.hstack(b));
  for (let i = 0; i < R.rows; i++) {
    const row = Array.from({ length: n }, (_, j) => R.get(i, j));
    if (row.every((c) => c instanceof Rational && c.isZero) && Array.from({ length: b.cols }, (_, c) => R.get(i, n + c)).some((e) => !isExactZero(e))) {
      throw new RangeError('Linear system has no solution');
    }
  }
  const pv = pivots.filter((p) => p < n);
  const free = Array.from({ length: n }, (_, j) => j).filter((j) => !pv.includes(j));
  const cols = b.cols;
  const prefix = uniquelyNamedSymbol('tau', [...A.data, ...b.data], {
    compare: (name) => name.replace(/\d+$/, ''), modify: (name) => `_${name}`,
  }).name;
  const taus = Matrix.fromFunction(free.length, cols, (i, c) => new Sym(`${prefix}${i * cols + c}`));
  const sol = Matrix.fromFunction(n, cols, (j, c) => {
    const f = free.indexOf(j);
    if (f >= 0) return taus.get(f, c);
    const i = pv.indexOf(j);
    // x_j = rhs_i - sum over free columns
    return add(R.get(i, n + c), ...free.map((fj, k) => mul(-1, R.get(i, fj), taus.get(k, c))));
  });
  return opts.freevar === true ? [sol, taus, free] : [sol, taus];
}

/**
 * The unique solution of A*x = b.
 * @param A - The input matrix.
 * @param b - The right-hand side of the linear system.
 * @returns The resulting matrix.
 * @throws NonInvertibleMatrixError when the matrix is singular.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.solve`
 * @remarks SymPy prints this result as `Matrix([[0, -5], [4, 3], [-6, 9]])`.
 * @example
 * ```ts
 * import { Matrix, matrixSolve } from '@symjs/symjs';
 * matrixSolve(Matrix.of([[0, -6, 1], [0, -6, -1], [-5, -2, 3]]), Matrix.of([[-30, -9], [-18, -27], [-26, 46]])); // => Matrix([
 * //   [ 0, -5],
 * //   [ 4,  3],
 * //   [-6,  9]])
 * ```
 */
export function matrixSolve(A: Matrix, b: Matrix): Matrix {
  const [sol, params] = gaussJordanSolve(A, b);
  if (params.rows) throw new NonInvertibleMatrixError('Matrix det == 0; not invertible.');
  return sol;
}

/**
 * Finds the least-squares solution for a coefficient matrix of full column rank.
 * @param A - The input matrix.
 * @param b - The right-hand side of the linear system.
 * @returns The least-squares solution for a coefficient matrix of full column rank.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.solve_least_squares`
 * @example
 * ```ts
 * import { Matrix, solveLeastSquares } from '@symjs/symjs';
 * solveLeastSquares(Matrix.of([[1, 2], [2, 3], [3, 4]]), Matrix.col(8, 14, 18)).toArray(); // => [[5/3], [10/3]]
 * ```
 */
export function solveLeastSquares(A: Matrix, b: Matrix): Matrix {
  const At = A.transpose();
  return matrixSolve(At.mul(A), At.mul(b));
}

/**
 * Orthogonalizes an ordered list of vectors and optionally normalizes them.
 * @param vs - The vectors to orthogonalize, in order.
 * @param orthonormal - Whether to normalize each orthogonal vector.
 * @param rankcheck - Whether to reject a rank deficiency.
 * @returns The orthogonal or orthonormal basis vectors.
 * @throws RangeError when the vectors are linearly dependent and rank checking is enabled.
 * @see SymPy `sympy.matrices.dense.GramSchmidt`
 */
export function gramSchmidt(vs: readonly Matrix[], orthonormal = false, rankcheck = true): Matrix[] {
  const out: Matrix[] = [];
  for (const v of vs) {
    let u = v;
    for (const w of out) u = u.sub(w.scale(cancel(mul(dot(w, v, true), pow(dot(w, w, true), -1)))));
    u = u.map((e) => cancel(e));
    if (u.data.every((e) => e instanceof Rational && e.isZero)) {
      if (rankcheck) throw new RangeError('GramSchmidt: the vectors are not linearly independent');
      continue;
    }
    out.push(u);
  }
  return orthonormal ? out.map((u) => normalized(u)) : out;
}

/**
 * Divides a vector by its Euclidean norm, leaving the zero vector unchanged.
 * @param v - The vector to normalize.
 * @returns The resulting matrix.
 * @throws ShapeError when a vector argument has more than one row and column.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.normalized`
 * @remarks SymPy prints this result as `Matrix([[3/5], [4/5]])`.
 * @example
 * ```ts
 * import { Matrix, normalized } from '@symjs/symjs';
 * normalized(Matrix.of([[3], [4]])); // => Matrix([
 * //   [3/5],
 * //   [4/5]])
 * ```
 */
export function normalized(v: Matrix): Matrix {
  if (v.rows !== 1 && v.cols !== 1) throw new ShapeError('normalized requires a row or column matrix');
  const n = norm(v);
  if (n instanceof Rational && n.isZero) return v;
  return v.map((e) => mul(e, pow(n, -1)));
}

/**
 * Computes the matrix of second partial derivatives, optionally bordered by constraint gradients.
 * @param f - The scalar function to evaluate or differentiate.
 * @param vars - The ordered differentiation variables.
 * @param constraints - The functions that border the Hessian.
 * @returns The matrix of second partial derivatives, optionally bordered by constraint gradients.
 * @throws ShapeError when the variable list is empty.
 * @see SymPy `sympy.matrices.dense.hessian`
 * @example
 * ```ts
 * import { ex, hessian } from '@symjs/symjs';
 * hessian(ex`x**2 + x*y`, [ex`x`, ex`y`]).toArray(); // => [[2, 1], [1, 0]]
 * ```
 */
export function hessian(f: ExprLike, vars: readonly Expr[], constraints: readonly ExprLike[] = []): Matrix {
  if (!vars.length) throw new ShapeError('hessian: variable list must not be empty');
  const e = sympify(f);
  const gs = constraints.map(sympify), m = gs.length;
  return Matrix.fromFunction(m + vars.length, m + vars.length, (i, j) => {
    if (i < m && j < m) return S.Zero;
    if (i < m) return diff(at(gs, i), at(vars, j - m));
    if (j < m) return diff(at(gs, j), at(vars, i - m));
    return diff(diff(e, at(vars, i - m)), at(vars, j - m));
  });
}

/**
 * Computes the determinant of the successive derivatives of a list of functions.
 * @param fs - The functions whose derivatives form the determinant.
 * @param x - The differentiation variable.
 * @returns The determinant of the successive derivatives of a list of functions.
 * @see SymPy `sympy.matrices.dense.wronskian`
 * @example
 * ```ts
 * import { symbols, wronskian } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * wronskian([], x); // => 1
 * ```
 */
export function wronskian(fs: readonly ExprLike[], x: Expr): Expr {
  const es = fs.map(sympify);
  if (!es.length) return S.One;
  return Matrix.fromFunction(es.length, es.length, (i, j) => diff(at(es, j), x, i)).det();
}

/**
 * Computes the determinant of successive shifts of a list of sequences.
 * @param seqs - The sequences whose shifts form the determinant.
 * @param n - The order of the square matrix.
 * @param zero - Whether to evaluate the shifts starting at zero.
 * @returns The determinant of successive shifts of a list of sequences.
 * @see SymPy `sympy.matrices.dense.casoratian`
 * @example
 * ```ts
 * import { casoratian, ex } from '@symjs/symjs';
 * casoratian([ex`2**n`, ex`factorial(n)`], ex`n`); // => -1
 * ```
 */
export function casoratian(seqs: readonly ExprLike[], n: Expr, zero = true): Expr {
  const es = seqs.map(sympify);
  const k = (i: number) => (zero ? Rational.of(i) : add(n, i));
  return Matrix.fromFunction(es.length, es.length, (i, j) => impl.subs(at(es, j), [[n, k(i)]])).det();
}

/**
 * Applies row reduction to a matrix and its right-hand side together.
 * @param A - The input matrix.
 * @param rhs - The right-hand side of the linear system.
 * @returns The pair of matrices after the same elementary row operations.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.rref_rhs`
 * @example
 * ```ts
 * import { Matrix, rrefRhs } from '@symjs/symjs';
 * rrefRhs(Matrix.of([[1, 1], [2, 1]]), Matrix.col(3, 4))[1].toArray(); // => [[1], [2]]
 * ```
 */
export function rrefRhs(A: Matrix, rhs: Matrix): [Matrix, Matrix] {
  const [R] = rref(A.hstack(Matrix.eye(A.rows), rhs));
  return [R.slice(range(0, A.rows), range(0, A.cols)), R.slice(range(0, A.rows), range(R.cols - rhs.cols, R.cols))];
}

/**
 * Factors a matrix as a column basis times a matrix of coordinates in that basis.
 * @param A - The input matrix.
 * @returns The factors `[C, F]` satisfying `A = C*F`.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.rank_decomposition`
 * @example
 * ```ts
 * import { Matrix, rankDecomposition } from '@symjs/symjs';
 *
 * const A = Matrix.of([[1, 2], [2, 4]]);
 * const [C, F] = rankDecomposition(A);
 * C.mul(F).equals(A); // => True
 * ```
 */
export function rankDecomposition(A: Matrix): [Matrix, Matrix] {
  const [R, pivots] = rref(A);
  const C = Matrix.fromFunction(A.rows, pivots.length, (i, j) => A.get(i, at(pivots, j)));
  const F = Matrix.fromFunction(pivots.length, A.cols, (i, j) => R.get(i, j));
  return [C, F];
}

/**
 * The inverse modulo m of an integer matrix.
 * @param A - The input matrix.
 * @param m - The integer modulus.
 * @returns The resulting matrix.
 * @throws TypeError when an entry is not an integer.
 * @throws NonInvertibleMatrixError when the determinant is not invertible modulo the modulus.
 * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.inv_mod`
 * @remarks SymPy prints this result as `Matrix([[3, 1], [4, 2]])`.
 * @example
 * ```ts
 * import { Matrix, invMod } from '@symjs/symjs';
 * invMod(Matrix.of([[1, 2], [3, 4]]), 5n); // => Matrix([
 * //   [3, 1],
 * //   [4, 2]])
 * ```
 */
export function invMod(A: Matrix, m: number | bigint): Matrix {
  const M = BigInt(m);
  const toInt = (e: Expr): bigint => {
    if (!(e instanceof Rational && e.q === 1n)) throw new TypeError('inv_mod: integer matrix expected');
    return ((e.p % M) + M) % M;
  };
  const det = toInt(A.det());
  // inverse of det modulo M by the extended Euclidean algorithm
  let [r0, r1, s0, s1] = [det, M, 1n, 0n];
  while (r1 !== 0n) {
    const q = r0 / r1;
    [r0, r1, s0, s1] = [r1, r0 - q * r1, s1, s0 - q * s1];
  }
  if (r0 !== 1n) throw new NonInvertibleMatrixError(`Matrix is not invertible (mod ${M})`);
  const dinv = ((s0 % M) + M) % M;
  return A.adjugate().map((e) => Rational.of((((toInt(e) * dinv) % M) + M) % M));
}

/**
 * Reorders the rows using a forward permutation.
 * @param A - The input matrix.
 * @param perm - The permutation to apply.
 * @returns The resulting matrix.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.permute_rows`
 */
export function permuteRows(A: Matrix, perm: readonly number[]): Matrix {
  return Matrix.fromFunction(A.rows, A.cols, (i, j) => A.get(perm[i] ?? i, j));
}
/**
 * Reorders the columns using a forward permutation.
 * @param A - The input matrix.
 * @param perm - The permutation to apply.
 * @returns The resulting matrix.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.permute_cols`
 */
export function permuteCols(A: Matrix, perm: readonly number[]): Matrix {
  return Matrix.fromFunction(A.rows, A.cols, (i, j) => A.get(i, perm[j] ?? j));
}

/**
 * Computes a similarity transformation to Jordan normal form.
 * @param A - The input matrix.
 * @returns The basis matrix and corresponding Jordan matrix.
 * @throws NonSquareMatrixError when the matrix is not square.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.jordan_form`
 * @example
 * ```ts
 * import { Matrix, jordanForm } from '@symjs/symjs';
 * jordanForm(Matrix.of([[2, 1], [0, 2]]))[1].toArray(); // => [[2, 1], [0, 2]]
 * ```
 */
export function jordanForm(A: Matrix): [Matrix, Matrix] {
  if (!A.isSquare) throw new NonSquareMatrixError('jordan_form: square matrix expected');
  // SymPy: Floats are made Rationals (nsimplify), and the result is evaluated at their precision
  const floats = A.data.flatMap((e) => (e instanceof Float ? [e] : []));
  if (floats.length) {
    const dps = Math.max(precToDps(Math.max(...floats.map((f) => f.prec))), 15);
    const [P, J] = jordanForm(A.map((e) => nsimplify(e, { rational: true })));
    return [P.evalf(dps), J.evalf(dps)];
  }
  const n = A.rows;
  const counts = new Map<string, [Expr, number]>();
  for (const v of A.eigenvals()) {
    const cur = counts.get(v.key);
    if (cur) cur[1]++;
    else counts.set(v.key, [v, 1]);
  }
  const eig = [...counts.values()].sort((a, b) => {
    if (a[0].freeSymbols().size || b[0].freeSymbols().size) return compareKeys(sortKey(a[0]), sortKey(b[0]));
    const ca = impl.toComplex(a[0]);
    const cb = impl.toComplex(b[0]);
    return ca.re - cb.re || ca.im - cb.im;
  });
  const columns: Matrix[] = [];
  const blocks: [Expr, number][] = [];
  // eigenvalues of an irreducible factor of degree >= 3 (simple roots): their eigenvectors over the number field
  const fields = rationalEigenspaces(A);
  const simp = (m: Matrix) => m.map((e) => simplify(e));
  const independent = (vs: readonly Matrix[]) => rank(vs.reduce((acc, v) => acc.hstack(v))) === vs.length;
  for (const [lam, mult] of eig) {
    // a root of an irreducible factor of degree >= 3 whose eigenspace has full dimension: no Jordan chains
    const field = fields.find(([f, basis]) => basis.length === mult && isRootOf(f, lam));
    if (field) {
      for (const vec of field[1]) {
        columns.push(Matrix.col(...vec.map((c) => expandMul(c.toExpr(lam)))));
        blocks.push([lam, 1]);
      }
      continue;
    }
    const N = simp(A.sub(Matrix.eye(n).scale(lam)));
    // null spaces of N**k until their dimension reaches the multiplicity
    const kernels: Matrix[][] = [[]];
    let Nk = Matrix.eye(n);
    for (let k = 1; k <= n && last(kernels).length < mult; k++) {
      Nk = simp(Nk.mul(N));
      kernels.push(nullspace(Nk));
    }
    // the generalized eigenspace has the dimension of the algebraic multiplicity (exact zero tests)
    defined(kernels.find((kk) => kk.length >= mult), 'generalized eigenspace');
    // chains from the top level down: v, N*v, N**2*v, ...
    const chainsOf: Matrix[][] = [];
    for (let k = kernels.length - 1; k >= 1; k--) {
      for (const v of at(kernels, k)) {
        // v must be new modulo ker(N**(k-1)) and the vectors already taken at this level
        // chains are stored from the eigenvector up: level k is entry k - 1
        const atLevel = chainsOf.filter((c) => c.length >= k).map((c) => at(c, k - 1));
        if (!independent([...at(kernels, k - 1), ...atLevel, v])) continue;
        const chain: Matrix[] = [v];
        for (let i = 1; i < k; i++) chain.push(simp(N.mul(at(chain, i - 1))));
        chainsOf.push(chain.reverse());
      }
    }
    for (const chain of chainsOf) {
      columns.push(...chain);
      blocks.push([lam, chain.length]);
    }
  }
  const P = columns.reduce((acc, c) => acc.hstack(c));
  const J = blockDiag(...blocks.map(([lam, k]) => (k === 1 ? lam : jordanBlock(k, lam))));
  return [P, J];
}

/**
 * The nonzero column indices on or below the diagonal of
 * each row and the parent array of the elimination tree (Liu's algorithm,
 * for symbolic sparse Cholesky factorization).
 * @param A - The input matrix.
 * @returns The lower nonzero column indices by row and the elimination-tree parents.
 * @see SymPy `sympy.matrices.sparse.SparseRepMatrix.liupc`
 * @example
 * ```ts
 * import { Matrix, liupc } from '@symjs/symjs';
 * liupc(Matrix.eye(2)); // => [[[0], [1]], [2, 2]]
 * ```
 */
export function liupc(A: Matrix): [number[][], number[]] {
  const n = A.rows;
  const R: number[][] = Array.from({ length: n }, (_, r) => Array.from({ length: r + 1 }, (_, c) => c).filter((c) => !isExactZero(A.get(r, c))));
  const inf = n;
  const parent = Array<number>(n).fill(inf);
  const virtual = Array<number>(n).fill(inf);
  for (let r = 0; r < n; r++) {
    for (let c of at(R, r).slice(0, -1)) {
      for (let t = at(virtual, c); t < r; t = at(virtual, c)) {
        virtual[c] = r;
        c = t;
      }
      if (virtual[c] === inf) parent[c] = virtual[c] = r;
    }
  }
  return [R, parent];
}

/**
 * Returns the nonzero structure of the rows of L.
 * @param A - The input matrix.
 * @returns The nonzero structure of the rows of L.
 * @see SymPy `sympy.matrices.sparse.SparseRepMatrix.row_structure_symbolic_cholesky`
 * @example
 * ```ts
 * import { Matrix, rowStructureSymbolicCholesky } from '@symjs/symjs';
 * rowStructureSymbolicCholesky(Matrix.eye(2)); // => [[0], [1]]
 * ```
 */
export function rowStructureSymbolicCholesky(A: Matrix): number[][] {
  const [R, parent] = liupc(A);
  const inf = R.length;
  return R.map((row, k) => {
    const out = new Set(row);
    for (let j of row) {
      while (j !== inf && j !== k) {
        out.add(j);
        j = at(parent, j);
      }
    }
    return [...out].sort((a, b) => a - b);
  });
}

/**
 * The matrix filled by the blocks in
 * order of appearance from left to right, top to bottom, ntop of them in the
 * first row.
 * @param ntop - The number of blocks in the top row.
 * @param blocks - The matrices to fit into the rectangular result.
 * @returns The resulting matrix.
 * @throws RangeError when the blocks do not tile a rectangle with the required dimensions.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.irregular`
 * @remarks SymPy prints this result as `Matrix([[1, 2, 2, 2, 3, 3], [1, 2, 2, 2, 3, 3], [4, 2, 2, 2, 5, 5], [6, 6, 7, 7, 5, 5]])`.
 * @example
 * ```ts
 * import { Matrix, irregular } from '@symjs/symjs';
 * irregular(3, Matrix.of([[1], [1]]), Matrix.of([[2, 2, 2], [2, 2, 2], [2, 2, 2]]), Matrix.of([[3, 3], [3, 3]]), Matrix.of([[4]]), Matrix.of([[5, 5], [5, 5]]), Matrix.of([[6, 6]]), Matrix.of([[7, 7]])); // => Matrix([
 * //   [1, 2, 2, 2, 3, 3],
 * //   [1, 2, 2, 2, 3, 3],
 * //   [4, 2, 2, 2, 5, 5],
 * //   [6, 6, 7, 7, 5, 5]])
 * ```
 */
export function irregular(ntop: number, ...blocks: Matrix[]): Matrix {
  const q = blocks.map((_, i) => i);
  const left = blocks.map((b) => b.rows);
  const active = q.splice(0, ntop);
  const cols = active.reduce((s, i) => s + at(blocks, i).cols, 0);
  const rows: Expr[][] = [];
  while (left.some((d) => d > 0)) {
    const r: Expr[] = [];
    active.forEach((j, a) => {
      const b = at(blocks, j);
      const remaining = at(left, j);
      const ri = b.rows - remaining;
      for (let c = 0; c < b.cols; c++) r.push(b.get(ri, c));
      left[j] = remaining - 1;
      const next = left[j] === 0 ? q.shift() : undefined;
      if (next !== undefined) active[a] = next;
    });
    if (r.length !== cols) throw new RangeError('Matrices provided do not appear to fill the space completely.');
    rows.push(r);
  }
  return Matrix.of(rows);
}

// ---------------------------------------------------------------------------
// Solving by decompositions and the inverse methods (SymPy matrices/solvers.py and inverse.py)
// ---------------------------------------------------------------------------

/**
 * The solution of a diagonal system.
 * @param M - The input matrix.
 * @param rhs - The right-hand side of the linear system.
 * @returns The resulting matrix.
 * @throws TypeError when the matrix is not diagonal or the operand sizes differ.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.diagonal_solve`
 * @remarks SymPy prints this result as `Matrix([[x/2, y/2], [y/2, x/2]])`.
 * @example
 * ```ts
 * import { Matrix, diagonalSolve, symbols } from '@symjs/symjs';
 *
 * const [x, y] = symbols('x y');
 * diagonalSolve(Matrix.of([[2, 0], [0, 2]]), Matrix.of([[x, y], [y, x]])); // => Matrix([
 * //   [x/2, y/2],
 * //   [y/2, x/2]])
 * ```
 */
export function diagonalSolve(M: Matrix, rhs: Matrix): Matrix {
  if (!M.isDiagonal()) throw new TypeError('Matrix should be diagonal');
  if (rhs.rows !== M.rows) throw new TypeError('Size mismatch');
  return Matrix.fromFunction(rhs.rows, rhs.cols, (i, j) => mul(rhs.get(i, j), pow(M.get(i, i), -1)));
}

/**
 * Solves a lower triangular system by forward substitution.
 * @param M - The input matrix.
 * @param rhs - The right-hand side of the linear system.
 * @returns The resulting matrix.
 * @throws NonSquareMatrixError when the matrix is not square.
 * @throws ShapeError when the matrix shapes differ.
 * @throws RangeError when the matrix is not lower triangular.
 * @throws TypeError when the matrix is singular.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.lower_triangular_solve`
 * @remarks SymPy prints this result as `Matrix([[4, 8], [2, 9]])`.
 * @example
 * ```ts
 * import { Matrix, lowerTriangularSolve } from '@symjs/symjs';
 * lowerTriangularSolve(Matrix.of([[1, 0], [0, 1]]), Matrix.of([[4, 8], [2, 9]])); // => Matrix([
 * //   [4, 8],
 * //   [2, 9]])
 * ```
 */
export function lowerTriangularSolve(M: Matrix, rhs: Matrix): Matrix {
  if (!M.isSquare) throw new NonSquareMatrixError('Matrix must be square.');
  if (rhs.rows !== M.rows) throw new ShapeError('Matrices size mismatch.');
  if (!M.isLower()) throw new RangeError('Matrix must be lower triangular.');
  const X: Expr[][] = Array.from({ length: M.rows }, () => Array.from({ length: rhs.cols }, (): Expr => S.Zero));
  for (let j = 0; j < rhs.cols; j++) {
    for (let i = 0; i < M.rows; i++) {
      if (isExactZero(M.get(i, i))) throw new TypeError('Matrix must be non-singular.');
      const s = add(rhs.get(i, j), ...range(0, i).map((k) => mul(-1, M.get(i, k), ent(X, k, j))));
      at(X, i)[j] = mul(s, pow(M.get(i, i), -1));
    }
  }
  return fromRows(X, rhs.cols);
}

/**
 * Solves an upper triangular system by back substitution.
 * @param M - The input matrix.
 * @param rhs - The right-hand side of the linear system.
 * @returns The resulting matrix.
 * @throws NonSquareMatrixError when the matrix is not square.
 * @throws ShapeError when the matrix shapes differ.
 * @throws TypeError when the matrix is not upper triangular.
 * @throws RangeError when the matrix is singular.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.upper_triangular_solve`
 * @remarks SymPy prints this result as `Matrix([[2, 4], [3, 8]])`.
 * @example
 * ```ts
 * import { Matrix, upperTriangularSolve } from '@symjs/symjs';
 * upperTriangularSolve(Matrix.of([[1, 0], [0, 1]]), Matrix.of([[2, 4], [3, 8]])); // => Matrix([
 * //   [2, 4],
 * //   [3, 8]])
 * ```
 */
export function upperTriangularSolve(M: Matrix, rhs: Matrix): Matrix {
  if (!M.isSquare) throw new NonSquareMatrixError('Matrix must be square.');
  if (rhs.rows !== M.rows) throw new ShapeError('Matrix size mismatch.');
  if (!M.isUpper()) throw new TypeError('Matrix is not upper triangular.');
  const n = M.rows;
  const X: Expr[][] = Array.from({ length: n }, () => Array.from({ length: rhs.cols }, (): Expr => S.Zero));
  for (let j = 0; j < rhs.cols; j++) {
    for (let i = n - 1; i >= 0; i--) {
      if (isExactZero(M.get(i, i))) throw new RangeError('Matrix must be non-singular.');
      const s = add(rhs.get(i, j), ...range(i + 1, n).map((k) => mul(-1, M.get(i, k), ent(X, k, j))));
      at(X, i)[j] = mul(s, pow(M.get(i, i), -1));
    }
  }
  return fromRows(X, rhs.cols);
}

/**
 * SymPy's reformulation of A x = b for the Cholesky and LDL solvers: a
 * matrix that is neither symmetric nor Hermitian (or not positive definite)
 * is replaced by A^H A, b by A^H b. Returns [A, b, hermitian].
 */
function normalSystem(M: Matrix, rhs: Matrix): [Matrix, Matrix, boolean] {
  if (M.rows < M.cols) throw new NotImplementedError('Under-determined System. Try M.gauss_jordan_solve(rhs)');
  let hermitian = true;
  let reform = false;
  if (M.isSymmetric()) hermitian = false;
  else if (M.isHermitian() !== true) reform = true;
  if (reform || isPositiveDefinite(M) === false) {
    const H = M.adjoint();
    const A = H.mul(M);
    return [A, H.mul(rhs), !A.isSymmetric()];
  }
  return [M, rhs, hermitian];
}

/**
 * Solves a linear system using Cholesky factors.
 * @param M - The input matrix.
 * @param rhsIn - The right-hand side of the linear system.
 * @returns The resulting matrix.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.cholesky_solve`
 * @remarks SymPy prints this result as `Matrix([[4], [-3]])`.
 * @example
 * ```ts
 * import { Matrix, choleskySolve } from '@symjs/symjs';
 * choleskySolve(Matrix.of([[1, 5], [5, 1]]), Matrix.of([[-11], [17]])); // => Matrix([
 * //   [ 4],
 * //   [-3]])
 * ```
 */
export function choleskySolve(M: Matrix, rhsIn: Matrix): Matrix {
  const [A, rhs, hermitian] = normalSystem(M, rhsIn);
  const L = cholesky(A, hermitian);
  const Y = lowerTriangularSolve(L, rhs);
  return upperTriangularSolve(hermitian ? L.adjoint() : L.transpose(), Y);
}

/** SymPy Matrix.LDLsolve(rhs): A x = b by the LDL decomposition. */
function ldlSolve(M: Matrix, rhsIn: Matrix): Matrix {
  const [A, rhs, hermitian] = normalSystem(M, rhsIn);
  const [L, D] = ldl(A, hermitian);
  const Z = diagonalSolve(D, lowerTriangularSolve(L, rhs));
  return upperTriangularSolve(hermitian ? L.adjoint() : L.transpose(), Z);
}

/** SymPy Matrix.QRsolve(b): A x = b by the QR decomposition (back substitution in R). */
function qrSolve(M: Matrix, b: Matrix): Matrix {
  const [Q, R] = qrDecomposition(M);
  const y = Q.transpose().mul(b);
  const n = R.rows;
  const x: Matrix[] = [];
  for (let j = n - 1; j >= 0; j--) {
    let tmp = y.row(j);
    for (let k = j + 1; k < n; k++) tmp = tmp.sub(at(x, n - 1 - k).scale(R.get(j, k)));
    x.push(tmp.map((e) => expandMul(e)).scale(pow(R.get(j, j), -1)));
  }
  x.reverse();
  return first(x).vstack(...x.slice(1));
}

/**
 * Solves a square matrix system by forward and back substitution using its LU factors.
 *
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.LUsolve`
 */
export function luSolve(M: Matrix, rhs: Matrix): Matrix {
  if (rhs.rows !== M.rows) throw new ShapeError('``M`` and ``rhs`` must have the same number of rows.');
  if (!M.isSquare) throw new NotImplementedError('LUsolve: only square systems are supported');
  const [L, U, perm] = luDecomposition(M);
  if (range(0, U.rows).some((i) => isExactZero(U.get(i, i)))) throw new NonInvertibleMatrixError('Matrix det == 0; not invertible.');
  let b = rhs;
  for (const [i, j] of perm) b = b.permute([[i, j]]);
  return upperTriangularSolve(U, lowerTriangularSolve(L, b));
}

/**
 * Solves a square linear system using ratios of determinants.
 * @param M - The input matrix.
 * @param rhs - The right-hand side of the linear system.
 * @returns The resulting matrix.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.cramer_solve`
 * @example
 * ```ts
 * import { Matrix, cramerSolve } from '@symjs/symjs';
 * cramerSolve(Matrix.of([[0, -6, 1], [0, -6, -1], [-5, -2, 3]]), Matrix.col(-30, -18, -26)).toArray(); // => [[0], [4], [-6]]
 * ```
 */
export function cramerSolve(M: Matrix, rhs: Matrix): Matrix {
  const d = M.det();
  return Matrix.fromFunction(rhs.rows, rhs.cols, (col, sol) => {
    const Mi = M.map((e, i, j) => (j === col ? rhs.get(i, sol) : e));
    return mul(Mi.det(), pow(d, -1));
  });
}

/** SymPy _verify_invertible: the determinant, or NonInvertibleMatrixError when it is zero. */
function verifyInvertible(M: Matrix): Expr {
  if (!M.isSquare) throw new NonSquareMatrixError('A Matrix must be square to invert.');
  const d = M.det();
  if (isZeroE(d)) throw new NonInvertibleMatrixError('Matrix det == 0; not invertible.');
  return d;
}

/**
 * Computes a square matrix inverse using the adjugate and determinant.
 * @param M - The input matrix.
 * @returns The inverse matrix.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.inverse_ADJ`
 */
export function inverseADJ(M: Matrix): Matrix {
  const d = verifyInvertible(M);
  return M.adjugate().map((e) => mul(e, pow(d, -1)));
}

/**
 * Computes a square matrix inverse using Gauss–Jordan elimination.
 * @param M - The input matrix.
 * @returns The inverse matrix.
 * @throws NonSquareMatrixError when the matrix is not square.
 * @throws NonInvertibleMatrixError when the matrix is singular.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.inverse_GE`
 */
export function inverseGE(M: Matrix): Matrix {
  if (!M.isSquare) throw new NonSquareMatrixError('A Matrix must be square to invert.');
  const n = M.rows;
  const [red] = rref(M.hstack(Matrix.eye(n)));
  if (range(0, n).some((j) => isZeroE(red.get(j, j)))) throw new NonInvertibleMatrixError('Matrix det == 0; not invertible.');
  return red.slice(range(0, n), range(n, 2 * n));
}

/**
 * Computes a square matrix inverse using LU factors.
 * @param M - The input matrix.
 * @returns The inverse matrix.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.inverse_LU`
 */
export function inverseLU(M: Matrix): Matrix {
  verifyInvertible(M);
  return luSolve(M, Matrix.eye(M.rows));
}

/**
 * Computes a square matrix inverse using a Cholesky factorization.
 * @param M - The input matrix.
 * @returns The inverse matrix.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.inverse_CH`
 */
export function inverseCH(M: Matrix): Matrix {
  verifyInvertible(M);
  return choleskySolve(M, Matrix.eye(M.rows));
}

/**
 * Computes a square matrix inverse using an LDL factorization.
 * @param M - The input matrix.
 * @returns The inverse matrix.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.inverse_LDL`
 */
export function inverseLDL(M: Matrix): Matrix {
  verifyInvertible(M);
  return ldlSolve(M, Matrix.eye(M.rows));
}

/**
 * Computes a square matrix inverse using a QR factorization.
 * @param M - The input matrix.
 * @returns The inverse matrix.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.inverse_QR`
 */
export function inverseQR(M: Matrix): Matrix {
  verifyInvertible(M);
  return qrSolve(M, Matrix.eye(M.rows));
}

/**
 * Computes a square matrix inverse using recursive block inversion with an LU fallback.
 * @param M - The input matrix.
 * @param threshold - The minimum order for recursive block inversion.
 * @returns The inverse matrix.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.inverse_BLOCK`
 */
export function inverseBLOCK(M: Matrix, threshold = 20): Matrix {
  const i = M.rows;
  if (i <= threshold || !M.isSquare) return inverseLU(M);
  const h = Math.floor(i / 2);
  const [lo, hi] = [range(0, h), range(h, i)];
  const [A, B, C, D] = [M.slice(lo, lo), M.slice(lo, hi), M.slice(hi, lo), M.slice(hi, hi)];
  // SymPy falls back to LU when the inverse of D or of the Schur complement raises NonInvertibleMatrixError
  if (isZeroE(D.det())) return inverseLU(M);
  const Dinv = inverseBLOCK(D, threshold);
  const BDi = B.mul(Dinv);
  const schur = A.sub(BDi.mul(C));
  if (isZeroE(schur.det())) return inverseLU(M);
  const An = inverseBLOCK(schur, threshold);
  const Bn = An.mul(BDi).neg();
  const dc = Dinv.mul(C);
  const Cn = dc.mul(An).neg();
  const Dn = Dinv.add(dc.mul(Bn.neg()));
  return Matrix.of([
    [An, Bn],
    [Cn, Dn],
  ]);
}

/**
 * The ratio of the largest to the smallest singular value.
 * @param M - The input matrix.
 * @returns The resulting symbolic expression.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.condition_number`
 * @example
 * ```ts
 * import { Matrix, conditionNumber, ex } from '@symjs/symjs';
 * conditionNumber(Matrix.of([[1, 0, 0], [0, 10, 0], [0, 0, ex`1/10`]])); // => 100
 * ```
 */
export function conditionNumber(M: Matrix): Expr {
  if (M.rows === 0 || M.cols === 0) return S.Zero;
  const sv = singularValues(M);
  return mul(Max(...sv), pow(Min(...sv), -1));
}

/**
 * Computes the eigenvalues and a row basis for each left eigenspace.
 * @param M - The input matrix.
 * @returns Triples of eigenvalue, algebraic multiplicity and left eigenvector basis.
 * @see SymPy `sympy.matrices.matrixbase.MatrixBase.left_eigenvects`
 * @example
 * ```ts
 * import { Matrix, leftEigenvects } from '@symjs/symjs';
 * leftEigenvects(Matrix.diag(1, 2)).map(([value, multiplicity]) => [value, multiplicity]); // => [[1, 1], [2, 1]]
 * ```
 */
export function leftEigenvects(M: Matrix): [Expr, number, Matrix[]][] {
  return eigenvects(M.transpose()).map(([v, k, vs]) => [v, k, vs.map((w) => w.transpose())]);
}

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Linear algebra on symbolic matrices (SymPy-compatible results):
 * row reduction, rank, null/column/row spaces, eigenvectors,
 * diagonalization, LU/QR/Cholesky/LDL decompositions, norms, singular
 * values, pseudo-inverse, matrix exponential and structural helpers.
 */

import { at, defined, expectType, first, last } from '../core/guard';
import { UPoly } from '../polys/poly';
import { isPositive, isReal } from '../core/assumptions';
import { MatrixError, NonInvertibleMatrixError, NonPositiveDefiniteMatrixError, NonSquareMatrixError } from '../core/errors';
import type { ExprLike } from '../core/nodes';
import { Dummy, Expr, Float, Rational, S, Special, Sym, impl } from '../core/nodes';
import { nsimplify } from '../numeric/nfloat';
import { precToDps } from '../numeric/mpf';
import { add, mul, pow, sqrt, sympify } from '../core/ops';
import { diff } from '../calculus/diff';
import { abs, conjugate, cos, log, sin } from '../functions/elementary';
import { Max, Min } from '../functions/special';
import { compareKeys, sortKey } from '../printing/sortkey';
import { expandMul } from '../simplify/expand';
import { cancel } from '../simplify/rational';
import { simplify } from '../simplify/simplify';
import { exp } from '../core/ops';
import { Matrix } from './matrix';

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
const fromRows = (r: Rows, cols: number): Matrix => (r.length === 0 ? Matrix.zeros(0, cols) : Matrix.of(r));

// ---------------------------------------------------------------------------
// row reduction
// ---------------------------------------------------------------------------

/** Reduced row echelon form and pivot columns. */
export function rref(m: Matrix): [Matrix, number[]] {
  const A = rowsOf(m);
  const pivots: number[] = [];
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
    const rowP = at(A, p);
    A[p] = at(A, r);
    const inv = pow(at(rowP, c), -1);
    const pivotRow = rowP.map((v) => tidy(mul(v, inv)));
    A[r] = pivotRow;
    for (let i = 0; i < m.rows; i++) {
      if (i === r) continue;
      const Ai = at(A, i);
      const f = at(Ai, c);
      if (isZeroE(f)) continue;
      A[i] = Ai.map((v, j) => tidy(add(v, mul(-1, f, at(pivotRow, j)))));
    }
    pivots.push(c);
    r++;
  }
  return [fromRows(A, m.cols), pivots];
}

/** Echelon form by fraction-free cross-multiplication (SymPy echelon_form). */
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

export function rank(m: Matrix): number {
  return rref(m)[1].length;
}

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

export function columnspace(m: Matrix): Matrix[] {
  return rref(m)[1].map((c) => m.col(c));
}

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

/** [(eigenvalue, algebraic multiplicity, basis of the eigenspace)] */
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

export function isDiagonalizable(m: Matrix, realsOnly = false): boolean {
  if (!m.isSquare) return false;
  for (const [v, k, vecs] of eigenvects(m)) {
    if (vecs.length !== k) return false;
    if (realsOnly && !isRealEigenvalue(v)) return false;
  }
  return true;
}

/** (P, D) with M = P D P^-1. */
export function diagonalize(m: Matrix): [Matrix, Matrix] {
  if (!isDiagonalizable(m)) throw new MatrixError('Matrix is not diagonalizable');
  const cols: Matrix[] = [];
  const vals: Expr[] = [];
  for (const [v, , vecs] of eigenvects(m)) {
    for (const vec of vecs) {
      cols.push(vec);
      vals.push(v);
    }
  }
  const P = first(cols).hstack(...cols.slice(1));
  return [P, Matrix.diag(...vals)];
}

/** Matrix exponential via diagonalization. */
export function matrixExp(m: Matrix): Matrix {
  const [P, D] = diagonalize(m);
  const E = Matrix.diag(...Array.from({ length: D.rows }, (_, i) => exp(D.get(i, i))));
  return P.mul(E).mul(P.inv()).map((e) => expandMul(e));
}

/**
 * f(A) for an analytic function f of x (SymPy Matrix.analytic_func): the
 * interpolating polynomial matching f and its derivatives at the
 * eigenvalues (with multiplicity) evaluated at A.
 */
export function analyticFunc(m: Matrix, fIn: ExprLike, x: Sym): Matrix {
  if (!m.isSquare) throw new NonSquareMatrixError('analytic_func: square matrix expected');
  const f = sympify(fIn);
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
      fv.push([subsValue(at(derivs, d), x, lam)]);
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

/** Matrix logarithm (SymPy Matrix.log) via analytic_func. */
export function matrixLog(m: Matrix): Matrix {
  const x = new Dummy('x');
  return analyticFunc(m, log(x), x);
}

// ---------------------------------------------------------------------------
// decompositions
// ---------------------------------------------------------------------------

/** Cholesky: lower L with A = L L^H (hermitian) or A = L L^T. */
export function cholesky(m: Matrix, hermitian = true): Matrix {
  if (!m.isSquare) throw new NonSquareMatrixError('Matrix must be square');
  // SymPy raises ValueError for these two
  if (hermitian && !m.isHermitian()) throw new MatrixError('Matrix must be Hermitian.');
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

/** LDL^H decomposition: (L, D). */
export function ldl(m: Matrix, hermitian = true): [Matrix, Matrix] {
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
    D.push(tidy(d));
  }
  return [Matrix.of(L), Matrix.diag(...D)];
}

/**
 * LU decomposition with row swaps: (L, U, perm) where perm lists the swaps [i, j]
 * (SymPy LUdecomposition with rankcheck=False: a column without a pivot is
 * skipped and the elimination goes on with the next column at the same row).
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
      for (let i = pr; i < n && p < 0; i++) if (!isZeroE(ent(lu, i, pc))) p = i;
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

/** QR decomposition by Gram-Schmidt: (Q, R). */
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
  return [first(qs).hstack(...qs.slice(1)), Rm];
}

// ---------------------------------------------------------------------------
// vector operations and norms
// ---------------------------------------------------------------------------

/** Dot product; with hermitian, the first argument is conjugated ('maths') or the second ('physics'). */
export function dot(a: Matrix, b: Matrix, hermitian = false, convention: 'maths' | 'physics' = 'maths'): Expr {
  if (a.data.length !== b.data.length) throw new RangeError('dot: dimension mismatch');
  let x = a.data;
  let y = b.data;
  if (hermitian && convention === 'maths') x = x.map((e) => conjugate(e));
  if (hermitian && convention === 'physics') y = y.map((e) => conjugate(e));
  return add(...x.map((e, i) => mul(e, at(y, i))));
}

export function cross(a: Matrix, b: Matrix): Matrix {
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

export function singularValues(m: Matrix): Expr[] {
  // eigenvals of the cols x cols matrix A^H A gives all cols values (or throws)
  const vals = m.adjoint().mul(m).eigenvals().map((v) => sqrt(v));
  return vals.sort((a, b) => compareKeys(sortKey(b), sortKey(a)));
}

/** SymPy Matrix.norm(ord). */
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
  if (o === undefined || o === 'fro' || o === 'f') return sqrt(add(...vals.map((v) => pow(abs(v), 2))));
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

/** Moore-Penrose pseudo-inverse (full rank matrices). */
export function pinv(m: Matrix): Matrix {
  const H = m.adjoint();
  if (m.rows >= m.cols) return H.mul(m).inv().mul(H).map(tidy);
  return H.mul(m.mul(H).inv()).map(tidy);
}

export function jacobian(X: Matrix, Y: Matrix | readonly Expr[]): Matrix {
  const ys = Y instanceof Matrix ? Y.data : Y;
  const xs = X.data;
  return Matrix.fromFunction(xs.length, ys.length, (i, j) => diff(at(xs, i), at(ys, j)));
}

// ---------------------------------------------------------------------------
// structural helpers
// ---------------------------------------------------------------------------

export const upperTriangular = (m: Matrix, k = 0): Matrix => m.map((e, i, j) => (j - i >= k ? e : 0));
export const lowerTriangular = (m: Matrix, k = 0): Matrix => m.map((e, i, j) => (j - i <= k ? e : 0));

export function diagonal(m: Matrix, k = 0): Matrix {
  const out: Expr[] = [];
  for (let i = 0; i < m.rows; i++) {
    const j = i + k;
    if (j >= 0 && j < m.cols) out.push(m.get(i, j));
  }
  return Matrix.row(...out);
}

export function extract(m: Matrix, rows: readonly (number | boolean)[], cols: readonly (number | boolean)[]): Matrix {
  const norm_ = (idx: readonly (number | boolean)[], n: number) =>
    idx.every((v) => typeof v === 'boolean')
      ? idx.flatMap((v, i) => (v ? [i] : []))
      : idx.map((v) => (typeof v === 'boolean' ? Number(v) : v < 0 ? v + n : v));
  return m.slice(norm_(rows, m.rows), norm_(cols, m.cols));
}

export function reshape(m: Matrix, r: number, c: number): Matrix {
  if (r * c !== m.data.length) throw new RangeError('reshape: invalid size');
  return Matrix.fromFunction(r, c, (i, j) => at(m.data, i * c + j));
}

export function rot90(m: Matrix, k = 1): Matrix {
  const t = ((k % 4) + 4) % 4;
  let r = m;
  for (let i = 0; i < t; i++) {
    const R = r;
    r = Matrix.fromFunction(R.cols, R.rows, (a, b) => R.get(R.rows - 1 - b, a));
  }
  return r;
}

export function vech(m: Matrix, includeDiagonal = true): Matrix {
  const out: Expr[] = [];
  for (let j = 0; j < m.cols; j++) for (let i = includeDiagonal ? j : j + 1; i < m.rows; i++) out.push(m.get(i, j));
  return Matrix.col(...out);
}

export const vec = (m: Matrix): Matrix => Matrix.col(...Array.from({ length: m.cols }, (_, j) => m.col(j).data).flat());

export const minorSubmatrix = (m: Matrix, i: number, j: number): Matrix => m.minor(i, j);
export const minorDet = (m: Matrix, i: number, j: number): Expr => m.minor(i, j).det();
export const cofactor = (m: Matrix, i: number, j: number): Expr => mul((i + j) % 2 === 0 ? 1 : -1, minorDet(m, i, j));

export function isSymmetric(m: Matrix): boolean {
  return m.isSquare && m.sub(m.transpose()).data.every(isZeroE);
}
export function isAntiSymmetric(m: Matrix): boolean {
  return m.isSquare && m.add(m.transpose()).data.every(isZeroE);
}
export function isDiagonal(m: Matrix): boolean {
  return m.data.every((e, k) => Math.floor(k / m.cols) === k % m.cols || isZeroE(e));
}
export function isUpper(m: Matrix): boolean {
  return m.data.every((e, k) => Math.floor(k / m.cols) <= k % m.cols || isZeroE(e));
}
export function isLower(m: Matrix): boolean {
  return m.data.every((e, k) => Math.floor(k / m.cols) >= k % m.cols || isZeroE(e));
}
export function isNilpotent(m: Matrix): boolean {
  if (!m.isSquare) throw new NonSquareMatrixError('Nilpotency is valid only for square matrices');
  return m.pow(m.rows).data.every(isZeroE);
}

export function multiplyElementwise(a: Matrix, b: Matrix): Matrix {
  return a.map((e, i, j) => mul(e, b.get(i, j)));
}

export function project(a: Matrix, b: Matrix): Matrix {
  return b.scale(mul(dot(a, b), pow(dot(b, b), -1)));
}

export const rowInsert = (m: Matrix, pos: number, o: Matrix): Matrix =>
  Matrix.of([...m.toArray().slice(0, pos), ...o.toArray(), ...m.toArray().slice(pos)]);
export const colInsert = (m: Matrix, pos: number, o: Matrix): Matrix => rowInsert(m.transpose(), pos, o.transpose()).transpose();

/** Block-diagonal matrix from scalars and matrices (SymPy diag). */
export function blockDiag(...blocks: (Matrix | ExprLike)[]): Matrix {
  const ms = blocks.map((b) => (b instanceof Matrix ? b : Matrix.of([[b]])));
  const rows = ms.reduce((s, m) => s + m.rows, 0);
  const cols = ms.reduce((s, m) => s + m.cols, 0);
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

export const rotAxis1 = (t: ExprLike): Matrix =>
  Matrix.of([[1, 0, 0], [0, cos(t), sin(t)], [0, mul(-1, sin(t)), cos(t)]]);
export const rotAxis2 = (t: ExprLike): Matrix =>
  Matrix.of([[cos(t), 0, mul(-1, sin(t))], [0, 1, 0], [sin(t), 0, cos(t)]]);
export const rotAxis3 = (t: ExprLike): Matrix =>
  Matrix.of([[cos(t), sin(t), 0], [mul(-1, sin(t)), cos(t), 0], [0, 0, 1]]);
export const rotCcwAxis1 = (t: ExprLike): Matrix => rotAxis1(t).transpose();
export const rotCcwAxis2 = (t: ExprLike): Matrix => rotAxis2(t).transpose();
export const rotCcwAxis3 = (t: ExprLike): Matrix => rotAxis3(t).transpose();

/** Givens rotation in the (i, j) plane of a dim x dim identity. */
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

/** SymPy Matrix.jordan_block(size, eigenvalue, band='upper'). */
export function jordanBlock(size: number, eigenvalue: ExprLike, band: 'upper' | 'lower' = 'upper'): Matrix {
  return Matrix.fromFunction(size, size, (i, j) => (i === j ? eigenvalue : band === 'upper' ? (j === i + 1 ? 1 : 0) : i === j + 1 ? 1 : 0));
}

/** Companion matrix of a monic polynomial given by its coefficients (highest first). */
export function companion(coeffs: readonly Expr[]): Matrix {
  const n = coeffs.length - 1;
  return Matrix.fromFunction(n, n, (i, j) => (j === n - 1 ? mul(-1, at(coeffs, n - i)) : i === j + 1 ? 1 : 0));
}

/** Permanent of a square matrix (Laplace expansion). */
export function permanent(mIn: Matrix): Expr {
  let m = mIn;
  let [r, c] = m.shape;
  if (r > c) {
    m = m.transpose();
    [r, c] = [c, r];
  }
  if (r === 0) return S.One;
  if (r === 1) return add(...m.row(0).data);
  const terms: Expr[] = [];
  for (let j = 0; j < c; j++) terms.push(mul(m.get(0, j), permanent(m.minor(0, j))));
  return add(...terms);
}

/** SymPy connected_components / strongly_connected_components of a graph or of a matrix's nonzero pattern (one definition, in utilities). */
export { connectedComponents, stronglyConnectedComponents } from '../utilities/iterables';

/** Least-squares solution A^+ B plus the null-space part (I - A^+ A) W (SymPy pinv_solve). */
export function pinvSolve(A: Matrix, B: Matrix, arbitrary?: Matrix): Matrix {
  const Ap = pinv(A);
  const n = A.shape[1];
  const W = arbitrary ?? Matrix.fromFunction(n, B.shape[1], (i, j) => new Dummy(`w${i}_${j}`));
  const proj = Matrix.eye(n).sub(Ap.mul(A));
  return Ap.mul(B).add(proj.mul(W)).map((e) => expandMul(e));
}

// ---- solving and constructions (SymPy Matrix.solve, GramSchmidt, hessian, wronskian, casoratian) ----

/**
 * SymPy Matrix.gauss_jordan_solve: [solution, parameters]. Free variables of
 * an underdetermined system are the parameters tau0, tau1, ...; an
 * inconsistent system throws.
 */
export function gaussJordanSolve(A: Matrix, b: Matrix): [Matrix, Matrix] {
  const n = A.cols;
  const [R, pivots] = rref(A.hstack(b));
  for (let i = 0; i < R.rows; i++) {
    const row = Array.from({ length: n }, (_, j) => R.get(i, j));
    if (row.every((c) => c instanceof Rational && c.isZero) && !isExactZero(R.get(i, n))) {
      throw new RangeError('Linear system has no solution');
    }
  }
  const pv = pivots.filter((p) => p < n);
  const free = Array.from({ length: n }, (_, j) => j).filter((j) => !pv.includes(j));
  const taus = free.map((_, k) => new Sym(`tau${k}`));
  const cols = b.cols;
  const sol = Matrix.fromFunction(n, cols, (j, c) => {
    const f = free.indexOf(j);
    if (f >= 0) return at(taus, f);
    const i = pv.indexOf(j);
    // x_j = rhs_i - sum over free columns
    return add(R.get(i, n + c), ...free.map((fj, k) => mul(-1, R.get(i, fj), at(taus, k))));
  });
  return [sol, Matrix.fromFunction(taus.length, 1, (i) => at(taus, i))];
}

/** SymPy Matrix.solve (and LUsolve, QRsolve, ...): the unique solution of A*x = b. */
export function matrixSolve(A: Matrix, b: Matrix): Matrix {
  const [sol, params] = gaussJordanSolve(A, b);
  if (params.rows) throw new NonInvertibleMatrixError('Matrix det == 0; not invertible.');
  return sol;
}

/** SymPy Matrix.solve_least_squares: the x minimizing |A*x - b| (A of full column rank). */
export function solveLeastSquares(A: Matrix, b: Matrix): Matrix {
  const At = A.transpose();
  return matrixSolve(At.mul(A), At.mul(b));
}

/** SymPy GramSchmidt(vlist, orthonormal=False). */
export function gramSchmidt(vs: readonly Matrix[], orthonormal = false): Matrix[] {
  const out: Matrix[] = [];
  for (const v of vs) {
    let u = v;
    for (const w of out) u = u.sub(w.scale(cancel(mul(dot(w, v), pow(dot(w, w), -1)))));
    u = u.map((e) => cancel(e));
    if (u.data.every((e) => e instanceof Rational && e.isZero)) throw new RangeError('GramSchmidt: the vectors are not linearly independent');
    out.push(u);
  }
  return orthonormal ? out.map((u) => normalized(u)) : out;
}

/** SymPy Matrix.normalized: v/|v|. */
export function normalized(v: Matrix): Matrix {
  const n = norm(v);
  return v.map((e) => mul(e, pow(n, -1)));
}

/** SymPy hessian(f, varlist): the matrix of second derivatives. */
export function hessian(f: ExprLike, vars: readonly Expr[]): Matrix {
  const e = sympify(f);
  return Matrix.fromFunction(vars.length, vars.length, (i, j) => diff(diff(e, at(vars, i)), at(vars, j)));
}

/** SymPy wronskian(functions, var): det of the derivatives 0..n-1 of the functions. */
export function wronskian(fs: readonly ExprLike[], x: Expr): Expr {
  const es = fs.map(sympify);
  if (!es.length) return S.One;
  return Matrix.fromFunction(es.length, es.length, (i, j) => diff(at(es, j), x, i)).det();
}

/** SymPy casoratian(seqs, n, zero=True): det of the shifted sequences (n = 0, 1, ... when zero). */
export function casoratian(seqs: readonly ExprLike[], n: Expr, zero = true): Expr {
  const es = seqs.map(sympify);
  const k = (i: number) => (zero ? Rational.of(i) : add(n, i));
  return Matrix.fromFunction(es.length, es.length, (i, j) => impl.subs(at(es, j), [[n, k(i)]])).det();
}

/** SymPy Matrix.rref_rhs(rhs): [rref of A, the right-hand side transformed alike]. */
export function rrefRhs(A: Matrix, rhs: Matrix): [Matrix, Matrix] {
  const [R] = rref(A.hstack(rhs));
  const range = (a: number, b: number) => Array.from({ length: b - a }, (_, i) => a + i);
  return [R.slice(range(0, A.rows), range(0, A.cols)), R.slice(range(0, A.rows), range(A.cols, A.cols + rhs.cols))];
}

/** SymPy Matrix.rank_decomposition: [C, F] with A = C*F, C the pivot columns of A and F the nonzero rows of rref(A). */
export function rankDecomposition(A: Matrix): [Matrix, Matrix] {
  const [R, pivots] = rref(A);
  const C = Matrix.fromFunction(A.rows, pivots.length, (i, j) => A.get(i, at(pivots, j)));
  const F = Matrix.fromFunction(pivots.length, A.cols, (i, j) => R.get(i, j));
  return [C, F];
}

/** SymPy Matrix.inv_mod(m): the inverse modulo m of an integer matrix. */
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

/** SymPy Matrix.permute_rows(perm) / permute_cols(perm) with a list of indices (direction 'forward'). */
export function permuteRows(A: Matrix, perm: readonly number[]): Matrix {
  return Matrix.fromFunction(A.rows, A.cols, (i, j) => A.get(perm[i] ?? i, j));
}
export function permuteCols(A: Matrix, perm: readonly number[]): Matrix {
  return Matrix.fromFunction(A.rows, A.cols, (i, j) => A.get(i, perm[j] ?? j));
}

/**
 * SymPy Matrix.jordan_form: [P, J] with A = P*J*P**-1, J block diagonal with
 * Jordan blocks (eigenvalues in increasing order of their real parts) and the
 * columns of P Jordan chains of generalized eigenvectors.
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
 * SymPy Matrix.liupc: the nonzero column indices on or below the diagonal of
 * each row and the parent array of the elimination tree (Liu's algorithm,
 * for symbolic sparse Cholesky factorization).
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

/** SymPy Matrix.row_structure_symbolic_cholesky: the nonzero structure of the rows of L. */
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
 * SymPy Matrix.irregular(ntop, *matrices): the matrix filled by the blocks in
 * order of appearance from left to right, top to bottom, ntop of them in the
 * first row.
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

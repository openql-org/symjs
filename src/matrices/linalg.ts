// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Linear algebra on symbolic matrices (SymPy-compatible results):
 * row reduction, rank, null/column/row spaces, eigenvectors,
 * diagonalization, LU/QR/Cholesky/LDL decompositions, norms, singular
 * values, pseudo-inverse, matrix exponential and structural helpers.
 */

import { Expr, ExprLike, Rational, S, Special, Sym } from '../core/nodes';
import { add, mul, pow, sqrt, sympify } from '../core/ops';
import { diff } from '../calculus/diff';
import { abs, conjugate, cos, sin } from '../functions/elementary';
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
  try {
    return cancel(e);
  } catch {
    return expandMul(e);
  }
};

type Rows = Expr[][];
const rowsOf = (m: Matrix): Rows => m.toArray();
const fromRows = (r: Rows, cols?: number): Matrix =>
  r.length === 0 ? Matrix.zeros(0, cols ?? 0) : Matrix.of(r);

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
      if (!isZeroE(A[i]![c]!)) {
        p = i;
        break;
      }
    }
    if (p < 0) continue;
    [A[r], A[p]] = [A[p]!, A[r]!];
    const inv = pow(A[r]![c]!, -1);
    A[r] = A[r]!.map((v) => tidy(mul(v, inv)));
    for (let i = 0; i < m.rows; i++) {
      if (i === r || isZeroE(A[i]![c]!)) continue;
      const f = A[i]![c]!;
      A[i] = A[i]!.map((v, j) => tidy(add(v, mul(-1, f, A[r]![j]!))));
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
      if (!isZeroE(A[i]![c]!)) {
        p = i;
        break;
      }
    }
    if (p < 0) continue;
    [A[r], A[p]] = [A[p]!, A[r]!];
    const piv = A[r]![c]!;
    for (let i = r + 1; i < m.rows; i++) {
      const f = A[i]![c]!;
      if (isZeroE(f)) continue;
      A[i] = A[i]!.map((v, j) => tidy(add(mul(piv, v), mul(-1, f, A[r]![j]!))));
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
  return eigenvalueMultiplicities(m).map(([v, k]) => {
    const shifted = m.sub(Matrix.eye(m.rows).scale(v));
    return [v, k, nullspace(shifted)];
  });
}

export function isDiagonalizable(m: Matrix, realsOnly = false): boolean {
  if (!m.isSquare) return false;
  for (const [v, k, vecs] of eigenvects(m)) {
    if (vecs.length !== k) return false;
    if (realsOnly && v.freeSymbols().size === 0) {
      try {
        if (Math.abs(v.toComplex().im) > 1e-12) return false;
      } catch {
        return false;
      }
    }
  }
  return true;
}

/** (P, D) with M = P D P^-1. */
export function diagonalize(m: Matrix): [Matrix, Matrix] {
  if (!isDiagonalizable(m)) throw new Error('Matrix is not diagonalizable');
  const cols: Matrix[] = [];
  const vals: Expr[] = [];
  for (const [v, , vecs] of eigenvects(m)) {
    for (const vec of vecs) {
      cols.push(vec);
      vals.push(v);
    }
  }
  const P = cols[0]!.hstack(...cols.slice(1));
  return [P, Matrix.diag(...vals)];
}

/** Matrix exponential via diagonalization. */
export function matrixExp(m: Matrix): Matrix {
  const [P, D] = diagonalize(m);
  const E = Matrix.diag(...Array.from({ length: D.rows }, (_, i) => exp(D.get(i, i))));
  return P.mul(E).mul(P.inv()).map((e) => expandMul(e));
}

// ---------------------------------------------------------------------------
// decompositions
// ---------------------------------------------------------------------------

/** Cholesky: lower L with A = L L^H (hermitian) or A = L L^T. */
export function cholesky(m: Matrix, hermitian = true): Matrix {
  if (!m.isSquare) throw new Error('Matrix must be square');
  const n = m.rows;
  const L: Expr[][] = Array.from({ length: n }, () => Array.from({ length: n }, () => S.Zero as Expr));
  const cj = (e: Expr) => (hermitian ? conjugate(e) : e);
  for (let i = 0; i < n; i++) {
    for (let j = 0; j < i; j++) {
      let s: Expr = m.get(i, j);
      for (let k = 0; k < j; k++) s = add(s, mul(-1, L[i]![k]!, cj(L[j]![k]!)));
      L[i]![j] = tidy(mul(s, pow(L[j]![j]!, -1)));
    }
    let d: Expr = m.get(i, i);
    for (let k = 0; k < i; k++) d = add(d, mul(-1, L[i]![k]!, cj(L[i]![k]!)));
    L[i]![i] = sqrt(tidy(d));
  }
  return Matrix.of(L);
}

/** LDL^H decomposition: (L, D). */
export function ldl(m: Matrix, hermitian = true): [Matrix, Matrix] {
  const n = m.rows;
  const L: Expr[][] = Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, j) => (i === j ? S.One : S.Zero) as Expr));
  const D: Expr[] = [];
  const cj = (e: Expr) => (hermitian ? conjugate(e) : e);
  for (let i = 0; i < n; i++) {
    for (let j = 0; j < i; j++) {
      let s: Expr = m.get(i, j);
      for (let k = 0; k < j; k++) s = add(s, mul(-1, L[i]![k]!, cj(L[j]![k]!), D[k]!));
      L[i]![j] = tidy(mul(s, pow(D[j]!, -1)));
    }
    let d: Expr = m.get(i, i);
    for (let k = 0; k < i; k++) d = add(d, mul(-1, L[i]![k]!, cj(L[i]![k]!), D[k]!));
    D.push(tidy(d));
  }
  return [Matrix.of(L), Matrix.diag(...D)];
}

/** LU decomposition with row swaps: (L, U, perm) where perm lists the swaps [i, j]. */
export function luDecomposition(m: Matrix): [Matrix, Matrix, [number, number][]] {
  const n = m.rows;
  const U = rowsOf(m);
  const L: Expr[][] = Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, j) => (i === j ? S.One : S.Zero) as Expr));
  const perm: [number, number][] = [];
  for (let c = 0; c < Math.min(n, m.cols); c++) {
    let p = c;
    while (p < n && isZeroE(U[p]![c]!)) p++;
    if (p === n) continue;
    if (p !== c) {
      [U[p], U[c]] = [U[c]!, U[p]!];
      for (let k = 0; k < c; k++) [L[p]![k], L[c]![k]] = [L[c]![k]!, L[p]![k]!];
      perm.push([c, p]);
    }
    for (let i = c + 1; i < n; i++) {
      const f = tidy(mul(U[i]![c]!, pow(U[c]![c]!, -1)));
      L[i]![c] = f;
      U[i] = U[i]!.map((v, j) => tidy(add(v, mul(-1, f, U[c]![j]!))));
    }
  }
  return [Matrix.of(L), fromRows(U, m.cols), perm];
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
    const nv = sqrt(tidy(dot(v, v, true)));
    if (isZeroE(nv)) continue;
    rcol.push(nv);
    qs.push(v.map((e) => tidy(mul(e, pow(nv, -1)))));
    R.push(rcol);
  }
  const k = qs.length;
  const Rm = Matrix.fromFunction(k, m.cols, (i, j) => (j < R.length && i < R[j]!.length ? R[j]![i]! : 0));
  return [qs[0]!.hstack(...qs.slice(1)), Rm];
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
  return add(...x.map((e, i) => mul(e, y[i]!)));
}

export function cross(a: Matrix, b: Matrix): Matrix {
  const [a1, a2, a3] = a.data;
  const [b1, b2, b3] = b.data;
  const v = [
    add(mul(a2!, b3!), mul(-1, a3!, b2!)),
    add(mul(a3!, b1!), mul(-1, a1!, b3!)),
    add(mul(a1!, b2!), mul(-1, a2!, b1!)),
  ];
  return a.rows === 1 ? Matrix.row(...v) : Matrix.col(...v);
}

export function singularValues(m: Matrix): Expr[] {
  const vals = m.adjoint().mul(m).eigenvals().map((v) => sqrt(v));
  while (vals.length < m.cols) vals.push(S.Zero);
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
    throw new Error(`norm: unsupported order ${String(ord)}`);
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
  throw new Error(`norm: unsupported order ${String(ord)}`);
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
  return Matrix.fromFunction(xs.length, ys.length, (i, j) => diff(xs[i]!, ys[j] as Sym));
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
      : (idx as number[]).map((v) => (v < 0 ? v + n : v));
  return m.slice(norm_(rows, m.rows), norm_(cols, m.cols));
}

export function reshape(m: Matrix, r: number, c: number): Matrix {
  if (r * c !== m.data.length) throw new RangeError('reshape: invalid size');
  return Matrix.fromFunction(r, c, (i, j) => m.data[i * c + j]!);
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
  if (!m.isSquare) return false;
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
    for (let i = 0; i < m.rows; i++) for (let j = 0; j < m.cols; j++) out[r0 + i]![c0 + j] = m.get(i, j);
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

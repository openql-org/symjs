// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/matrices/dense.py), Copyright (c)
// 2006-2023 SymPy Development Team, BSD 3-Clause License (see LICENSE).

/**
 * @file In-place arithmetic, elimination, determinant, inverse, LU and
 * characteristic polynomial of dense matrices stored as lists of rows of
 * domain elements (SymPy sympy.polys.matrices.dense: ddm_iadd,
 * ddm_irref, ddm_idet, ddm_berk, ...). The functions that SymPy calls
 * without a domain take it as an optional last argument; without one the
 * elements are combined as expressions.
 */

import { at, defined, expectType } from '../../core/guard';
import type { ExprLike } from '../../core/nodes';
import { Expr, Float, Rational, S } from '../../core/nodes';
import { add, mul, neg, pow, sympify } from '../../core/ops';
import type { Domain } from '../domains';
import { exquo, isExact } from './domainops';
import { DMDomainError, DMNonInvertibleMatrixError, DMNonSquareMatrixError, DMShapeError } from './exceptions';

/** A dense matrix: a list of rows of domain elements. */
export type DenseRows = Expr[][];

/** The arithmetic of a domain, or of expressions when no domain is given. */
interface Ops {
  add(a: Expr, b: Expr): Expr;
  sub(a: Expr, b: Expr): Expr;
  mul(a: Expr, b: Expr): Expr;
  neg(a: Expr): Expr;
  div(a: Expr, b: Expr): Expr;
  isZero(a: Expr): boolean;
}

const EXPR_OPS: Ops = {
  add: (a, b) => add(a, b),
  sub: (a, b) => add(a, neg(b)),
  mul: (a, b) => mul(a, b),
  neg: (a) => neg(a),
  div: (a, b) => mul(a, pow(b, -1)),
  isZero: (a) => (a instanceof Rational || a instanceof Float) && a.isZero,
};

/** @internal */
export function opsOf(K?: Domain): Ops {
  if (K === undefined) return EXPR_OPS;
  return {
    add: (a, b) => K.add(a, b),
    sub: (a, b) => K.sub(a, b),
    mul: (a, b) => K.mul(a, b),
    neg: (a) => K.neg(a),
    div: (a, b) => K.quo(a, b),
    isZero: (a) => K.isZero(a),
  };
}

const isExprRows = (a: unknown): a is Expr[][] => Array.isArray(a) && a.every((r) => Array.isArray(r) && r.every((x) => x instanceof Expr));
const elem = (x: ExprLike, K?: Domain): Expr => (x instanceof Expr ? x : K ? K.fromSympy(x) : sympify(x));

/** The rows with every value converted (in place) to a domain element or expression. */
function rowsOf(a: ExprLike[][], K?: Domain): Expr[][] {
  for (const row of a) row.forEach((x, j) => (row[j] = elem(x, K)));
  return expectType(a, isExprRows, 'rows of domain elements');
}

/** Copies of read-only rows with every value converted to a domain element or expression. */
const rowsCopy = (a: readonly (readonly ExprLike[])[], K?: Domain): Expr[][] => a.map((row) => row.map((x) => elem(x, K)));

/** SymPy ddm_transpose: the transposed list of rows. */
export function ddmTranspose<T>(matrix: readonly (readonly T[])[]): T[][] {
  if (!matrix.length) return [];
  return first0(matrix).map((_, j) => matrix.map((row) => at(row, j)));
}

const first0 = <T>(m: readonly (readonly T[])[]): readonly T[] => at(m, 0);

/** SymPy ddm_iadd: a += b. */
export function ddmIadd(aIn: ExprLike[][], bIn: readonly (readonly ExprLike[])[], K?: Domain): void {
  const o = opsOf(K);
  const [a, b] = [rowsOf(aIn, K), rowsCopy(bIn, K)];
  a.forEach((ai, i) => at(b, i).forEach((bij, j) => (ai[j] = o.add(at(ai, j), bij))));
}

/** SymPy ddm_isub: a -= b. */
export function ddmIsub(aIn: ExprLike[][], bIn: readonly (readonly ExprLike[])[], K?: Domain): void {
  const o = opsOf(K);
  const [a, b] = [rowsOf(aIn, K), rowsCopy(bIn, K)];
  a.forEach((ai, i) => at(b, i).forEach((bij, j) => (ai[j] = o.sub(at(ai, j), bij))));
}

/** SymPy ddm_ineg: a = -a. */
export function ddmIneg(aIn: ExprLike[][], K?: Domain): void {
  const o = opsOf(K);
  const a = rowsOf(aIn, K);
  for (const ai of a) ai.forEach((aij, j) => (ai[j] = o.neg(aij)));
}

/** SymPy ddm_imul: a = a*b. */
export function ddmImul(aIn: ExprLike[][], bIn: ExprLike, K?: Domain): void {
  const o = opsOf(K);
  const [a, b] = [rowsOf(aIn, K), elem(bIn, K)];
  for (const ai of a) ai.forEach((aij, j) => (ai[j] = o.mul(aij, b)));
}

/** SymPy ddm_irmul: a = b*a. */
export function ddmIrmul(aIn: ExprLike[][], bIn: ExprLike, K?: Domain): void {
  const o = opsOf(K);
  const [a, b] = [rowsOf(aIn, K), elem(bIn, K)];
  for (const ai of a) ai.forEach((aij, j) => (ai[j] = o.mul(b, aij)));
}

/** SymPy ddm_imatmul: a += b @ c. */
export function ddmImatmul(aIn: ExprLike[][], bIn: readonly (readonly ExprLike[])[], cIn: readonly (readonly ExprLike[])[], K?: Domain): void {
  const o = opsOf(K);
  const [a, b, c] = [rowsOf(aIn, K), rowsCopy(bIn, K), rowsCopy(cIn, K)];
  const cT = ddmTranspose(c);
  b.forEach((bi, i) => {
    const ai = at(a, i);
    cT.forEach((cTj, j) => {
      let s = at(ai, j);
      bi.forEach((bik, k) => (s = o.add(s, o.mul(bik, at(cTj, k)))));
      ai[j] = s;
    });
  });
}

function swap<T>(a: T[], i: number, j: number): void {
  [a[i], a[j]] = [at(a, j), at(a, i)];
}

const magnitude = (e: Expr): number => (e instanceof Float ? Math.abs(e.value) : 0);

/**
 * SymPy ddm_irref: reduced row echelon form in place over a field; returns
 * the pivot columns. With partial pivoting (for floats) the row with the
 * largest entry is the pivot row.
 */
export function ddmIrref(aIn: ExprLike[][], partialPivot = false, K?: Domain): number[] {
  const o = opsOf(K);
  const a = rowsOf(aIn, K);
  const m = a.length;
  if (!m) return [];
  const n = at(a, 0).length;
  let i = 0;
  const pivots: number[] = [];
  for (let j = 0; j < n; j++) {
    if (partialPivot) {
      let ip = i;
      for (let r = i + 1; r < m; r++) if (magnitude(at(at(a, r), j)) > magnitude(at(at(a, ip), j))) ip = r;
      swap(a, i, ip);
    }
    let aij = at(at(a, i), j);
    if (o.isZero(aij)) {
      let found = false;
      for (let ip = i + 1; ip < m; ip++) {
        aij = at(at(a, ip), j);
        if (!o.isZero(aij)) {
          swap(a, i, ip);
          found = true;
          break;
        }
      }
      if (!found) continue;
    }
    const ai = at(a, i);
    const aijinv = o.div(K ? K.one : S.One, aij);
    for (let l = j; l < n; l++) ai[l] = o.mul(at(ai, l), aijinv);
    a.forEach((ak, k) => {
      if (k === i || o.isZero(at(ak, j))) return;
      const akj = at(ak, j);
      ak[j] = o.sub(akj, akj);
      for (let l = j + 1; l < n; l++) ak[l] = o.sub(at(ak, l), o.mul(akj, at(ai, l)));
    });
    pivots.push(j);
    i++;
    if (i >= m) break;
  }
  return pivots;
}

/**
 * SymPy ddm_irref_den: fraction-free reduced row echelon form in place;
 * returns [denominator, pivots] with the pivot entries equal to the
 * denominator.
 */
export function ddmIrrefDen(aIn: ExprLike[][], K: Domain): [Expr, number[]] {
  const a = rowsOf(aIn, K);
  const m = a.length;
  if (!m) return [K.one, []];
  const n = at(a, 0).length;
  let d: Expr | undefined;
  const pivots: number[] = [];
  const noPivots: number[] = [];
  let i = 0;
  const ex = (x: Expr): Expr => (d === undefined ? x : exquo(K, x, d));
  for (let j = 0; j < n; j++) {
    let aij = at(at(a, i), j);
    if (K.isZero(aij)) {
      let found = false;
      for (let ip = i + 1; ip < m; ip++) {
        aij = at(at(a, ip), j);
        if (!K.isZero(aij)) {
          swap(a, i, ip);
          found = true;
          break;
        }
      }
      if (!found) {
        noPivots.push(j);
        continue;
      }
    }
    if (pivots.length) {
      const pivotVal = ex(K.mul(aij, at(at(a, 0), at(pivots, 0))));
      pivots.forEach((jp, ip) => (at(a, ip)[jp] = pivotVal));
    }
    for (const jnp of noPivots) {
      for (let ip = 0; ip < i; ip++) {
        const aijp = at(at(a, ip), jnp);
        if (!K.isZero(aijp)) at(a, ip)[jnp] = ex(K.mul(aijp, aij));
      }
    }
    const ai = at(a, i);
    a.forEach((aj, jp) => {
      if (jp === i) return;
      for (let kp = j + 1; kp < n; kp++) aj[kp] = ex(K.sub(K.mul(aij, at(aj, kp)), K.mul(at(aj, j), at(ai, kp))));
      aj[j] = K.zero;
    });
    pivots.push(j);
    i++;
    if (i >= m) break;
    d = K.isOne(aij) ? undefined : aij;
  }
  const denom = pivots.length ? at(at(a, 0), at(pivots, 0)) : K.one;
  return [denom, pivots];
}

/** SymPy ddm_idet: the determinant by fraction-free (Bareiss) elimination in place. */
export function ddmIdet(aIn: ExprLike[][], K: Domain): Expr {
  const a = rowsOf(aIn, K);
  const m = a.length;
  if (!m) return K.one;
  const n = at(a, 0).length;
  let uf = K.one;
  for (let k = 0; k < n - 1; k++) {
    if (K.isZero(at(at(a, k), k))) {
      let found = false;
      for (let i = k + 1; i < n; i++) {
        if (!K.isZero(at(at(a, i), k))) {
          swap(a, k, i);
          uf = K.neg(uf);
          found = true;
          break;
        }
      }
      if (!found) return K.zero;
    }
    const akkm1 = k ? at(at(a, k - 1), k - 1) : K.one;
    const ak = at(a, k);
    for (let i = k + 1; i < n; i++) {
      const ai = at(a, i);
      for (let j = k + 1; j < n; j++) ai[j] = exquo(K, K.sub(K.mul(at(ai, j), at(ak, k)), K.mul(at(ai, k), at(ak, j))), akkm1);
    }
  }
  return K.mul(uf, at(at(a, -1), -1));
}

/** SymPy ddm_iinv: ainv = a**-1 over a field (in place). */
export function ddmIinv(ainv: ExprLike[][], aIn: readonly (readonly ExprLike[])[], K: Domain): void {
  const a = rowsCopy(aIn, K);
  if (!K.isField) throw new DMDomainError('Not a field');
  const m = a.length;
  if (!m) return;
  const n = at(a, 0).length;
  if (m !== n) throw new DMNonSquareMatrixError();
  const aug = a.map((row, i) => [...row, ...Array.from({ length: n }, (_, j) => (i === j ? K.one : K.zero))]);
  const pivots = ddmIrref(aug, false, K);
  if (pivots.length !== n || pivots.some((p, i) => p !== i)) throw new DMNonInvertibleMatrixError('Matrix det == 0; not invertible.');
  ainv.splice(0, ainv.length, ...aug.map((row) => row.slice(n)));
}

/** SymPy ddm_ilu_split: LU decomposition of U in place, with the multipliers moved to L; returns the row swaps. */
export function ddmIluSplit(LIn: ExprLike[][], UIn: ExprLike[][], K: Domain): [number, number][] {
  const [L, U] = [rowsOf(LIn, K), rowsOf(UIn, K)];
  const m = U.length;
  if (!m) return [];
  const n = at(U, 0).length;
  const swaps = ddmIlu(U, K);
  for (let i = 1; i < m; i++) {
    const j = Math.min(i, n);
    const [Li, Ui] = [at(L, i), at(U, i)];
    for (let k = 0; k < j; k++) {
      Li[k] = at(Ui, k);
      Ui[k] = K.zero;
    }
  }
  return swaps;
}

/** SymPy ddm_ilu: LU decomposition in place (L below the diagonal); returns the row swaps. */
export function ddmIlu(aIn: ExprLike[][], K?: Domain): [number, number][] {
  const o = opsOf(K);
  const a = rowsOf(aIn, K);
  const m = a.length;
  if (!m) return [];
  const n = at(a, 0).length;
  const swaps: [number, number][] = [];
  for (let i = 0; i < Math.min(m, n); i++) {
    if (o.isZero(at(at(a, i), i))) {
      let found = false;
      for (let ip = i + 1; ip < m; ip++) {
        if (!o.isZero(at(at(a, ip), i))) {
          swaps.push([i, ip]);
          swap(a, i, ip);
          found = true;
          break;
        }
      }
      if (!found) continue;
    }
    const ai = at(a, i);
    for (let j = i + 1; j < m; j++) {
      const aj = at(a, j);
      const lji = o.div(at(aj, i), at(ai, i));
      aj[i] = lji;
      for (let k = i + 1; k < n; k++) aj[k] = o.sub(at(aj, k), o.mul(lji, at(ai, k)));
    }
  }
  return swaps;
}

/** SymPy ddm_ilu_solve: solve L*U*x = b (b with the row swaps applied) into x. */
export function ddmIluSolve(xIn: unknown[][], LIn: readonly (readonly ExprLike[])[], UIn: readonly (readonly ExprLike[])[], swaps: readonly (readonly [number, number])[], bIn: readonly (readonly ExprLike[])[], K?: Domain): void {
  const o = opsOf(K);
  const [L, U] = [rowsCopy(LIn, K), rowsCopy(UIn, K)];
  const x: Expr[][] = xIn.map((): Expr[] => []);
  const m = U.length;
  if (!m) return;
  const n = at(U, 0).length;
  const m2 = bIn.length;
  if (!m2) throw new DMShapeError('Shape mismtch');
  const nb = at(bIn, 0).length;
  if (m !== m2) throw new DMShapeError('Shape mismtch');
  if (m < n) throw new DMShapeError('Underdetermined');
  const b = rowsCopy(bIn, K);
  for (const [i1, i2] of swaps) swap(b, i1, i2);
  const y: Expr[][] = Array.from({ length: m }, () => []);
  for (let k = 0; k < nb; k++) {
    for (let i = 0; i < m; i++) {
      let rhs = at(at(b, i), k);
      for (let j = 0; j < i; j++) rhs = o.sub(rhs, o.mul(at(at(L, i), j), defined(at(y, j)[k])));
      at(y, i)[k] = rhs;
    }
  }
  for (let i = n; i < m; i++) for (let j = 0; j < nb; j++) if (!o.isZero(defined(at(y, i)[j]))) throw new DMNonInvertibleMatrixError();
  for (let k = 0; k < nb; k++) {
    for (let i = n - 1; i >= 0; i--) {
      const Uii = at(at(U, i), i);
      if (o.isZero(Uii)) throw new DMNonInvertibleMatrixError();
      let rhs = defined(at(y, i)[k]);
      for (let j = i + 1; j < n; j++) rhs = o.sub(rhs, o.mul(at(at(U, i), j), at(at(x, j), k)));
      at(x, i)[k] = o.div(rhs, Uii);
      at(xIn, i)[k] = at(at(x, i), k);
    }
  }
}

/** SymPy ddm_berk: the characteristic polynomial coefficients (as a column) by Berkowitz's algorithm. */
export function ddmBerk(MIn: readonly (readonly ExprLike[])[], K: Domain): Expr[][] {
  const M = rowsCopy(MIn, K);
  const m = M.length;
  if (!m) return [[K.one]];
  const n = at(M, 0).length;
  if (m !== n) throw new DMShapeError('Not square');
  if (n === 1) return [[K.one], [K.neg(at(at(M, 0), 0))]];
  const a = at(at(M, 0), 0);
  const R = [at(M, 0).slice(1)];
  let C: Expr[][] = M.slice(1).map((row) => [at(row, 0)]);
  const A = M.slice(1).map((row) => row.slice(1));
  const q = ddmBerk(A, K);
  const T: Expr[][] = Array.from({ length: n + 1 }, () => Array.from({ length: n }, () => K.zero));
  for (let i = 0; i < n; i++) {
    at(T, i)[i] = K.one;
    at(T, i + 1)[i] = K.neg(a);
  }
  let AnC = C;
  for (let i = 2; i <= n; i++) {
    if (i > 2) {
      C = AnC;
      AnC = C.map(() => [K.zero]);
      ddmImatmul(AnC, A, C, K);
    }
    const RAnC = [[K.zero]];
    ddmImatmul(RAnC, R, AnC, K);
    for (let j = 0; j <= n - i; j++) at(T, i + j)[j] = K.neg(at(at(RAnC, 0), 0));
  }
  const qout = Array.from({ length: n + 1 }, () => [K.zero]);
  ddmImatmul(qout, T, q, K);
  return qout;
}

/** @internal partial pivoting is used for floating-point domains (SymPy K.is_RR or K.is_CC). */
export const usePartialPivot = (K: Domain): boolean => !isExact(K) && K.symbols.length === 0;

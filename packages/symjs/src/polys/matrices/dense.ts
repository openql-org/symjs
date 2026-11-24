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

/**
 * Interchanges the rows and columns of a dense matrix.
 *
 * @param matrix - Rows of the matrix.
 * @returns The transposed rows.
 * @see SymPy `sympy.polys.matrices.dense.ddm_transpose`
 */
export function ddmTranspose<T>(matrix: readonly (readonly T[])[]): T[][] {
  if (!matrix.length) return [];
  return first0(matrix).map((_, j) => matrix.map((row) => at(row, j)));
}

const first0 = <T>(m: readonly (readonly T[])[]): readonly T[] => at(m, 0);

/**
 * Adds the second matrix to the first in place.
 *
 * @param aIn - Matrix updated in place.
 * @param bIn - Matrix to combine with the first.
 * @param K - Coefficient domain.
 * @see SymPy `sympy.polys.matrices.dense.ddm_iadd`
 */
export function ddmIadd(aIn: ExprLike[][], bIn: readonly (readonly ExprLike[])[], K?: Domain): void {
  const o = opsOf(K);
  const [a, b] = [rowsOf(aIn, K), rowsCopy(bIn, K)];
  a.forEach((ai, i) => at(b, i).forEach((bij, j) => (ai[j] = o.add(at(ai, j), bij))));
}

/**
 * Subtracts the second matrix from the first in place.
 *
 * @param aIn - Matrix updated in place.
 * @param bIn - Matrix to combine with the first.
 * @param K - Coefficient domain.
 * @see SymPy `sympy.polys.matrices.dense.ddm_isub`
 */
export function ddmIsub(aIn: ExprLike[][], bIn: readonly (readonly ExprLike[])[], K?: Domain): void {
  const o = opsOf(K);
  const [a, b] = [rowsOf(aIn, K), rowsCopy(bIn, K)];
  a.forEach((ai, i) => at(b, i).forEach((bij, j) => (ai[j] = o.sub(at(ai, j), bij))));
}

/**
 * Negates each matrix entry in place.
 *
 * @param aIn - Matrix to negate in place.
 * @param K - Coefficient domain.
 * @see SymPy `sympy.polys.matrices.dense.ddm_ineg`
 */
export function ddmIneg(aIn: ExprLike[][], K?: Domain): void {
  const o = opsOf(K);
  const a = rowsOf(aIn, K);
  for (const ai of a) ai.forEach((aij, j) => (ai[j] = o.neg(aij)));
}

/**
 * Multiplies each entry on the right by a scalar in place.
 *
 * @param aIn - Matrix to scale in place.
 * @param bIn - Scalar multiplier.
 * @param K - Coefficient domain.
 * @see SymPy `sympy.polys.matrices.dense.ddm_imul`
 */
export function ddmImul(aIn: ExprLike[][], bIn: ExprLike, K?: Domain): void {
  const o = opsOf(K);
  const [a, b] = [rowsOf(aIn, K), elem(bIn, K)];
  for (const ai of a) ai.forEach((aij, j) => (ai[j] = o.mul(aij, b)));
}

/**
 * Multiplies each entry on the left by a scalar in place.
 *
 * @param aIn - Matrix to scale in place.
 * @param bIn - Scalar multiplier.
 * @param K - Coefficient domain.
 * @see SymPy `sympy.polys.matrices.dense.ddm_irmul`
 */
export function ddmIrmul(aIn: ExprLike[][], bIn: ExprLike, K?: Domain): void {
  const o = opsOf(K);
  const [a, b] = [rowsOf(aIn, K), elem(bIn, K)];
  for (const ai of a) ai.forEach((aij, j) => (ai[j] = o.mul(b, aij)));
}

/**
 * Adds the product of two matrices to an accumulator in place.
 *
 * @param aIn - Matrix in which to accumulate the product.
 * @param bIn - Left matrix factor.
 * @param cIn - Right matrix factor.
 * @param K - Coefficient domain.
 * @see SymPy `sympy.polys.matrices.dense.ddm_imatmul`
 */
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
 * Reduces a matrix over a field to reduced row echelon form in place. Partial pivoting selects a
 * largest-magnitude pivot.
 *
 * @param aIn - Rows to reduce in place.
 * @param partialPivot - Choose the largest available pivot by absolute value.
 * @param K - Coefficient field.
 * @returns The column indices of the pivots.
 * @see SymPy `sympy.polys.matrices.dense.ddm_irref`
 * @example
 * ```ts
 * import { QQ, ddmIrref } from '@symjs/symjs';
 *
 * const rows = [[1, 2, 3], [4, 5, 6]];
 * ddmIrref(rows, false, QQ); // => [0, 1]
 * rows; // => [[1, 0, -1], [0, 1, 2]]
 * ```
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
 * Reduces a matrix in place using fraction-free elimination. The pivot entries equal the common
 * denominator.
 *
 * @remarks SymPy returns the pair `(-3, [0, 1])`.
 * @param aIn - Rows to reduce in place.
 * @param K - Coefficient domain for exact division.
 * @returns The common denominator and pivot indices.
 * @see SymPy `sympy.polys.matrices.dense.ddm_irref_den`
 * @example
 * ```ts
 * import { ZZ, ddmIrrefDen } from '@symjs/symjs';
 *
 * const rows = [[1, 2, 3], [4, 5, 6]];
 * ddmIrrefDen(rows, ZZ); // => [-3, [0, 1]]
 * rows; // => [[-3, 0, 3], [0, -3, -6]]
 * ```
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

/**
 * Computes the determinant in place with fraction-free Bareiss elimination.
 *
 * @param aIn - Square matrix used as elimination workspace.
 * @param K - Coefficient domain.
 * @returns The determinant of the original matrix.
 * @see SymPy `sympy.polys.matrices.dense.ddm_idet`
 * @example
 * ```ts
 * import { ZZ, ddmIdet } from '@symjs/symjs';
 *
 * ddmIdet([[1, 2, 3], [4, 5, 6], [7, 8, 9]], ZZ); // => 0
 * ```
 */
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

/**
 * Writes the inverse of a square matrix over a field into the supplied rows.
 *
 * @param ainv - Rows in which to store the inverse.
 * @param aIn - Square matrix to invert.
 * @param K - Coefficient field.
 * @throws DMDomainError when the coefficient domains are incompatible with the operation.
 * @throws DMNonSquareMatrixError when the matrix is not square.
 * @throws DMNonInvertibleMatrixError when the matrix is singular or the system lacks a unique
 *   solution.
 * @see SymPy `sympy.polys.matrices.dense.ddm_iinv`
 * @example
 * ```ts
 * import { QQ, ddmIinv } from '@symjs/symjs';
 *
 * const inverse = [[0, 0], [0, 0]];
 * ddmIinv(inverse, [[1, 2], [3, 4]], QQ);
 * inverse; // => [[-2, 1], [3/2, -1/2]]
 * ```
 */
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

/**
 * Reduces the upper factor in place and writes its elimination multipliers into the lower factor.
 *
 * @param LIn - Storage for the lower triangular multipliers.
 * @param UIn - Matrix to reduce to its upper factor.
 * @param K - Coefficient field.
 * @returns The row interchanges made during elimination.
 * @see SymPy `sympy.polys.matrices.dense.ddm_ilu_split`
 * @example
 * ```ts
 * import { QQ, ddmIluSplit } from '@symjs/symjs';
 *
 * const L = [[0, 0], [0, 0]];
 * const U = [[1, 2], [3, 4]];
 * ddmIluSplit(L, U, QQ); // => []
 * L; // => [[0, 0], [3, 0]]
 * ```
 */
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

/**
 * Overwrites the matrix with packed triangular factors, storing the lower multipliers below the
 * diagonal.
 *
 * @param aIn - Matrix overwritten with the packed triangular factors.
 * @param K - Coefficient field.
 * @returns The pairs of row indices interchanged.
 * @see SymPy `sympy.polys.matrices.dense.ddm_ilu`
 * @example
 * ```ts
 * import { QQ, ddmIlu, ex } from '@symjs/symjs';
 *
 * const rows = [[ex`1/2`, ex`1/3`], [ex`1/4`, ex`1/5`]];
 * ddmIlu(rows, QQ); // => []
 * rows; // => [[1/2, 1/3], [1/2, 1/30]]
 * ```
 */
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

/**
 * Solves a matrix equation using triangular factors and the row exchanges from LU decomposition.
 *
 * @param xIn - Rows in which to store the solution.
 * @param LIn - Lower triangular factor.
 * @param UIn - Upper triangular factor.
 * @param swaps - Row exchanges from the LU factorization.
 * @param bIn - Right-hand side.
 * @param K - Coefficient field.
 * @throws DMShapeError when the matrix dimensions are incompatible with the operation.
 * @throws DMNonInvertibleMatrixError when the matrix is singular or the system lacks a unique
 *   solution.
 * @see SymPy `sympy.polys.matrices.dense.ddm_ilu_solve`
 * @example
 * ```ts
 * import { QQ, ddmIlu, ddmIluSolve } from '@symjs/symjs';
 *
 * const LU = [[1, 2], [3, 4]];
 * const swaps = ddmIlu(LU, QQ);
 * const x = [[0], [0]];
 * ddmIluSolve(x, LU, LU, swaps, [[5], [6]], QQ);
 * x; // => [[-4], [9/2]]
 * ```
 */
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

/**
 * Computes the characteristic polynomial of a dense square matrix with Berkowitz’s algorithm.
 *
 * @param MIn - Square matrix whose characteristic polynomial to compute.
 * @param K - Coefficient domain.
 * @returns The characteristic coefficients as a column, highest degree first.
 * @throws DMShapeError when the matrix dimensions are incompatible with the operation.
 * @see SymPy `sympy.polys.matrices.dense.ddm_berk`
 * @example
 * ```ts
 * import { ZZ, ddmBerk } from '@symjs/symjs';
 *
 * ddmBerk([[1, 2], [3, 4]], ZZ); // => [[1], [-5], [-2]]
 * ```
 */
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

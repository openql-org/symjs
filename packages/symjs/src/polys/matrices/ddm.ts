// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/matrices/ddm.py), Copyright (c)
// 2006-2023 SymPy Development Team, BSD 3-Clause License (see LICENSE).

/**
 * @file The dense representation of a DomainMatrix: a list of rows of
 * domain elements with its shape and domain (SymPy DDM).
 */

import { at, defined } from '../../core/guard';
import type { Expr } from '../../core/nodes';
import type { Domain } from '../domains';
import type { DenseRows } from './dense';
import { ddmBerk, ddmIadd, ddmIdet, ddmIinv, ddmIluSolve, ddmIluSplit, ddmImatmul, ddmImul, ddmIneg, ddmIrmul, ddmIrref, ddmIrrefDen, ddmIsub, ddmTranspose, usePartialPivot } from './dense';
import { convertFrom, elemEq, elemRepr, elemStr, exquo } from './domainops';
import { DMBadInputError, DMDomainError, DMNonSquareMatrixError, DMShapeError } from './exceptions';
import type { SDM } from './sdm';

/** A matrix shape (rows, columns). */
export type Shape = readonly [number, number];

/** A Python slice start:stop of a row or column range (null for an open end). */
export type Slice = readonly [number | null, number | null];

/** The indices a Python slice selects from range(n). */
export function sliceIndices(s: Slice, n: number): number[] {
  const norm = (v: number | null, dflt: number): number => {
    if (v === null) return dflt;
    const w = v < 0 ? v + n : v;
    return Math.min(Math.max(w, 0), n);
  };
  const [a, b] = [norm(s[0], 0), norm(s[1], n)];
  return Array.from({ length: Math.max(b - a, 0) }, (_, k) => a + k);
}

/** A nonzero element as a Python truth value. */
const nz = (K: Domain, e: Expr): boolean => !K.isZero(e);

/** The conversions to the sparse format, set by sdm.ts (which imports this module). @internal */
export const ddmHooks: { toSdm?: (a: DDM) => SDM } = {};

/** SymPy DDM: a dense matrix over a domain, stored as a list of rows. */
export class DDM {
  /** The format name (SymPy fmt). */
  readonly fmt = 'dense';
  readonly shape: Shape;
  readonly rows: number;
  readonly cols: number;
  /** The rows of elements. */
  readonly data: DenseRows;

  constructor(
    rowslist: readonly (readonly Expr[])[],
    shape: Shape,
    readonly domain: Domain,
  ) {
    const [m, n] = shape;
    if (rowslist.length !== m || rowslist.some((row) => row.length !== n)) throw new DMBadInputError('Inconsistent row-list/shape');
    this.data = rowslist.map((row) => [...row]);
    this.shape = [m, n];
    this.rows = m;
    this.cols = n;
  }

  /** The element at (i, j) (negative indices count from the end). */
  getitem(i: number, j: number): Expr {
    return at(at(this.data, i), j);
  }
  /** Set the element at (i, j) in place. */
  setitem(i: number, j: number, value: Expr): void {
    at(this.data, i)[j < 0 ? j + this.cols : j] = value;
  }
  /** The submatrix of a row slice and a column slice. */
  extractSlice(slice1: Slice, slice2: Slice): DDM {
    const ri = sliceIndices(slice1, this.rows);
    const ci = sliceIndices(slice2, this.cols);
    return new DDM(
      ri.map((i) => ci.map((j) => this.getitem(i, j))),
      [ri.length, ci.length],
      this.domain,
    );
  }
  /** The submatrix of the given rows and columns. */
  extract(rows: readonly number[], cols: readonly number[]): DDM {
    return new DDM(
      rows.map((i) => cols.map((j) => this.getitem(i, j))),
      [rows.length, cols.length],
      this.domain,
    );
  }
  static fromList(rowslist: readonly (readonly Expr[])[], shape: Shape, domain: Domain): DDM {
    return new DDM(rowslist, shape, domain);
  }
  static fromDdm(other: DDM): DDM {
    return other.copy();
  }
  /** The list of rows (SymPy to_list). */
  toList(): Expr[][] {
    return this.data.map((row) => [...row]);
  }
  /** The elements row by row. */
  toListFlat(): Expr[] {
    return this.data.flat();
  }
  static fromListFlat(flat: readonly Expr[], shape: Shape, domain: Domain): DDM {
    const [rows, cols] = shape;
    if (flat.length !== rows * cols) throw new DMBadInputError('Inconsistent flat-list shape');
    return new DDM(
      Array.from({ length: rows }, (_, i) => flat.slice(i * cols, (i + 1) * cols)),
      shape,
      domain,
    );
  }
  /** The elements row by row (SymPy flat). */
  flat(): Expr[] {
    return this.toListFlat();
  }
  /** The nonzero elements and the data to rebuild the matrix from them (SymPy to_flat_nz). */
  toFlatNz(): [Expr[], [[number, number][], Shape]] {
    const dok = this.toDok();
    return [[...dok.values()], [[...dok.keys()], this.shape]];
  }
  static fromFlatNz(elements: readonly Expr[], data: readonly [readonly (readonly [number, number])[], Shape], domain: Domain): DDM {
    const [indices, shape] = data;
    return DDM.fromDok(new Map(indices.map((ij, k) => [ij, at(elements, k)] as const)), shape, domain);
  }
  /** The nonzero elements as row -> column -> element (SymPy to_dod). */
  toDod(): Map<number, Map<number, Expr>> {
    const dod = new Map<number, Map<number, Expr>>();
    this.data.forEach((row, i) => {
      const r = new Map<number, Expr>();
      row.forEach((e, j) => nz(this.domain, e) && r.set(j, e));
      if (r.size) dod.set(i, r);
    });
    return dod;
  }
  static fromDod(dod: ReadonlyMap<number, ReadonlyMap<number, Expr>>, shape: Shape, domain: Domain): DDM {
    const z = DDM.zeros(shape, domain);
    for (const [i, row] of dod) for (const [j, e] of row) z.setitem(i, j, e);
    return z;
  }
  /** The nonzero elements by position (SymPy to_dok). */
  toDok(): Map<[number, number], Expr> {
    const dok = new Map<[number, number], Expr>();
    this.data.forEach((row, i) => row.forEach((e, j) => nz(this.domain, e) && dok.set([i, j], e)));
    return dok;
  }
  static fromDok(dok: ReadonlyMap<readonly [number, number], Expr>, shape: Shape, domain: Domain): DDM {
    const z = DDM.zeros(shape, domain);
    for (const [[i, j], e] of dok) z.setitem(i, j, e);
    return z;
  }
  /** The nonzero elements. */
  iterValues(): Expr[] {
    return this.data.flat().filter((e) => nz(this.domain, e));
  }
  /** The nonzero elements with their positions. */
  iterItems(): [[number, number], Expr][] {
    return [...this.toDok()];
  }
  toDdm(): DDM {
    return this;
  }
  /** The sparse form (SymPy to_sdm). */
  toSdm(): SDM {
    return defined(ddmHooks.toSdm, 'sdm module')(this);
  }
  /** The dense form (SymPy to_dfm_or_ddm: python-flint matrices are not used, so a DDM). */
  toDfmOrDdm(): DDM {
    return this;
  }
  /** The matrix over another domain. */
  convertTo(K: Domain): DDM {
    const K0 = this.domain;
    if (K.equals(K0)) return this.copy();
    return new DDM(
      this.data.map((row) => row.map((e) => convertFrom(K, e, K0))),
      this.shape,
      K,
    );
  }
  /** SymPy str(): the list of rows. */
  toString(): string {
    return `[${this.data.map((row) => `[${row.map((e) => elemStr(this.domain, e)).join(', ')}]`).join(', ')}]`;
  }
  /** SymPy repr(): DDM([[...]], (m, n), K). */
  repr(): string {
    const rows = `[${this.data.map((row) => `[${row.map((e) => elemRepr(this.domain, e)).join(', ')}]`).join(', ')}]`;
    return `DDM(${rows}, (${this.rows}, ${this.cols}), ${this.domain.toString()})`;
  }
  /** Equal elements over the same domain. */
  equals(other: unknown): boolean {
    return (
      other instanceof DDM &&
      this.domain.equals(other.domain) &&
      this.rows === other.rows &&
      this.cols === other.cols &&
      this.data.every((row, i) => row.every((e, j) => elemEq(e, other.getitem(i, j))))
    );
  }
  static zeros(shape: Shape, domain: Domain): DDM {
    const [m, n] = shape;
    return new DDM(
      Array.from({ length: m }, () => Array.from({ length: n }, () => domain.zero)),
      shape,
      domain,
    );
  }
  static ones(shape: Shape, domain: Domain): DDM {
    const [m, n] = shape;
    return new DDM(
      Array.from({ length: m }, () => Array.from({ length: n }, () => domain.one)),
      shape,
      domain,
    );
  }
  /** The identity matrix of a size or shape. */
  static eye(size: number | Shape, domain: Domain): DDM {
    const [m, n] = typeof size === 'number' ? [size, size] : size;
    const z = DDM.zeros([m, n], domain);
    for (let i = 0; i < Math.min(m, n); i++) z.setitem(i, i, domain.one);
    return z;
  }
  copy(): DDM {
    return new DDM(this.data, this.shape, this.domain);
  }
  transpose(): DDM {
    const [rows, cols] = this.shape;
    const t = rows ? ddmTranspose(this.data) : Array.from({ length: cols }, (): Expr[] => []);
    return new DDM(t, [cols, rows], this.domain);
  }
  private static check(a: DDM, op: string, b: DDM, ashape: unknown, bshape: unknown): void {
    if (!a.domain.equals(b.domain)) throw new DMDomainError(`Domain mismatch: ${a.domain.toString()} ${op} ${b.domain.toString()}`);
    if (String(ashape) !== String(bshape)) throw new DMShapeError(`Shape mismatch: (${a.shape.join(', ')}) ${op} (${b.shape.join(', ')})`);
  }
  add(b: DDM): DDM {
    DDM.check(this, '+', b, this.shape, b.shape);
    const c = this.copy();
    ddmIadd(c.data, b.data, this.domain);
    return c;
  }
  sub(b: DDM): DDM {
    DDM.check(this, '-', b, this.shape, b.shape);
    const c = this.copy();
    ddmIsub(c.data, b.data, this.domain);
    return c;
  }
  neg(): DDM {
    const c = this.copy();
    ddmIneg(c.data, this.domain);
    return c;
  }
  /** Multiplication by a domain element on the right. */
  mul(b: Expr): DDM {
    const c = this.copy();
    ddmImul(c.data, b, this.domain);
    return c;
  }
  /** Multiplication by a domain element on the left. */
  rmul(b: Expr): DDM {
    const c = this.copy();
    ddmIrmul(c.data, b, this.domain);
    return c;
  }
  matmul(b: DDM): DDM {
    const [m, o] = this.shape;
    const [o2, n] = b.shape;
    DDM.check(this, '*', b, o, o2);
    const c = DDM.zeros([m, n], this.domain);
    ddmImatmul(c.data, this.data, b.data, this.domain);
    return c;
  }
  /** The elementwise (Hadamard) product. */
  mulElementwise(b: DDM): DDM {
    DDM.check(this, '*', b, this.shape, b.shape);
    const K = this.domain;
    return new DDM(
      this.data.map((ai, i) => ai.map((aij, j) => K.mul(aij, b.getitem(i, j)))),
      this.shape,
      K,
    );
  }
  /** The matrices side by side. */
  hstack(...B: DDM[]): DDM {
    const rows = this.toList();
    let cols = this.cols;
    for (const Bk of B) {
      DDM.check(this, 'hstack', Bk, this.rows, Bk.rows);
      cols += Bk.cols;
      Bk.data.forEach((Bki, i) => at(rows, i).push(...Bki));
    }
    return new DDM(rows, [this.rows, cols], this.domain);
  }
  /** The matrices one above the other. */
  vstack(...B: DDM[]): DDM {
    const rows = this.toList();
    for (const Bk of B) {
      DDM.check(this, 'vstack', Bk, this.cols, Bk.cols);
      rows.push(...Bk.toList());
    }
    return new DDM(rows, [rows.length, this.cols], this.domain);
  }
  /** The matrix of func applied to each element, over the given domain. */
  applyfunc(func: (e: Expr) => Expr, domain: Domain): DDM {
    return new DDM(
      this.data.map((row) => row.map(func)),
      this.shape,
      domain,
    );
  }
  /** The number of nonzero elements. */
  nnz(): number {
    return this.iterValues().length;
  }
  /** The strongly connected components of the graph of the nonzero elements. */
  scc(): number[][] {
    return this.toSdm().scc();
  }
  /** The diagonal matrix of the given elements. */
  static diag(values: readonly Expr[], domain: Domain): DDM {
    const n = values.length;
    const z = DDM.zeros([n, n], domain);
    values.forEach((v, i) => z.setitem(i, i, v));
    return z;
  }
  /** Reduced row echelon form over a field: [rref, pivots]. */
  rref(): [DDM, number[]] {
    const b = this.copy();
    const pivots = ddmIrref(b.data, usePartialPivot(this.domain), this.domain);
    return [b, pivots];
  }
  /** Fraction-free reduced row echelon form: [rref, denominator, pivots]. */
  rrefDen(): [DDM, Expr, number[]] {
    const b = this.copy();
    const [den, pivots] = ddmIrrefDen(b.data, this.domain);
    return [b, den, pivots];
  }
  /** A basis of the nullspace (as rows) and the nonpivot columns. */
  nullspace(): [DDM, number[]] {
    const [r, pivots] = this.rref();
    return r.nullspaceFromRref(pivots);
  }
  /** The nullspace of a matrix in (fraction-free) reduced row echelon form. */
  nullspaceFromRref(pivotsIn?: readonly number[]): [DDM, number[]] {
    const [m, n] = this.shape;
    const K = this.domain;
    let pivots = pivotsIn;
    if (pivots === undefined) {
      const found: number[] = [];
      let lastPivot = -1;
      for (let i = 0; i < m; i++) {
        for (let j = lastPivot + 1; j < n; j++) {
          if (nz(K, this.getitem(i, j))) {
            lastPivot = j;
            found.push(j);
            break;
          }
        }
      }
      pivots = found;
    }
    if (!pivots.length) return [DDM.eye(n, K), Array.from({ length: n }, (_, i) => i)];
    const pivotVal = this.getitem(0, at(pivots, 0));
    const basis: Expr[][] = [];
    const nonpivots: number[] = [];
    for (let i = 0; i < n; i++) {
      if (pivots.includes(i)) continue;
      nonpivots.push(i);
      const vec = Array.from({ length: n }, (_, j) => (i === j ? pivotVal : K.zero));
      pivots.forEach((jj, ii) => (vec[jj] = K.sub(at(vec, jj), this.getitem(ii, i))));
      basis.push(vec);
    }
    return [new DDM(basis, [basis.length, n], K), nonpivots];
  }
  /** A particular solution of the augmented system in reduced row echelon form. */
  particular(): DDM {
    return this.toSdm().particular().toDdm();
  }
  /** The determinant. */
  det(): Expr {
    if (this.rows !== this.cols) throw new DMNonSquareMatrixError('Determinant of non-square matrix');
    return ddmIdet(this.copy().data, this.domain);
  }
  /** The inverse over a field. */
  inv(): DDM {
    if (this.rows !== this.cols) throw new DMNonSquareMatrixError('Determinant of non-square matrix');
    const ainv = this.copy();
    ddmIinv(ainv.data, this.data, this.domain);
    return ainv;
  }
  /** LU decomposition over a field: [L, U, swaps]. */
  lu(): [DDM, DDM, [number, number][]] {
    const U = this.copy();
    const L = DDM.eye(this.rows, this.domain);
    const swaps = ddmIluSplit(L.data, U.data, this.domain);
    return [L, U, swaps];
  }
  /** The fraction-free LU factors in one matrix and the row permutation (SymPy _fflu). */
  private ffluCombined(): [DDM, number[]] {
    const [rows, cols] = this.shape;
    const K = this.domain;
    const LU = this.copy();
    const perm = Array.from({ length: rows }, (_, i) => i);
    let rank = 0;
    for (let j = 0; j < Math.min(rows, cols); j++) {
      let pivotRow = -1;
      for (let i = rank; i < rows; i++) {
        if (nz(K, LU.getitem(i, j))) {
          pivotRow = i;
          break;
        }
      }
      if (pivotRow === -1) continue;
      if (pivotRow !== rank) {
        [LU.data[rank], LU.data[pivotRow]] = [at(LU.data, pivotRow), at(LU.data, rank)];
        [perm[rank], perm[pivotRow]] = [at(perm, pivotRow), at(perm, rank)];
      }
      const pivot = LU.getitem(rank, j);
      for (let i = rank + 1; i < rows; i++) {
        const multiplier = LU.getitem(i, j);
        const denominator = rank > 0 ? LU.getitem(rank - 1, rank - 1) : K.one;
        for (let k = j + 1; k < cols; k++) {
          LU.setitem(i, k, exquo(K, K.sub(K.mul(pivot, LU.getitem(i, k)), K.mul(LU.getitem(rank, k), multiplier)), denominator));
        }
        LU.setitem(i, j, multiplier);
      }
      rank++;
    }
    return [LU, perm];
  }
  /** Fraction-free LU decomposition P*A = L*D**-1*U: [P, L, D, U]. */
  fflu(): [DDM, DDM, DDM, DDM] {
    const [rows, cols] = this.shape;
    const K = this.domain;
    const [U, perm] = this.ffluCombined();
    const P = DDM.zeros([rows, rows], K);
    perm.forEach((pi, i) => P.setitem(i, pi, K.one));
    const L = DDM.zeros([rows, rows], K);
    let i = 0;
    let j = 0;
    while (i < rows && j < cols) {
      if (nz(K, U.getitem(i, j))) {
        L.setitem(i, i, U.getitem(i, j));
        for (let l = i + 1; l < rows; l++) {
          L.setitem(l, i, U.getitem(l, j));
          U.setitem(l, j, K.zero);
        }
        i++;
      }
      j++;
    }
    for (; i < rows; i++) L.setitem(i, i, K.one);
    const D = DDM.zeros([rows, rows], K);
    if (rows >= 1) D.setitem(0, 0, L.getitem(0, 0));
    for (let k = 1; k < rows; k++) D.setitem(k, k, K.mul(L.getitem(k - 1, k - 1), L.getitem(k, k)));
    return [P, L, D, U];
  }
  /** QR decomposition over a field with an unnormalized Q (Gram-Schmidt): [Q, R]. */
  qr(): [DDM, DDM] {
    const [rows, cols] = this.shape;
    const K = this.domain;
    if (!K.isField) throw new DMDomainError('QR decomposition requires a field (e.g. QQ).');
    const Q = this.copy();
    const R = DDM.zeros([Math.min(rows, cols), cols], K);
    const dotCols = (i: number, j: number): Expr => {
      let s = K.zero;
      for (let k = 0; k < rows; k++) s = K.add(s, K.mul(Q.getitem(k, i), Q.getitem(k, j)));
      return s;
    };
    for (let j = 0; j < cols; j++) {
      for (let i = 0; i < Math.min(j, rows); i++) {
        const dotII = dotCols(i, i);
        if (nz(K, dotII)) {
          R.setitem(i, j, K.quo(dotCols(i, j), dotII));
          for (let k = 0; k < rows; k++) Q.setitem(k, j, K.sub(Q.getitem(k, j), K.mul(R.getitem(i, j), Q.getitem(k, i))));
        }
      }
      if (j < rows && nz(K, dotCols(j, j))) R.setitem(j, j, K.one);
    }
    return [Q.extract(Array.from({ length: rows }, (_, k) => k), Array.from({ length: Math.min(rows, cols) }, (_, k) => k)), R];
  }
  /** Solve self*x = b over a field by LU decomposition. */
  luSolve(b: DDM): DDM {
    const [m, n] = this.shape;
    const [m2, o] = b.shape;
    DDM.check(this, 'lu_solve', b, m, m2);
    if (!this.domain.isField) throw new DMDomainError('lu_solve requires a field');
    const [L, U, swaps] = this.lu();
    const x = DDM.zeros([n, o], this.domain);
    ddmIluSolve(x.data, L.data, U.data, swaps, b.data, this.domain);
    return x;
  }
  /** The characteristic polynomial coefficients (Berkowitz's algorithm). */
  charpoly(): Expr[] {
    const K = this.domain;
    const [m, n] = this.shape;
    if (m !== n) throw new DMNonSquareMatrixError('Charpoly of non-square matrix');
    const vec = ddmBerk(this.data, K);
    return Array.from({ length: n + 1 }, (_, i) => at(at(vec, i), 0));
  }
  isZeroMatrix(): boolean {
    return this.data.every((row) => row.every((e) => !nz(this.domain, e)));
  }
  isUpper(): boolean {
    return this.data.every((row, i) => row.slice(0, i).every((e) => !nz(this.domain, e)));
  }
  isLower(): boolean {
    return this.data.every((row, i) => row.slice(i + 1).every((e) => !nz(this.domain, e)));
  }
  isDiagonal(): boolean {
    return this.isUpper() && this.isLower();
  }
  /** The diagonal elements. */
  diagonal(): Expr[] {
    return Array.from({ length: Math.min(this.rows, this.cols) }, (_, i) => this.getitem(i, i));
  }
}

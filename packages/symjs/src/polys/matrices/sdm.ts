// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/matrices/sdm.py), Copyright (c)
// 2006-2023 SymPy Development Team, BSD 3-Clause License (see LICENSE).

/**
 * @file The sparse representation of a DomainMatrix: a dict of rows, each
 * a dict of the nonzero elements by column (SymPy SDM), with the sparse
 * elimination (sdm_irref, sdm_rref_den), nullspace and Berkowitz
 * characteristic polynomial (sdm_berk) functions.
 */

import { at, defined, first, getOrThrow } from '../../core/guard';
import type { ExprLike } from '../../core/nodes';
import { Expr } from '../../core/nodes';
import { stronglyConnectedComponents } from '../../utilities/iterables';
import type { Domain } from '../domains';
import type { Shape, Slice } from './ddm';
import { DDM, ddmHooks, sliceIndices } from './ddm';
import { convertFrom, elemEq, elemRepr, elemStr, exquo, inv, isExact } from './domainops';
import { DMBadInputError, DMDomainError, DMShapeError } from './exceptions';

/** A sparse row: column -> nonzero element. */
export type SdmRow = Map<number, Expr>;
/** Sparse rows: row -> nonzero row. */
export type SdmRows = Map<number, SdmRow>;

const copyRows = (A: ReadonlyMap<number, ReadonlyMap<number, Expr>>): SdmRows => new Map([...A].map(([i, r]) => [i, new Map(r)]));
const minKey = (r: ReadonlyMap<number, unknown>): number => Math.min(...r.keys());
const keySet = (r: ReadonlyMap<number, unknown>): Set<number> => new Set(r.keys());
const inter = (a: Set<number>, b: Set<number>): number[] => [...a].filter((x) => b.has(x));
const minus = (a: Set<number>, b: Set<number>): number[] => [...a].filter((x) => !b.has(x));

/** SymPy SDM: a sparse matrix over a domain. */
export class SDM {
  /** The format name (SymPy fmt). */
  readonly fmt = 'sparse';
  readonly shape: Shape;
  readonly rows: number;
  readonly cols: number;
  /** The nonzero rows. */
  readonly data: SdmRows;

  constructor(
    elemsdict: ReadonlyMap<number, ReadonlyMap<number, Expr>>,
    shape: Shape,
    readonly domain: Domain,
  ) {
    const [m, n] = shape;
    this.data = new Map([...elemsdict].map(([i, r]) => [i, new Map(r)] as const));
    this.shape = [m, n];
    this.rows = m;
    this.cols = n;
    if (![...this.data.keys()].every((r) => r >= 0 && r < m)) throw new DMBadInputError('Row out of range');
    if (![...this.data.values()].every((row) => [...row.keys()].every((c) => c >= 0 && c < n))) throw new DMBadInputError('Column out of range');
  }

  /** The element at (i, j) (negative indices count from the end). */
  getitem(i: number, j: number): Expr {
    const [m, n] = this.shape;
    if (!(-m <= i && i < m && -n <= j && j < n)) throw new RangeError('index out of range');
    return this.data.get((i + m) % m)?.get((j + n) % n) ?? this.domain.zero;
  }
  /** Set the element at (i, j) in place (a zero removes it). */
  setitem(iIn: number, jIn: number, value: Expr): void {
    const [m, n] = this.shape;
    if (!(-m <= iIn && iIn < m && -n <= jIn && jIn < n)) throw new RangeError('index out of range');
    const [i, j] = [(iIn + m) % m, (jIn + n) % n];
    if (!this.domain.isZero(value)) {
      const row = this.data.get(i);
      if (row) row.set(j, value);
      else this.data.set(i, new Map([[j, value]]));
      return;
    }
    const row = this.data.get(i);
    if (row?.delete(j) && !row.size) this.data.delete(i);
  }
  /** The submatrix of a row slice and a column slice. */
  extractSlice(slice1: Slice, slice2: Slice): SDM {
    const ri = sliceIndices(slice1, this.rows);
    const ci = sliceIndices(slice2, this.cols);
    const sdm: SdmRows = new Map();
    for (const [i, row] of this.data) {
      if (!ri.includes(i)) continue;
      const r: SdmRow = new Map();
      for (const [j, e] of row) if (ci.includes(j)) r.set(ci.indexOf(j), e);
      if (r.size) sdm.set(ri.indexOf(i), r);
    }
    return new SDM(sdm, [ri.length, ci.length], this.domain);
  }
  /** The submatrix of the given rows and columns (repeated and negative indices allowed). */
  extract(rows: readonly number[], cols: readonly number[]): SDM {
    if (!(this.data.size && rows.length && cols.length)) return SDM.zeros([rows.length, cols.length], this.domain);
    const [m, n] = this.shape;
    if (!(-m <= Math.min(...rows) && Math.max(...rows) < m)) throw new RangeError('Row index out of range');
    if (!(-n <= Math.min(...cols) && Math.max(...cols) < n)) throw new RangeError('Column index out of range');
    const rowmap = new Map<number, number[]>();
    const colmap = new Map<number, number[]>();
    rows.forEach((i1, i2) => rowmap.set((i1 + m) % m, [...(rowmap.get((i1 + m) % m) ?? []), i2]));
    cols.forEach((j1, j2) => colmap.set((j1 + n) % n, [...(colmap.get((j1 + n) % n) ?? []), j2]));
    const sdm2: SdmRows = new Map();
    for (const i1 of inter(keySet(rowmap), keySet(this.data))) {
      const row1 = getOrThrow(this.data, i1);
      const row2: SdmRow = new Map();
      for (const j1 of inter(keySet(colmap), keySet(row1))) for (const j2 of getOrThrow(colmap, j1)) row2.set(j2, getOrThrow(row1, j1));
      if (row2.size) for (const i2 of getOrThrow(rowmap, i1)) sdm2.set(i2, new Map(row2));
    }
    return new SDM(sdm2, [rows.length, cols.length], this.domain);
  }
  /** SymPy str(): the dict of rows. */
  toString(): string {
    return dodString(this.data, (e) => elemStr(this.domain, e));
  }
  /** SymPy repr(): SDM({...}, (m, n), K). */
  repr(): string {
    return `SDM(${dodString(this.data, (e) => elemRepr(this.domain, e))}, (${this.rows}, ${this.cols}), ${this.domain.toString()})`;
  }
  /** A new SDM of the same class (SymPy SDM.new). */
  static new(sdm: ReadonlyMap<number, ReadonlyMap<number, Expr>>, shape: Shape, domain: Domain): SDM {
    return new SDM(sdm, shape, domain);
  }
  copy(): SDM {
    return new SDM(copyRows(this.data), this.shape, this.domain);
  }
  /** The sparse matrix of a list of rows. */
  static fromList(ddm: readonly (readonly Expr[])[], shape: Shape, domain: Domain): SDM {
    const [m, n] = shape;
    if (!(ddm.length === m && ddm.every((row) => row.length === n))) throw new DMBadInputError('Inconsistent row-list/shape');
    const sdm: SdmRows = new Map();
    ddm.forEach((row, i) => {
      const r: SdmRow = new Map();
      row.forEach((e, j) => !domain.isZero(e) && r.set(j, e));
      if (r.size) sdm.set(i, r);
    });
    return new SDM(sdm, shape, domain);
  }
  static fromDdm(ddm: DDM): SDM {
    return SDM.fromList(ddm.data, ddm.shape, ddm.domain);
  }
  /** The list of rows (zeros filled in). */
  toList(): Expr[][] {
    const out = Array.from({ length: this.rows }, () => Array.from({ length: this.cols }, () => this.domain.zero));
    for (const [i, row] of this.data) for (const [j, e] of row) at(out, i)[j] = e;
    return out;
  }
  /** The elements row by row. */
  toListFlat(): Expr[] {
    return this.toList().flat();
  }
  static fromListFlat(elements: readonly Expr[], shape: Shape, domain: Domain): SDM {
    const [m, n] = shape;
    if (elements.length !== m * n) throw new DMBadInputError('Inconsistent flat-list shape');
    const sdm: SdmRows = new Map();
    elements.forEach((e, k) => {
      if (domain.isZero(e)) return;
      const i = Math.floor(k / n);
      const row = sdm.get(i) ?? new Map<number, Expr>();
      row.set(k % n, e);
      sdm.set(i, row);
    });
    return new SDM(sdm, shape, domain);
  }
  /** The nonzero elements and the data to rebuild the matrix from them. */
  toFlatNz(): [Expr[], [[number, number][], Shape]] {
    const dok = this.toDok();
    return [[...dok.values()], [[...dok.keys()], this.shape]];
  }
  static fromFlatNz(elements: readonly Expr[], data: readonly [readonly (readonly [number, number])[], Shape], domain: Domain): SDM {
    const [indices, shape] = data;
    return SDM.fromDok(new Map(indices.map((ij, k) => [ij, at(elements, k)] as const)), shape, domain);
  }
  /** The nonzero elements as row -> column -> element. */
  toDod(): Map<number, Map<number, Expr>> {
    return copyRows(this.data);
  }
  static fromDod(dod: ReadonlyMap<number, ReadonlyMap<number, Expr>>, shape: Shape, domain: Domain): SDM {
    const sdm: SdmRows = new Map();
    for (const [i, row] of dod) {
      for (const [j, e] of row) {
        if (domain.isZero(e)) continue;
        const r = sdm.get(i) ?? new Map<number, Expr>();
        r.set(j, e);
        sdm.set(i, r);
      }
    }
    return new SDM(sdm, shape, domain);
  }
  /** The nonzero elements by position. */
  toDok(): Map<[number, number], Expr> {
    const dok = new Map<[number, number], Expr>();
    for (const [i, row] of this.data) for (const [j, e] of row) dok.set([i, j], e);
    return dok;
  }
  static fromDok(dok: ReadonlyMap<readonly [number, number], Expr>, shape: Shape, domain: Domain): SDM {
    const sdm: SdmRows = new Map();
    for (const [[i, j], e] of dok) {
      if (domain.isZero(e)) continue;
      const r = sdm.get(i) ?? new Map<number, Expr>();
      r.set(j, e);
      sdm.set(i, r);
    }
    return new SDM(sdm, shape, domain);
  }
  /** The nonzero elements. */
  iterValues(): Expr[] {
    return [...this.data.values()].flatMap((row) => [...row.values()]);
  }
  /** The nonzero elements with their positions. */
  iterItems(): [[number, number], Expr][] {
    return [...this.toDok()];
  }
  /** The dense form. */
  toDdm(): DDM {
    return new DDM(this.toList(), this.shape, this.domain);
  }
  toSdm(): SDM {
    return this;
  }
  /** The dense form (SymPy to_dfm_or_ddm: python-flint matrices are not used, so a DDM). */
  toDfmOrDdm(): DDM {
    return this.toDdm();
  }
  static zeros(shape: Shape, domain: Domain): SDM {
    return new SDM(new Map(), shape, domain);
  }
  static ones(shape: Shape, domain: Domain): SDM {
    const [m, n] = shape;
    const row = () => new Map(Array.from({ length: n }, (_, j) => [j, domain.one] as const));
    return new SDM(new Map(Array.from({ length: m }, (_, i) => [i, row()] as const)), shape, domain);
  }
  /** The identity matrix of a size or shape. */
  static eye(shape: number | Shape, domain: Domain): SDM {
    const [rows, cols] = typeof shape === 'number' ? [shape, shape] : shape;
    const sdm: SdmRows = new Map(Array.from({ length: Math.min(rows, cols) }, (_, i) => [i, new Map([[i, domain.one]])] as const));
    return new SDM(sdm, [rows, cols], domain);
  }
  /** The diagonal matrix of the given elements (square unless a shape is given). */
  static diag(diagonal: readonly Expr[], domain: Domain, shape?: Shape): SDM {
    const sdm: SdmRows = new Map();
    diagonal.forEach((v, i) => !domain.isZero(v) && sdm.set(i, new Map([[i, v]])));
    return new SDM(sdm, shape ?? [diagonal.length, diagonal.length], domain);
  }
  transpose(): SDM {
    return new SDM(sdmTranspose(this.data), [this.cols, this.rows], this.domain);
  }
  matmul(B: SDM): SDM {
    if (!this.domain.equals(B.domain)) throw new DMDomainError();
    const [m, n] = this.shape;
    const [n2, o] = B.shape;
    if (n !== n2) throw new DMShapeError();
    return new SDM(sdmMatmul(this.data, B.data, this.domain), [m, o], this.domain);
  }
  /** Multiplication by a domain element on the right. */
  mul(b: Expr): SDM {
    return new SDM(
      unopDict(this.data, (a) => this.domain.mul(a, b), this.domain),
      this.shape,
      this.domain,
    );
  }
  /** Multiplication by a domain element on the left. */
  rmul(b: Expr): SDM {
    return new SDM(
      unopDict(this.data, (a) => this.domain.mul(b, a), this.domain),
      this.shape,
      this.domain,
    );
  }
  /** The elementwise (Hadamard) product. */
  mulElementwise(B: SDM): SDM {
    if (!this.domain.equals(B.domain)) throw new DMDomainError();
    if (String(this.shape) !== String(B.shape)) throw new DMShapeError();
    const K = this.domain;
    const zero = () => K.zero;
    return new SDM(binopDict(this.data, B.data, (a, b) => K.mul(a, b), zero, zero, K), this.shape, K);
  }
  add(B: SDM): SDM {
    const K = this.domain;
    return new SDM(
      binopDict(this.data, B.data, (a, b) => K.add(a, b), (a) => a, (b) => b, K),
      this.shape,
      K,
    );
  }
  sub(B: SDM): SDM {
    const K = this.domain;
    return new SDM(
      binopDict(this.data, B.data, (a, b) => K.sub(a, b), (a) => a, (b) => K.neg(b), K),
      this.shape,
      K,
    );
  }
  neg(): SDM {
    return new SDM(
      unopDict(this.data, (a) => this.domain.neg(a), this.domain),
      this.shape,
      this.domain,
    );
  }
  /** The matrix over another domain. */
  convertTo(K: Domain): SDM {
    const K0 = this.domain;
    if (K.equals(K0)) return this.copy();
    return new SDM(
      unopDict(this.data, (e) => convertFrom(K, e, K0), K),
      this.shape,
      K,
    );
  }
  /** The number of nonzero elements. */
  nnz(): number {
    return [...this.data.values()].reduce((s, row) => s + row.size, 0);
  }
  /** The strongly connected components of the graph of the nonzero elements. */
  scc(): number[][] {
    const V = Array.from({ length: this.rows }, (_, i) => i);
    const E: [number, number][] = V.flatMap((v) => [...(this.data.get(v)?.keys() ?? [])].map((w): [number, number] => [v, w]));
    return stronglyConnectedComponents([V, E]);
  }
  /** Reduced row echelon form over a field: [rref, pivots]. */
  rref(): [SDM, number[]] {
    const [B, pivots] = sdmIrref(this.data, this.domain);
    return [new SDM(B, this.shape, this.domain), pivots];
  }
  /** Fraction-free reduced row echelon form: [rref, denominator, pivots]. */
  rrefDen(): [SDM, Expr, number[]] {
    const [B, den, pivots] = sdmRrefDen(this.data, this.domain);
    return [new SDM(B, this.shape, this.domain), den, pivots];
  }
  /** The inverse over a field. */
  inv(): SDM {
    return SDM.fromDdm(this.toDdm().inv());
  }
  /** The determinant. */
  det(): Expr {
    return this.toDdm().det();
  }
  /** LU decomposition over a field: [L, U, swaps]. */
  lu(): [SDM, SDM, [number, number][]] {
    const [L, U, swaps] = this.toDdm().lu();
    return [SDM.fromDdm(L), SDM.fromDdm(U), swaps];
  }
  /** QR decomposition over a field: [Q, R]. */
  qr(): [SDM, SDM] {
    const [Q, R] = this.toDdm().qr();
    return [SDM.fromDdm(Q), SDM.fromDdm(R)];
  }
  /** Solve self*x = b over a field by LU decomposition. */
  luSolve(b: SDM): SDM {
    return SDM.fromDdm(this.toDdm().luSolve(b.toDdm()));
  }
  /** Fraction-free LU decomposition: [P, L, D, U]. */
  fflu(): [SDM, SDM, SDM, SDM] {
    const [P, L, D, U] = this.toDdm().fflu();
    return [SDM.fromDdm(P), SDM.fromDdm(L), SDM.fromDdm(D), SDM.fromDdm(U)];
  }
  /** A basis of the nullspace (as rows) and the nonpivot columns. */
  nullspace(): [SDM, number[]] {
    const ncols = this.cols;
    const [B, pivots, nzcols] = sdmIrref(this.data, this.domain);
    const [K, nonpivots] = sdmNullspaceFromRref(B, this.domain.one, ncols, pivots, nzcols, this.domain);
    return [new SDM(new Map(K.map((r, i) => [i, r] as const)), [K.length, ncols], this.domain), nonpivots];
  }
  /** The nullspace of a matrix in (fraction-free) reduced row echelon form. */
  nullspaceFromRref(pivotsIn?: readonly number[]): [SDM, number[]] {
    const [, n] = this.shape;
    const K = this.domain;
    const pivots = pivotsIn ?? [...this.data.values()].map((r) => minKey(r)).sort((a, b) => a - b);
    if (!pivots.length) return [SDM.eye([n, n], K), Array.from({ length: n }, (_, i) => i)];
    if (pivots.length === n) return [SDM.zeros([0, n], K), []];
    const pivotVal = this.getitem(0, at(pivots, 0));
    const nonzeroCols = new Map<number, [number, Expr][]>();
    for (const [i, Ai] of this.data) for (const [j, Aij] of Ai) nonzeroCols.set(j, [...(nonzeroCols.get(j) ?? []), [i, Aij]]);
    const basis: SdmRow[] = [];
    const nonpivots: number[] = [];
    for (let j = 0; j < n; j++) {
      if (pivots.includes(j)) continue;
      nonpivots.push(j);
      const vec: SdmRow = new Map([[j, pivotVal]]);
      for (const [ip, Aij] of nonzeroCols.get(j) ?? []) vec.set(at(pivots, ip), K.neg(Aij));
      basis.push(vec);
    }
    return [new SDM(new Map(basis.map((r, i) => [i, r] as const)), [basis.length, n], K), nonpivots];
  }
  /** A particular solution of an augmented system (the last column is the right-hand side). */
  particular(): SDM {
    const ncols = this.cols;
    const [B, pivots] = sdmIrref(this.data, this.domain);
    const P = sdmParticularFromRref(B, ncols, pivots, this.domain);
    return new SDM(P.size ? new Map([[0, P]]) : new Map(), [1, ncols - 1], this.domain);
  }
  /** The matrices side by side. */
  hstack(...B: SDM[]): SDM {
    const Anew = copyRows(this.data);
    let cols = this.cols;
    for (const Bk of B) {
      checkStack(this, Bk, this.rows, Bk.rows);
      for (const [i, Bki] of Bk.data) {
        const Ai = Anew.get(i) ?? new Map<number, Expr>();
        Anew.set(i, Ai);
        for (const [j, Bkij] of Bki) Ai.set(j + cols, Bkij);
      }
      cols += Bk.cols;
    }
    return new SDM(Anew, [this.rows, cols], this.domain);
  }
  /** The matrices one above the other. */
  vstack(...B: SDM[]): SDM {
    const Anew = copyRows(this.data);
    let rows = this.rows;
    for (const Bk of B) {
      checkStack(this, Bk, this.cols, Bk.cols);
      for (const [i, Bki] of Bk.data) Anew.set(i + rows, new Map(Bki));
      rows += Bk.rows;
    }
    return new SDM(Anew, [rows, this.cols], this.domain);
  }
  /** The matrix of func applied to each nonzero element, over the given domain. */
  applyfunc(func: (e: Expr) => Expr, domain: Domain): SDM {
    return new SDM(new Map([...this.data].map(([i, row]) => [i, new Map([...row].map(([j, e]) => [j, func(e)] as const))] as const)), this.shape, domain);
  }
  /** The characteristic polynomial coefficients (sparse Berkowitz). */
  charpoly(): Expr[] {
    const K = this.domain;
    const n = this.rows;
    const pdict = sdmBerk(this.data, n, K);
    return Array.from({ length: n + 1 }, (_, i) => pdict.get(i) ?? K.zero);
  }
  isZeroMatrix(): boolean {
    return this.data.size === 0;
  }
  isUpper(): boolean {
    return [...this.data].every(([i, row]) => [...row.keys()].every((j) => i <= j));
  }
  isLower(): boolean {
    return [...this.data].every(([i, row]) => [...row.keys()].every((j) => i >= j));
  }
  isDiagonal(): boolean {
    return [...this.data].every(([i, row]) => [...row.keys()].every((j) => i === j));
  }
  /** The diagonal elements of the nonzero rows (SymPy SDM.diagonal). */
  diagonal(): Expr[] {
    return [...this.data].filter(([i]) => i < this.cols).map(([i, row]) => row.get(i) ?? this.domain.zero);
  }
  /** Equal elements over the same domain. */
  equals(other: unknown): boolean {
    if (!(other instanceof SDM) || !this.domain.equals(other.domain) || String(this.shape) !== String(other.shape)) return false;
    return this.nnz() === other.nnz() && [...this.data].every(([i, row]) => [...row].every(([j, e]) => elemEq(e, other.getitem(i, j))));
  }
}

ddmHooks.toSdm = (a: DDM): SDM => SDM.fromDdm(a);

function checkStack(A: SDM, B: SDM, a: number, b: number): void {
  if (a !== b) throw new DMShapeError('Shape mismatch');
  if (!A.domain.equals(B.domain)) throw new DMDomainError('Domain mismatch');
}

/** Python's str of a dict of dicts. */
function dodString(A: ReadonlyMap<number, ReadonlyMap<number, Expr>>, s: (e: Expr) => string): string {
  return `{${[...A].map(([i, row]) => `${i}: {${[...row].map(([j, e]) => `${j}: ${s(e)}`).join(', ')}}`).join(', ')}}`;
}

/** SymPy binop_dict: an elementwise operation of two sparse matrices (fa and fb for elements present in one of them). */
export function binopDict(A: ReadonlyMap<number, ReadonlyMap<number, Expr>>, B: ReadonlyMap<number, ReadonlyMap<number, Expr>>, fab: (a: Expr, b: Expr) => Expr, fa: (a: Expr) => Expr, fb: (b: Expr) => Expr, K: Domain): SdmRows {
  const C: SdmRows = new Map();
  const put = (Ci: SdmRow, j: number, v: Expr) => !K.isZero(v) && Ci.set(j, v);
  const [Anz, Bnz] = [keySet(A), keySet(B)];
  for (const i of inter(Anz, Bnz)) {
    const [Ai, Bi] = [getOrThrow(A, i), getOrThrow(B, i)];
    const Ci: SdmRow = new Map();
    const [Anzi, Bnzi] = [keySet(Ai), keySet(Bi)];
    for (const j of inter(Anzi, Bnzi)) put(Ci, j, fab(getOrThrow(Ai, j), getOrThrow(Bi, j)));
    for (const j of minus(Anzi, Bnzi)) put(Ci, j, fa(getOrThrow(Ai, j)));
    for (const j of minus(Bnzi, Anzi)) put(Ci, j, fb(getOrThrow(Bi, j)));
    if (Ci.size) C.set(i, Ci);
  }
  for (const [rows, f] of [[minus(Anz, Bnz).map((i) => [i, getOrThrow(A, i)] as const), fa], [minus(Bnz, Anz).map((i) => [i, getOrThrow(B, i)] as const), fb]] as const) {
    for (const [i, Xi] of rows) {
      const Ci: SdmRow = new Map();
      for (const [j, x] of Xi) put(Ci, j, f(x));
      if (Ci.size) C.set(i, Ci);
    }
  }
  return C;
}

/** SymPy unop_dict: f applied to each element, zeros dropped. */
export function unopDict(A: ReadonlyMap<number, ReadonlyMap<number, Expr>>, f: (a: Expr) => Expr, K: Domain): SdmRows {
  const B: SdmRows = new Map();
  for (const [i, Ai] of A) {
    const Bi: SdmRow = new Map();
    for (const [j, Aij] of Ai) {
      const v = f(Aij);
      if (!K.isZero(v)) Bi.set(j, v);
    }
    if (Bi.size) B.set(i, Bi);
  }
  return B;
}

/** SymPy sdm_transpose. */
export function sdmTranspose(M: ReadonlyMap<number, ReadonlyMap<number, Expr>>): SdmRows {
  const MT: SdmRows = new Map();
  for (const [i, Mi] of M) {
    for (const [j, Mij] of Mi) {
      const r = MT.get(j);
      if (r) r.set(i, Mij);
      else MT.set(j, new Map([[i, Mij]]));
    }
  }
  return MT;
}

/** SymPy sdm_dotvec: the dot product of two sparse vectors. */
export function sdmDotvec(A: ReadonlyMap<number, Expr>, B: ReadonlyMap<number, Expr>, K: Domain): Expr {
  let s = K.zero;
  for (const j of A.keys()) {
    const b = B.get(j);
    if (b !== undefined) s = K.add(s, K.mul(getOrThrow(A, j), b));
  }
  return s;
}

/** SymPy sdm_matvecmul: a sparse matrix times a sparse vector. */
export function sdmMatvecmul(A: ReadonlyMap<number, ReadonlyMap<number, Expr>>, B: ReadonlyMap<number, Expr>, K: Domain): SdmRow {
  const C: SdmRow = new Map();
  for (const [i, Ai] of A) {
    const Ci = sdmDotvec(Ai, B, K);
    if (!K.isZero(Ci)) C.set(i, Ci);
  }
  return C;
}

/** SymPy sdm_matmul: the product of two sparse matrices. */
export function sdmMatmul(A: ReadonlyMap<number, ReadonlyMap<number, Expr>>, B: ReadonlyMap<number, ReadonlyMap<number, Expr>>, K: Domain): SdmRows {
  const C: SdmRows = new Map();
  for (const [i, Ai] of A) {
    const Ci: SdmRow = new Map();
    for (const [k, Aik] of Ai) {
      const Bk = B.get(k);
      if (!Bk) continue;
      for (const [j, Bkj] of Bk) {
        const Cij = Ci.get(j);
        const v = Cij === undefined ? K.mul(Aik, Bkj) : K.add(Cij, K.mul(Aik, Bkj));
        if (!K.isZero(v)) Ci.set(j, v);
        else Ci.delete(j);
      }
    }
    if (Ci.size) C.set(i, Ci);
  }
  return C;
}

/**
 * SymPy sdm_irref: reduced row echelon form of a sparse matrix over a
 * field; returns [rref rows, pivots, the rows (by pivot index) in which
 * each non-pivot column is nonzero].
 */
export function sdmIrref(A: ReadonlyMap<number, ReadonlyMap<number, Expr>>, K: Domain): [SdmRows, number[], Map<number, Set<number>>] {
  // the rows sorted by their leading column, processed from the last
  const Arows = [...A.values()].map((r) => new Map(r)).sort((a, b) => minKey(a) - minKey(b));
  const pivotRowMap = new Map<number, SdmRow>();
  const reducedPivots = new Set<number>();
  const nonreducedPivots = new Set<number>();
  const nonzeroColumns = new Map<number, Set<number>>();
  const nzc = (l: number): Set<number> => {
    const s = nonzeroColumns.get(l) ?? new Set<number>();
    nonzeroColumns.set(l, s);
    return s;
  };
  for (let Ai0 = Arows.pop(); Ai0 !== undefined; Ai0 = Arows.pop()) {
    const Ai: SdmRow = new Map([...Ai0].filter(([j]) => !reducedPivots.has(j)));
    for (const j of [...nonreducedPivots].filter((p) => Ai.has(p))) {
      const Aj = getOrThrow(pivotRowMap, j);
      const Aij = getOrThrow(Ai, j);
      const Ainz = keySet(Ai);
      const Ajnz = keySet(Aj);
      for (const k of minus(Ajnz, Ainz)) Ai.set(k, K.neg(K.mul(Aij, getOrThrow(Aj, k))));
      Ai.delete(j);
      Ainz.delete(j);
      for (const k of inter(Ajnz, Ainz)) {
        const Aik = K.sub(getOrThrow(Ai, k), K.mul(Aij, getOrThrow(Aj, k)));
        if (!K.isZero(Aik)) Ai.set(k, Aik);
        else Ai.delete(k);
      }
    }
    if (!Ai.size) continue;
    const j = minKey(Ai);
    const Aij = getOrThrow(Ai, j);
    pivotRowMap.set(j, Ai);
    const Ainz = keySet(Ai);
    const Aijinv = inv(K, Aij);
    for (const [l, v] of Ai) Ai.set(l, K.mul(v, Aijinv));
    const cols = nonzeroColumns.get(j) ?? new Set<number>();
    nonzeroColumns.delete(j);
    for (const k of cols) {
      const Ak = getOrThrow(pivotRowMap, k);
      const Akj = getOrThrow(Ak, j);
      const Aknz = keySet(Ak);
      for (const l of minus(Ainz, Aknz)) {
        Ak.set(l, K.neg(K.mul(Akj, getOrThrow(Ai, l))));
        nzc(l).add(k);
      }
      Ak.delete(j);
      Aknz.delete(j);
      for (const l of inter(Ainz, Aknz)) {
        const Akl = K.sub(getOrThrow(Ak, l), K.mul(Akj, getOrThrow(Ai, l)));
        if (!K.isZero(Akl)) Ak.set(l, Akl);
        else {
          Ak.delete(l);
          nzc(l).delete(k);
        }
      }
      if (Ak.size === 1) {
        reducedPivots.add(k);
        nonreducedPivots.delete(k);
      }
    }
    if (Ai.size === 1) reducedPivots.add(j);
    else {
      nonreducedPivots.add(j);
      for (const l of Ai.keys()) if (l !== j) nzc(l).add(j);
    }
  }
  const pivots = [...reducedPivots, ...nonreducedPivots].sort((a, b) => a - b);
  const pivot2row = new Map(pivots.map((p, n) => [p, n] as const));
  const nonzeroCols = new Map([...nonzeroColumns].map(([c, s]) => [c, new Set([...s].map((p) => getOrThrow(pivot2row, p)))] as const));
  const rref: SdmRows = new Map(pivots.map((p, i) => [i, getOrThrow(pivotRowMap, p)] as const));
  return [rref, pivots, nonzeroCols];
}

/**
 * SymPy sdm_rref_den: fraction-free reduced row echelon form of a sparse
 * matrix; returns [rref rows, denominator, pivots].
 */
export function sdmRrefDen(A: ReadonlyMap<number, ReadonlyMap<number, Expr>>, K: Domain): [SdmRows, Expr, number[]] {
  if (!A.size) return [new Map(), K.one, []];
  if (A.size === 1) {
    const Ai = first([...A.values()]);
    const j = minKey(Ai);
    return [new Map([[0, new Map(Ai)]]), getOrThrow(Ai, j), [j]];
  }
  const ex = (a: Expr, b: Expr): Expr => (isExact(K) ? exquo(K, a, b) : K.quo(a, b));
  const rowsInOrder = [...A].sort(([a], [b]) => a - b).map(([, r]) => r);
  const colToRowReduced = new Map<number, number>();
  const colToRowUnreduced = new Map<number, number>();
  const rrefRows: SdmRow[] = [];
  let denom: Expr | undefined;
  let divisor: Expr | undefined;
  const div = (a: Expr): Expr => (divisor === undefined ? a : ex(a, divisor));
  const ARows = [...rowsInOrder].sort((a, b) => minKey(a) - minKey(b));
  for (const Ai0 of ARows) {
    const Ai: SdmRow = new Map([...Ai0].filter(([j]) => !colToRowReduced.has(j)));
    const AiCancel: SdmRow = new Map();
    for (const j of [...colToRowUnreduced.keys()].filter((c) => Ai.has(c))) {
      const Aij = getOrThrow(Ai, j);
      Ai.delete(j);
      const Aj = at(rrefRows, getOrThrow(colToRowUnreduced, j));
      for (const [k, Ajk] of Aj) {
        const c = AiCancel.get(k);
        if (c === undefined) AiCancel.set(k, K.mul(Aij, Ajk));
        else {
          const v = K.add(c, K.mul(Aij, Ajk));
          if (!K.isZero(v)) AiCancel.set(k, v);
          else AiCancel.delete(k);
        }
      }
    }
    const AiNz = keySet(Ai);
    const AiCancelNz = keySet(AiCancel);
    const d = denom ?? K.one;
    for (const k of minus(AiCancelNz, AiNz)) Ai.set(k, K.neg(getOrThrow(AiCancel, k)));
    for (const k of minus(AiNz, AiCancelNz)) Ai.set(k, K.mul(getOrThrow(Ai, k), d));
    for (const k of inter(AiCancelNz, AiNz)) {
      const v = K.sub(K.mul(getOrThrow(Ai, k), d), getOrThrow(AiCancel, k));
      if (!K.isZero(v)) Ai.set(k, v);
      else Ai.delete(k);
    }
    if (!Ai.size) continue;
    const j = minKey(Ai);
    const Aij = getOrThrow(Ai, j);
    Ai.delete(j);
    for (const [pk, k] of [...colToRowUnreduced]) {
      const Ak = at(rrefRows, k);
      if (!Ak.has(j)) {
        for (const [l, Akl] of Ak) Ak.set(l, div(K.mul(Akl, Aij)));
        continue;
      }
      const Akj = getOrThrow(Ak, j);
      Ak.delete(j);
      const AiNz2 = keySet(Ai);
      const AkNz = keySet(Ak);
      for (const l of minus(AiNz2, AkNz)) Ak.set(l, div(K.neg(K.mul(Akj, getOrThrow(Ai, l)))));
      for (const l of minus(AkNz, AiNz2)) Ak.set(l, div(K.mul(Aij, getOrThrow(Ak, l))));
      for (const l of inter(AiNz2, AkNz)) {
        const v = K.sub(K.mul(Aij, getOrThrow(Ak, l)), K.mul(Akj, getOrThrow(Ai, l)));
        if (!K.isZero(v)) Ak.set(l, div(v));
        else Ak.delete(l);
      }
      if (!Ak.size) {
        colToRowUnreduced.delete(pk);
        colToRowReduced.set(pk, k);
      }
    }
    const i = rrefRows.length;
    rrefRows.push(Ai);
    if (Ai.size) colToRowUnreduced.set(j, i);
    else colToRowReduced.set(j, i);
    if (!K.isOne(Aij)) denom = denom === undefined ? Aij : K.mul(denom, Aij);
    if (divisor !== undefined) denom = ex(defined(denom), divisor);
    divisor = denom;
  }
  const den = denom ?? K.one;
  const rowToCol = new Map([...colToRowReduced, ...colToRowUnreduced].map(([c, r]) => [r, c] as const));
  const withCols = rrefRows.map((Ai, i) => [getOrThrow(rowToCol, i), Ai] as const).sort(([a], [b]) => a - b);
  const pivots = withCols.map(([c]) => c);
  withCols.forEach(([c, Ai]) => Ai.set(c, den));
  return [new Map(withCols.map(([, Ai], i) => [i, Ai] as const)), den, pivots];
}

/** SymPy sdm_nullspace_from_rref: the nullspace basis rows of a reduced matrix. */
export function sdmNullspaceFromRref(A: ReadonlyMap<number, ReadonlyMap<number, Expr>>, one: Expr, ncols: number, pivots: readonly number[], nonzeroCols: ReadonlyMap<number, ReadonlySet<number>>, K: Domain): [SdmRow[], number[]] {
  const nonpivots = Array.from({ length: ncols }, (_, j) => j).filter((j) => !pivots.includes(j));
  const out: SdmRow[] = [];
  for (const j of nonpivots) {
    const Kj: SdmRow = new Map([[j, one]]);
    for (const i of nonzeroCols.get(j) ?? []) Kj.set(at(pivots, i), K.neg(getOrThrow(getOrThrow(A, i), j)));
    out.push(Kj);
  }
  return [out, nonpivots];
}

/** SymPy sdm_particular_from_rref: a particular solution of a reduced augmented system. */
export function sdmParticularFromRref(A: ReadonlyMap<number, ReadonlyMap<number, Expr>>, ncols: number, pivots: readonly number[], K: Domain): SdmRow {
  const P: SdmRow = new Map();
  pivots.forEach((j, i) => {
    const Ai = getOrThrow(A, i);
    const Ain = Ai.get(ncols - 1);
    if (Ain !== undefined) P.set(j, K.quo(Ain, getOrThrow(Ai, j)));
  });
  return P;
}

/** SymPy sdm_berk: the characteristic polynomial coefficients by degree (sparse Berkowitz algorithm). */
export function sdmBerk(M: ReadonlyMap<number, ReadonlyMap<number, ExprLike>>, n: number, K: Domain): Map<number, Expr> {
  return berk(new Map([...M].map(([i, r]) => [i, new Map([...r].map(([j, e]) => [j, e instanceof Expr ? e : K.fromSympy(e)] as const))] as const)), n, K);
}

function berk(M: ReadonlyMap<number, ReadonlyMap<number, Expr>>, n: number, K: Domain): Map<number, Expr> {
  const { zero, one } = K;
  if (n === 0) return new Map([[0, one]]);
  if (n === 1) {
    const pdict = new Map([[0, one]]);
    const M00 = M.get(0)?.get(0) ?? zero;
    if (!K.isZero(M00)) pdict.set(1, K.neg(M00));
    return pdict;
  }
  let a = zero;
  const R: SdmRow = new Map();
  const C: SdmRow = new Map();
  const A: SdmRows = new Map();
  for (const [i, Mi] of M) {
    for (const [j, Mij] of Mi) {
      if (i && j) {
        const r = A.get(i - 1) ?? new Map<number, Expr>();
        r.set(j - 1, Mij);
        A.set(i - 1, r);
      } else if (i) C.set(i - 1, Mij);
      else if (j) R.set(j - 1, Mij);
      else a = Mij;
    }
  }
  let AnC = C;
  const RC = sdmDotvec(R, C, K);
  const Tvals = [one, K.neg(a), K.neg(RC)];
  for (let i = 3; i <= n; i++) {
    AnC = sdmMatvecmul(A, AnC, K);
    if (!AnC.size) break;
    Tvals.push(K.neg(sdmDotvec(R, AnC, K)));
  }
  while (Tvals.length && K.isZero(at(Tvals, -1))) Tvals.pop();
  const q = berk(A, n - 1, K);
  Tvals.reverse();
  const Tq = new Map<number, Expr>();
  const qkeys = [...q.keys()];
  const [qmin, qmax] = [Math.min(...qkeys), Math.max(...qkeys)];
  for (let i = qmin; i < Math.min(qmax + Tvals.length, n + 1); i++) {
    const Ti = new Map(Tvals.map((t, k) => [i - Tvals.length + 1 + k, t] as const));
    const Tqi = sdmDotvec(Ti, q, K);
    if (!K.isZero(Tqi)) Tq.set(i, Tqi);
  }
  return Tq;
}

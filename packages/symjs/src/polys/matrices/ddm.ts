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

/**
 * A dense matrix over a domain, stored as a list of rows.
 *
 * @see SymPy `sympy.polys.matrices.ddm.DDM`
 */
export class DDM {
  /**
   * The format name.
   *
   * @see SymPy `sympy.polys.matrices.ddm.DDM.fmt`
   */
  readonly fmt = 'dense';
  /**
   * The ordered pair of row and column counts.
   *
   * @see SymPy `sympy.polys.matrices.ddm.DDM.shape`
   */
  readonly shape: Shape;
  /**
   * The number of rows.
   *
   * @see SymPy `sympy.polys.matrices.ddm.DDM.rows`
   */
  readonly rows: number;
  /**
   * The number of columns.
   *
   * @see SymPy `sympy.polys.matrices.ddm.DDM.cols`
   */
  readonly cols: number;
  /** The rows of elements. */
  readonly data: DenseRows;

  /**
   * Stores a dense rectangular array with its shape and coefficient domain.
   *
   * @param rowslist - Matrix entries grouped by row.
   * @param shape - Row and column counts.
   * @param domain - Coefficient domain for the values.
   * @throws DMBadInputError when the entries do not match the specified matrix shape.
   */
  constructor(
    rowslist: readonly (readonly Expr[])[],
    shape: Shape,
    /**
     * The coefficient domain.
     *
     * @see SymPy `sympy.polys.matrices.ddm.DDM.domain`
     */
    readonly domain: Domain,
  ) {
    const [m, n] = shape;
    if (rowslist.length !== m || rowslist.some((row) => row.length !== n)) throw new DMBadInputError('Inconsistent row-list/shape');
    this.data = rowslist.map((row) => [...row]);
    this.shape = [m, n];
    this.rows = m;
    this.cols = n;
  }

  /**
   * The element at (i, j) (negative indices count from the end).
   *
   * @param i - Row index.
   * @param j - Column index.
   * @returns The entry at the given row and column.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.getitem`
   */
  getitem(i: number, j: number): Expr {
    return at(at(this.data, i), j);
  }
  /**
   * Set the element at (i, j) in place.
   *
   * @param i - Row index.
   * @param j - Column index.
   * @param value - Replacement entry in the coefficient domain.
   * @throws RangeError when a row or column index is out of bounds.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.setitem`
   */
  setitem(i: number, j: number, value: Expr): void {
    if (!Number.isInteger(j) || j < -this.cols || j >= this.cols) throw new RangeError('column index out of range');
    at(this.data, i)[j < 0 ? j + this.cols : j] = value;
  }
  /**
   * The submatrix of a row slice and a column slice.
   *
   * @param slice1 - Row index or slice.
   * @param slice2 - Column index or slice.
   * @returns The selected submatrix.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.extract_slice`
   */
  extractSlice(slice1: Slice, slice2: Slice): DDM {
    const ri = sliceIndices(slice1, this.rows);
    const ci = sliceIndices(slice2, this.cols);
    return new DDM(
      ri.map((i) => ci.map((j) => this.getitem(i, j))),
      [ri.length, ci.length],
      this.domain,
    );
  }
  /**
   * The submatrix of the given rows and columns.
   *
   * @param rows - Row indices in the requested order.
   * @param cols - Column indices in the requested order.
   * @returns The selected submatrix.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.extract`
   */
  extract(rows: readonly number[], cols: readonly number[]): DDM {
    return new DDM(
      rows.map((i) => cols.map((j) => this.getitem(i, j))),
      [rows.length, cols.length],
      this.domain,
    );
  }
  /**
   * Builds a matrix from entries grouped by row.
   *
   * @param rowslist - Matrix entries grouped by row.
   * @param shape - Row and column counts.
   * @param domain - Coefficient domain for the values.
   * @returns The matrix with the given rows.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.from_list`
   */
  static fromList(rowslist: readonly (readonly Expr[])[], shape: Shape, domain: Domain): DDM {
    return new DDM(rowslist, shape, domain);
  }
  /**
   * Builds a matrix from a dense domain-matrix representation.
   *
   * @param other - Source dense domain matrix.
   * @returns The matrix represented by the dense rows.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.from_ddm`
   */
  static fromDdm(other: DDM): DDM {
    return other.copy();
  }
  /**
   * Converts the matrix to a list of rows in the coefficient domain.
   *
   * @returns The entries grouped into rows.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.to_list`
   */
  toList(): Expr[][] {
    return this.data.map((row) => [...row]);
  }
  /**
   * The elements row by row.
   *
   * @returns The entries in row-major order.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.to_list_flat`
   */
  toListFlat(): Expr[] {
    return this.data.flat();
  }
  /**
   * Fills the matrix row by row from a flat sequence.
   *
   * @param flat - Entries in row-major order.
   * @param shape - Row and column counts.
   * @param domain - Coefficient domain for the values.
   * @returns The matrix filled in row-major order.
   * @throws DMBadInputError when the entries do not match the specified matrix shape.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.from_list_flat`
   */
  static fromListFlat(flat: readonly Expr[], shape: Shape, domain: Domain): DDM {
    const [rows, cols] = shape;
    if (flat.length !== rows * cols) throw new DMBadInputError('Inconsistent flat-list shape');
    return new DDM(
      Array.from({ length: rows }, (_, i) => flat.slice(i * cols, (i + 1) * cols)),
      shape,
      domain,
    );
  }
  /**
   * The elements row by row.
   *
   * @returns The entries in row-major order.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.flat`
   */
  flat(): Expr[] {
    return this.toListFlat();
  }
  /**
   * The nonzero elements and the data to rebuild the matrix from them.
   *
   * @returns The nonzero entries with their positions and matrix shape.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.to_flat_nz`
   */
  toFlatNz(): [Expr[], [[number, number][], Shape]] {
    const dok = this.toDok();
    return [[...dok.values()], [[...dok.keys()], this.shape]];
  }
  /**
   * Restores nonzero entries to their original positions.
   *
   * @param elements - Entries in their given order.
   * @param data - Positions and shape returned by `toFlatNz`.
   * @param domain - Coefficient domain for the values.
   * @returns The matrix reconstructed from its nonzero entries and their positions.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.from_flat_nz`
   */
  static fromFlatNz(elements: readonly Expr[], data: readonly [readonly (readonly [number, number])[], Shape], domain: Domain): DDM {
    const [indices, shape] = data;
    return DDM.fromDok(new Map(indices.map((ij, k) => [ij, at(elements, k)] as const)), shape, domain);
  }
  /**
   * The nonzero elements as row -> column -> element.
   *
   * @returns The nonzero entries indexed first by row, then by column.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.to_dod`
   */
  toDod(): Map<number, Map<number, Expr>> {
    const dod = new Map<number, Map<number, Expr>>();
    this.data.forEach((row, i) => {
      const r = new Map<number, Expr>();
      row.forEach((e, j) => nz(this.domain, e) && r.set(j, e));
      if (r.size) dod.set(i, r);
    });
    return dod;
  }
  /**
   * Builds a matrix from nested row and column maps.
   *
   * @param dod - Nonzero entries keyed by row and then by column.
   * @param shape - Row and column counts.
   * @param domain - Coefficient domain for the values.
   * @returns The matrix with the specified sparse rows.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.from_dod`
   */
  static fromDod(dod: ReadonlyMap<number, ReadonlyMap<number, Expr>>, shape: Shape, domain: Domain): DDM {
    const z = DDM.zeros(shape, domain);
    for (const [i, row] of dod) for (const [j, e] of row) z.setitem(i, j, e);
    return z;
  }
  /**
   * The nonzero elements by position.
   *
   * @returns The nonzero entries indexed by coordinate pair.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.to_dok`
   */
  toDok(): Map<[number, number], Expr> {
    const dok = new Map<[number, number], Expr>();
    this.data.forEach((row, i) => row.forEach((e, j) => nz(this.domain, e) && dok.set([i, j], e)));
    return dok;
  }
  /**
   * Builds a matrix from a map of index pairs to entries.
   *
   * @param dok - Nonzero entries keyed by coordinate pair.
   * @param shape - Row and column counts.
   * @param domain - Coefficient domain for the values.
   * @returns The matrix with the specified nonzero entries.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.from_dok`
   */
  static fromDok(dok: ReadonlyMap<readonly [number, number], Expr>, shape: Shape, domain: Domain): DDM {
    const z = DDM.zeros(shape, domain);
    for (const [[i, j], e] of dok) z.setitem(i, j, e);
    return z;
  }
  /**
   * Collects the stored nonzero values of the matrix.
   *
   * @returns The nonzero entries.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.iter_values`
   */
  iterValues(): Expr[] {
    return this.data.flat().filter((e) => nz(this.domain, e));
  }
  /**
   * The nonzero elements with their positions.
   *
   * @returns The index pairs and values of the nonzero entries.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.iter_items`
   */
  iterItems(): [[number, number], Expr][] {
    return [...this.toDok()];
  }
  /**
   * Exposes the entries as a dense domain matrix.
   *
   * @returns The dense domain-matrix representation.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.to_ddm`
   */
  toDdm(): DDM {
    return this;
  }
  /**
   * Exposes the entries as a sparse domain matrix.
   *
   * @returns The sparse domain-matrix representation.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.to_sdm`
   */
  toSdm(): SDM {
    return defined(ddmHooks.toSdm, 'sdm module')(this);
  }
  /**
   * Returns the dense matrix representation over the coefficient domain.
   *
   * @returns The dense domain-matrix representation.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.to_dfm_or_ddm`
   */
  toDfmOrDdm(): DDM {
    return this;
  }
  /**
   * The matrix over another domain.
   *
   * @param K - Coefficient domain for the values.
   * @returns The value over the target domain.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.convert_to`
   */
  convertTo(K: Domain): DDM {
    const K0 = this.domain;
    if (K.equals(K0)) return this.copy();
    return new DDM(
      this.data.map((row) => row.map((e) => convertFrom(K, e, K0))),
      this.shape,
      K,
    );
  }
  /**
   * Displays the matrix as a list of rows.
   *
   * @returns The printable representation.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.__str__`
   */
  toString(): string {
    return `[${this.data.map((row) => `[${row.map((e) => elemStr(this.domain, e)).join(', ')}]`).join(', ')}]`;
  }
  /**
   * Includes the dense rows, matrix dimensions and domain in the representation.
   *
   * @returns The constructor-style representation.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.__repr__`
   */
  repr(): string {
    const rows = `[${this.data.map((row) => `[${row.map((e) => elemRepr(this.domain, e)).join(', ')}]`).join(', ')}]`;
    return `DDM(${rows}, (${this.rows}, ${this.cols}), ${this.domain.toString()})`;
  }
  /**
   * Equal elements over the same domain.
   *
   * @param other - Value to compare against.
   * @returns Whether the operands are equal.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.__eq__`
   */
  equals(other: unknown): boolean {
    return (
      other instanceof DDM &&
      this.domain.equals(other.domain) &&
      this.rows === other.rows &&
      this.cols === other.cols &&
      this.data.every((row, i) => row.every((e, j) => elemEq(e, other.getitem(i, j))))
    );
  }
  /**
   * Constructs a rectangular matrix in which every entry is the additive identity.
   *
   * @param shape - Row and column counts.
   * @param domain - Coefficient domain for the values.
   * @returns A zero matrix of the specified shape.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.zeros`
   */
  static zeros(shape: Shape, domain: Domain): DDM {
    const [m, n] = shape;
    return new DDM(
      Array.from({ length: m }, () => Array.from({ length: n }, () => domain.zero)),
      shape,
      domain,
    );
  }
  /**
   * Constructs a rectangular matrix in which every entry is the multiplicative identity.
   *
   * @param shape - Row and column counts.
   * @param domain - Coefficient domain for the values.
   * @returns A matrix filled with ones.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.ones`
   */
  static ones(shape: Shape, domain: Domain): DDM {
    const [m, n] = shape;
    return new DDM(
      Array.from({ length: m }, () => Array.from({ length: n }, () => domain.one)),
      shape,
      domain,
    );
  }
  /**
   * The identity matrix of a size or shape.
   *
   * @param size - Matrix dimension.
   * @param domain - Coefficient domain for the values.
   * @returns An identity matrix of the given shape.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.eye`
   */
  static eye(size: number | Shape, domain: Domain): DDM {
    const [m, n] = typeof size === 'number' ? [size, size] : size;
    const z = DDM.zeros([m, n], domain);
    for (let i = 0; i < Math.min(m, n); i++) z.setitem(i, i, domain.one);
    return z;
  }
  /**
   * Copies the matrix so its entries can be updated independently.
   *
   * @returns An independent copy of the matrix.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.copy`
   */
  copy(): DDM {
    return new DDM(this.data, this.shape, this.domain);
  }
  /**
   * Interchanges the rows and columns.
   *
   * @returns The matrix with its rows and columns interchanged.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.transpose`
   */
  transpose(): DDM {
    const [rows, cols] = this.shape;
    const t = rows ? ddmTranspose(this.data) : Array.from({ length: cols }, (): Expr[] => []);
    return new DDM(t, [cols, rows], this.domain);
  }
  private static check(a: DDM, op: string, b: DDM, ashape: unknown, bshape: unknown): void {
    if (!a.domain.equals(b.domain)) throw new DMDomainError(`Domain mismatch: ${a.domain.toString()} ${op} ${b.domain.toString()}`);
    if (String(ashape) !== String(bshape)) throw new DMShapeError(`Shape mismatch: (${a.shape.join(', ')}) ${op} (${b.shape.join(', ')})`);
  }
  /**
   * Adds the other operand to this value.
   *
   * @param b - Addend.
   * @returns The sum of the operands.
   * @throws DMDomainError when the coefficient domains are incompatible with the operation.
   * @throws DMShapeError when the matrix dimensions are incompatible with the operation.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.add`
   */
  add(b: DDM): DDM {
    DDM.check(this, '+', b, this.shape, b.shape);
    const c = this.copy();
    ddmIadd(c.data, b.data, this.domain);
    return c;
  }
  /**
   * Subtracts the other operand from this value.
   *
   * @param b - Value to subtract.
   * @returns The difference in operand order.
   * @throws DMDomainError when the coefficient domains are incompatible with the operation.
   * @throws DMShapeError when the matrix dimensions are incompatible with the operation.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.sub`
   */
  sub(b: DDM): DDM {
    DDM.check(this, '-', b, this.shape, b.shape);
    const c = this.copy();
    ddmIsub(c.data, b.data, this.domain);
    return c;
  }
  /**
   * Reverses the sign of the value.
   *
   * @returns The additive inverse.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.neg`
   */
  neg(): DDM {
    const c = this.copy();
    ddmIneg(c.data, this.domain);
    return c;
  }
  /**
   * Multiplication by a domain element on the right.
   *
   * @param b - Factor on the right.
   * @returns The product in operand order.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.mul`
   */
  mul(b: Expr): DDM {
    const c = this.copy();
    ddmImul(c.data, b, this.domain);
    return c;
  }
  /**
   * Multiplication by a domain element on the left.
   *
   * @param b - Factor on the left.
   * @returns The product in operand order.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.rmul`
   */
  rmul(b: Expr): DDM {
    const c = this.copy();
    ddmIrmul(c.data, b, this.domain);
    return c;
  }
  /**
   * Multiplies the rows of this matrix by the columns of the right operand.
   *
   * @param b - Matrix on the right.
   * @returns The matrix product.
   * @throws DMDomainError when the coefficient domains are incompatible with the operation.
   * @throws DMShapeError when the matrix dimensions are incompatible with the operation.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.matmul`
   */
  matmul(b: DDM): DDM {
    const [m, o] = this.shape;
    const [o2, n] = b.shape;
    DDM.check(this, '*', b, o, o2);
    const c = DDM.zeros([m, n], this.domain);
    ddmImatmul(c.data, this.data, b.data, this.domain);
    return c;
  }
  /**
   * The elementwise (Hadamard) product.
   *
   * @param b - Matrix with matching dimensions.
   * @returns The entrywise product.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.mul_elementwise`
   */
  mulElementwise(b: DDM): DDM {
    DDM.check(this, '*', b, this.shape, b.shape);
    const K = this.domain;
    return new DDM(
      this.data.map((ai, i) => ai.map((aij, j) => K.mul(aij, b.getitem(i, j)))),
      this.shape,
      K,
    );
  }
  /**
   * The matrices side by side.
   *
   * @param B - Matrix to combine with this one.
   * @returns The horizontal concatenation.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.hstack`
   */
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
  /**
   * The matrices one above the other.
   *
   * @param B - Matrix to combine with this one.
   * @returns The vertical concatenation.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.vstack`
   */
  vstack(...B: DDM[]): DDM {
    const rows = this.toList();
    for (const Bk of B) {
      DDM.check(this, 'vstack', Bk, this.cols, Bk.cols);
      rows.push(...Bk.toList());
    }
    return new DDM(rows, [rows.length, this.cols], this.domain);
  }
  /**
   * The matrix of func applied to each element, over the given domain.
   *
   * @param func - Function applied to each entry.
   * @param domain - Coefficient domain for the values.
   * @returns The matrix of transformed entries.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.applyfunc`
   */
  applyfunc(func: (e: Expr) => Expr, domain: Domain): DDM {
    return new DDM(
      this.data.map((row) => row.map(func)),
      this.shape,
      domain,
    );
  }
  /**
   * The number of nonzero elements.
   *
   * @returns The number of nonzero entries.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.nnz`
   */
  nnz(): number {
    return this.iterValues().length;
  }
  /**
   * The strongly connected components of the graph of the nonzero elements.
   *
   * @returns The strongly connected components of the nonzero pattern.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.scc`
   */
  scc(): number[][] {
    return this.toSdm().scc();
  }
  /**
   * The diagonal matrix of the given elements.
   *
   * @param values - Entries on the main diagonal.
   * @param domain - Coefficient domain for the values.
   * @returns The matrix with the specified diagonal.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.diag`
   */
  static diag(values: readonly Expr[], domain: Domain): DDM {
    const n = values.length;
    const z = DDM.zeros([n, n], domain);
    values.forEach((v, i) => z.setitem(i, i, v));
    return z;
  }
  /**
   * Reduced row echelon form over a field: [rref, pivots].
   *
   * @returns The reduced matrix and pivot indices.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.rref`
   */
  rref(): [DDM, number[]] {
    const b = this.copy();
    const pivots = ddmIrref(b.data, usePartialPivot(this.domain), this.domain);
    return [b, pivots];
  }
  /**
   * Fraction-free reduced row echelon form: [rref, denominator, pivots].
   *
   * @returns The reduced numerator matrix, denominator and pivot indices.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.rref_den`
   */
  rrefDen(): [DDM, Expr, number[]] {
    const b = this.copy();
    const [den, pivots] = ddmIrrefDen(b.data, this.domain);
    return [b, den, pivots];
  }
  /**
   * A basis of the nullspace (as rows) and the nonpivot columns.
   *
   * @returns A matrix of basis rows and the corresponding free column indices.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.nullspace`
   */
  nullspace(): [DDM, number[]] {
    const [r, pivots] = this.rref();
    return r.nullspaceFromRref(pivots);
  }
  /**
   * The nullspace of a matrix in (fraction-free) reduced row echelon form.
   *
   * @param pivotsIn - Indices of the pivot columns.
   * @returns A matrix of basis rows and the corresponding free column indices.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.nullspace_from_rref`
   */
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
  /**
   * A particular solution of the augmented system in reduced row echelon form.
   *
   * @returns A particular solution of the augmented system.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.particular`
   */
  particular(): DDM {
    return this.toSdm().particular().toDdm();
  }
  /**
   * Computes the determinant of a square matrix over its coefficient domain.
   *
   * @returns The determinant.
   * @throws DMNonSquareMatrixError when the matrix is not square.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.det`
   */
  det(): Expr {
    if (this.rows !== this.cols) throw new DMNonSquareMatrixError('Determinant of non-square matrix');
    return ddmIdet(this.copy().data, this.domain);
  }
  /**
   * The inverse over a field.
   *
   * @returns The multiplicative inverse.
   * @throws DMNonSquareMatrixError when the matrix is not square.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.inv`
   */
  inv(): DDM {
    if (this.rows !== this.cols) throw new DMNonSquareMatrixError('Determinant of non-square matrix');
    const ainv = this.copy();
    ddmIinv(ainv.data, this.data, this.domain);
    return ainv;
  }
  /**
   * LU decomposition over a field: [L, U, swaps].
   *
   * @returns The lower and upper factors and row interchanges.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.lu`
   */
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
  /**
   * Fraction-free LU decomposition P*A = L*D**-1*U: [P, L, D, U].
   *
   * @returns The permutation, lower, diagonal and upper factors.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.fflu`
   */
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
  /**
   * QR decomposition over a field with an unnormalized Q (Gram-Schmidt): [Q, R].
   *
   * @returns The orthogonal and upper triangular factors.
   * @throws DMDomainError when the coefficient domains are incompatible with the operation.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.qr`
   */
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
  /**
   * Solve self*x = b over a field by LU decomposition.
   *
   * @param b - Right-hand side of the matrix equation.
   * @returns The solution of the matrix equation.
   * @throws DMDomainError when the coefficient domains are incompatible with the operation.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.lu_solve`
   */
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
  /**
   * The characteristic polynomial coefficients (Berkowitz's algorithm).
   *
   * @returns The characteristic coefficients in descending degree.
   * @throws DMNonSquareMatrixError when the matrix is not square.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.charpoly`
   */
  charpoly(): Expr[] {
    const K = this.domain;
    const [m, n] = this.shape;
    if (m !== n) throw new DMNonSquareMatrixError('Charpoly of non-square matrix');
    const vec = ddmBerk(this.data, K);
    return Array.from({ length: n + 1 }, (_, i) => at(at(vec, i), 0));
  }
  /**
   * Checks all matrix entries for zero.
   *
   * @returns Whether all entries vanish.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.is_zero_matrix`
   */
  isZeroMatrix(): boolean {
    return this.data.every((row) => row.every((e) => !nz(this.domain, e)));
  }
  /**
   * Checks that the subdiagonal entries vanish.
   *
   * @returns Whether all entries below the diagonal vanish.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.is_upper`
   */
  isUpper(): boolean {
    return this.data.every((row, i) => row.slice(0, i).every((e) => !nz(this.domain, e)));
  }
  /**
   * Checks that the superdiagonal entries vanish.
   *
   * @returns Whether all entries above the diagonal vanish.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.is_lower`
   */
  isLower(): boolean {
    return this.data.every((row, i) => row.slice(i + 1).every((e) => !nz(this.domain, e)));
  }
  /**
   * Checks that only diagonal entries can be nonzero.
   *
   * @returns Whether all off-diagonal entries vanish.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.is_diagonal`
   */
  isDiagonal(): boolean {
    return this.isUpper() && this.isLower();
  }
  /**
   * Extracts entries from the main diagonal in order.
   *
   * @returns The entries on the main diagonal.
   * @see SymPy `sympy.polys.matrices.ddm.DDM.diagonal`
   */
  diagonal(): Expr[] {
    return Array.from({ length: Math.min(this.rows, this.cols) }, (_, i) => this.getitem(i, i));
  }
}

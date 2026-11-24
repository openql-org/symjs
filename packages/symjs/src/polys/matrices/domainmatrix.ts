// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/matrices/domainmatrix.py; dup_content,
// dup_primitive, dup_clear_denoms and dup_transform of polys/densetools.py,
// _sort_factors of polys/polyutils.py), Copyright (c) 2006-2023 SymPy
// Development Team, BSD 3-Clause License (see LICENSE).

/**
 * @file SymPy DomainMatrix: a matrix whose elements belong to a domain
 * (ZZ, QQ, a polynomial ring, ...), stored densely (DDM) or sparsely
 * (SDM), with exact fraction-free linear algebra: rref, nullspace,
 * determinant, inverse, characteristic polynomial, adjugate, ...
 */

import { NotImplementedError } from '../../core/errors';
import { at, defined, first } from '../../core/guard';
import type { ExprLike } from '../../core/nodes';
import { Dummy, Expr, Rational } from '../../core/nodes';
import { add, mul, pow } from '../../core/ops';
import type { Matrix } from '../../matrices/matrix';
import { MutableDenseMatrix } from '../../matrices/mutable';
import type { Domain } from '../domains';
import { ZZ } from '../domains';
import { EXRAW } from '../domains/expressionrawdomain';
import { Poly } from '../sympoly';
import type { Shape, Slice } from './ddm';
import { DDM } from './ddm';
import { canonicalUnit, cofactors, convertFrom, denom, domainOfExprs, elemEq, elemStr, gcd, hasAssocRing, isNegative, isQQ, isZZ, lcm, quo, rat } from './domainops';
import { DomainScalar } from './domainscalar';
import { DMBadInputError, DMDomainError, DMFormatError, DMNonInvertibleMatrixError, DMNonSquareMatrixError, DMNotAField, DMShapeError } from './exceptions';
import type { RrefMethod } from './rref';
import { dmRref, dmRrefDen } from './rref';
import { SDM } from './sdm';

/** The rows of a dense DomainMatrix or the dict of rows of a sparse one. */
export type DomainMatrixRows = readonly (readonly Expr[])[] | ReadonlyMap<number, ReadonlyMap<number, Expr>>;

/** A characteristic polynomial factor (coefficients from the highest degree) with its multiplicity. */
export type DomainFactor = [Expr[], number];

const isRows = (r: DomainMatrixRows): r is readonly (readonly Expr[])[] => Array.isArray(r);
const range = (n: number): number[] => Array.from({ length: n }, (_, i) => i);

/**
 * A matrix over a domain, with the dense (DDM) or sparse (SDM) representation in `rep`.
 *
 * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix`
 * @example
 * ```ts
 * import { DomainMatrix, ZZ } from '@symjs/symjs';
 *
 * const A = DomainMatrix.fromList([[1, 2], [3, 4]], ZZ);
 * A.toList(); // => [[1, 2], [3, 4]]
 * ```
 */
export class DomainMatrix {
  /**
   * The dense or sparse representation of the matrix.
   *
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.rep`
   */
  readonly rep: DDM | SDM;

  /**
   * The matrix of a list of rows (dense) or a dict of rows (sparse), optionally converted to the
   * format `fmt`.
   *
   * @param rows - Matrix entries grouped by row.
   * @param shape - Row and column counts.
   * @param domain - Coefficient domain for the values.
   * @param opts - Use `fmt` to choose dense or sparse storage.
   */
  constructor(rows: DomainMatrixRows | DDM | SDM, shape?: Shape, domain?: Domain, opts: { fmt?: 'dense' | 'sparse' } = {}) {
    if (rows instanceof DDM || rows instanceof SDM) {
      this.rep = rows;
      return;
    }
    const sh = defined(shape, 'shape');
    const K = defined(domain, 'domain');
    let rep: DDM | SDM = isRows(rows) ? new DDM(rows, sh, K) : new SDM(new Map([...rows].map(([i, r]) => [i, new Map(r)] as const)), sh, K);
    if (opts.fmt === 'sparse') rep = rep.toSdm();
    else if (opts.fmt === 'dense') rep = rep.toDdm();
    this.rep = rep;
  }
  /**
   * Gives the dimensions required to index the matrix.
   *
   * @returns The ordered pair of row and column counts.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.shape`
   */
  get shape(): Shape {
    return this.rep.shape;
  }
  /**
   * Identifies the arithmetic used for matrix coefficients.
   *
   * @returns The coefficient domain.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.domain`
   */
  get domain(): Domain {
    return this.rep.domain;
  }

  /**
   * The element at (i, j) as a DomainScalar.
   *
   * @param i - Row index.
   * @param j - Column index.
   * @returns The entry at the given row and column.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.__getitem__`
   */
  getitem(i: number, j: number): DomainScalar {
    return new DomainScalar(this.rep.getitem(i, j), this.domain);
  }
  /**
   * The submatrix of a row and a column index or slice.
   *
   * @param i - Row index or slice.
   * @param j - Column index or slice.
   * @returns The selected submatrix.
   * @throws RangeError when a row or column index is out of bounds.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.__getitem__`
   */
  extractSlice(i: number | Slice, j: number | Slice): DomainMatrix {
    const [m, n] = this.shape;
    const asSlice = (k: number | Slice, size: number, what: string): Slice => {
      if (typeof k !== 'number') return k;
      if (!(-size <= k && k < size)) throw new RangeError(`${what} index out of range`);
      const kk = (k + size) % size;
      return [kk, kk + 1];
    };
    return this.fromRep(this.rep.extractSlice(asSlice(i, m, 'Row'), asSlice(j, n, 'Column')));
  }
  /**
   * The element at (i, j) as an expression.
   *
   * @param i - Row index.
   * @param j - Column index.
   * @returns The entry at the given row and column.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.getitem_sympy`
   */
  getitemSympy(i: number, j: number): Expr {
    return this.domain.toSympy(this.rep.getitem(i, j));
  }
  /**
   * The submatrix of the given rows and columns.
   *
   * @param rowslist - Row indices in the requested order.
   * @param colslist - Column indices in the requested order.
   * @returns The selected submatrix.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.extract`
   */
  extract(rowslist: readonly number[], colslist: readonly number[]): DomainMatrix {
    return this.fromRep(this.rep.extract(rowslist, colslist));
  }
  /**
   * Set an element in place.
   *
   * @param i - Row index.
   * @param j - Column index.
   * @param value - Replacement entry in the coefficient domain.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.__setitem__`
   */
  setitem(i: number, j: number, value: Expr): void {
    this.rep.setitem(i, j, value);
  }
  /**
   * Wraps an existing dense or sparse matrix representation in a domain matrix.
   *
   * @param rep - Representation from which to construct the value.
   * @returns The matrix with the supplied representation.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.from_rep`
   */
  static fromRep(rep: DDM | SDM): DomainMatrix {
    return new DomainMatrix(rep);
  }
  /**
   * Wraps an existing dense or sparse matrix representation in a domain matrix.
   *
   * @param rep - Representation from which to construct the value.
   * @returns The matrix with the supplied representation.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.from_rep`
   */
  fromRep(rep: DDM | SDM): DomainMatrix {
    return new DomainMatrix(rep);
  }
  /**
   * The dense matrix of rows of values converted to the domain.
   *
   * @param rows - Matrix entries grouped by row.
   * @param domain - Coefficient domain for the values.
   * @returns The matrix with the given rows.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.from_list`
   */
  static fromList(rows: readonly (readonly (ExprLike | readonly ExprLike[])[])[], domain: Domain): DomainMatrix {
    const nrows = rows.length;
    const ncols = nrows ? at(rows, 0).length : 0;
    return new DomainMatrix(
      rows.map((row) => row.map((e) => e instanceof Expr || typeof e === 'number' || typeof e === 'bigint' ? domain.fromSympy(e) : domain.toSympy(domain.new(...e)))),
      [nrows, ncols],
      domain,
    );
  }
  /**
   * The dense matrix of rows of expressions over the domain construct_domain chooses.
   *
   * @param nrows - Number of rows.
   * @param ncols - Number of columns.
   * @param rows - Matrix entries grouped by row.
   * @param opts - Set `field` to promote the inferred domain to a field.
   * @returns The matrix with the given rows.
   * @throws DMBadInputError when the entries do not match the specified matrix shape.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.from_list_sympy`
   */
  static fromListSympy(nrows: number, ncols: number, rows: readonly (readonly ExprLike[])[], opts: { field?: boolean } = {}): DomainMatrix {
    if (rows.length !== nrows || rows.some((r) => r.length !== ncols)) throw new DMBadInputError('Inconsistent row-list/shape');
    const [domain, items] = domainOfExprs(rows.flat(), opts);
    return new DomainMatrix(
      range(nrows).map((r) => items.slice(ncols * r, ncols * (r + 1))),
      [nrows, ncols],
      domain,
    );
  }
  /**
   * The sparse matrix of a dict of rows of expressions over the domain construct_domain chooses.
   *
   * @param nrows - Number of rows.
   * @param ncols - Number of columns.
   * @param elemsdict - Nonzero entries keyed by row and then by column.
   * @param opts - Set `field` to promote the inferred domain to a field.
   * @returns The matrix with the specified sparse rows.
   * @throws DMBadInputError when a stored index is outside the declared shape.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.from_dict_sympy`
   */
  static fromDictSympy(nrows: number, ncols: number, elemsdict: ReadonlyMap<number, ReadonlyMap<number, ExprLike>>, opts: { field?: boolean } = {}): DomainMatrix {
    if (![...elemsdict.keys()].every((r) => r >= 0 && r < nrows)) throw new DMBadInputError('Row out of range');
    if (![...elemsdict.values()].every((row) => [...row.keys()].every((c) => c >= 0 && c < ncols))) throw new DMBadInputError('Column out of range');
    const [domain, items] = domainOfExprs([...elemsdict.values()].flatMap((row) => [...row.values()]), opts);
    let idx = 0;
    const dict = new Map([...elemsdict].map(([i, row]) => [i, new Map([...row.keys()].map((j) => [j, at(items, idx++)] as const))] as const));
    return new DomainMatrix(dict, [nrows, ncols], domain);
  }
  /**
   * The DomainMatrix of a Matrix over the domain construct_domain chooses (sparse unless fmt is
   * 'dense').
   *
   * @param M - Input matrix.
   * @param opts - Use `fmt` to choose dense or sparse storage. Set `field` to promote the inferred
   *   domain to a field.
   * @returns The value reconstructed from the matrix entries.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.from_Matrix`
   */
  static fromMatrix(M: Matrix, opts: { fmt?: 'dense' | 'sparse'; field?: boolean } = {}): DomainMatrix {
    const { fmt, ...rest } = opts;
    if (fmt === 'dense') return DomainMatrix.fromListSympy(M.rows, M.cols, M.toArray(), rest);
    return DomainMatrix.fromDictSympy(M.rows, M.cols, M.todod(), rest);
  }
  /**
   * Infers a common coefficient domain for the given expressions and converts them into it.
   *
   * @param itemsSympy - Expressions from which to infer the coefficient domain.
   * @param opts - Set `field` to promote the inferred domain to a field.
   * @returns The inferred domain and converted entries.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.get_domain`
   */
  static getDomain(itemsSympy: readonly ExprLike[], opts: { field?: boolean } = {}): [Domain, Expr[]] {
    return domainOfExprs(itemsSympy, opts);
  }
  /**
   * The matrix over the domain construct_domain chooses for its elements.
   *
   * @param opts - Set `field` to promote the inferred domain to a field.
   * @returns The matrix over the inferred coefficient domain.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.choose_domain`
   */
  chooseDomain(opts: { field?: boolean } = {}): DomainMatrix {
    const [elements, data] = this.toFlatNz();
    const [dom, elementsDom] = domainOfExprs(
      elements.map((e) => this.domain.toSympy(e)),
      opts,
    );
    return this.fromFlatNz(elementsDom, data, dom);
  }
  /**
   * Copies the matrix so its entries can be updated independently.
   *
   * @returns An independent copy of the matrix.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.copy`
   */
  copy(): DomainMatrix {
    return this.fromRep(this.rep.copy());
  }
  /**
   * The matrix over another domain.
   *
   * @param K - Coefficient domain for the values.
   * @returns The value over the target domain.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.convert_to`
   */
  convertTo(K: Domain): DomainMatrix {
    if (K.equals(this.domain)) return this.copy();
    return this.fromRep(this.rep.convertTo(K));
  }
  /**
   * The matrix over EXRAW (its elements as expressions).
   *
   * @returns The matrix over the raw expression domain.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.to_sympy`
   */
  toSympy(): DomainMatrix {
    return this.convertTo(EXRAW);
  }
  /**
   * The matrix over the field of fractions of the domain.
   *
   * @returns The matrix over the associated field of fractions.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.to_field`
   */
  toField(): DomainMatrix {
    return this.convertTo(this.domain.getField());
  }
  /**
   * Uses sparse storage for the nonzero matrix entries.
   *
   * @returns The matrix in sparse format.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.to_sparse`
   */
  toSparse(): DomainMatrix {
    return this.rep instanceof SDM ? this : this.fromRep(this.rep.toSdm());
  }
  /**
   * Uses dense storage for the entries of this matrix.
   *
   * @returns The matrix in dense format.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.to_dense`
   */
  toDense(): DomainMatrix {
    return this.rep instanceof DDM ? this : this.fromRep(this.rep.toDdm());
  }
  /**
   * Exposes the entries as a dense domain matrix.
   *
   * @returns The dense domain-matrix representation.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.to_ddm`
   */
  toDdm(): DDM {
    return this.rep.toDdm();
  }
  /**
   * Exposes the entries as a sparse domain matrix.
   *
   * @returns The sparse domain-matrix representation.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.to_sdm`
   */
  toSdm(): SDM {
    return this.rep.toSdm();
  }
  /**
   * Returns the dense matrix representation over the coefficient domain.
   *
   * @returns The dense domain-matrix representation.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.to_dfm_or_ddm`
   */
  toDfmOrDdm(): DDM {
    return this.rep.toDfmOrDdm();
  }
  /**
   * Converts the operands to a common coefficient domain.
   *
   * @param others - Other matrices to convert to a common domain.
   * @returns The operands over a common domain.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.unify`
   */
  unify(...others: DomainMatrix[]): DomainMatrix[];
  /**
   * Converts the operands to a common coefficient domain.
   *
   * @param other - Operand to convert to a common module or coefficient domain.
   * @returns The operands over a common domain.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.unify`
   */
  unify(other: DomainScalar): [DomainMatrix, DomainScalar];
  unify(...others: (DomainMatrix | DomainScalar)[]): (DomainMatrix | DomainScalar)[] {
    const all = [this, ...others];
    if (new Set(all.map((m) => m.domain.toString())).size === 1) return all;
    const domain = all.map((m) => m.domain).reduce((x, y) => x.unify(y));
    return all.map((m) => m.convertTo(domain));
  }
  /**
   * The matrices over a common domain in the format fmt.
   *
   * @param others - Other matrices to convert to a common domain.
   * @param fmt - Representation in which to return the result.
   * @returns The matrices in a common format.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix._unify_fmt`
   */
  unifyFmt(others: readonly DomainMatrix[], fmt: 'dense' | 'sparse'): DomainMatrix[] {
    const ms = this.unify(...others);
    if (new Set(ms.map((m) => m.rep.fmt)).size === 1) return ms;
    return ms.map((m) => (fmt === 'sparse' ? m.toSparse() : m.toDense()));
  }
  /**
   * The Matrix of the elements as expressions.
   *
   * @returns The matrix of expression entries.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.to_Matrix`
   */
  toMatrix(): MutableDenseMatrix {
    const [m, n] = this.shape;
    return MutableDenseMatrix.fromFunction(m, n, (i, j) => this.getitemSympy(i, j));
  }
  /**
   * Converts the matrix to a list of rows in the coefficient domain.
   *
   * @returns The entries grouped into rows.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.to_list`
   */
  toList(): Expr[][] {
    return this.rep.toList();
  }
  /**
   * The elements row by row.
   *
   * @returns The entries in row-major order.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.to_list_flat`
   */
  toListFlat(): Expr[] {
    return this.rep.toListFlat();
  }
  /**
   * Fills the matrix row by row from a flat sequence.
   *
   * @param elements - Entries in their given order.
   * @param shape - Row and column counts.
   * @param domain - Coefficient domain for the values.
   * @returns The matrix filled in row-major order.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.from_list_flat`
   */
  static fromListFlat(elements: readonly Expr[], shape: Shape, domain: Domain): DomainMatrix {
    return new DomainMatrix(DDM.fromListFlat(elements, shape, domain));
  }
  /**
   * The nonzero elements and the data to rebuild the matrix from them.
   *
   * @returns The nonzero entries with their positions and matrix shape.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.to_flat_nz`
   */
  toFlatNz(): [Expr[], [[number, number][], Shape]] {
    return this.rep.toFlatNz();
  }
  /**
   * The matrix (in the format of this one) of nonzero elements and the data of toFlatNz.
   *
   * @param elements - Entries in their given order.
   * @param data - Positions and shape returned by `toFlatNz`.
   * @param domain - Coefficient domain for the values.
   * @returns The matrix reconstructed from its nonzero entries and their positions.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.from_flat_nz`
   */
  fromFlatNz(elements: readonly Expr[], data: readonly [readonly (readonly [number, number])[], Shape], domain: Domain): DomainMatrix {
    return this.fromRep(this.rep instanceof SDM ? SDM.fromFlatNz(elements, data, domain) : DDM.fromFlatNz(elements, data, domain));
  }
  /**
   * The nonzero elements as row -> column -> element.
   *
   * @returns The nonzero entries indexed first by row, then by column.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.to_dod`
   */
  toDod(): Map<number, Map<number, Expr>> {
    return this.rep.toDod();
  }
  /**
   * Builds a matrix from nested row and column maps.
   *
   * @param dod - Nonzero entries keyed by row and then by column.
   * @param shape - Row and column counts.
   * @param domain - Coefficient domain for the values.
   * @returns The matrix with the specified sparse rows.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.from_dod`
   */
  static fromDod(dod: ReadonlyMap<number, ReadonlyMap<number, Expr>>, shape: Shape, domain: Domain): DomainMatrix {
    return new DomainMatrix(SDM.fromDod(dod, shape, domain));
  }
  /**
   * A matrix of the shape and format of this one from a dict of rows.
   *
   * @param dod - Nonzero entries keyed by row and then by column.
   * @param domain - Coefficient domain for the values.
   * @returns The matrix with the specified sparse rows.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.from_dod_like`
   */
  fromDodLike(dod: ReadonlyMap<number, ReadonlyMap<number, Expr>>, domain: Domain = this.domain): DomainMatrix {
    return this.fromRep(this.rep instanceof SDM ? SDM.fromDod(dod, this.shape, domain) : DDM.fromDod(dod, this.shape, domain));
  }
  /**
   * The nonzero elements by position.
   *
   * @returns The nonzero entries indexed by coordinate pair.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.to_dok`
   */
  toDok(): Map<[number, number], Expr> {
    return this.rep.toDok();
  }
  /**
   * Builds a matrix from a map of index pairs to entries.
   *
   * @param dok - Nonzero entries keyed by coordinate pair.
   * @param shape - Row and column counts.
   * @param domain - Coefficient domain for the values.
   * @returns The matrix with the specified nonzero entries.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.from_dok`
   */
  static fromDok(dok: ReadonlyMap<readonly [number, number], Expr>, shape: Shape, domain: Domain): DomainMatrix {
    return new DomainMatrix(SDM.fromDok(dok, shape, domain));
  }
  /**
   * Collects the stored nonzero values of the matrix.
   *
   * @returns The nonzero entries.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.iter_values`
   */
  iterValues(): Expr[] {
    return this.rep.iterValues();
  }
  /**
   * Pairs each nonzero entry with its row and column indices.
   *
   * @returns The index pairs and values of the nonzero entries.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.iter_items`
   */
  iterItems(): [[number, number], Expr][] {
    return this.rep.iterItems();
  }
  /**
   * The number of nonzero elements.
   *
   * @returns The number of nonzero entries.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.nnz`
   */
  nnz(): number {
    return this.rep.nnz();
  }
  /**
   * Formats the matrix with its shape and coefficient domain.
   *
   * @returns The printable representation.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.__repr__`
   */
  toString(): string {
    return `DomainMatrix(${this.rep.toString()}, (${this.shape.join(', ')}), ${this.domain.toString()})`;
  }
  /**
   * Interchanges the rows and columns.
   *
   * @returns The matrix with its rows and columns interchanged.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.transpose`
   */
  transpose(): DomainMatrix {
    return this.fromRep(this.rep.transpose());
  }
  /**
   * The elements row by row.
   *
   * @returns The entries in row-major order.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.flat`
   */
  flat(): Expr[] {
    return this.rep.toListFlat();
  }
  /**
   * Checks all matrix entries for zero.
   *
   * @returns Whether all entries vanish.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.is_zero_matrix`
   */
  get isZeroMatrix(): boolean {
    return this.rep.isZeroMatrix();
  }
  /**
   * Checks that the subdiagonal entries vanish.
   *
   * @returns Whether all entries below the diagonal vanish.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.is_upper`
   */
  get isUpper(): boolean {
    return this.rep.isUpper();
  }
  /**
   * Checks that the superdiagonal entries vanish.
   *
   * @returns Whether all entries above the diagonal vanish.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.is_lower`
   */
  get isLower(): boolean {
    return this.rep.isLower();
  }
  /**
   * Checks that only diagonal entries can be nonzero.
   *
   * @returns Whether all off-diagonal entries vanish.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.is_diagonal`
   */
  get isDiagonal(): boolean {
    return this.rep.isDiagonal();
  }
  /**
   * Extracts entries from the main diagonal in order.
   *
   * @returns The entries on the main diagonal.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.diagonal`
   */
  diagonal(): Expr[] {
    return this.rep.diagonal();
  }
  /**
   * Compares the row count with the column count.
   *
   * @returns Whether the row and column counts agree.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.is_square`
   */
  get isSquare(): boolean {
    return this.shape[0] === this.shape[1];
  }
  /**
   * Counts the pivots in a row echelon form.
   *
   * @returns The dimension of the column space.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.rank`
   */
  rank(): number {
    return this.rref()[1].length;
  }
  /**
   * The matrices side by side (in the format of this one).
   *
   * @param B - Matrix to combine with this one.
   * @returns The horizontal concatenation.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.hstack`
   */
  hstack(...B: DomainMatrix[]): DomainMatrix {
    const [A, ...Bs] = this.unifyFmt(B, this.rep.fmt);
    const a = defined(A).rep;
    return new DomainMatrix(a instanceof SDM ? a.hstack(...Bs.map((b) => b.toSdm())) : a.hstack(...Bs.map((b) => b.toDdm())));
  }
  /**
   * The matrices one above the other (dense when the formats differ).
   *
   * @param B - Matrix to combine with this one.
   * @returns The vertical concatenation.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.vstack`
   */
  vstack(...B: DomainMatrix[]): DomainMatrix {
    const [A, ...Bs] = this.unifyFmt(B, 'dense');
    const a = defined(A).rep;
    return new DomainMatrix(a instanceof SDM ? a.vstack(...Bs.map((b) => b.toSdm())) : a.vstack(...Bs.map((b) => b.toDdm())));
  }
  /**
   * The matrix of func applied to the elements, over the given domain.
   *
   * @param func - Function applied to each entry.
   * @param domain - Coefficient domain for the values.
   * @returns The matrix of transformed entries.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.applyfunc`
   */
  applyfunc(func: (e: Expr) => Expr, domain: Domain = this.domain): DomainMatrix {
    return this.fromRep(this.rep.applyfunc(func, domain));
  }
  private check(op: string, B: DomainMatrix, ashape: unknown, bshape: unknown): void {
    if (!this.domain.equals(B.domain)) throw new DMDomainError(`Domain mismatch: ${this.domain.toString()} ${op} ${B.domain.toString()}`);
    if (String(ashape) !== String(bshape)) throw new DMShapeError(`Shape mismatch: (${this.shape.join(', ')}) ${op} (${B.shape.join(', ')})`);
    if (this.rep.fmt !== B.rep.fmt) throw new DMFormatError(`Format mismatch: ${this.rep.fmt} ${op} ${B.rep.fmt}`);
  }
  /**
   * The sum (same domain and format).
   *
   * @param B - Addend.
   * @returns The sum of the operands.
   * @throws DMDomainError when the coefficient domains are incompatible with the operation.
   * @throws DMShapeError when the matrix dimensions are incompatible with the operation.
   * @throws DMFormatError when the operands use different storage formats.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.add`
   */
  add(B: DomainMatrix): DomainMatrix {
    this.check('+', B, this.shape, B.shape);
    return this.fromRep(this.rep instanceof SDM ? this.rep.add(B.toSdm()) : this.rep.add(B.toDdm()));
  }
  /**
   * The difference (same domain and format).
   *
   * @param B - Value to subtract.
   * @returns The difference in operand order.
   * @throws DMDomainError when the coefficient domains are incompatible with the operation.
   * @throws DMShapeError when the matrix dimensions are incompatible with the operation.
   * @throws DMFormatError when the operands use different storage formats.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.sub`
   */
  sub(B: DomainMatrix): DomainMatrix {
    this.check('-', B, this.shape, B.shape);
    return this.fromRep(this.rep instanceof SDM ? this.rep.sub(B.toSdm()) : this.rep.sub(B.toDdm()));
  }
  /**
   * Reverses the sign of the value.
   *
   * @returns The additive inverse.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.neg`
   */
  neg(): DomainMatrix {
    return this.fromRep(this.rep.neg());
  }
  /**
   * Multiplication by a matrix or by a domain element on the right.
   *
   * @param b - Factor on the right.
   * @returns The product in operand order.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.mul`
   */
  mul(b: Expr | DomainMatrix): DomainMatrix {
    return b instanceof DomainMatrix ? this.matmul(b) : this.fromRep(this.rep.mul(b));
  }
  /**
   * Multiplication by a domain element on the left.
   *
   * @param b - Factor on the left.
   * @returns The product in operand order.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.rmul`
   */
  rmul(b: Expr): DomainMatrix {
    return this.fromRep(this.rep.rmul(b));
  }
  /**
   * The matrix product (same domain and format).
   *
   * @param B - Matrix on the right.
   * @returns The matrix product.
   * @throws DMDomainError when the coefficient domains are incompatible with the operation.
   * @throws DMShapeError when the matrix dimensions are incompatible with the operation.
   * @throws DMFormatError when the operands use different storage formats.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.matmul`
   */
  matmul(B: DomainMatrix): DomainMatrix {
    this.check('*', B, this.shape[1], B.shape[0]);
    return this.fromRep(this.rep instanceof SDM ? this.rep.matmul(B.toSdm()) : this.rep.matmul(B.toDdm()));
  }
  private scalarmul0(lamda: Expr, reverse: boolean): DomainMatrix {
    const K = this.domain;
    if (elemEq(lamda, K.zero)) return DomainMatrix.zeros(this.shape, K);
    if (elemEq(lamda, K.one)) return this.copy();
    return reverse ? this.rmul(lamda) : this.mul(lamda);
  }
  /**
   * Multiplication by a scalar on the right (zero and one handled directly).
   *
   * @param lamda - Scalar in the coefficient domain.
   * @returns The scalar multiple in the specified order.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.scalarmul`
   */
  scalarmul(lamda: Expr): DomainMatrix {
    return this.scalarmul0(lamda, false);
  }
  /**
   * Multiplication by a scalar on the left.
   *
   * @param lamda - Scalar in the coefficient domain.
   * @returns The scalar multiple in the specified order.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.rscalarmul`
   */
  rscalarmul(lamda: Expr): DomainMatrix {
    return this.scalarmul0(lamda, true);
  }
  /**
   * The elementwise product.
   *
   * @param B - Matrix with matching dimensions.
   * @returns The entrywise product.
   * @throws DMDomainError when the coefficient domains are incompatible with the operation.
   * @throws DMShapeError when the matrix dimensions are incompatible with the operation.
   * @throws DMFormatError when the operands use different storage formats.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.mul_elementwise`
   */
  mulElementwise(B: DomainMatrix): DomainMatrix {
    this.check('*', B, this.shape, B.shape);
    return this.fromRep(this.rep instanceof SDM ? this.rep.mulElementwise(B.toSdm()) : this.rep.mulElementwise(B.toDdm()));
  }
  /**
   * Division by a scalar over the field of fractions.
   *
   * @param lamdaIn - Divisor.
   * @returns The quotient.
   * @throws RangeError when the divisor or denominator is zero.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.__truediv__`
   */
  div(lamdaIn: DomainScalar | Expr | number): DomainMatrix {
    let lamda: DomainScalar;
    if (lamdaIn instanceof DomainScalar) lamda = lamdaIn;
    else if (typeof lamdaIn === 'number' || (lamdaIn instanceof Rational && lamdaIn.isInteger)) lamda = new DomainScalar(ZZ.fromSympy(lamdaIn), ZZ);
    else lamda = new DomainScalar(this.domain.getField().fromSympy(lamdaIn), this.domain.getField());
    const [A, l] = this.toField().unify(lamda);
    const K = l.domain;
    if (K.isZero(l.element)) throw new RangeError('division by zero');
    if (K.isOne(l.element)) return A;
    return A.mul(K.quo(K.one, l.element));
  }
  /**
   * Raises a square matrix to a nonnegative integer power.
   *
   * @param k - Exponent to which to raise the value.
   * @returns The value raised to the given exponent.
   * @throws TypeError when the exponent is not an integer.
   * @throws DMNonSquareMatrixError when the matrix is not square.
   * @throws NotImplementedError when the exponent is negative.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.pow`
   */
  pow(k: number | Rational): DomainMatrix {
    // (SymPy DomainMatrix.__pow__: the exponent must be an integer, not a Rational such as 1/2)
    const n = k instanceof Rational ? (k.isInteger ? Number(k.p) : Number.NaN) : k;
    if (!Number.isInteger(n)) throw new TypeError('Power of a DomainMatrix must be an integer');
    const [nrows, ncols] = this.shape;
    if (nrows !== ncols) throw new DMNonSquareMatrixError('Power of a nonsquare matrix');
    if (n < 0) throw new NotImplementedError('Negative powers');
    if (n === 0) return DomainMatrix.eye(nrows, this.domain);
    if (n === 1) return this;
    if (n % 2 === 1) return opMul(this, this.pow(n - 1));
    const s = this.pow(n / 2);
    return opMul(s, s);
  }
  /**
   * The strongly connected components of the graph of the nonzero elements.
   *
   * @returns The strongly connected components of the nonzero pattern.
   * @throws DMNonSquareMatrixError when the matrix is not square.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.scc`
   */
  scc(): number[][] {
    if (!this.isSquare) throw new DMNonSquareMatrixError('Matrix must be square for scc');
    return this.rep.scc();
  }
  /**
   * Clears all entry denominators using a single scalar factor.
   *
   * @param convert - Convert the numerator to the associated ring.
   * @returns The denominator and the cleared numerator matrix.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.clear_denoms`
   */
  clearDenoms(convert = false): [DomainScalar, DomainMatrix] {
    const [elems0, data] = this.toFlatNz();
    const K0 = this.domain;
    const K1 = hasAssocRing(K0) ? K0.getRing() : K0;
    const [den, elems1] = dupClearDenoms(elems0, K0, K1, convert);
    const [Kden, Knum] = convert ? [K1, K1] : [K1, K0];
    return [new DomainScalar(den, Kden), this.fromFlatNz(elems1, data, Knum)];
  }
  /**
   * Clears entry denominators independently in each row and records the factors on a diagonal matrix.
   *
   * @param convert - Convert the numerator to the associated ring.
   * @returns The denominator and the cleared numerator matrix.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.clear_denoms_rowwise`
   */
  clearDenomsRowwise(convert = false): [DomainMatrix, DomainMatrix] {
    const dod = this.toDod();
    const K0 = this.domain;
    const K1 = hasAssocRing(K0) ? K0.getRing() : K0;
    const diagonals = range(this.shape[0]).map(() => K0.one);
    const dodNum = new Map<number, Map<number, Expr>>();
    for (const [i, rowi] of dod) {
      const [den, elemsNum] = dupClearDenoms([...rowi.values()], K0, K1, convert);
      diagonals[i] = den;
      dodNum.set(i, new Map([...rowi.keys()].map((j, k) => [j, at(elemsNum, k)] as const)));
    }
    const [Kden, Knum] = convert ? [K1, K1] : [K1, K0];
    return [DomainMatrix.diag(diagonals, Kden), this.fromDodLike(dodNum, Knum)];
  }
  /**
   * Cancels common factors between the matrix entries and a scalar denominator.
   *
   * @param denomIn - Common denominator.
   * @returns The reduced matrix numerator and common denominator.
   * @throws RangeError when the divisor or denominator is zero.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.cancel_denom`
   */
  cancelDenom(denomIn: Expr): [DomainMatrix, Expr] {
    const K = this.domain;
    let d = denomIn;
    if (K.isZero(d)) throw new RangeError('denominator is zero');
    if (K.isOne(d)) return [this.copy(), d];
    let [elements] = this.toFlatNz();
    const data = this.toFlatNz()[1];
    const u = isNegative(K, d) ? K.neg(K.one) : canonicalUnit(K, d);
    const content = dupContent(elements, K);
    let common = gcd(K, content, d);
    if (!K.isOne(content)) {
      common = gcd(K, content, d);
      if (!K.isOne(common)) {
        elements = dupQuoGround(elements, common, K);
        d = quo(K, d, common);
      }
    }
    if (!K.isOne(u)) {
      elements = elements.map((e) => K.mul(e, u));
      d = K.mul(u, d);
    } else if (K.isOne(common)) return [this.copy(), d];
    return [this.fromFlatNz(elements, data, K), d];
  }
  /**
   * Reduces each entry separately against the given denominator.
   *
   * @param d - Denominator to cancel.
   * @returns The matrices of reduced numerators and denominators.
   * @throws RangeError when the divisor or denominator is zero.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.cancel_denom_elementwise`
   */
  cancelDenomElementwise(d: Expr): [DomainMatrix, DomainMatrix] {
    const K = this.domain;
    if (K.isZero(d)) throw new RangeError('denominator is zero');
    if (K.isOne(d)) return [this.copy(), DomainMatrix.ones(this.shape, K)];
    const [elements, data] = this.toFlatNz();
    const cof = elements.map((e) => cofactors(K, e, d));
    return [this.fromFlatNz(cof.map((c) => c[1]), data, K), this.fromFlatNz(cof.map((c) => c[2]), data, K)];
  }
  /**
   * The gcd of the elements.
   *
   * @returns The greatest common divisor of the entries.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.content`
   */
  content(): Expr {
    return dupContent(this.toFlatNz()[0], this.domain);
  }
  /**
   * Factors out the common content of the matrix entries.
   *
   * @returns The content and primitive matrix.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.primitive`
   */
  primitive(): [Expr, DomainMatrix] {
    const K = this.domain;
    const [elements, data] = this.toFlatNz();
    const [content, prims] = dupPrimitive(elements, K);
    return [content, this.fromFlatNz(prims, data, K)];
  }
  /**
   * Reduces the matrix over the associated field and identifies the pivot columns.
   *
   * @param opts - Choose the elimination algorithm with `method`.
   * @returns The reduced matrix and pivot indices.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.rref`
   * @example
   * ```ts
   * import { DM, QQ } from '@symjs/symjs';
   *
   * const A = DM([[1, 2, 3], [4, 5, 6]], QQ);
   * const [reduced, pivots] = A.rref();
   * reduced.toList(); // => [[1, 0, -1], [0, 1, 2]]
   * pivots; // => [0, 1]
   * ```
   */
  rref(opts: { method?: RrefMethod } = {}): [DomainMatrix, number[]] {
    return dmRref(this, opts);
  }
  /**
   * Fraction-free reduced row echelon form: [rref, denominator, pivots].
   *
   * @param opts - Choose the elimination `method` and whether to `keepDomain`.
   * @returns The reduced numerator matrix, denominator and pivot indices.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.rref_den`
   */
  rrefDen(opts: { method?: RrefMethod; keepDomain?: boolean } = {}): [DomainMatrix, Expr, number[]] {
    return dmRrefDen(this, opts);
  }
  /**
   * A basis of the column space (the pivot columns) over a field.
   *
   * @returns The basis columns.
   * @throws DMNotAField when the operation requires a coefficient field.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.columnspace`
   */
  columnspace(): DomainMatrix {
    if (!this.domain.isField) throw new DMNotAField('Not a field');
    const [, pivots] = this.rref();
    return this.extract(range(this.shape[0]), pivots);
  }
  /**
   * A basis of the row space, using the original linearly independent rows.
   *
   * @returns A matrix of basis rows.
   * @throws DMNotAField when the operation requires a coefficient field.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.rowspace`
   */
  rowspace(): DomainMatrix {
    if (!this.domain.isField) throw new DMNotAField('Not a field');
    const [, pivots] = this.transpose().rref();
    return this.extract(pivots, range(this.shape[1]));
  }
  /**
   * A basis of the nullspace as rows (with divideLast over a field, the last nonzero element of each
   * is 1).
   *
   * @param opts - Set `divideLast` to normalize the basis vectors over a field.
   * @returns A basis of the right nullspace.
   * @throws DMNotAField when the operation requires a coefficient field.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.nullspace`
   */
  nullspace(opts: { divideLast?: boolean } = {}): DomainMatrix {
    const K = this.domain;
    if (opts.divideLast && !K.isField) throw new DMNotAField('Cannot normalize vectors over a non-field');
    let A: DomainMatrix;
    let pivots: number[];
    if (opts.divideLast) [A, pivots] = this.rref();
    else {
      let den: Expr;
      [A, den, pivots] = this.rrefDen();
      const u = canonicalUnit(K, den);
      if (!K.isOne(u)) A = A.scalarmul(u);
    }
    return A.nullspaceFromRref(pivots);
  }
  /**
   * The nullspace of a matrix in (fraction-free) reduced row echelon form.
   *
   * @param pivots - Indices of the pivot columns.
   * @returns A basis of the right nullspace.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.nullspace_from_rref`
   */
  nullspaceFromRref(pivots?: readonly number[]): DomainMatrix {
    return this.fromRep(this.rep.nullspaceFromRref(pivots)[0]);
  }
  /**
   * The inverse over a field.
   *
   * @returns The multiplicative inverse.
   * @throws DMNotAField when the operation requires a coefficient field.
   * @throws DMNonSquareMatrixError when the matrix is not square.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.inv`
   */
  inv(): DomainMatrix {
    if (!this.domain.isField) throw new DMNotAField('Not a field');
    if (!this.isSquare) throw new DMNonSquareMatrixError();
    return this.fromRep(this.rep.inv());
  }
  /**
   * The determinant (fraction-free).
   *
   * @returns The determinant.
   * @throws DMNonSquareMatrixError when the matrix is not square.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.det`
   */
  det(): Expr {
    if (!this.isSquare) throw new DMNonSquareMatrixError();
    return this.rep.det();
  }
  /**
   * Computes the classical adjoint and determinant without division.
   *
   * @returns The adjugate and determinant.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.adj_det`
   */
  adjDet(): [DomainMatrix, Expr] {
    const m = this.shape[0];
    const I = DomainMatrix.eye([m, m], this.domain);
    const [adjA0, detA] = this.solveDenCharpoly(I, undefined, false);
    return [this.rep instanceof DDM ? adjA0.toDense() : adjA0, detA];
  }
  /**
   * The adjugate (classical adjoint).
   *
   * @returns The transpose of the cofactor matrix.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.adjugate`
   */
  adjugate(): DomainMatrix {
    return this.adjDet()[0];
  }
  /**
   * Represents the inverse as a matrix numerator over a single scalar denominator.
   *
   * @param method - Algorithm used for elimination or solving.
   * @returns The numerator matrix and common denominator.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.inv_den`
   */
  invDen(method?: 'rref' | 'charpoly'): [DomainMatrix, Expr] {
    return this.solveDen(DomainMatrix.eye(this.shape, this.domain), method);
  }
  /**
   * Solves the matrix equation over the original domain using a common denominator for the unknowns.
   *
   * @param b - Right-hand side of the matrix equation.
   * @param method - Algorithm used for elimination or solving.
   * @returns The numerator matrix and common denominator.
   * @throws DMShapeError when the matrix dimensions are incompatible with the operation.
   * @throws DMNonSquareMatrixError when the matrix is not square.
   * @throws DMBadInputError when the method is unrecognized.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.solve_den`
   */
  solveDen(b: DomainMatrix, method: string = 'rref'): [DomainMatrix, Expr] {
    const [m, n] = this.shape;
    if (m !== b.shape[0]) throw new DMShapeError('Matrix equation shape mismatch.');
    if (method === 'charpoly') {
      if (m !== n) throw new DMNonSquareMatrixError("method='charpoly' requires a square matrix.");
      return this.solveDenCharpoly(b);
    }
    if (method === 'rref') return this.solveDenRref(b);
    throw new DMBadInputError(`unknown solve method: ${method}`);
  }
  /**
   * Solves the matrix equation by fraction-free reduction of the augmented matrix.
   *
   * @param b - Right-hand side of the matrix equation.
   * @returns The numerator matrix and common denominator.
   * @throws DMShapeError when the matrix dimensions are incompatible with the operation.
   * @throws DMNonInvertibleMatrixError when the matrix is singular or the system lacks a unique
   *   solution.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.solve_den_rref`
   */
  solveDenRref(b: DomainMatrix): [DomainMatrix, Expr] {
    const [m, n] = this.shape;
    if (m !== b.shape[0]) throw new DMShapeError('Matrix equation shape mismatch.');
    if (m < n) throw new DMShapeError('Underdetermined matrix equation.');
    const [aRref, den, pivots] = this.hstack(b).rrefDen();
    if (pivots.length !== n || (pivots.length && at(pivots, -1) >= n)) throw new DMNonInvertibleMatrixError('Non-unique solution.');
    return [aRref.extractSlice([null, n], [n, null]), den];
  }
  /**
   * Solves the matrix equation using the adjugate and determinant from the characteristic polynomial.
   *
   * @param bIn - Right-hand side of the matrix equation.
   * @param cp - Characteristic polynomial coefficients in descending degree.
   * @param check - Check invertibility before returning the solution.
   * @returns The numerator matrix and common denominator.
   * @throws DMNonSquareMatrixError when the matrix is not square.
   * @throws DMShapeError when the matrix dimensions are incompatible with the operation.
   * @throws DMNonInvertibleMatrixError when the matrix is singular or the system lacks a unique
   *   solution.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.solve_den_charpoly`
   */
  solveDenCharpoly(bIn: DomainMatrix, cp?: readonly Expr[], check = true): [DomainMatrix, Expr] {
    const [, b] = this.unify(bIn);
    const [m, n] = this.shape;
    if (m !== n) throw new DMNonSquareMatrixError('Matrix must be square');
    if (defined(b).shape[0] !== m) throw new DMShapeError('Matrix and vector must have the same number of rows');
    const [f, detA] = this.adjPolyDet(cp);
    if (check && this.domain.isZero(detA)) throw new DMNonInvertibleMatrixError('Matrix is not invertible');
    return [this.evalPolyMul(f, defined(b)), detA];
  }
  /**
   * Finds a polynomial whose matrix value is the adjugate and computes the determinant.
   *
   * @param cpIn - Characteristic polynomial coefficients in descending degree.
   * @returns The adjugate polynomial coefficients and determinant.
   * @throws DMNonSquareMatrixError when the matrix is not square.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.adj_poly_det`
   */
  adjPolyDet(cpIn?: readonly Expr[]): [Expr[], Expr] {
    if (!this.isSquare) throw new DMNonSquareMatrixError('Matrix must be square');
    const cp = cpIn ?? this.charpoly();
    const K = this.domain;
    if (cp.length % 2) return [cp.slice(0, -1).map((c) => K.neg(c)), at(cp, -1)];
    return [cp.slice(0, -1), K.neg(at(cp, -1))];
  }
  /**
   * Evaluates a polynomial at this square matrix by Horner’s rule.
   *
   * @param p - Polynomial coefficients in descending degree.
   * @returns The polynomial evaluated at this matrix.
   * @throws DMNonSquareMatrixError when the matrix is not square.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.eval_poly`
   */
  evalPoly(p: readonly Expr[]): DomainMatrix {
    if (!this.isSquare) throw new DMNonSquareMatrixError('Matrix must be square');
    if (!p.length) return DomainMatrix.zeros(this.shape, this.domain);
    const I = DomainMatrix.eye(this.shape, this.domain);
    if (p.length === 1) return I.rscalarmul(first(p));
    let pA = I.rscalarmul(first(p));
    for (const pi of p.slice(1)) pA = opAdd(opMul(this, pA), I.rscalarmul(pi));
    return pA;
  }
  /**
   * Evaluates a matrix polynomial and multiplies its value by the matrix on the right.
   *
   * @param p - Polynomial coefficients in descending degree.
   * @param B - Matrix to combine with this one.
   * @returns The matrix polynomial times the right-hand factor.
   * @throws DMNonSquareMatrixError when the matrix is not square.
   * @throws DMShapeError when the matrix dimensions are incompatible with the operation.
   * @throws DMDomainError when the coefficient domains are incompatible with the operation.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.eval_poly_mul`
   */
  evalPolyMul(p: readonly Expr[], B: DomainMatrix): DomainMatrix {
    if (!this.isSquare) throw new DMNonSquareMatrixError('Matrix must be square');
    if (B.shape[0] !== this.shape[1]) throw new DMShapeError('Matrices are not aligned');
    if (!this.domain.equals(B.domain)) throw new DMDomainError('Matrices must have the same domain');
    if (!p.length) return DomainMatrix.zeros(B.shape, B.domain);
    let pAB = B.rscalarmul(first(p));
    for (const pi of p.slice(1)) pAB = opAdd(opMul(this, pAB), B.rscalarmul(pi));
    return pAB;
  }
  /**
   * LU decomposition over a field: [L, U, swaps].
   *
   * @returns The lower and upper factors and row interchanges.
   * @throws DMNotAField when the operation requires a coefficient field.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.lu`
   */
  lu(): [DomainMatrix, DomainMatrix, [number, number][]] {
    if (!this.domain.isField) throw new DMNotAField('Not a field');
    const [L, U, swaps] = this.rep.lu();
    return [this.fromRep(L), this.fromRep(U), swaps];
  }
  /**
   * QR decomposition (Gram-Schmidt with unnormalized columns): [Q, R].
   *
   * @returns The orthogonal and upper triangular factors.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.qr`
   */
  qr(): [DomainMatrix, DomainMatrix] {
    const [Q, R] = this.rep.qr();
    return [this.fromRep(Q), this.fromRep(R)];
  }
  /**
   * Solve self*x = rhs over a field by LU decomposition.
   *
   * @param rhs - Right-hand side of the matrix equation.
   * @returns The solution of the matrix equation.
   * @throws DMShapeError when the matrix dimensions are incompatible with the operation.
   * @throws DMNotAField when the operation requires a coefficient field.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.lu_solve`
   */
  luSolve(rhs: DomainMatrix): DomainMatrix {
    if (this.shape[0] !== rhs.shape[0]) throw new DMShapeError('Shape');
    if (!this.domain.isField) throw new DMNotAField('Not a field');
    return this.fromRep(this.rep instanceof SDM ? this.rep.luSolve(rhs.toSdm()) : this.rep.luSolve(rhs.toDdm()));
  }
  /**
   * Fraction-free LU decomposition P*A = L*D**-1*U: [P, L, D, U].
   *
   * @returns The permutation, lower, diagonal and upper factors.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.fflu`
   */
  fflu(): [DomainMatrix, DomainMatrix, DomainMatrix, DomainMatrix] {
    const [P, L, D, U] = this.rep.fflu();
    return [this.fromRep(P), this.fromRep(L), this.fromRep(D), this.fromRep(U)];
  }
  /**
   * The characteristic polynomial coefficients from the highest degree.
   *
   * @returns The characteristic coefficients in descending degree.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.charpoly`
   */
  charpoly(): Expr[] {
    const K = this.domain;
    let cp: Expr[] = [K.one];
    for (const [f, mult] of this.charpolyFactorBlocks()) for (let k = 0; k < mult; k++) cp = dupMul(cp, f, K);
    return cp;
  }
  /**
   * The irreducible factors of the characteristic polynomial with their multiplicities.
   *
   * @returns The irreducible factors with their multiplicities.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.charpoly_factor_list`
   */
  charpolyFactorList(): DomainFactor[] {
    const K = this.domain;
    const out: DomainFactor[] = [];
    for (const [fi, mi] of this.charpolyFactorBlocks()) for (const [fj, mj] of dupFactorList(fi, K)) out.push([fj, mi * mj]);
    return collectFactors(out, K);
  }
  /**
   * The characteristic polynomials of the diagonal blocks (strongly connected components), with
   * multiplicities.
   *
   * @returns The block factors with their multiplicities.
   * @throws DMNonSquareMatrixError when the matrix is not square.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.charpoly_factor_blocks`
   */
  charpolyFactorBlocks(): DomainFactor[] {
    if (!this.isSquare) throw new DMNonSquareMatrixError('not square');
    return collectFactors(
      this.scc().map((idx) => [this.extract(idx, idx).charpolyBase(), 1]),
      this.domain,
    );
  }
  /**
   * The characteristic polynomial without the block decomposition (denominators cleared first over
   * QQ).
   *
   * @returns The characteristic coefficients in descending degree.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.charpoly_base`
   */
  charpolyBase(): Expr[] {
    const K = this.domain;
    const density = this.nnz() / this.shape[0] ** 2;
    let M: DomainMatrix = density < 0.5 ? this.toSparse() : this.toDense();
    if (!(K.isField && hasAssocRing(K))) return M.charpolyBerk();
    const [dS, Mr] = M.clearDenoms(true);
    M = Mr;
    const d = dS.element;
    const cp = M.charpolyBerk().map((c) => convertFrom(K, c, M.domain));
    // cp(x) -> d**-n * cp(d*x): coefficient i divided by d**i
    const dinv = K.quo(K.one, convertFrom(K, d, dS.domain));
    let s = K.one;
    return cp.map((c) => {
      const r = K.mul(c, s);
      s = K.mul(s, dinv);
      return r;
    });
  }
  /**
   * The characteristic polynomial by Berkowitz's algorithm on the representation.
   *
   * @returns The characteristic coefficients in descending degree.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.charpoly_berk`
   */
  charpolyBerk(): Expr[] {
    return this.rep.charpoly();
  }
  /**
   * The identity matrix (sparse).
   *
   * @param shape - Row and column counts.
   * @param domain - Coefficient domain for the values.
   * @returns An identity matrix of the given shape.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.eye`
   */
  static eye(shape: number | Shape, domain: Domain): DomainMatrix {
    return new DomainMatrix(SDM.eye(typeof shape === 'number' ? [shape, shape] : shape, domain));
  }
  /**
   * The diagonal matrix of the elements (sparse).
   *
   * @param diagonal - Entries on the main diagonal.
   * @param domain - Coefficient domain for the values.
   * @param shape - Row and column counts.
   * @returns The matrix with the specified diagonal.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.diag`
   */
  static diag(diagonal: readonly Expr[], domain: Domain, shape?: Shape): DomainMatrix {
    return new DomainMatrix(SDM.diag(diagonal, domain, shape));
  }
  /**
   * The zero matrix (sparse).
   *
   * @param shape - Row and column counts.
   * @param domain - Coefficient domain for the values.
   * @returns A zero matrix of the specified shape.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.zeros`
   */
  static zeros(shape: Shape, domain: Domain): DomainMatrix {
    return new DomainMatrix(SDM.zeros(shape, domain));
  }
  /**
   * The matrix of ones (dense).
   *
   * @param shape - Row and column counts.
   * @param domain - Coefficient domain for the values.
   * @returns A matrix filled with ones.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.ones`
   */
  static ones(shape: Shape, domain: Domain): DomainMatrix {
    return new DomainMatrix(DDM.ones(shape, domain));
  }
  /**
   * Equal domains, formats and elements.
   *
   * @param B - Value to compare against.
   * @returns Whether the operands are equal.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.__eq__`
   */
  equals(B: unknown): boolean {
    return B instanceof DomainMatrix && this.domain.equals(B.domain) && this.rep.equals(B.rep);
  }
  /**
   * Equal after unifying the domains (formats must agree).
   *
   * @param B - Matrix to combine with this one.
   * @returns Whether the matrices compare equal over a common domain.
   * @see SymPy `sympy.polys.matrices.domainmatrix.DomainMatrix.unify_eq`
   */
  unifyEq(B: DomainMatrix): boolean {
    if (String(this.shape) !== String(B.shape)) return false;
    const [A1, B1] = this.unify(B);
    return defined(A1).equals(B1);
  }
}

/**
 * The dense DomainMatrix of rows of values converted to the domain.
 *
 * @param rows - Entries grouped by row.
 * @param domain - Target coefficient domain.
 * @returns A dense matrix over the given domain.
 * @see SymPy `sympy.polys.matrices.domainmatrix.DM`
 * @example
 * ```ts
 * import { DM, ZZ } from '@symjs/symjs';
 *
 * DM([[1, 2], [3, 4]], ZZ).toString(); // => DomainMatrix([[1, 2], [3, 4]], (2, 2), ZZ)
 * ```
 */
export function DM(rows: readonly (readonly ExprLike[])[], domain: Domain): DomainMatrix {
  return DomainMatrix.fromList(rows, domain);
}

/** A*B of DomainMatrices (SymPy __mul__: domains unified, dense if the formats differ). */
function opMul(A: DomainMatrix, B: DomainMatrix): DomainMatrix {
  const [a, b] = A.unifyFmt([B], 'dense');
  return defined(a).matmul(defined(b));
}

/** A+B of DomainMatrices (SymPy __add__). */
function opAdd(A: DomainMatrix, B: DomainMatrix): DomainMatrix {
  const [a, b] = A.unifyFmt([B], 'dense');
  return defined(a).add(defined(b));
}

// ---- dense univariate polynomial helpers (densearith, densetools, factortools) ----

/** SymPy dup_mul. */
function dupMul(f: readonly Expr[], g: readonly Expr[], K: Domain): Expr[] {
  const out = Array.from({ length: f.length + g.length - 1 }, () => K.zero);
  f.forEach((a, i) => g.forEach((b, j) => (out[i + j] = K.add(at(out, i + j), K.mul(a, b)))));
  return out;
}

/** SymPy dup_content: the gcd of the coefficients. */
function dupContent(f: readonly Expr[], K: Domain): Expr {
  let cont = K.zero;
  for (const c of f) {
    cont = gcd(K, cont, c);
    if (!isQQ(K) && K.isOne(cont)) break;
  }
  return cont;
}

/** SymPy dup_quo_ground: f // c (exact division in a field). */
function dupQuoGround(f: readonly Expr[], c: Expr, K: Domain): Expr[] {
  return f.map((cf) => (K.isField ? K.quo(cf, c) : quo(K, cf, c)));
}

/** SymPy dup_primitive: [content, f/content]. */
function dupPrimitive(f: readonly Expr[], K: Domain): [Expr, Expr[]] {
  if (!f.length) return [K.zero, []];
  const cont = dupContent(f, K);
  return K.isOne(cont) ? [cont, [...f]] : [cont, dupQuoGround(f, cont, K)];
}

/** SymPy dup_clear_denoms: [common denominator, f times it] (converted to the ring K1 with convert). */
function dupClearDenoms(f: readonly Expr[], K0: Domain, K1: Domain, convert: boolean): [Expr, Expr[]] {
  let common = K1.one;
  for (const c of f) common = lcm(K1, common, denom(K0, c));
  const g = K1.isOne(common) ? [...f] : f.map((c) => K0.mul(c, convertFrom(K0, common, K1)));
  return [common, convert ? g.map((c) => convertFrom(K1, c, K0)) : g];
}

/** SymPy dup_factor_list over ZZ or QQ: the factors (primitive over ZZ, with a positive leading coefficient) and multiplicities. */
function dupFactorList(f: readonly Expr[], K: Domain): DomainFactor[] {
  if (!(isZZ(K) || isQQ(K))) throw new NotImplementedError(`factorization over ${K.toString()}`);
  const x = new Dummy('x');
  const n = f.length - 1;
  const [, Fz] = dupClearDenoms(f, K, ZZ, true);
  const e = add(...Fz.map((c, i) => mul(c, pow(x, n - i))));
  const [, factors] = Poly.from(e, [x], { domain: 'ZZ' }).factorList();
  return factors.map(([p, k]) => [p.allCoeffs().map((c) => K.fromSympy(c)), k]);
}

/** Lexicographic order of two different coefficient lists of ZZ or QQ of the same length. */
function cmpCoeffs(a: readonly Expr[], b: readonly Expr[]): number {
  // the lists have the same length and differ (equal factors were merged)
  const i = a.findIndex((c, k) => !elemEq(c, at(b, k)));
  const [x, y] = [rat(at(a, i)), rat(at(b, i))];
  return x.p * y.q < y.p * x.q ? -1 : 1;
}

/** SymPy _collect_factors: equal factors merged (multiplicities added), sorted by (degree, multiplicity, coefficients). */
function collectFactors(factors: readonly DomainFactor[], K: Domain): DomainFactor[] {
  const out: DomainFactor[] = [];
  for (const [f, e] of factors) {
    const key = f.map((c) => elemStr(K, c)).join(',');
    const found = out.find(([g]) => g.map((c) => elemStr(K, c)).join(',') === key);
    if (found) found[1] += e;
    else out.push([[...f], e]);
  }
  return out.sort((a, b) => a[0].length - b[0].length || a[1] - b[1] || cmpCoeffs(a[0], b[0]));
}

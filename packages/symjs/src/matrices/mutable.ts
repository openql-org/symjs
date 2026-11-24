// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy MutableDenseMatrix: a matrix changed in place. Matrix itself
 * is immutable (SymPy ImmutableDenseMatrix); sympify turns a mutable
 * matrix into an immutable copy, as SymPy does.
 */

import type { Expr, ExprLike } from '../core/nodes';
import { add, mul, sympify } from '../core/ops';
import { sympifyMethod } from '../core/sympify';
import { Matrix } from './matrix';

/**
 * A matrix whose entries can be changed in place.
 * @see SymPy `sympy.matrices.dense.MutableDenseMatrix`
 */
export class MutableDenseMatrix extends Matrix {
  /**
   * Gets the priority for choosing the result class in mixed matrix operations.
   * @returns The priority for choosing the result class in mixed matrix operations.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix._class_priority`
   */
  override get classPriority(): number { return 4; }
  readonly #cells: Expr[];

  protected constructor(rows: number, cols: number, cells: Expr[]) {
    super(rows, cols, cells);
    this.#cells = cells;
  }

  /**
   * Returns a mutable copy of m.
   * @param m - The input matrix.
   * @returns A mutable copy of m.
   */
  static from(m: Matrix): MutableDenseMatrix {
    return new MutableDenseMatrix(m.rows, m.cols, [...m.data]);
  }
  /**
   * Builds a mutable dense matrix from rows of entries.
   * @param rows - The rows of entries.
   * @returns A mutable matrix containing the supplied rows.
   */
  static override of(rows: readonly (readonly ExprLike[])[]): MutableDenseMatrix {
    return MutableDenseMatrix.from(Matrix.of(rows));
  }
  /**
   * Builds a mutable matrix by evaluating a function at each row and column index.
   * @param rows - The number of rows.
   * @param cols - The number of columns.
   * @param f - Computes the entry at the given row and column indices.
   * @returns A mutable matrix with entry `f(i, j)` at each position.
   */
  static override fromFunction(rows: number, cols: number, f: (i: number, j: number) => ExprLike): MutableDenseMatrix {
    return MutableDenseMatrix.from(Matrix.fromFunction(rows, cols, f));
  }
  /**
   * Returns a matrix of zeros.
   * @param rows - The number of rows.
   * @param cols - The number of columns.
   * @returns A matrix of zeros.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.zeros`
   */
  static override zeros(rows: number, cols = rows): MutableDenseMatrix {
    return MutableDenseMatrix.from(Matrix.zeros(rows, cols));
  }
  /**
   * Returns an identity matrix.
   * @param n - The order of the square matrix.
   * @returns An identity matrix.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.eye`
   */
  static override eye(n: number): MutableDenseMatrix {
    return MutableDenseMatrix.from(Matrix.eye(n));
  }

  /**
   * Set the entry at (i, j).
   * @param iIn - The zero-based row index.
   * @param jIn - The zero-based column index.
   * @param v - The replacement entry.
   * @throws RangeError when an index is out of bounds.
   */
  set(iIn: number, jIn: number, v: ExprLike): void {
    let i = iIn;
    let j = jIn;
    if (i < 0) i += this.rows;
    if (j < 0) j += this.cols;
    if (i < 0 || i >= this.rows || j < 0 || j >= this.cols) throw new RangeError(`index (${i}, ${j}) out of range`);
    this.#cells[i * this.cols + j] = sympify(v);
  }
  /**
   * Copy the entries of m into the block starting at (i, j).
   * @param i - The zero-based row index.
   * @param j - The zero-based column index.
   * @param m - The input matrix.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.copyin_matrix`
   */
  copyinMatrix(i: number, j: number, m: Matrix): void {
    for (let r = 0; r < m.rows; r++) for (let c = 0; c < m.cols; c++) this.set(i + r, j + c, m.get(r, c));
  }
  /**
   * Set every entry to v.
   * @param v - The replacement entry.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.fill`
   */
  fill(v: ExprLike): void {
    this.#cells.fill(sympify(v));
  }
  /**
   * Swap two rows in place.
   * @param i - The zero-based row index.
   * @param j - The zero-based column index.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.row_swap`
   */
  rowSwap(i: number, j: number): void {
    for (let c = 0; c < this.cols; c++) {
      const t = this.get(i, c);
      this.set(i, c, this.get(j, c));
      this.set(j, c, t);
    }
  }
  /**
   * Swap two columns in place.
   * @param i - The zero-based row index.
   * @param j - The zero-based column index.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.col_swap`
   */
  colSwap(i: number, j: number): void {
    for (let r = 0; r < this.rows; r++) {
      const t = this.get(r, i);
      this.set(r, i, this.get(r, j));
      this.set(r, j, t);
    }
  }
  /**
   * Row i entries replaced by f(value, column).
   * @param i - The zero-based row index.
   * @param f - The function computing each replacement entry.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.row_op`
   */
  rowOp(i: number, f: (v: Expr, j: number) => ExprLike): void {
    for (let c = 0; c < this.cols; c++) this.set(i, c, f(this.get(i, c), c));
  }
  /**
   * Column j entries replaced by f(value, row).
   * @param j - The zero-based column index.
   * @param f - The function computing each replacement entry.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.col_op`
   */
  colOp(j: number, f: (v: Expr, i: number) => ExprLike): void {
    for (let r = 0; r < this.rows; r++) this.set(r, j, f(this.get(r, j), r));
  }
  /**
   * Row i entries replaced by f(value, value in row k).
   * @param i - The zero-based row index.
   * @param k - The index of the selected element.
   * @param f - The function computing each replacement entry.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.zip_row_op`
   */
  zipRowOp(i: number, k: number, f: (v: Expr, u: Expr) => ExprLike): void {
    for (let c = 0; c < this.cols; c++) this.set(i, c, f(this.get(i, c), this.get(k, c)));
  }
  /**
   * Add k times row s to row t.
   * @param s - The input sequence.
   * @param t - The rotation angle in radians.
   * @param k - The index of the selected element.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.row_add`
   */
  rowAdd(s: number, t: number, k: ExprLike): void {
    for (let c = 0; c < this.cols; c++) this.set(t, c, add(this.get(t, c), mul(k, this.get(s, c))));
  }
  /**
   * Multiply row i by k.
   * @param i - The zero-based row index.
   * @param k - The index of the selected element.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.row_mult`
   */
  rowMult(i: number, k: ExprLike): void {
    for (let c = 0; c < this.cols; c++) this.set(i, c, mul(k, this.get(i, c)));
  }
  /**
   * Copy a list into the block starting at (i, j): a
   * flat list fills a column, a nested list fills rows.
   * @param i - The zero-based row index.
   * @param j - The zero-based column index.
   * @param values - The entries to copy into the selected positions.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.copyin_list`
   */
  copyinList(i: number, j: number, values: readonly ExprLike[] | readonly (readonly ExprLike[])[]): void {
    const items: readonly (ExprLike | readonly ExprLike[])[] = values;
    const rows = items.map((v): readonly ExprLike[] => (isRow(v) ? v : [v]));
    this.copyinMatrix(i, j, Matrix.of(rows));
  }
  /**
   * Delete row i in place.
   * @param i - The zero-based row index.
   * @throws RangeError when the row index is out of bounds.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.row_del`
   */
  rowDel(i: number): void {
    const r = i < 0 ? i + this.rows : i;
    if (r < 0 || r >= this.rows) throw new RangeError(`Row ${r} is out of range.`);
    this.#cells.splice(r * this.cols, this.cols);
    this.reshapeInPlace(this.rows - 1, this.cols);
  }
  /**
   * Delete column j in place.
   * @param j - The zero-based column index.
   * @throws RangeError when the column index is out of bounds.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.col_del`
   */
  colDel(j: number): void {
    const c = j < 0 ? j + this.cols : j;
    if (c < 0 || c >= this.cols) throw new RangeError(`Column ${c} is out of range.`);
    for (let r = this.rows - 1; r >= 0; r--) this.#cells.splice(r * this.cols + c, 1);
    this.reshapeInPlace(this.rows, this.cols - 1);
  }
  /**
   * Returns a mutable copy.
   * @returns A mutable copy.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.copy`
   */
  override copy(): MutableDenseMatrix {
    return MutableDenseMatrix.from(this);
  }
  /**
   * Returns a mutable copy.
   * @returns A mutable copy.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.as_mutable`
   */
  asMutable(): MutableDenseMatrix {
    return MutableDenseMatrix.from(this);
  }
  /**
   * An immutable copy.
   * @returns The resulting matrix.
   * @see SymPy `sympy.matrices.dense.MutableDenseMatrix.as_immutable`
   */
  asImmutable(): Matrix {
    return Matrix.of(this.toArray());
  }
  /** Returns an immutable copy of this matrix when converting it to a symbolic expression. */
  override [sympifyMethod](): Matrix {
    return this.asImmutable();
  }
}

/**
 * An alias for the mutable dense matrix class.
 * @see SymPy `sympy.matrices.dense.MutableDenseMatrix`
 */
export const MutableMatrix = MutableDenseMatrix;

const isRow = (v: ExprLike | readonly ExprLike[]): v is readonly ExprLike[] => Array.isArray(v);

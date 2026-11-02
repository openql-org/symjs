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

/** A matrix whose entries can be changed in place (SymPy MutableDenseMatrix). */
export class MutableDenseMatrix extends Matrix {
  readonly #cells: Expr[];

  private constructor(rows: number, cols: number, cells: Expr[]) {
    super(rows, cols, cells);
    this.#cells = cells;
  }

  /** A mutable copy of m. */
  static from(m: Matrix): MutableDenseMatrix {
    return new MutableDenseMatrix(m.rows, m.cols, [...m.data]);
  }
  static override of(rows: readonly (readonly ExprLike[])[]): MutableDenseMatrix {
    return MutableDenseMatrix.from(Matrix.of(rows));
  }
  static override fromFunction(rows: number, cols: number, f: (i: number, j: number) => ExprLike): MutableDenseMatrix {
    return MutableDenseMatrix.from(Matrix.fromFunction(rows, cols, f));
  }
  static override zeros(rows: number, cols = rows): MutableDenseMatrix {
    return MutableDenseMatrix.from(Matrix.zeros(rows, cols));
  }
  static override eye(n: number): MutableDenseMatrix {
    return MutableDenseMatrix.from(Matrix.eye(n));
  }

  /** Set the entry at (i, j) (SymPy M[i, j] = v). */
  set(iIn: number, jIn: number, v: ExprLike): void {
    let i = iIn;
    let j = jIn;
    if (i < 0) i += this.rows;
    if (j < 0) j += this.cols;
    if (i < 0 || i >= this.rows || j < 0 || j >= this.cols) throw new RangeError(`index (${i}, ${j}) out of range`);
    this.#cells[i * this.cols + j] = sympify(v);
  }
  /** Copy the entries of m into the block starting at (i, j) (SymPy copyin_matrix). */
  copyinMatrix(i: number, j: number, m: Matrix): void {
    for (let r = 0; r < m.rows; r++) for (let c = 0; c < m.cols; c++) this.set(i + r, j + c, m.get(r, c));
  }
  /** Set every entry to v (SymPy fill). */
  fill(v: ExprLike): void {
    this.#cells.fill(sympify(v));
  }
  /** Swap two rows in place (SymPy row_swap). */
  rowSwap(i: number, j: number): void {
    for (let c = 0; c < this.cols; c++) {
      const t = this.get(i, c);
      this.set(i, c, this.get(j, c));
      this.set(j, c, t);
    }
  }
  /** Swap two columns in place (SymPy col_swap). */
  colSwap(i: number, j: number): void {
    for (let r = 0; r < this.rows; r++) {
      const t = this.get(r, i);
      this.set(r, i, this.get(r, j));
      this.set(r, j, t);
    }
  }
  /** Row i entries replaced by f(value, column) (SymPy row_op). */
  rowOp(i: number, f: (v: Expr, j: number) => ExprLike): void {
    for (let c = 0; c < this.cols; c++) this.set(i, c, f(this.get(i, c), c));
  }
  /** Column j entries replaced by f(value, row) (SymPy col_op). */
  colOp(j: number, f: (v: Expr, i: number) => ExprLike): void {
    for (let r = 0; r < this.rows; r++) this.set(r, j, f(this.get(r, j), r));
  }
  /** Row i entries replaced by f(value, value in row k) (SymPy zip_row_op). */
  zipRowOp(i: number, k: number, f: (v: Expr, u: Expr) => ExprLike): void {
    for (let c = 0; c < this.cols; c++) this.set(i, c, f(this.get(i, c), this.get(k, c)));
  }
  /** Add k times row s to row t (SymPy row_add). */
  rowAdd(s: number, t: number, k: ExprLike): void {
    for (let c = 0; c < this.cols; c++) this.set(t, c, add(this.get(t, c), mul(k, this.get(s, c))));
  }
  /** Multiply row i by k (SymPy row_mult). */
  rowMult(i: number, k: ExprLike): void {
    for (let c = 0; c < this.cols; c++) this.set(i, c, mul(k, this.get(i, c)));
  }
  /**
   * Copy a list into the block starting at (i, j) (SymPy copyin_list): a
   * flat list fills a column, a nested list fills rows.
   */
  copyinList(i: number, j: number, values: readonly ExprLike[] | readonly (readonly ExprLike[])[]): void {
    const items: readonly (ExprLike | readonly ExprLike[])[] = values;
    const rows = items.map((v): readonly ExprLike[] => (isRow(v) ? v : [v]));
    this.copyinMatrix(i, j, Matrix.of(rows));
  }
  /** An immutable copy (SymPy as_immutable). */
  asImmutable(): Matrix {
    return Matrix.of(this.toArray());
  }
  /** sympify gives an immutable copy, as in SymPy. */
  override [sympifyMethod](): Matrix {
    return this.asImmutable();
  }
}

/** SymPy alias. */
export const MutableMatrix = MutableDenseMatrix;

const isRow = (v: ExprLike | readonly ExprLike[]): v is readonly ExprLike[] => Array.isArray(v);

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/matrices/sparse.py, sympy/matrices/immutable.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sparse matrices: MutableSparseMatrix (SparseMatrix) and
 * ImmutableSparseMatrix, built from the nonzero entries. They store their
 * entries like the dense matrices and print like SymPy, `Matrix([...])`.
 */

import type { ExprLike } from '../core/nodes';
import type { Expr } from '../core/nodes';
import { Float, Rational } from '../core/nodes';
import { sympify } from '../core/ops';
import { at } from '../core/guard';
import { ImmutableMatrixNode } from './expressions/matexpr';
import { Matrix, type MatrixPosition } from './matrix';
import { MutableDenseMatrix } from './mutable';

export type { MatrixPosition } from './matrix';
/** A value of the dictionary form: an entry, a matrix (expanded as a block) or a list of entries or rows (likewise). */
export type SparseValue = ExprLike | Matrix | readonly (ExprLike | readonly ExprLike[])[];
/** The entries of a sparse matrix: a generator f(i, j), a map position -> value, a flat list or a list of rows. */
export type SparseData = ((i: number, j: number) => ExprLike) | ReadonlyMap<MatrixPosition, SparseValue> | readonly (ExprLike | readonly ExprLike[])[];
/**
 * The constructor forms of SymPy's sparse matrices: `()`, `(matrix)`,
 * `(rows)` (a possibly ragged list of rows, or a list of entries of a
 * column), `(rows, cols, data)` and `(null, data)` (the size is that of the
 * data).
 */
export type SparseMatrixArgs = [] | [Matrix] | [readonly (ExprLike | readonly ExprLike[])[]] | [number, number, SparseData] | [null, SparseData] | [null, null, SparseData];

/** The nonzero entries keyed by "i,j". */
type Smat = Map<string, { i: number; j: number; v: Expr }>;

/** SymPy `value != 0` for a sympified entry (structural). */
const isZeroEntry = (v: Expr): boolean => (v instanceof Rational || v instanceof Float) && v.isZero;

const isRowList = (v: SparseValue | ExprLike): v is readonly (ExprLike | readonly ExprLike[])[] => Array.isArray(v);
const isPositionMap = (d: SparseData): d is ReadonlyMap<MatrixPosition, SparseValue> => d instanceof Map;

/** The nonzero entries of a list of rows (a non-list item is a row of one entry). */
function fromRows(v: readonly (ExprLike | readonly ExprLike[])[]): { rows: number; cols: number; smat: Smat } {
  const smat: Smat = new Map();
  let c = 0;
  v.forEach((rowIn, i) => {
    const row: readonly ExprLike[] = isRowList(rowIn) ? rowIn : [rowIn];
    row.forEach((vv, j) => {
      const e = sympify(vv);
      if (!isZeroEntry(e)) smat.set(`${i},${j}`, { i, j, v: e });
    });
    c = Math.max(c, row.length);
  });
  return { rows: c ? v.length : 0, cols: c, smat };
}

/** SymPy SparseRepMatrix._handle_creation_inputs: the shape and the nonzero entries. */
function handleCreationInputs(args: SparseMatrixArgs): { rows: number; cols: number; smat: Smat } {
  if (args.length === 0) return { rows: 0, cols: 0, smat: new Map() };
  if (args.length === 1) {
    const [a] = args;
    if (a instanceof Matrix) {
      const smat: Smat = new Map();
      for (let i = 0; i < a.rows; i++) for (let j = 0; j < a.cols; j++) if (!isZeroEntry(a.get(i, j))) smat.set(`${i},${j}`, { i, j, v: a.get(i, j) });
      return { rows: a.rows, cols: a.cols, smat };
    }
    return fromRows(a);
  }
  // autosizing
  const data = args.length === 2 ? args[1] : args[2];
  const dims = args.length === 3 && args[0] !== null ? { r: args[0], c: args[1] } : undefined;
  const smat: Smat = new Map();
  if (typeof data === 'function') {
    if (dims === undefined) throw new RangeError('null and null must be integers for this specification.');
    const { r, c } = dims;
    for (let i = 0; i < r; i++) {
      for (let j = 0; j < c; j++) {
        const value = sympify(data(i, j));
        if (!isZeroEntry(value)) smat.set(`${i},${j}`, { i, j, v: value });
      }
    }
    return { rows: r, cols: c, smat };
  }
  if (isPositionMap(data)) {
    const update = (i: number, j: number, v: Expr): void => {
      if (isZeroEntry(v)) return;
      const old = smat.get(`${i},${j}`);
      if (old !== undefined && old.v.key !== v.key) throw new RangeError(`There is a collision at (${i}, ${j}) for ${String(v)} and ${String(old.v)}.`);
      smat.set(`${i},${j}`, { i, j, v });
    };
    for (const [[r0, c0], v] of data) {
      if (v instanceof Matrix || isRowList(v)) {
        const block = v instanceof Matrix ? handleCreationInputs([v]) : fromRows(v);
        for (const e of block.smat.values()) update(r0 + e.i, c0 + e.j, e.v);
      } else update(r0, c0, sympify(v));
    }
  } else {
    const flat: ExprLike[] = [];
    let nested = false;
    for (const item of data) {
      if (isRowList(item)) nested = true;
      else flat.push(item);
    }
    if (nested) return sizedResult(dims, fromRows(data).smat);
    if (dims === undefined) throw new RangeError('null and null must be integers for a flat list.');
    const { r, c } = dims;
    if (data.length !== r * c) throw new RangeError(`The length of the flat list (${data.length}) does not match the specified size (${r} * ${c}).`);
    for (let i = 0; i < r; i++) {
      for (let j = 0; j < c; j++) {
        const value = sympify(at(flat, i * c + j));
        if (!isZeroEntry(value)) smat.set(`${i},${j}`, { i, j, v: value });
      }
    }
  }
  return sizedResult(dims, smat);
}

/** The shape (that of the entries when autosizing) after checking that the entries lie inside it. */
function sizedResult(dims: { r: number; c: number } | undefined, smat: Smat): { rows: number; cols: number; smat: Smat } {
  if (dims === undefined) {
    const keys = [...smat.values()];
    return { rows: keys.length ? Math.max(...keys.map((e) => e.i)) + 1 : 0, cols: keys.length ? Math.max(...keys.map((e) => e.j)) + 1 : 0, smat };
  }
  const { r, c } = dims;
  for (const { i, j } of smat.values()) {
    if ((i > 0 && i >= r) || (j > 0 && j >= c)) throw new RangeError(`The location (${i}, ${j}) is out of the designated range[0, ${r - 1}]x[0, ${c - 1}]`);
  }
  return { rows: r, cols: c, smat };
}

/** The row-major entries of a sparse specification. */
function denseEntries(args: SparseMatrixArgs): { rows: number; cols: number; cells: Expr[] } {
  const { rows, cols, smat } = handleCreationInputs(args);
  const cells: Expr[] = Array.from({ length: rows * cols }, () => sympify(0));
  for (const { i, j, v } of smat.values()) cells[i * cols + j] = v;
  return { rows, cols, cells };
}

/**
 * SymPy MutableSparseMatrix (SparseMatrix): a mutable matrix built from its
 * nonzero entries, e.g. `new SparseMatrix(2, 2, new Map([[[1, 1], 2]]))`,
 * `new SparseMatrix([[1, 2, 3], [1, 2], [1]])` (ragged rows are padded with
 * zeros) or `new SparseMatrix(null, new Map([[[3, 3], 3]]))` (sized by the
 * entries). A matrix value of the map is a block placed at its position.
 */
export class MutableSparseMatrix extends MutableDenseMatrix {
  constructor(...args: SparseMatrixArgs) {
    const { rows, cols, cells } = denseEntries(args);
    super(rows, cols, cells);
  }
}

/** SymPy SparseMatrix, an alias of MutableSparseMatrix. */
export const SparseMatrix = MutableSparseMatrix;
export type SparseMatrix = MutableSparseMatrix;

/**
 * SymPy ImmutableSparseMatrix: an immutable explicit matrix (a matrix
 * expression, like ImmutableMatrix) built from its nonzero entries, with the
 * constructor forms of {@link MutableSparseMatrix}.
 */
export class ImmutableSparseMatrix extends ImmutableMatrixNode {
  constructor(...args: SparseMatrixArgs) {
    const m = new MutableSparseMatrix(...args);
    super(Matrix.fromFunction(m.rows, m.cols, (i, j) => m.get(i, j)));
  }

  /** SymPy todok(): the nonzero entries by position. */
  todok(): Map<MatrixPosition, Expr> {
    return this.matrix.todok();
  }
}

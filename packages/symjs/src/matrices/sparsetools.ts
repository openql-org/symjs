// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy sympy.matrices.sparsetools: banded, a sparse matrix built from
 * its diagonals.
 */

import { at } from '../core/guard';
import { Expr, Float, Rational, type ExprLike } from '../core/nodes';
import { sympify } from '../core/sympify';
import { asInt, type IntLike } from '../ntheory/intutil';
import { Matrix, type MatrixPosition } from './matrix';
import { MutableSparseMatrix } from './sparse';

/**
 * The value of a diagonal of `banded`: a scalar repeated along it, a
 * function of the position on the diagonal, a list of entries (a nested
 * list is a block), or a matrix repeated as blocks along it.
 */
export type BandedValue = ExprLike | Matrix | ((i: number) => ExprLike) | readonly BandedEntry[];
/** An entry of a list diagonal: a scalar, or a block (a matrix or nested lists). */
export type BandedEntry = ExprLike | Matrix | readonly ExprLike[] | readonly (readonly ExprLike[])[];
/** The diagonals of `banded`, by offset (positive above the main diagonal). */
export type BandedDiagonals = ReadonlyMap<IntLike, BandedValue>;
/** The size of a `banded` matrix given by keyword (SymPy rows=, cols=). */
export interface BandedOptions {
  rows?: IntLike;
  cols?: IntLike;
}
/** The arguments of `banded`: [[rows,] cols,] diagonals, or diagonals with the size as options. */
export type BandedArgs = [BandedDiagonals] | [BandedDiagonals, BandedOptions] | [IntLike, BandedDiagonals] | [IntLike, IntLike, BandedDiagonals];

/** SymPy `value != 0` for a sympified entry (structural). */
const isZeroEntry = (v: Expr): boolean => (v instanceof Rational || v instanceof Float) && v.isZero;
const isEntryList = (v: BandedValue): v is readonly BandedEntry[] => Array.isArray(v);
const isRow = (v: ExprLike | readonly ExprLike[]): v is readonly ExprLike[] => Array.isArray(v);
const isBlock = (v: BandedEntry): v is Matrix | readonly ExprLike[] | readonly (readonly ExprLike[])[] => v instanceof Matrix || Array.isArray(v);
const isDiagonals = (v: BandedDiagonals | BandedOptions | IntLike): v is BandedDiagonals => v instanceof Map;
const isOptions = (v: BandedDiagonals | BandedOptions | IntLike | undefined): v is BandedOptions =>
  typeof v === 'object' && !(v instanceof Map) && !(v instanceof Expr);

function toMatrix(v: Matrix | readonly ExprLike[] | readonly (readonly ExprLike[])[]): Matrix {
  if (v instanceof Matrix) return v;
  // a flat list is a column, like SparseMatrix([1, 2])
  const rows: (readonly ExprLike[])[] = [];
  for (const r of v) rows.push(isRow(r) ? r : [r]);
  return Matrix.of(rows);
}

const badInput = (): TypeError => new TypeError('unrecognized input to banded: expecting [[row,] col,] {int: value}');

/**
 * A sparse matrix from its diagonals (SymPy banded), e.g.
 * `banded(new Map([[1, [1, 2, 3]], [-1, [4, 5, 6]], [0, x]]))`. Each key is
 * the offset of a diagonal; a scalar or a function of the position fills the
 * whole diagonal, a list gives its entries (nested lists and matrices are
 * blocks, the next entry follows the block), and a matrix value is repeated
 * as blocks as often as it fits. Without a size, the matrix is as large as
 * the lists and blocks need.
 */
export function banded(...args: BandedArgs): MutableSparseMatrix {
  let rows: number | undefined;
  let cols: number | undefined;
  const a: readonly (BandedDiagonals | BandedOptions | IntLike)[] = args;
  const int = (n: BandedDiagonals | BandedOptions | IntLike): number => {
    if (isDiagonals(n) || isOptions(n)) throw badInput();
    return Number(asInt(n));
  };
  const specIn = at(a, -1);
  const opts = a[1];
  if (a.length === 3) [rows, cols] = [int(at(a, 0)), int(at(a, 1))];
  else if (a.length === 2 && isOptions(opts)) [rows, cols] = [opts.rows === undefined ? undefined : int(opts.rows), opts.cols === undefined ? undefined : int(opts.cols)];
  else if (a.length === 2) rows = cols = int(at(a, 0));
  const diagonals = a.length === 2 && isOptions(opts) ? at(a, 0) : specIn;
  if (!isDiagonals(diagonals)) throw badInput();
  const spec = new Map([...diagonals].map(([k, v]) => [int(k), v]));

  const start = (d: number): [number, number] => (d < 0 ? [-d, 0] : [0, d]);
  const smat = new Map<string, { i: number; j: number; v: Expr | undefined }>();
  const put = (i: number, j: number, v: Expr | undefined): void => {
    if (v !== undefined && isZeroEntry(v)) return;
    const old = smat.get(`${i},${j}`);
    if (old?.v !== undefined && v !== undefined && old.v.key !== v.key) throw new RangeError(`collision at (${i}, ${j})`);
    smat.set(`${i},${j}`, { i, j, v: v ?? old?.v });
  };
  const putBlock = (r: number, c: number, M: Matrix): void => {
    for (let i = 0; i < M.rows; i++) for (let j = 0; j < M.cols; j++) put(r + i, c + j, M.get(i, j));
  };
  const undone: [number, (i: number) => ExprLike][] = [];
  // first the values with a size; a scalar or function diagonal is marked at its start (v undefined)
  for (const [d, v] of spec) {
    let [r, c] = start(d);
    if (isEntryList(v)) {
      let extra = 0;
      v.forEach((vi, i) => {
        const k = i + extra;
        if (isBlock(vi)) {
          const M = toMatrix(vi);
          putBlock(r + k, c + k, M);
          extra += Math.min(M.rows, M.cols) - 1;
        } else put(r + k, c + k, sympify(vi));
      });
    } else if (v instanceof Matrix) {
      const fit = (n: number, from: number, size: number): [number, number] => [Math.floor((n - from) / size), (n - from) % size];
      let times: number;
      let rest: number;
      if (rows !== undefined && cols !== undefined) {
        const [nr, xr] = fit(rows, r, v.rows);
        const [nc, xc] = fit(cols, c, v.cols);
        [times, rest] = [Math.min(nr, nc), xr || xc];
      } else if (rows !== undefined) [times, rest] = fit(rows, r, v.rows);
      else if (cols !== undefined) [times, rest] = fit(cols, c, v.cols);
      else [times, rest] = [1, 0];
      if (rest) throw new RangeError('sequence does not fit an integral number of times in the matrix');
      const step = Math.min(v.rows, v.cols);
      for (let i = 0; i < times; i++, r += step, c += step) putBlock(r, c, v);
    } else if (typeof v === 'function') {
      put(r, c, undefined);
      undone.push([d, v]);
    } else if (!isZeroEntry(sympify(v))) {
      put(r, c, undefined);
      undone.push([d, () => v]);
    }
  }
  const entries = [...smat.values()];
  const needRows = entries.length ? Math.max(...entries.map((e) => e.i)) + 1 : 0;
  const needCols = entries.length ? Math.max(...entries.map((e) => e.j)) + 1 : 0;
  if (rows !== undefined && rows < needRows) throw new RangeError(`Designated rows ${rows} < needed ${needRows}`);
  if (cols !== undefined && cols < needCols) throw new RangeError(`Designated cols ${cols} < needed ${needCols}`);
  const R = rows ?? (cols === undefined ? needRows : Math.max(cols, needRows));
  const C = cols ?? (rows === undefined ? needCols : Math.max(rows, needCols));
  for (const [d, f] of undone) {
    const [r, c] = start(d);
    for (let i = 0; r + i < R && c + i < C; i++) put(r + i, c + i, sympify(f(i)));
  }
  const data = new Map<MatrixPosition, Expr>();
  for (const { i, j, v } of smat.values()) if (v !== undefined) data.set([i, j], v);
  return new MutableSparseMatrix(R, C, data);
}

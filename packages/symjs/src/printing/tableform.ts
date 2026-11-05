// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/printing/tableform.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy's `TableForm`: a table of expressions printed as aligned
 * text (`toString`) or as a LaTeX tabular (`asLatex`), with optional row
 * and column headings.
 */

import type { Expr, ExprLike } from '../core/nodes';
import { Sym } from '../core/nodes';
import { sympify } from '../core/ops';
import { at } from '../core/guard';
import type { Matrix } from '../matrices/matrix';
import { latex } from './latex';
import { str } from './str';

/** A heading: 'automatic' (1, 2, ...), the labels, or none. */
export type TableHeading = 'automatic' | readonly (ExprLike | string)[] | null;

/** A column format: the LaTeX of an entry from the entry and its position, or undefined for the default. */
export type TableColumnFormat = ((x: Expr, i: number, j: number) => string | undefined) | null;

/** The options of {@link TableForm}. */
export interface TableFormOptions {
  /** 'automatic' or [row headings, column headings] (default none). */
  readonly headings?: 'automatic' | readonly [TableHeading, TableHeading];
  /** The alignment of every column ('l', 'r', 'c', 'left', '<', ...), or one letter per column ('rcl'; one more for the row headings). */
  readonly alignments?: string;
  /** The LaTeX format of each column (`asLatex`). */
  readonly formats?: readonly TableColumnFormat[];
  /** Print zeros as blanks (default true). */
  readonly wipeZeros?: boolean;
  /** The entry that fills short rows and replaces null entries (default: short rows are filled with blanks and null prints as None). */
  readonly pad?: string;
}

/** A table entry: an expression (numbers are sympified), a text (printed as it is, as a symbol of that name) or null. */
export type TableEntry = ExprLike | string | null;

/** The data of a table: rows of entries, or a matrix. */
export type TableData = readonly (readonly TableEntry[])[] | { readonly rows: number; readonly cols: number; get(i: number, j: number): Expr };

/** The matrix constructor, registered by the matrices entry point (matrices are a higher layer). */
let matrixOf: ((rows: readonly (readonly Expr[])[]) => Matrix) | undefined;

/** Registers the matrix constructor of {@link TableForm.asMatrix} (called by the matrices entry point). */
export function registerTableFormMatrix(f: (rows: readonly (readonly Expr[])[]) => Matrix): void {
  matrixOf = f;
}

/** SymPy `_std_align`: 'l', 'r' or 'c' for the spellings of an alignment. */
function stdAlign(a0: string): string {
  const a = a0.trim().toLowerCase();
  if (a.length > 1) return ({ left: 'l', right: 'r', center: 'c' } as Record<string, string>)[a] ?? a;
  return ({ '<': 'l', '>': 'r', '^': 'c' } as Record<string, string>)[a] ?? a;
}

/** Python's `str.center(width)`. */
function center(s: string, width: number): string {
  const marg = width - s.length;
  if (marg <= 0) return s;
  // eslint-like note: Python puts the odd space on the left when the width is odd
  const left = Math.floor(marg / 2) + (marg & width & 1);
  return ' '.repeat(left) + s + ' '.repeat(marg - left);
}

/** Python's `'%-Ns'` (left) or `'%Ns'` (right) formatting. */
const justify = (s: string, align: string, w: number): string => (align === 'l' ? s.padEnd(w) : s.padStart(w));

/** The text of a cell: str of the entry, None for a null entry. */
const cellText = (x: Expr | null): string => (x === null ? 'None' : str(x));

const label = (x: ExprLike | string): string => (typeof x === 'string' ? x : typeof x === 'number' || typeof x === 'bigint' ? String(x) : str(sympify(x)));

/**
 * SymPy `TableForm(data, headings=..., alignments=..., formats=..., wipe_zeros=..., pad=...)`:
 * a table that prints as aligned columns.
 *
 * ```
 * String(new TableForm([[5, 7], [4, 2], [10, 3]]))
 * // 5  7
 * // 4  2
 * // 10 3
 * ```
 */
export class TableForm {
  private readonly w: number;
  private readonly h: number;
  private readonly lines: readonly (readonly (Expr | null)[])[];
  private readonly rowHeadings: readonly string[] | undefined;
  private readonly colHeadings: readonly string[] | undefined;
  private readonly headAlign: string;
  private readonly alignments: readonly string[];
  private readonly formats: readonly TableColumnFormat[];
  private readonly wipeZeros: boolean;

  constructor(data: TableData, options: TableFormOptions = {}) {
    const rows: (readonly TableEntry[])[] = isRows(data) ? [...data] : matrixRows(data);
    this.h = rows.length;
    const padText = options.pad;
    const pad = new Sym(padText ?? ' ');
    this.w = Math.max(...rows.map((r) => r.length));
    const entry = (x: TableEntry): Expr | null => {
      // a null entry is the pad when one is given, else it prints as None
      if (x === null) return padText === undefined ? null : pad;
      // SymPy sympifies a text and makes a symbol of what is not an expression; it prints the same
      return typeof x === 'string' ? new Sym(x) : sympify(x);
    };
    this.lines = rows.map((r) => [...r.map(entry), ...Array<Expr | null>(this.w - r.length).fill(pad)]);
    const headings = options.headings ?? [null, null];
    const [h1, h2] = headings === 'automatic' ? ['automatic' as const, 'automatic' as const] : headings;
    const auto = (n: number): string[] => Array.from({ length: n }, (_, i) => String(i + 1));
    const heading = (hd: TableHeading, n: number): string[] | undefined => (hd === null || hd.length === 0 ? undefined : hd === 'automatic' ? auto(n) : hd.map(label));
    this.rowHeadings = heading(h1, this.h);
    this.colHeadings = heading(h2, this.w);
    const alignments = options.alignments ?? 'l';
    const one = stdAlign(alignments);
    let aligns: string[];
    if (['l', 'r', 'c'].includes(one)) aligns = Array<string>(this.w).fill(one);
    else {
      // one letter per column
      aligns = alignments.split('').map((a) => {
        const s = stdAlign(a);
        if (!['l', 'r', 'c'].includes(s)) throw new RangeError(`alignment "${alignments}" unrecognized`);
        return s;
      });
    }
    if (this.rowHeadings && aligns.length === this.w + 1) {
      this.headAlign = at(aligns, 0);
      aligns = aligns.slice(1);
    } else this.headAlign = 'r';
    if (aligns.length !== this.w) throw new RangeError(`wrong number of alignments: expected ${this.w} but got ${aligns.length}`);
    this.alignments = aligns;
    this.formats = options.formats ?? Array<TableColumnFormat>(this.w).fill(null);
    this.wipeZeros = options.wipeZeros ?? true;
  }

  /** SymPy `as_matrix`: the entries as a matrix. */
  asMatrix(): Matrix {
    if (matrixOf === undefined) throw new TypeError('TableForm.asMatrix needs the matrices: import @symjs/symjs/matrices');
    const entry = (x: Expr | null): Expr => {
      if (x === null) throw new TypeError('TableForm.asMatrix: a matrix has no None entry');
      return x;
    };
    return matrixOf(this.lines.map((line) => line.map(entry)));
  }

  /** SymPy `as_str`: the aligned text. */
  asStr(): string {
    return this.toString();
  }

  /** SymPy `as_latex`: a LaTeX tabular. */
  asLatex(): string {
    const alignments = [...(this.rowHeadings ? [this.headAlign] : []), ...this.alignments];
    let s = `\\begin{tabular}{${alignments.join(' ')}}\n`;
    if (this.colHeadings) s += `${[...(this.rowHeadings ? [''] : []), ...this.colHeadings].join(' & ')} \\\\\n\\hline\n`;
    this.lines.forEach((line, i) => {
      const d = line.map((x, j) => {
        if (this.wipeZeros && cellText(x) === '0') return ' ';
        const f = this.formats[j];
        const v = f && x !== null ? f(x, i, j) : undefined;
        return v ?? (f ? latex(x) : `$${latex(x)}$`);
      });
      s += `${[...(this.rowHeadings ? [at(this.rowHeadings, i)] : []), ...d].join(' & ')} \\\\\n`;
    });
    return `${s}\\end{tabular}`;
  }

  /** SymPy `_sympystr`: the columns padded to their widths, the headings separated by `|` and a rule. */
  toString(): string {
    const widths = Array<number>(this.w).fill(0);
    const lines = this.lines.map((line) =>
      line.map((x, i) => {
        let s = cellText(x);
        if (this.wipeZeros && s === '0') s = ' ';
        widths[i] = Math.max(at(widths, i), s.length);
        return s;
      }),
    );
    const rh = this.rowHeadings;
    const headWidth = rh ? Math.max(...rh.map((x) => x.length)) : 0;
    const ch = this.colHeadings;
    if (ch) ch.forEach((s, i) => (widths[i] = Math.max(at(widths, i), s.length)));
    const format = (cells: readonly string[], head: string | undefined): string => {
      const body = cells.map((c, j) => justify(c, at(this.alignments, j), at(widths, j)));
      return `${[...(head === undefined ? [] : [justify(head, this.headAlign, headWidth), '|']), ...body].join(' ')}\n`;
    };
    const out: string[] = [];
    if (ch) {
      const first = format(ch, rh ? '' : undefined);
      out.push(first, `${'-'.repeat(first.length - 1)}\n`);
    }
    lines.forEach((line, i) => {
      const cells = line.map((l, j) => (this.alignments[j] === 'c' ? center(l, at(widths, j)) : l));
      const head = rh ? (this.headAlign === 'c' ? center(at(rh, i), headWidth) : at(rh, i)) : undefined;
      out.push(format(cells, head));
    });
    return out.join('').slice(0, -1);
  }
}

const isRows = (d: TableData): d is readonly (readonly TableEntry[])[] => Array.isArray(d);

/** The rows of a matrix (SymPy `Matrix.tolist`). */
function matrixRows(m: { readonly rows: number; readonly cols: number; get(i: number, j: number): Expr }): Expr[][] {
  return Array.from({ length: m.rows }, (_, i) => Array.from({ length: m.cols }, (_, j) => m.get(i, j)));
}

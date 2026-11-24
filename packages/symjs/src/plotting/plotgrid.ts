// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { Plot } from './plot';
import type { PlotDescription } from './plot';
import { at } from '../core/guard';
/** Specifies the size and display preferences of a grid of plots. */
export interface PlotGridOptions {
  /** The requested width and height of the figure. */
  size?: readonly [number, number];
  /** The display preference supplied by the caller. */
  show?: boolean; }
/** A serializable description of a rectangular grid of plots in row-major order. */
export interface PlotGridDescription { version: 1; kind: 'plotGrid'; nrows: number; ncolumns: number; size: readonly number[]; plots: PlotDescription[]; }
/**
 * A row-major arrangement of plots for connector packages.
 *
 * @see SymPy `sympy.plotting.plotgrid.PlotGrid`
 * @example
 * ```ts
 * import { ex, symbols } from '@symjs/symjs';
 * import { PlotGrid, plot } from '@symjs/symjs/plotting';
 *
 * const [x] = symbols('x');
 * new PlotGrid(1, 2, plot(x), plot(ex`x**2`)).plots.length; // => 2
 * ```
 */
export class PlotGrid {
  /** The plots arranged in the grid. */
  readonly plots: Plot[];
  /** The requested width and height of the figure. */
  readonly size: readonly number[];
  /**
   * Creates a PlotGrid instance.
   *
   * @param nrows - The number of grid rows.
   * @param ncolumns - The number of grid columns.
   * @param args - The plots in row-major order and optional grid settings.
   * @throws RangeError when a grid dimension is not a positive integer.
   */
  constructor(
    /** The number of rows in the plot grid. */
    readonly nrows: number,
    /** The number of columns in the plot grid. */
    readonly ncolumns: number, ...args: (Plot | PlotGridOptions)[]) {
    if (!Number.isInteger(nrows) || !Number.isInteger(ncolumns) || nrows < 1 || ncolumns < 1) throw new RangeError('Grid dimensions must be positive integers.');
    this.plots = args.filter((a): a is Plot => a instanceof Plot);
    if (this.plots.length > nrows * ncolumns) throw new RangeError('More plots than grid cells.');
    this.size = args.find((a): a is PlotGridOptions => !(a instanceof Plot))?.size ?? [];
    if (this.size.some((v) => !Number.isFinite(v) || v <= 0)) throw new RangeError('Grid size must be positive and finite.');
  }
  /**
   * Retrieves a plot by its row-major index.
   *
   * @param i - The zero-based row-major plot index.
   * @returns The plot at that position.
   */
  get(i: number): Plot { return at(this.plots, i); }
  /**
   * Builds a serializable description for a plotting connector.
   *
   * @returns The serializable plot data.
   */
  toData(): PlotGridDescription { return { version: 1, kind: 'plotGrid', nrows: this.nrows, ncolumns: this.ncolumns, size: this.size, plots: this.plots.map((p) => p.toData()) }; }
  /**
   * Formats this value as a string.
   *
   * @returns The formatted text.
   */
  toString(): string { return 'PlotGrid object containing:\n' + this.plots.map((p, i) => `Plot[${i}]:${p.toString()}`).join('\n'); }
}

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { Plot } from './plot';
import type { PlotDescription } from './plot';
import { at } from '../core/guard';
export interface PlotGridOptions { size?: readonly [number, number]; show?: boolean; }
export interface PlotGridDescription { version: 1; kind: 'plotGrid'; nrows: number; ncolumns: number; size: readonly number[]; plots: PlotDescription[]; }
/** A row-major arrangement of plots for connector packages. */
export class PlotGrid {
  readonly plots: Plot[];
  readonly size: readonly number[];
  constructor(readonly nrows: number, readonly ncolumns: number, ...args: (Plot | PlotGridOptions)[]) {
    if (!Number.isInteger(nrows) || !Number.isInteger(ncolumns) || nrows < 1 || ncolumns < 1) throw new RangeError('Grid dimensions must be positive integers.');
    this.plots = args.filter((a): a is Plot => a instanceof Plot);
    if (this.plots.length > nrows * ncolumns) throw new RangeError('More plots than grid cells.');
    this.size = args.find((a): a is PlotGridOptions => !(a instanceof Plot))?.size ?? [];
    if (this.size.some((v) => !Number.isFinite(v) || v <= 0)) throw new RangeError('Grid size must be positive and finite.');
  }
  get(i: number): Plot { return at(this.plots, i); }
  toData(): PlotGridDescription { return { version: 1, kind: 'plotGrid', nrows: this.nrows, ncolumns: this.ncolumns, size: this.size, plots: this.plots.map((p) => p.toData()) }; }
  toString(): string { return 'PlotGrid object containing:\n' + this.plots.map((p, i) => `Plot[${i}]:${p.toString()}`).join('\n'); }
}

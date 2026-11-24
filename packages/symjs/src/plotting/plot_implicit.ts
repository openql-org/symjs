// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { Expr, Sym } from '../core/nodes';
import { cast, first, at } from '../core/guard';
import { ImplicitSeries } from './series';
import { Plot, parsePlotArguments } from './plot';
import { isPlotRange } from './utils';
/**
 * Computes implicit raster boxes or a uniform contour mesh without rendering.
 *
 * @param args - The plotted expressions, variable ranges and optional plotting settings.
 * @returns A plot containing the requested series.
 * @see SymPy `sympy.plotting.plot_implicit.plot_implicit`
 * @example
 * ```ts
 * import { ex, symbols } from '@symjs/symjs';
 * import { plotImplicit } from '@symjs/symjs/plotting';
 *
 * const [x, y] = symbols('x y');
 * plotImplicit(ex`x**2 + y**2 - 1`, [x, -2, 2], [y, -2, 2]).get(0).kind; // => implicit
 * ```
 */
export function plotImplicit(...args: unknown[]): Plot {
  const values = args.map((v, i) => i > 0 && v instanceof Sym ? [v, -5, 5] : v);
  const explicit = values.filter(isPlotRange), parsed = parsePlotArguments(values, 1, 2);
  return new Plot(parsed.series.map((s) => {
    const ranges = s.ranges.map((r) => explicit.some((e) => e[0].equals(r[0])) ? r : [r[0], -5, 5] as const);
    return new ImplicitSeries(cast(first(s.exprs), Expr), first(ranges), at(ranges, 1), s.label, { adaptive: true, n: 300, lineColor: 'blue', ...parsed.options, renderingKw: s.renderingKw });
  }), parsed.options);
}

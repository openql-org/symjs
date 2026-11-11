// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { Expr, Sym } from '../core/nodes';
import { cast, first, at } from '../core/guard';
import { ImplicitSeries } from './series';
import { Plot, parsePlotArguments } from './plot';
import { isPlotRange } from './utils';
/** Compute implicit raster boxes or a uniform contour mesh without rendering. */
export function plotImplicit(...args: unknown[]): Plot {
  const values = args.map((v, i) => i > 0 && v instanceof Sym ? [v, -5, 5] : v);
  const explicit = values.filter(isPlotRange), parsed = parsePlotArguments(values, 1, 2);
  return new Plot(parsed.series.map((s) => {
    const ranges = s.ranges.map((r) => explicit.some((e) => e[0].equals(r[0])) ? r : [r[0], -5, 5] as const);
    return new ImplicitSeries(cast(first(s.exprs), Expr), first(ranges), at(ranges, 1), s.label, { adaptive: true, n: 300, lineColor: 'blue', ...parsed.options, renderingKw: s.renderingKw });
  }), parsed.options);
}

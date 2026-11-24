// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 plotting/plot.py (BSD-3-Clause).
import { Expr } from '../core/nodes';
import { at, first } from '../core/guard';
import { NoMatch } from '../core/truth';
import type { NoMatchResult } from '../core/truth';
import { BaseSeries, LineOver1DRangeSeries, Parametric2DLineSeries, Parametric3DLineSeries, SurfaceOver2DRangeSeries, ParametricSurfaceSeries, ContourSeries, encodePlotData } from './series';
import type { JsonValue, PlotExpression, PlotRange, SeriesOptions, SeriesDescription, RenderingOptions } from './series';
import { createRanges, isPlotRange } from './utils';
/** Controls the labels, axes, limits and styling of a plot. */
export interface PlotOptions extends SeriesOptions {
  /** The title displayed above the plot. */
  title?: string;
  /** The label of the x axis. */
  xlabel?: string;
  /** The label of the y axis. */
  ylabel?: string;
  /** The label of the z axis. */
  zlabel?: string;
  /** The visible limits of the x axis. */
  xlim?: readonly [number, number];
  /** The visible limits of the y axis. */
  ylim?: readonly [number, number];
  /** The visible limits of the z axis. */
  zlim?: readonly [number, number];
  /** The relative scale of the plot axes. */
  aspectRatio?: string | readonly [number, number];
  /** The position where the axes cross. */
  axisCenter?: string | readonly [number, number];
  /** Requests display of the series legend. */
  legend?: boolean;
  /** The requested width and height of the figure. */
  size?: readonly [number, number];
  /** The annotations attached to the plot. */
  annotations?: JsonValue;
  /** The additional markers to draw. */
  markers?: JsonValue;
  /** The rectangles to overlay on the plot. */
  rectangles?: JsonValue;
  /** The regions to fill in the plot. */
  fill?: JsonValue;
  /** The display preference supplied by the caller. */
  show?: boolean;
  /** The requested rendering backend. */
  backend?: unknown;
  /** The text identifying the series. */
  label?: string | readonly string[];
}
/** A serializable description of the plot and its ordered data series. */
export interface PlotDescription { version: 1; kind: 'plot'; options: Record<string, JsonValue>; series: SeriesDescription[]; }
/**
 * A collection of numeric series and rendering preferences, with no rendering methods.
 *
 * @see SymPy `sympy.plotting.backends.base_backend.Plot`
 */
export class Plot implements Iterable<BaseSeries> {
  /** The ordered data series in the plot. */
  readonly series: BaseSeries[];
  /** The display preferences for the plot. */
  readonly options: PlotOptions;
  /**
   * Creates a Plot instance.
   *
   * @param series - The data series in drawing order.
   * @param options - The plot settings.
   * @throws RangeError when the requested size does not give two positive finite dimensions.
   */
  constructor(series: readonly BaseSeries[] = [], options: PlotOptions = {}) {
    this.series = [...series]; this.options = { ...options };
    if (options.size?.some((n) => !Number.isFinite(n) || n <= 0)) throw new RangeError('Plot size requires two positive finite dimensions.');
    for (const bounds of [options.xlim, options.ylim, options.zlim]) if (bounds?.some((v) => !Number.isFinite(v))) throw new RangeError('Plot limits must be finite.');
  }
  /**
   * The number of series in the plot.
   *
   * @returns The total length of the preperiod and period.
   */
  get length(): number { return this.series.length; }
  /**
   * Retrieves a series by its position in the plot.
   *
   * @param i - The zero-based series index.
   * @returns The series at the given index.
   */
  get(i: number): BaseSeries { return at(this.series, i); }
  /**
   * Replaces the series at a given position.
   *
   * @param i - The zero-based series index.
   * @param value - The replacement series.
   */
  set(i: number, value: BaseSeries): void { this.get(i); this.series[i < 0 ? this.length + i : i] = value; }
  /**
   * Appends one series to the plot.
   *
   * @param series - The series to add to the end of the plot.
   * @throws TypeError when an item is not a plot series.
   * @see SymPy `sympy.plotting.backends.base_backend.Plot.append`
   */
  append(series: BaseSeries): void { if (!(series instanceof BaseSeries)) throw new TypeError('A plot can only contain data series.'); this.series.push(series); }
  /**
   * Appends all series from another collection.
   *
   * @param other - The series or plot to append.
   * @see SymPy `sympy.plotting.backends.base_backend.Plot.extend`
   */
  extend(other: Plot | readonly BaseSeries[]): void { for (const s of other) this.append(s); }
  /**
   * Removes the series at a given position.
   *
   * @param i - The zero-based series index.
   */
  delete(i: number): void { this.get(i); this.series.splice(i < 0 ? this.length + i : i, 1); }
  [Symbol.iterator](): IterableIterator<BaseSeries> { return this.series.values(); }
  /**
   * Builds a serializable description for a plotting connector.
   *
   * @returns The serializable plot data.
   * @example
   * ```ts
   * import { ex, symbols } from '@symjs/symjs';
   * import { plot } from '@symjs/symjs/plotting';
   * const [x] = symbols('x');
   * plot(ex`x**2`, [x, 0, 2], { n: 3 }).toData().series[0].kind; // => line
   * ```
   */
  toData(): PlotDescription {
    const options: Record<string, JsonValue> = {};
    for (const key of ['title', 'xlabel', 'ylabel', 'zlabel', 'xlim', 'ylim', 'zlim', 'aspectRatio', 'axisCenter', 'legend', 'xscale', 'yscale', 'zscale', 'size', 'annotations', 'markers', 'rectangles', 'fill']) {
      const v: unknown = Reflect.get(this.options, key); if (v !== undefined) options[key] = encodePlotData(v);
    }
    return { version: 1, kind: 'plot', options, series: this.series.map((s) => s.toData()) };
  }
  /**
   * Formats this value as a string.
   *
   * @returns The formatted text.
   */
  toString(): string { return 'Plot object containing:\n' + this.series.map((s, i) => `[${i}]: ${s instanceof LineOver1DRangeSeries ? s.toString() : s.kind + ': ' + s.getLabel()}`).join('\n'); }
}
const isExpression = (v: unknown): v is PlotExpression => v instanceof Expr || typeof v === 'number' || typeof v === 'bigint' || typeof v === 'function';
const isOptions = (v: unknown): v is PlotOptions => typeof v === 'object' && v !== null && !Array.isArray(v) && !(v instanceof Expr) && !(v instanceof BaseSeries) && !(v instanceof Map);
interface ParsedSeries { exprs: PlotExpression[]; ranges: PlotRange[]; label: string | NoMatchResult; renderingKw: RenderingOptions; }
const optionNames = new Set('title xlabel ylabel zlabel xlim ylim zlim aspectRatio axisCenter legend size annotations markers rectangles fill show backend label adaptive depth n n1 n2 n3 nbOfPoints nbOfPointsX nbOfPointsY nbOfPointsU nbOfPointsV xscale yscale zscale params isPolar isPoint isFilled useCm showInLegend renderingKw contourKw clabels colorFunc lineColor surfaceColor detectPoles eps exclude onlyIntegers steps unwrap return forceRealEval tx ty tz tp'.split(' '));
const renderingOptions = (value: object): RenderingOptions => Object.fromEntries(Object.entries(value).map(([k, v]) => [k, encodePlotData(v)]));
/** Shared argument interpretation for Cartesian and parametric plot factories. */
export function parsePlotArguments(args: readonly unknown[], nexpr: number, npar: number): { series: ParsedSeries[]; options: PlotOptions } {
  const values = [...args]; let options: PlotOptions = {};
  const tail = values[values.length - 1]; if (isOptions(tail)) { options = Object.keys(tail).some((key) => optionNames.has(key)) ? tail : { renderingKw: renderingOptions(tail) }; values.pop(); }
  const sharedRendering = values.find(isOptions);
  if (sharedRendering) options = { ...options, renderingKw: renderingOptions(sharedRendering) };
  const ranges = values.filter(isPlotRange), labels = values.filter((v): v is string => typeof v === 'string');
  const input = values.filter((v) => !isPlotRange(v) && typeof v !== 'string' && !isOptions(v));
  if (!input.length) return { series: [], options };
  const groups = input.every(isExpression) ? nexpr === 1 ? input.map((v) => [v]) : [input] : input.map((v) => { if (!Array.isArray(v)) throw new TypeError('Expected an expression or a series tuple.'); return v; });
  const series = groups.map((group, i) => {
    const expressions = group.filter(isExpression), localRanges = group.filter(isPlotRange), localLabels = group.filter((v): v is string => typeof v === 'string');
    if (expressions.length !== nexpr) throw new RangeError(`Expected ${nexpr} expressions per series.`);
    const label = options.label;
    const localRendering = group.find(isOptions);
    const rendering = localRendering ? localRendering.renderingKw ?? renderingOptions(localRendering) : options.renderingKw ?? {};
    return { exprs: expressions, ranges: createRanges(expressions, localRanges.length ? localRanges : ranges, npar, options.params), label: localLabels[0] ?? labels[0] ?? (typeof label === 'string' ? label : label?.[i]) ?? NoMatch, renderingKw: rendering };
  });
  return { series, options };
}
function makePlot(kind: 'line' | 'parametric2d' | 'parametric3d' | 'surface' | 'parametricSurface' | 'contour', args: readonly unknown[]): Plot {
  const count = kind === 'parametric2d' ? 2 : kind === 'parametric3d' || kind === 'parametricSurface' ? 3 : 1;
  const npar = kind === 'surface' || kind === 'parametricSurface' || kind === 'contour' ? 2 : 1;
  const parsed = parsePlotArguments(args, count, npar);
  return new Plot(parsed.series.map(({ exprs: e, ranges: r, label, renderingKw }) => {
    const options = { ...parsed.options, renderingKw };
    switch (kind) {
      case 'line': return new LineOver1DRangeSeries(first(e), first(r), label, options);
      case 'parametric2d': return new Parametric2DLineSeries(first(e), at(e, 1), first(r), label, options);
      case 'parametric3d': return new Parametric3DLineSeries(first(e), at(e, 1), at(e, 2), first(r), label, options);
      case 'surface': return new SurfaceOver2DRangeSeries(first(e), first(r), at(r, 1), label, options);
      case 'parametricSurface': return new ParametricSurfaceSeries(first(e), at(e, 1), at(e, 2), first(r), at(r, 1), label, options);
      case 'contour': return new ContourSeries(first(e), first(r), at(r, 1), label, options);
    }
  }), parsed.options);
}
/**
 * Constructs a plot of one or more functions of a single variable.
 *
 * @param args - The plotted expressions, variable ranges and optional plotting settings.
 * @returns A plot containing the requested series.
 * @see SymPy `sympy.plotting.plot.plot`
 * @example
 * ```ts
 * import { ex, symbols } from '@symjs/symjs';
 * import { plot } from '@symjs/symjs/plotting';
 *
 * const [x] = symbols('x');
 * plot(ex`x**2`, [x, -2, 2]).get(0).kind; // => line
 * ```
 */
export const plot = (...args: unknown[]): Plot => makePlot('line', args);
/**
 * Constructs a planar curve from two coordinate functions of a parameter.
 *
 * @param args - The plotted expressions, variable ranges and optional plotting settings.
 * @returns A plot containing the requested series.
 * @see SymPy `sympy.plotting.plot.plot_parametric`
 * @example
 * ```ts
 * import { ex, symbols } from '@symjs/symjs';
 * import { plotParametric } from '@symjs/symjs/plotting';
 *
 * const [t] = symbols('t');
 * plotParametric(ex`cos(t)`, ex`sin(t)`, [t, 0, 1]).get(0).kind; // => parametric2d
 * ```
 */
export const plotParametric = (...args: unknown[]): Plot => makePlot('parametric2d', args);
/**
 * Constructs a surface plot from a height function of two variables.
 *
 * @param args - The plotted expressions, variable ranges and optional plotting settings.
 * @returns A plot containing the requested series.
 * @see SymPy `sympy.plotting.plot.plot3d`
 * @example
 * ```ts
 * import { ex, symbols } from '@symjs/symjs';
 * import { plot3d } from '@symjs/symjs/plotting';
 *
 * const [x, y] = symbols('x y');
 * plot3d(ex`x*y`, [x, -1, 1], [y, -1, 1]).get(0).kind; // => surface
 * ```
 */
export const plot3d = (...args: unknown[]): Plot => makePlot('surface', args);
/**
 * Constructs a space curve from three coordinate functions of a parameter.
 *
 * @param args - The plotted expressions, variable ranges and optional plotting settings.
 * @returns A plot containing the requested series.
 * @see SymPy `sympy.plotting.plot.plot3d_parametric_line`
 * @example
 * ```ts
 * import { ex, symbols } from '@symjs/symjs';
 * import { plot3dParametricLine } from '@symjs/symjs/plotting';
 *
 * const [t] = symbols('t');
 * plot3dParametricLine(ex`cos(t)`, ex`sin(t)`, t, [t, 0, 1]).get(0).kind; // => parametric3d
 * ```
 */
export const plot3dParametricLine = (...args: unknown[]): Plot => makePlot('parametric3d', args);
/**
 * Constructs a surface from three coordinate functions of two parameters.
 *
 * @param args - The plotted expressions, variable ranges and optional plotting settings.
 * @returns A plot containing the requested series.
 * @see SymPy `sympy.plotting.plot.plot3d_parametric_surface`
 * @example
 * ```ts
 * import { ex, symbols } from '@symjs/symjs';
 * import { plot3dParametricSurface } from '@symjs/symjs/plotting';
 *
 * const [u, v] = symbols('u v');
 * plot3dParametricSurface(u, v, ex`u*v`, [u, 0, 1], [v, 0, 1]).get(0).kind; // => parametricSurface
 * ```
 */
export const plot3dParametricSurface = (...args: unknown[]): Plot => makePlot('parametricSurface', args);
/**
 * Constructs a contour plot of a scalar field in two variables.
 *
 * @param args - The plotted expressions, variable ranges and optional plotting settings.
 * @returns A plot containing the requested series.
 * @see SymPy `sympy.plotting.plot.plot_contour`
 */
export const plotContour = (...args: unknown[]): Plot => makePlot('contour', args);

/**
 * Groups expressions with their plotting ranges and fills in missing variable ranges.
 *
 * @remarks SymPy returns `[(x, (x, -10, 10)), (x**2, (x, -10, 10))]`.
 *
 * @param args - The plotted expressions, variable ranges and optional plotting settings.
 * @param nexpr - The number of coordinate expressions per series.
 * @param npar - The number of parameter ranges per series.
 * @returns The resulting coordinate samples.
 * @see SymPy `sympy.plotting.plot.check_arguments`
 * @example
 * ```ts
 * import { ex } from '@symjs/symjs';
 * import { checkArguments } from '@symjs/symjs/plotting';
 * checkArguments([ex`x`, ex`x**2`], 1, 1); // => [[x, [x, -10, 10]], [x**2, [x, -10, 10]]]
 * ```
 */
export function checkArguments(args: readonly unknown[], nexpr: number, npar: number): (PlotExpression | PlotRange)[][] {
  return parsePlotArguments(args, nexpr, npar).series.map((s) => [...s.exprs, ...s.ranges]);
}

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
export interface PlotOptions extends SeriesOptions {
  title?: string; xlabel?: string; ylabel?: string; zlabel?: string;
  xlim?: readonly [number, number]; ylim?: readonly [number, number]; zlim?: readonly [number, number];
  aspectRatio?: string | readonly [number, number]; axisCenter?: string | readonly [number, number];
  legend?: boolean; size?: readonly [number, number]; annotations?: JsonValue; markers?: JsonValue; rectangles?: JsonValue; fill?: JsonValue;
  show?: boolean; backend?: unknown; label?: string | readonly string[];
}
export interface PlotDescription { version: 1; kind: 'plot'; options: Record<string, JsonValue>; series: SeriesDescription[]; }
/** A collection of numeric series and rendering preferences, with no rendering methods. */
export class Plot implements Iterable<BaseSeries> {
  readonly series: BaseSeries[];
  readonly options: PlotOptions;
  constructor(series: readonly BaseSeries[] = [], options: PlotOptions = {}) {
    this.series = [...series]; this.options = { ...options };
    if (options.size?.some((n) => !Number.isFinite(n) || n <= 0)) throw new RangeError('Plot size requires two positive finite dimensions.');
    for (const bounds of [options.xlim, options.ylim, options.zlim]) if (bounds?.some((v) => !Number.isFinite(v))) throw new RangeError('Plot limits must be finite.');
  }
  get length(): number { return this.series.length; }
  get(i: number): BaseSeries { return at(this.series, i); }
  set(i: number, value: BaseSeries): void { this.get(i); this.series[i < 0 ? this.length + i : i] = value; }
  append(series: BaseSeries): void { if (!(series instanceof BaseSeries)) throw new TypeError('A plot can only contain data series.'); this.series.push(series); }
  extend(other: Plot | readonly BaseSeries[]): void { for (const s of other) this.append(s); }
  delete(i: number): void { this.get(i); this.series.splice(i < 0 ? this.length + i : i, 1); }
  [Symbol.iterator](): IterableIterator<BaseSeries> { return this.series.values(); }
  toData(): PlotDescription {
    const options: Record<string, JsonValue> = {};
    for (const key of ['title', 'xlabel', 'ylabel', 'zlabel', 'xlim', 'ylim', 'zlim', 'aspectRatio', 'axisCenter', 'legend', 'xscale', 'yscale', 'zscale', 'size', 'annotations', 'markers', 'rectangles', 'fill']) {
      const v: unknown = Reflect.get(this.options, key); if (v !== undefined) options[key] = encodePlotData(v);
    }
    return { version: 1, kind: 'plot', options, series: this.series.map((s) => s.toData()) };
  }
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
export const plot = (...args: unknown[]): Plot => makePlot('line', args);
export const plotParametric = (...args: unknown[]): Plot => makePlot('parametric2d', args);
export const plot3d = (...args: unknown[]): Plot => makePlot('surface', args);
export const plot3dParametricLine = (...args: unknown[]): Plot => makePlot('parametric3d', args);
export const plot3dParametricSurface = (...args: unknown[]): Plot => makePlot('parametricSurface', args);
export const plotContour = (...args: unknown[]): Plot => makePlot('contour', args);

/** Legacy argument normalizer: expression tuples followed by complete ranges. */
export function checkArguments(args: readonly unknown[], nexpr: number, npar: number): (PlotExpression | PlotRange)[][] {
  return parsePlotArguments(args, nexpr, npar).series.map((s) => [...s.exprs, ...s.ranges]);
}

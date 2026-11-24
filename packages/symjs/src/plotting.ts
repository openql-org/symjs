// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
/**
 * Renderer-independent plotting data, isolated from the root entry point.
 *
 * `plot(expr, [x, -10, 10], { n: 100 }).toData()` returns a versioned JSON
 * description. Each series has a kind, named coordinate arrays (row-major
 * matrices for surfaces), a label and style hints. Parametric coordinates
 * include the parameter (or the computed color channel when a color function
 * replaces it); implicit plots contain either contour meshes or
 * interval boxes. Non-finite numbers encode as "NaN", "Infinity", and
 * "-Infinity", preserving gaps through JSON. `getData()` uses numeric arrays
 * with IEEE NaN instead. Color arrays and renderingKw are passed to connectors;
 * plot-level options retain titles, labels, bounds, scales and annotations.
 * PlotGrid.toData() nests these descriptions in row-major order. Sampling never
 * displays or saves a figure. Connector packages own all rendering dependencies.
 */
import './core';
export { Plot, checkArguments, plot, plotParametric, plot3d, plot3dParametricLine, plot3dParametricSurface, plotContour } from './plotting/plot';
export type { PlotOptions, PlotDescription } from './plotting/plot';
export { plotImplicit } from './plotting/plot_implicit';
export { PlotGrid } from './plotting/plotgrid';
export type { PlotGridOptions, PlotGridDescription } from './plotting/plotgrid';
export { textplot, textplotStr } from './plotting/textplot';
export { BaseSeries, Line2DBaseSeries, LineOver1DRangeSeries, ParametricLineBaseSeries, Parametric2DLineSeries, Line3DBaseSeries, Parametric3DLineSeries, List2DSeries, SurfaceBaseSeries, SurfaceOver2DRangeSeries, ParametricSurfaceSeries, ContourSeries, GenericDataSeries, ImplicitSeries, centersOfSegments, centersOfFaces, flat } from './plotting/series';
export type { NumericFunction, PlotExpression, PlotBound, PlotRange, PlotParameters, NumericArray, IntervalBox, SeriesValues, JsonValue, RenderingOptions, PlotScale, SeriesKind, SeriesOptions, SeriesDescription } from './plotting/series';
export { extractSolution } from './plotting/utils';
/**
 * Interval arithmetic for adaptive plotting: intervals with validity flags and
 * the elementary functions on them.
 *
 * @see SymPy `sympy.plotting.intervalmath`
 */
export * as intervalmath from './plotting/intervalmath/index';

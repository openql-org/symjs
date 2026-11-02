// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Entry point `@symjs/symjs/calculus`: integration, limits, series,
 * summations and products.
 */

// every entry point brings the core with its registrations
import './core';

export { Concrete } from './concrete/node';
export {
  doit,
} from './calculus/doit';
export {
  integrate,
} from './integrals/integrate';
export {
  transformIntegral,
  principalValue,
  asSum,
  Curve,
  lineIntegrate,
} from './integrals/transform';
export {
  limit,
} from './series/limits';
export {
  Sum,
  Product,
  summation,
  product,
  reverseOrder,
  eulerMaclaurin,
} from './concrete/summations';
export {
  series,
  O,
} from './series/series';

export {
} from './concrete/summations';
export {
  leadterm,
  aseries,
  taylorTerm,
  asLeadingTerm,
} from './series/series';
export {
  finiteDiffWeights,
  asFiniteDifference,
} from './calculus/finitediff';

// ---- deprecated names (kept during 0.x, removed in 1.0; see docs/api-policy.md) ----

import { doitConcrete as _doitConcrete_ } from './concrete/summations';
import { piecewiseIntegrate as _piecewiseIntegrate_ } from './integrals/integrate';
import { sumIsConvergent as _sumIsConvergent_ } from './concrete/summations';
import { getn as _getn_ } from './series/series';
import { type NoMatchResult, type Truth, orNoMatch as _orNoMatch_, toTruth as _toTruth_ } from './core/truth';
import type { Expr as _Expr_, ExprLike as _ExprLike_ } from './core/nodes';
import type { Concrete as _Concrete_ } from './concrete/summations';
import { sumIsAbsolutelyConvergent as _sumIsAbsolutelyConvergent_ } from './concrete/summations';
import { extractLeadingOrder as _extractLeadingOrder_ } from './series/series';

/** @deprecated Internal; removed from the public API in 1.0. */
export const doitConcrete = _doitConcrete_;

/** @deprecated Internal; removed from the public API in 1.0. */
export const piecewiseIntegrate = _piecewiseIntegrate_;

/** @deprecated Use `isConvergent`. */
export const sumIsConvergent = (s: _Concrete_): Truth => _toTruth_(_sumIsConvergent_(s));

/** @deprecated Use `isAbsolutelyConvergent`. */
export const sumIsAbsolutelyConvergent = (s: _Concrete_): Truth => _toTruth_(_sumIsAbsolutelyConvergent_(s));

/** SymPy Sum.is_convergent: true, false or 'unknown'. */
export const isConvergent = sumIsConvergent;
/** SymPy Sum.is_absolutely_convergent: true, false or 'unknown'. */
export const isAbsolutelyConvergent = sumIsAbsolutelyConvergent;

/** SymPy Order.getn: the order of the Order term in the expression, or NoMatch. */
export function getn(e: _ExprLike_): _Expr_ | NoMatchResult {
  return _orNoMatch_(_getn_(e));
}

/** @deprecated Internal; removed from the public API in 1.0. */
export const extractLeadingOrder = _extractLeadingOrder_;
export { lseries, dir, fps, fourierSeries, FormalPowerSeries, FourierSeries } from './series/more';

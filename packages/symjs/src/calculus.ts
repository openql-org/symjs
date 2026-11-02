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
  sumIsConvergent as isConvergent,
  sumIsAbsolutelyConvergent as isAbsolutelyConvergent,
} from './concrete/summations';
export {
  leadterm,
  taylorTerm,
  asLeadingTerm,
  getn,
} from './series/series';
export {
  finiteDiffWeights,
  asFiniteDifference,
} from './calculus/finitediff';

// ---- deprecated names (kept during 0.x, removed in 1.0; see docs/api-policy.md) ----

import { doitConcrete as _doitConcrete_ } from './concrete/summations';
import { piecewiseIntegrate as _piecewiseIntegrate_ } from './integrals/integrate';
import { sumIsConvergent as _sumIsConvergent_ } from './concrete/summations';
import { sumIsAbsolutelyConvergent as _sumIsAbsolutelyConvergent_ } from './concrete/summations';
import { extractLeadingOrder as _extractLeadingOrder_ } from './series/series';

/** @deprecated Internal; removed from the public API in 1.0. */
export const doitConcrete = _doitConcrete_;

/** @deprecated Internal; removed from the public API in 1.0. */
export const piecewiseIntegrate = _piecewiseIntegrate_;

/** @deprecated Use `isConvergent`. */
export const sumIsConvergent = _sumIsConvergent_;

/** @deprecated Use `isAbsolutelyConvergent`. */
export const sumIsAbsolutelyConvergent = _sumIsAbsolutelyConvergent_;

/** @deprecated Internal; removed from the public API in 1.0. */
export const extractLeadingOrder = _extractLeadingOrder_;

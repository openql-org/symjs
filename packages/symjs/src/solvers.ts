// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Entry point `@symjs/symjs/solvers`: algebraic equations, inequalities,
 * polynomial systems, recurrences and ordinary differential equations.
 */

// every entry point brings the core with its registrations
import './core';

export {
  solve,
  linsolve,
  linearEqToMatrix,
  nonlinsolve,
  solveLinear,
  solveUndeterminedCoeffs,
  nsolve,
} from './solvers/solve';
export { dsolveSystem } from './solvers/odesystem';
export {
  dsolve,
  homogeneousOrder,
  odeOrder,
} from './solvers/ode';
export {
  solveset,
  solveUnivariateInequality,
  solvePolyInequality,
  solveRationalInequalities,
  reduceInequalities,
  periodicity,
  singularities,
  stationaryPoints,
  isIncreasing,
  isStrictlyIncreasing,
  isDecreasing,
  isStrictlyDecreasing,
  isMonotonic,
  isConvex,
  maximum,
  minimum,
  asExprSetPairs,
  notEmptyIn,
  piecewiseExclusive,
} from './solvers/inequalities';
export {
  factorSystem,
  factorSystemCond,
  solvePolySystem,
} from './solvers/polysys';
export {
  rsolve,
  rsolveHyper,
  rsolvePoly,
  rsolveRatio,
} from './solvers/recurr';

// ---- deprecated names (kept during 0.x, removed in 1.0; see docs/api-policy.md) ----

import { asEquation as _asEquation_ } from './solvers/solve';
import { invertEquation as _invertEquation_ } from './solvers/solve';

/** @deprecated Internal; removed from the public API in 1.0. */
export const asEquation = _asEquation_;

/** @deprecated Internal; removed from the public API in 1.0. */
export const invertEquation = _invertEquation_;

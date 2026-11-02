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
  asEquation,
  linsolve,
  linearEqToMatrix,
  nonlinsolve,
  solveLinear,
  solveUndeterminedCoeffs,
  nsolve,
  invertEquation,
} from './solvers/solve';
export { dsolve, homogeneousOrder, odeOrder } from './solvers/ode';
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
export { factorSystem, factorSystemCond, solvePolySystem } from './solvers/polysys';
export { rsolve, rsolveHyper, rsolvePoly, rsolveRatio } from './solvers/recurr';

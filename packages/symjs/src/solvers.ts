// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Entry point `@symjs/symjs/solvers`: algebraic equations, inequalities,
 * polynomial systems, recurrences and ordinary differential equations.
 */

// every entry point brings the core with its registrations
import './core';

export {
  linsolve,
  linearEqToMatrix,
  homogeneousOrder,
  periodicity,
  isIncreasing,
  isStrictlyIncreasing,
  isDecreasing,
  isStrictlyDecreasing,
  isMonotonic,
  rsolve,
  rsolveHyper,
  rsolvePoly,
  rsolveRatio,
} from './solvers/public';

export {
  solve,
  nonlinsolve,
  solveLinear,
  solveUndeterminedCoeffs,
  nsolve,
} from './solvers/solve';
export { dsolveSystem, checkodesol } from './solvers/odesystem';
export {
  diophantine,
  classifyDiop,
  diopSolve,
  diopLinear,
  baseSolutionLinear,
  diopUnivariate,
  diopQuadratic,
  diopDN,
  diopBfDN,
  cornacchia,
  PQa,
  transformationToDN,
  findDN,
  diopTernaryQuadratic,
  parametrizeTernaryQuadratic,
  diopTernaryQuadraticNormal,
  sqfNormal,
  squareFactor,
  ldescent,
  descent,
  gaussianReduce,
  holzer,
  diopGeneralPythagorean,
  diopGeneralSumOfSquares,
  diopGeneralSumOfEvenPowers,
  primeAsSumOfTwoSquares,
  sumOfThreeSquares,
  sumOfFourSquares,
  powerRepresentation,
  sumOfSquares,
  DiophantineSolutionSet,
  DiophantineEquationType,
  Univariate,
  Linear,
  BinaryQuadratic,
  InhomogeneousTernaryQuadratic,
  HomogeneousTernaryQuadraticNormal,
  HomogeneousTernaryQuadratic,
  InhomogeneousGeneralQuadratic,
  HomogeneousGeneralQuadratic,
  GeneralSumOfSquares,
  GeneralPythagorean,
  CubicThue,
  GeneralSumOfEvenPowers,
} from './solvers/diophantine';
export type { DiophantineOptions, DiophantineSolveOptions, PowerRepresentationOptions } from './solvers/diophantine';
export { classifyOde } from './solvers/dsolve';
export {
  dsolve,
  odeOrder,
} from './solvers/ode';
export type { DsolveOptions } from './solvers/ode';
export { infinitesimals, checkinfsol } from './solvers/liegroup';
export {
  solveset,
  solveUnivariateInequality,
  asSet,
  solvePolyInequality,
  solveRationalInequalities,
  reduceInequalities,
  singularities,
  stationaryPoints,
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
} from './solvers/recurr';

// ---- deprecated names (kept during 0.x, removed in 1.0; see docs/api-policy.md) ----

import { asEquation as _asEquation_ } from './solvers/solve';
import { invertEquation as _invertEquation_ } from './solvers/solve';

/** @deprecated Internal; removed from the public API in 1.0. */
export const asEquation = _asEquation_;

/** @deprecated Internal; removed from the public API in 1.0. */
export const invertEquation = _invertEquation_;

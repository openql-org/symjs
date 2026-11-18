// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Entry point `@symjs/symjs/solvers`: algebraic equations, inequalities,
 * polynomial systems, recurrences and ordinary differential equations.
 */

// every entry point brings the core with its registrations
import './core';
import { impl } from './core/nodes';
import { asSet as asSetOf } from './solvers/inequalities';

export {
  linsolve,
  linsolveAugmented,
  solveLinearSystem,
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
  nonlinsolve as solveSystem,
  denoms,
  unrad,
  checksol,
  solveLinear,
  solveUndeterminedCoeffs,
  nsolve,
  detPerm,
  detMinor,
  detQuick,
  invQuick,
  solveLinearSystemLU,
} from './solvers/solve';
export { nonlinsolve, substitution, domainCheck, linearCoeffs, solvesetReal, solvesetComplex, solveDecomposition, solvify, invertComplex, invertReal } from './solvers/solveset';
export { dsolveSystem, matrixExp as odeMatrixExp, canonicalOdes, linodesolveType, checkodesol, checksysodesol, subFuncDoit } from './solvers/odesystem';
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
  equivalent,
  length,
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
export { classifyOde } from './solvers/ode';
export { constantsimp, constantRenumber, odeSolSimplicity, solveIcs } from './solvers/odesimp';
export {
  dsolve,
  odeOrder,
  classifySysode,
} from './solvers/ode';
export type { DsolveOptions } from './solvers/ode';
export { infinitesimals, checkinfsol } from './solvers/liegroup';
export {
  solveset,
  solveUnivariateInequality,
  asSet,
  solvePolyInequality,
  solveRationalInequalities,
  solvePolyInequalities,
  reduceRationalInequalities,
  reduceInequalities,
  reduceAbsInequality,
  reduceAbsInequalities,
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
  factorSystemBool,
  factorSystemPoly,
  solveGeneric,
  solveBiquadratic,
  solvePolySystem,
  solveTriangulated,
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
export { pdsolve, classifyPde, checkpdesol, pdeSeparate, pdeSeparateAdd, pdeSeparateMul } from './solvers/pde';
export { decompogen, compogen } from './solvers/decompogen';
export { continuousDomain, functionRange, lcim } from './solvers/calculusutil';
export { lpmin, lpmax, linprog, showLinprog, UnboundedLPError, InfeasibleLPError } from './solvers/simplex';
export type { LPMatrixLike, LPBound, LPBounds } from './solvers/simplex';
export { bivariateType } from './solvers/bivariate';
export { SingleODEProblem, SingleODESolver, FirstLinear, getNumberedConstants, NthAlgebraic, ODEMatchError } from './solvers/ode/single';

impl.asSet = asSetOf;

export { linodesolve } from './solvers/linodesolve';
export type { LinodesolveOptions } from './solvers/linodesolve';

export { matchRiccati, valAtInf, checkNecessaryConds, limitAtInf, inverseTransformPoly, rationalLaurentSeries, constructCCase1, constructCCase2, constructCCase3, constructC, constructDCase4, constructDCase5, constructDCase6, constructD } from './solvers/ode/riccati';
export { linearOdeToMatrix, ODEOrderError, ODENonlinearError } from './solvers/odesystem';

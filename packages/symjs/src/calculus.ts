// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Entry point `@symjs/symjs/calculus`: integration, limits, series,
 * summations and products.
 */

// every entry point brings the core with its registrations
import './core';

export { Concrete } from './core/concrete';
export { testDerivativeNumerically } from './calculus/numerical-derivative';

export {
  doit,
} from './calculus/doit';
export {
  integral, integrate,
} from './integrals/integrate';
export {
  transformIntegral,
  principalValue,
  asSum,
  lineIntegrate,
} from './integrals/transform';
export type { ParametricCurve } from './integrals/transform';
// integral transforms (SymPy sympy.integrals.transforms and laplace)
export * from './integrals/transforms/index';
export { asPoly1t, fracIn, gcdexDiophantine } from './integrals/risch';
export { DifferentialExtension, NonElementaryIntegral, integerPowers, rischIntegrate } from './integrals/risch';
export { manualintegrate, manualSubs, findSubstitutions } from './integrals/manualintegrate';
export { singularityintegrate } from './integrals/singularityfunctions';
// the helpers of SymPy's integrators (rationaltools, trigonometry, deltafunctions, meijerint, heurisch)
export { ratintRatpart, logToAtan } from './integrals/rationaltools';
export {
  ratint,
  ratintLogpart,
  logToReal,
  trigintegrate,
  deltaintegrate,
  changeMul,
  meijerintDefinite,
  meijerintIndefinite,
  meijerintInversion,
  components,
  heurisch,
  heurischWrapper,
} from './integrals/public';
export type { HeurischOptions } from './integrals/heurisch';
export {
  limit, heuristics,
} from './series/limits';
export {
  Sum,
  Product,
  summation,
  product,
  reverseOrder,
  eulerMaclaurin,
  telescopicDirect,
  evalSumResidue,
} from './concrete/summations';
export {
  series,
  O, asExprVariables,
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
  applyFiniteDiff,
  differentiateFinite,
} from './calculus/finitediff';
export { eulerEquations } from './calculus/euler';
export { residue } from './series/residues';
export { differenceDelta, limitSeq } from './series/limitseq';
export { finiteDiff, finiteDiffKauers } from './series/kauers';
export { deltasummation, deltaproduct } from './concrete/delta';
export { gosperNormal, gosperTerm, gosperSum } from './concrete/gosper';
export type { DeltaLimit } from './concrete/delta';
export {
  SeqBase,
  SeqExpr,
  SeqExprNode,
  SeqExprOp,
  SeqExprOpNode,
  EmptySequenceNode,
  EmptySequence,
  SeqFormulaNode,
  SeqFormula,
  SeqPerNode,
  SeqPer,
  RecursiveSeqNode,
  RecursiveSeq,
  SeqAddNode,
  SeqAdd,
  SeqMulNode,
  SeqMul,
  sequence,
  type SeqLimits,
} from './series/sequences';

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
import { dominant as _dominant_ } from './series/limitseq';
import type { Sym as _Sym_ } from './core/nodes';

/** The unique asymptotically dominant term of a sum, or NoMatch. */
export function dominant(expr: _ExprLike_, n: _Sym_): _Expr_ | NoMatchResult {
  return _orNoMatch_(_dominant_(expr, n));
}

/** @deprecated Internal; removed from the public API in 1.0. */
export const doitConcrete = _doitConcrete_;

/** @deprecated Internal; removed from the public API in 1.0. */
export const piecewiseIntegrate = _piecewiseIntegrate_;

/** SymPy Sum.is_convergent: true, false or 'unknown'. */
export const isConvergent = (s: _Concrete_): Truth => _toTruth_(_sumIsConvergent_(s));
/** SymPy Sum.is_absolutely_convergent: true, false or 'unknown'. */
export const isAbsolutelyConvergent = (s: _Concrete_): Truth => _toTruth_(_sumIsAbsolutelyConvergent_(s));

/** @deprecated Use `isConvergent`. */
export const sumIsConvergent = isConvergent;

/** @deprecated Use `isAbsolutelyConvergent`. */
export const sumIsAbsolutelyConvergent = isAbsolutelyConvergent;

/** SymPy Order.getn: the order of the Order term in the expression, or NoMatch. */
export function getn(e: _ExprLike_): _Expr_ | NoMatchResult {
  return _orNoMatch_(_getn_(e));
}

/** @deprecated Internal; removed from the public API in 1.0. */
export const extractLeadingOrder = _extractLeadingOrder_;
export { lseries, dir } from './series/lseries';
export { fps, FormalPowerSeries, expRe, hyperRe, rationalIndependent, rationalAlgorithm, simpleDE, solveDe, hyperAlgorithm } from './series/formal';
export { fourierSeries, FourierSeries } from './series/fourier';
// integration of polynomials over polytopes (SymPy sympy.integrals.intpoly); the helpers, whose names collide with
// other SymPy functions (decompose, intersection, norm), are members of the namespace intpoly
export { polytopeIntegrate } from './integrals/intpoly';
export * as intpoly from './integrals/intpoly';
export type { PointLike, SegmentLike, PolygonLike, Hyperplane, Face, Polytope3D, MonomialRecord2D, MonomialRecord3D, MonomialTable3D } from './integrals/intpoly';
// guessing sequences and generating functions (SymPy sympy.concrete.guess) and Pade approximants
export { findSimpleRecurrenceVector, findSimpleRecurrence, rationalize, guessGeneratingFunctionRational, guessGeneratingFunction, guess } from './concrete/guess';
export type { GuessGeneratingFunctionOptions, GuessOptions } from './concrete/guess';
export { approximants } from './series/approximants';
export type { ApproximantsOptions } from './series/approximants';
export { variables, hasFiniteLimits, hasReversedLimits } from './concrete/exprwithlimits';
export { gaussLegendre, gaussLaguerre, gaussHermite, gaussGenLaguerre, gaussJacobi, gaussChebyshevT, gaussChebyshevU, gaussLobatto } from './integrals/quadrature';
export type { QuadratureRule } from './integrals/quadrature';
export type { HyperSeriesResult } from './series/formal';

export { SeriesBase } from './series/series_class';

export { orderAt, orderAtOo } from './integrals/orders';
export { Gruntz, gruntz } from './series/gruntz';

export { richardson, shanks } from './series/acceleration';

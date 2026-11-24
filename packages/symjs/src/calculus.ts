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
  integrate,
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
  telescopic,
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
import { summationHooks } from './concrete/summations';
import { gosperSum } from './concrete/gosper';
summationHooks.gosperSum = gosperSum;
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

/**
 * The unique asymptotically dominant term of a sum, or NoMatch.
 *
 * @param expr - The input expression.
 * @param n - The index tending to infinity.
 * @returns The dominant term, or `NoMatch` when no term dominates uniquely.
 * @see SymPy `sympy.series.limitseq.dominant`
 * @example
 * ```ts
 * import { dominant, ex, symbols } from '@symjs/symjs';
 *
 * dominant(ex`5*n**3 + 4*n**2 + n + 1`, symbols('n')[0]); // => 5*n**3
 * ```
 */
export function dominant(expr: _ExprLike_, n: _Sym_): _Expr_ | NoMatchResult {
  return _orNoMatch_(_dominant_(expr, n));
}

/**
 * Evaluates the summand or product over its limits.
 *
 * @deprecated Internal; removed from the public API in 1.0.
 */
export const doitConcrete = _doitConcrete_;

/**
 * Integrates the branches of a piecewise expression.
 *
 * @deprecated Internal; removed from the public API in 1.0.
 */
export const piecewiseIntegrate = _piecewiseIntegrate_;

/**
 * Tests a sum for convergence.
 *
 * @param s - The unevaluated sum to test.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 * @see SymPy `sympy.concrete.summations.Sum.is_convergent`
 * @example
 * ```ts
 * import { Concrete, ex, isConvergent, oo } from '@symjs/symjs';
 *
 * isConvergent(new Concrete('Sum', [ex`1/k**2`, ex`k`, ex`1`, oo])); // => True
 * ```
 */
export const isConvergent = (s: _Concrete_): Truth => _toTruth_(_sumIsConvergent_(s));
/**
 * Tests a sum for absolute convergence.
 *
 * @param s - The unevaluated sum to test.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 * @see SymPy `sympy.concrete.summations.Sum.is_absolutely_convergent`
 * @example
 * ```ts
 * import { Concrete, ex, isAbsolutelyConvergent, oo } from '@symjs/symjs';
 *
 * isAbsolutelyConvergent(new Concrete('Sum', [ex`1/k**2`, ex`k`, ex`1`, oo])); // => True
 * ```
 */
export const isAbsolutelyConvergent = (s: _Concrete_): Truth => _toTruth_(_sumIsAbsolutelyConvergent_(s));

/**
 * Alias for {@link isConvergent}.
 *
 * @deprecated Use {@link isConvergent}.
 * @param s - The input value.
 * @returns The truth value, or `'unknown'` if convergence cannot be decided.
 * @see SymPy `sympy.concrete.summations.Sum.is_convergent`
 * @example
 * ```ts
 * import { Concrete, ex, oo, sumIsConvergent } from '@symjs/symjs';
 *
 * sumIsConvergent(new Concrete('Sum', [ex`1/k**2`, ex`k`, ex`1`, oo])); // => True
 * ```
 */
export const sumIsConvergent = isConvergent;

/**
 * Alias for {@link isAbsolutelyConvergent}.
 *
 * @deprecated Use {@link isAbsolutelyConvergent}.
 * @param s - The input value.
 * @returns The truth value, or `'unknown'` if convergence cannot be decided.
 * @see SymPy `sympy.concrete.summations.Sum.is_absolutely_convergent`
 * @example
 * ```ts
 * import { Concrete, ex, oo, sumIsAbsolutelyConvergent } from '@symjs/symjs';
 *
 * sumIsAbsolutelyConvergent(new Concrete('Sum', [ex`1/k**2`, ex`k`, ex`1`, oo])); // => True
 * ```
 */
export const sumIsAbsolutelyConvergent = isAbsolutelyConvergent;

/**
 * The order of the Order term in the expression, or NoMatch.
 *
 * @param e - The input expression.
 * @returns The exponent of the order term, or `NoMatch`.
 * @see SymPy `sympy.core.expr.Expr.getn`
 * @example
 * ```ts
 * import { Order, ex, getn } from '@symjs/symjs';
 *
 * getn(new Order([ex`x**3`, ex`x`, ex`0`])); // => 3
 * ```
 */
export function getn(e: _ExprLike_): _Expr_ | NoMatchResult {
  return _orNoMatch_(_getn_(e));
}

/**
 * Extracts the terms that determine the leading order of a sum.
 *
 * @deprecated Internal; removed from the public API in 1.0.
 */
export const extractLeadingOrder = _extractLeadingOrder_;
export { lseries, dir } from './series/lseries';
export { fps, FormalPowerSeries, expRe, hyperRe, rationalIndependent, rationalAlgorithm, simpleDE, solveDe, hyperAlgorithm } from './series/formal';
export { fourierSeries, FourierSeries } from './series/fourier';
// integration of polynomials over polytopes (SymPy sympy.integrals.intpoly); the helpers, whose names collide with
// other SymPy functions (decompose, intersection, norm), are members of the namespace intpoly
export { polytopeIntegrate } from './integrals/intpoly';
/**
 * The integration of polynomials over polytopes and its helpers (`decompose`,
 * `intersection`, `norm`, ...), whose names collide with other functions.
 *
 * @see SymPy `sympy.integrals.intpoly`
 */
export * as intpoly from './integrals/intpoly';
export type { PointLike, SegmentLike, PolygonLike, Hyperplane, Face, Polytope3D, MonomialRecord2D, MonomialRecord3D, MonomialTable3D } from './integrals/intpoly';
// guessing sequences and generating functions (SymPy sympy.concrete.guess) and Pade approximants
export { findSimpleRecurrenceVector, findSimpleRecurrence, rationalize, guessGeneratingFunctionRational, guessGeneratingFunction, guess } from './concrete/guess';
export type { GuessGeneratingFunctionOptions, GuessOptions } from './concrete/guess';
export { approximants } from './series/approximants';
export type { ApproximantsOptions } from './series/approximants';
import { integral as makeIntegral } from './integrals/integrate';
import { asSet as conditionSet } from './solvers/inequalities';
import { processContinuousLimit } from './concrete/exprwithlimits';

/**
 * Construct an unevaluated integral from variables, endpoints, intervals or inequalities.
 *
 * @param ex - The integrand.
 * @param limits - The integration variables with optional endpoints or domains, innermost first.
 * @returns An unevaluated integral with the specified limits.
 * @see SymPy `sympy.integrals.integrals.Integral`
 */
export function integral(ex: _ExprLike_, ...limits: readonly (_ExprLike_ | readonly _ExprLike_[])[]): _Expr_ {
  return makeIntegral(ex, ...limits.map(input => processContinuousLimit(input, conditionSet)));
}

export { variables, hasFiniteLimits, hasReversedLimits } from './concrete/exprwithlimits';
export { gaussLegendre, gaussLaguerre, gaussHermite, gaussGenLaguerre, gaussJacobi, gaussChebyshevT, gaussChebyshevU, gaussLobatto } from './integrals/quadrature';
export type { QuadratureRule } from './integrals/quadrature';
export type { HyperSeriesResult } from './series/formal';

export { SeriesBase } from './series/series_class';

export { orderAt, orderAtOo } from './integrals/orders';
export { Gruntz, gruntz } from './series/gruntz';

export { richardson, shanks } from './series/acceleration';

// Heaviside, DiracDelta and SingularityFunction in parsed strings: parsing may not import the calculus area
import { parserHooks as _parserHooks_ } from './parsing/parser';
import { DiracDelta as _DiracDelta_, Heaviside as _Heaviside_, SingularityFunction as _SingularityFunction_ } from './integrals/transforms/delta';
import { at as _at_ } from './core/guard';
_parserHooks_.constructors.set('Heaviside', (args) => _Heaviside_(_at_(args, 0), args[1]));
_parserHooks_.constructors.set('DiracDelta', (args) => _DiracDelta_(_at_(args, 0), args[1]));
_parserHooks_.constructors.set('SingularityFunction', (args) => _SingularityFunction_(_at_(args, 0), _at_(args, 1), _at_(args, 2)));
// the unevaluated integral transforms in parsed strings
import {
  CosineTransform as _CosineTransform_, FourierTransform as _FourierTransform_, HankelTransform as _HankelTransform_,
  InverseCosineTransform as _InverseCosineTransform_, InverseFourierTransform as _InverseFourierTransform_,
  InverseHankelTransform as _InverseHankelTransform_, InverseLaplaceTransform as _InverseLaplaceTransform_,
  InverseMellinTransform as _InverseMellinTransform_, InverseSineTransform as _InverseSineTransform_,
  LaplaceTransform as _LaplaceTransform_, MellinTransform as _MellinTransform_, SineTransform as _SineTransform_,
} from './integrals/transforms/index';
for (const [name, Transform] of [
  ['LaplaceTransform', _LaplaceTransform_], ['MellinTransform', _MellinTransform_], ['FourierTransform', _FourierTransform_],
  ['InverseFourierTransform', _InverseFourierTransform_], ['SineTransform', _SineTransform_], ['InverseSineTransform', _InverseSineTransform_],
  ['CosineTransform', _CosineTransform_], ['InverseCosineTransform', _InverseCosineTransform_],
] as const) _parserHooks_.constructors.set(name, (args) => new Transform(_at_(args, 0), _at_(args, 1), _at_(args, 2)));
_parserHooks_.constructors.set('HankelTransform', (args) => new _HankelTransform_(_at_(args, 0), _at_(args, 1), _at_(args, 2), _at_(args, 3)));
_parserHooks_.constructors.set('InverseHankelTransform', (args) => new _InverseHankelTransform_(_at_(args, 0), _at_(args, 1), _at_(args, 2), _at_(args, 3)));
_parserHooks_.constructors.set('InverseLaplaceTransform', (args) => new _InverseLaplaceTransform_(_at_(args, 0), _at_(args, 1), _at_(args, 2), args[3]));
_parserHooks_.constructors.set('InverseMellinTransform', (args) => new _InverseMellinTransform_(_at_(args, 0), _at_(args, 1), _at_(args, 2), args[3], args[4]));

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * Entry point `@symjs/symjs/simplify`: simplification and rewriting.
 * @module
 */

// every entry point brings the core with its registrations
import './core';
import { impl } from './core/nodes';
import { isHypergeometric as isHypergeometricOf } from './simplify/gammasimp';
// simplify's final doit stage also works when this entry is imported by itself.
import './calculus/doit';
import { hasFiniteLimits } from './concrete/exprwithlimits';
import { expandHooks } from './simplify/expand';

expandHooks.canDistributeIntegral = (e) => hasFiniteLimits(e) !== false;

export {
  simplify,
  exprEquals,
  clearCoefficients,
  factorSum,
  inversecombine,
  nthroot,
  ncSimplify,
  type SimplifyOptions,
} from './simplify/simplify';
export { powdenestPolar, hyperexpand, Hyper_Function, G_Function, Operator, Formula, HyperRep, devisePlan, devisePlanMeijer, reduceOrder, reduceOrderMeijer, type HyperexpandOptions } from './simplify/hyperexpand';
export { ratsimpmodprime } from './simplify/ratsimp';
export { basicCompare as compare } from './simplify/csemain';
export { gammasimp, combsimp, hypersimilar, isHypergeometric } from './simplify/gammasimp';
export {
  besselsimp,
} from './simplify/besselsimp';
export {
  powsimp,
  powdenest,
  logcombine,
  posify,
} from './simplify/powsimp';
export type { PowsimpOptions } from './simplify/powsimp';
export {
  radsimp,
  collect,
  rcollect,
  collectAbs,
  collectSqrt,
} from './simplify/radsimp';
export {
  rewrite,
  registerRewrite,
} from './simplify/rewrite';
export {
  decomposePower,
  decomposePowerRat,
  gcdTerms,
  factorTerms,
  collectConst,
  signsimp,
  subPre,
  subPost,
} from './simplify/exprtools';
export {
  trigsimp,
  exptrigsimp,
  futrig,
  trigsimpGroebner,
  type TrigsimpOptions,
} from './simplify/trigsimp';
export {
  fu, processCommonAddends, FU, L, TR0, TR1, TR2, TR2i, TR3, TR4, TR5, TR6, TR7, TR8, TR9,
  TR10, TR10i, TR11, TR12, TR12i, TR13, TR14, TR15, TR16, TR22, TR111,
  TRmorrie, TRpower, sincosToSum,
} from './simplify/fu';
export {
  together,
  cancel,
  fraction,
  numer,
  denom,
  ratsimp,
} from './simplify/rational';
export {
} from './simplify/separatevars';
export { hypersimp, separatevars, trigSplit, asFSign1, sqrtBiquadraticDenest } from './simplify/public';
export {
  sqrtdenest,
  sqrtDepth,
  splitSurds,
  radRationalize,
} from './simplify/sqrtdenest';
export { cse, preprocessForCse, postprocessForCse, cseSeparate, repsToposort } from './simplify/csemain';
export type {
  CseOptions,
  CseResult,
  CseReplacement,
  CseSymbol,
  CseItem,
  CseReduced,
  CseOptimization,
  CseHomogeneousInput,
  CseHomogeneous,
} from './simplify/csemain';
export { epath, EPath } from './simplify/epathtools';
export type { EPathFunction } from './simplify/epathtools';

// the groebner method of trigsimp (registered here: a direct import would be an import cycle)
import { ratsimpmodprime as _ratsimpmodprime_ } from './simplify/ratsimp';
import { trigsimpHooks as _trigsimpHooks_ } from './simplify/trigsimp';
_trigsimpHooks_.ratsimpmodprime = _ratsimpmodprime_;
// the Mathematica parser (SymPy sympy.parsing.mathematica): exported here, since it needs the special functions and cancel
export { parseMathematica, MathematicaParser } from './parsing/mathematica';
export type { FullForm } from './parsing/mathematica';
// cancel(...) in parsed strings (parse("cancel(x)"), Mathematica Cancel[...]): parsing may not import simplify
import { parserHooks as _parserHooks_ } from './parsing/parser';
import { cancel as _cancelForParser_ } from './simplify/rational';
import { first as _first_ } from './core/guard';
_parserHooks_.constructors.set('cancel', (args) => _cancelForParser_(_first_(args)));

// ---- deprecated names (kept during 0.x, removed in 1.0; see docs/api-policy.md) ----

import { rewriteRules as _rewriteRules_ } from './simplify/rewrite';
import { keepCoeff as _keepCoeffSympy_ } from './simplify/exprtools';
import { unevaluatedAdd as _unevaluatedAdd_ } from './simplify/exprtools';
import { rewriteExp as _rewriteExp_ } from './simplify/trigsimp';
import { rewriteTrig as _rewriteTrig_ } from './simplify/trigsimp';
import { expsimp as _expsimp_ } from './simplify/trigsimp';
import { exptotrig as _exptotrig_ } from './simplify/trigsimp';
import { combineExp as _combineExp_ } from './simplify/trigsimp';

/**
 * The registered rules for rewriting function applications.
 *
 * @deprecated Internal; removed from the public API in 1.0.
 */
export const rewriteRules = _rewriteRules_;

/**
 * Attaches a coefficient to an expression while preserving its additive grouping.
 *
 * @deprecated Internal; removed from the public API in 1.0.
 */
export const keepCoeffSympy = _keepCoeffSympy_;

/**
 * Builds a sum without evaluating its terms.
 *
 * @deprecated Internal; removed from the public API in 1.0.
 */
export const unevaluatedAdd = _unevaluatedAdd_;

/**
 * Rewrites an expression in terms of exponentials.
 *
 * @deprecated Internal; removed from the public API in 1.0.
 */
export const rewriteExp = _rewriteExp_;

/**
 * Rewrites an expression in terms of trigonometric functions.
 *
 * @deprecated Internal; removed from the public API in 1.0.
 */
export const rewriteTrig = _rewriteTrig_;

/**
 * Simplifies products and powers of exponentials.
 *
 * @deprecated Internal; removed from the public API in 1.0.
 */
export const expsimp = _expsimp_;

/**
 * Rewrites exponentials using trigonometric or hyperbolic functions.
 *
 * @deprecated Internal; removed from the public API in 1.0.
 */
export const exptotrig = _exptotrig_;

/**
 * Combines exponential factors into a single exponential.
 *
 * @deprecated Internal; removed from the public API in 1.0.
 */
export const combineExp = _combineExp_;

impl.isHypergeometric = isHypergeometricOf;

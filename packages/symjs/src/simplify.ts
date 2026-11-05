// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Entry point `@symjs/symjs/simplify`: simplification and rewriting.
 */

// every entry point brings the core with its registrations
import './core';

export {
  simplify,
  type SimplifyOptions,
} from './simplify/simplify';
export { hyperexpand, Hyper_Function, G_Function, Operator, type HyperexpandOptions } from './simplify/hyperexpand';
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
} from './simplify/radsimp';
export {
  rewrite,
  registerRewrite,
} from './simplify/rewrite';
export {
  gcdTerms,
  factorTerms,
  collectConst,
  signsimp,
} from './simplify/exprtools';
export {
  trigsimp,
  exptrigsimp,
  type TrigsimpOptions,
} from './simplify/trigsimp';
export { fu, FU } from './simplify/fu';
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
export { hypersimp, separatevars } from './simplify/public';
export {
  sqrtdenest,
} from './simplify/sqrtdenest';
export { cse } from './simplify/csemain';
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

// ---- deprecated names (kept during 0.x, removed in 1.0; see docs/api-policy.md) ----

import { rewriteRules as _rewriteRules_ } from './simplify/rewrite';
import { keepCoeff as _keepCoeffSympy_ } from './simplify/exprtools';
import { unevaluatedAdd as _unevaluatedAdd_ } from './simplify/exprtools';
import { rewriteExp as _rewriteExp_ } from './simplify/trigsimp';
import { rewriteTrig as _rewriteTrig_ } from './simplify/trigsimp';
import { expsimp as _expsimp_ } from './simplify/trigsimp';
import { exptotrig as _exptotrig_ } from './simplify/trigsimp';
import { combineExp as _combineExp_ } from './simplify/trigsimp';

/** @deprecated Internal; removed from the public API in 1.0. */
export const rewriteRules = _rewriteRules_;

/** @deprecated Internal; removed from the public API in 1.0. */
export const keepCoeffSympy = _keepCoeffSympy_;

/** @deprecated Internal; removed from the public API in 1.0. */
export const unevaluatedAdd = _unevaluatedAdd_;

/** @deprecated Internal; removed from the public API in 1.0. */
export const rewriteExp = _rewriteExp_;

/** @deprecated Internal; removed from the public API in 1.0. */
export const rewriteTrig = _rewriteTrig_;

/** @deprecated Internal; removed from the public API in 1.0. */
export const expsimp = _expsimp_;

/** @deprecated Internal; removed from the public API in 1.0. */
export const exptotrig = _exptotrig_;

/** @deprecated Internal; removed from the public API in 1.0. */
export const combineExp = _combineExp_;

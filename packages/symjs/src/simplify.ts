// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Entry point `@symjs/symjs/simplify`: simplification and rewriting.
 */

// every entry point brings the core with its registrations
import './core';

export {
  simplify,
} from './simplify/simplify';
export { ratsimpmodprime } from './simplify/ratsimpmodprime';
export { gammasimp, combsimp, hypersimp, hypersimilar, isHypergeometric } from './simplify/gammasimp';
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
} from './simplify/trigsimp';
export {
  together,
  cancel,
  fraction,
  ratsimp,
} from './simplify/rational';
export {
  separatevars,
} from './simplify/separatevars';
export {
  sqrtdenest,
} from './simplify/sqrtdenest';

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

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Public forms of simplification functions that report a missing
 * form as NoMatch (docs/api-policy.md).
 */

import type { Expr, ExprLike, Pow, Sym } from '../core/nodes';
import type { NoMatchResult } from '../core/truth';
import { orNoMatch } from '../core/truth';
import { hypersimp as hypersimpImpl } from './gammasimp';
import { separatevars as separatevarsImpl } from './separatevars';
import { hyperexpand } from './hyperexpand';
import { simplifyHooks } from './simplify';
import { asFSign1 as asFSign1Impl, trigSplit as trigSplitImpl } from './fu';
import { sqrtBiquadraticDenest as sqrtBiquadraticDenestImpl } from './sqrtdenest';

// the hyperexpand step of simplify (a direct import would be an import cycle)
simplifyHooks.hyperexpand = (e) => hyperexpand(e);

/** Recognize a pair of trigonometric terms, or return NoMatch. */
export function trigSplit(a: Expr, b: Expr, two = false): [Expr, number, number, Expr, Expr, boolean] | NoMatchResult {
  return orNoMatch(trigSplitImpl(a, b, two));
}

/** Split g*(f + s), with s = +/-1, or return NoMatch. */
export function asFSign1(e: Expr): [Expr, Expr, Expr] | NoMatchResult {
  return orNoMatch(asFSign1Impl(e));
}

/** Denest a biquadratic square root, or return NoMatch. */
export function sqrtBiquadraticDenest(expr: Pow, a: Expr, b: Expr, r: Expr, d2: Expr): Expr | NoMatchResult {
  return orNoMatch(sqrtBiquadraticDenestImpl(expr, a, b, r, d2));
}

/** SymPy hypersimp: f(k + 1)/f(k) simplified, or NoMatch when f is not hypergeometric in k. */
export function hypersimp(f: ExprLike, k: Expr): Expr | NoMatchResult {
  return orNoMatch(hypersimpImpl(f, k));
}

/**
 * SymPy separatevars: the expression with its variables separated; with
 * `dict`, {symbol: factor, coeff: rest}, or NoMatch when it does not separate.
 * `symbols: null` groups the entire expression under the coeff key.
 */
export function separatevars(e: ExprLike, opts: { symbols?: readonly Sym[] | null; dict: true; force?: boolean }): Map<Sym | 'coeff', Expr> | NoMatchResult;
export function separatevars(e: ExprLike, opts?: { symbols?: readonly Sym[] | null; dict?: false; force?: boolean }): Expr;
export function separatevars(e: ExprLike, opts: { symbols?: readonly Sym[] | null; dict?: boolean; force?: boolean } = {}): Expr | Map<Sym | 'coeff', Expr> | NoMatchResult {
  return orNoMatch(separatevarsImpl(e, opts));
}

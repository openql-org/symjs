// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Public forms of simplification functions that report a missing
 * form as NoMatch (docs/api-policy.md).
 */

import type { Expr, ExprLike, Sym } from '../core/nodes';
import type { NoMatchResult } from '../core/truth';
import { orNoMatch } from '../core/truth';
import { hypersimp as hypersimpImpl } from './gammasimp';
import { separatevars as separatevarsImpl } from './separatevars';

/** SymPy hypersimp: f(k + 1)/f(k) simplified, or NoMatch when f is not hypergeometric in k. */
export function hypersimp(f: ExprLike, k: Expr): Expr | NoMatchResult {
  return orNoMatch(hypersimpImpl(f, k));
}

/**
 * SymPy separatevars: the expression with its variables separated; with
 * `dict`, {symbol: factor, coeff: rest}, or NoMatch when it does not separate.
 */
export function separatevars(e: ExprLike, opts: { symbols?: readonly Sym[]; dict: true; force?: boolean }): Map<Sym | 'coeff', Expr> | NoMatchResult;
export function separatevars(e: ExprLike, opts?: { symbols?: readonly Sym[]; dict?: false; force?: boolean }): Expr;
export function separatevars(e: ExprLike, opts: { symbols?: readonly Sym[]; dict?: boolean; force?: boolean } = {}): Expr | Map<Sym | 'coeff', Expr> | NoMatchResult {
  return orNoMatch(separatevarsImpl(e, opts));
}

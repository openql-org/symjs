// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Public forms of the core queries (docs/api-policy.md): three-valued
 * answers as Truth, a missing form as NoMatch; never undefined.
 */

import { Expr, ExprLike, Sym } from './nodes';
import { sympify } from './ops';
import * as A from './assumptions';
import * as M from './methods';
import { match as matchImpl } from './match';
import { NoMatch, NoMatchResult, Truth, orNoMatch, toTruth } from './truth';

/** e is real (SymPy is_real): true, false or 'unknown'. */
export const isReal = (e: ExprLike): Truth => toTruth(A.isReal(sympify(e)));
/** e is positive (SymPy is_positive). */
export const isPositive = (e: ExprLike): Truth => toTruth(A.isPositive(sympify(e)));
/** e is negative (SymPy is_negative). */
export const isNegative = (e: ExprLike): Truth => toTruth(A.isNegative(sympify(e)));
/** e is nonnegative (SymPy is_nonnegative). */
export const isNonNegative = (e: ExprLike): Truth => toTruth(A.isNonNegative(sympify(e)));
/** e is nonzero (SymPy is_nonzero). */
export const isNonZero = (e: ExprLike): Truth => toTruth(A.isNonZero(sympify(e)));
/** e is zero (SymPy is_zero). */
export const isZero = (e: ExprLike): Truth => toTruth(A.isZero(sympify(e)));
/** e is an integer (SymPy is_integer). */
export const isIntegerValued = (e: ExprLike): Truth => toTruth(A.isIntegerQ(sympify(e)));

/**
 * SymPy Expr.match: the values of the Wilds making pattern equal to expr,
 * or NoMatch.
 */
export function match(expr: ExprLike, pattern: ExprLike, opts: { old?: boolean } = {}): Map<Sym, Expr> | NoMatchResult {
  return orNoMatch(matchImpl(expr, pattern, opts));
}

/** SymPy extract_multiplicatively: e/c when it is "simpler", else NoMatch. */
export function extractMultiplicatively(e: ExprLike, c: ExprLike): Expr | NoMatchResult {
  return orNoMatch(M.extractMultiplicatively(e, c));
}
/** SymPy extract_additively: e - c when it is "simpler", else NoMatch. */
export function extractAdditively(e: ExprLike, c: ExprLike): Expr | NoMatchResult {
  return orNoMatch(M.extractAdditively(e, c));
}
/** SymPy as_coefficient: the coefficient of x in e, or NoMatch when e is not c*x. */
export function asCoefficient(e: ExprLike, x: ExprLike): Expr | NoMatchResult {
  return orNoMatch(M.asCoefficient(e, x));
}
/** SymPy is_meromorphic(x, a). */
export function isMeromorphic(e: ExprLike, x: Expr, a: ExprLike): Truth {
  return toTruth(M.isMeromorphic(e, x, a));
}

export { NoMatch };

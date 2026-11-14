// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Public forms of the core queries (docs/api-policy.md): three-valued
 * answers as Truth, a missing form as NoMatch; never undefined.
 */

import type { Expr, ExprLike, Sym } from './nodes';
import { Special } from './nodes';
import { sympify } from './ops';
import * as A from './assumptions';
import * as M from './methods';
import { match as matchImpl } from './match';
import type { NoMatchResult, Truth } from './truth';
import { NoMatch, orNoMatch, toTruth } from './truth';
import { ask, Q } from './refine';

/** e is real (SymPy is_real): true, false or 'unknown'. */
export const isReal = (e: ExprLike): Truth => {
  const x = sympify(e);
  // oo, -oo and zoo are not real numbers; nan is undecided
  if (x instanceof Special) return x.name === 'nan' ? 'unknown' : false;
  return toTruth(A.isReal(x));
};
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
/** e is irrational (SymPy is_irrational). */
export const isIrrational = (e: ExprLike): Truth => ask(Q.irrational(e));
/** e is algebraic (SymPy is_algebraic). */
export const isAlgebraic = (e: ExprLike): Truth => ask(Q.algebraic(e));
/** e is a complex number (SymPy is_complex). */
export const isComplex = (e: ExprLike): Truth => ask(Q.complex(e));
/** e is finite (SymPy is_finite). */
export const isFinite = (e: ExprLike): Truth => ask(Q.finite(e));
/** e is a prime integer (SymPy is_prime). */
export const isPrime = (e: ExprLike): Truth => ask(Q.prime(e));

/**
 * SymPy Expr.match: the values of the Wilds making pattern equal to expr,
 * or NoMatch.
 */
export function match(expr: ExprLike, pattern: ExprLike, opts: { old?: boolean } = {}): Map<Sym, Expr> | NoMatchResult {
  return orNoMatch(matchImpl(expr, pattern, opts));
}

/**
 * SymPy Basic.matches: the values of the Wilds making pattern equal to expr
 * (pattern.matches(expr) is expr.match(pattern)), or NoMatch.
 */
export function matches(pattern: ExprLike, expr: ExprLike, opts: { old?: boolean } = {}): Map<Sym, Expr> | NoMatchResult {
  return match(expr, pattern, opts);
}

/** SymPy getO: the additive order term O(...) of e, or NoMatch when there is none. */
export function getO(e: ExprLike): Expr | NoMatchResult {
  return orNoMatch(M.getO(e));
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

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Public forms of the core queries (docs/api-policy.md): three-valued
 * answers as Truth, a missing form as NoMatch; never undefined.
 */

import type { Expr, ExprLike, Sym } from './nodes';
import { mul, pow, sub, sympify } from './ops';
import { E, I, headName } from './nodes';
import type { Head } from './nodes';
import { SINGULARITIES } from './singularities';
import * as M from './methods';
import { match as matchImpl } from './match';
import type { NoMatchResult, Truth } from './truth';
import { NoMatch, orNoMatch, toTruth } from './truth';
import { fact } from './exprfacts';

/** SymPy `e.is_<name>` of the assumption fact name, as a Truth. */
const factTruth = (e: ExprLike, name: string): Truth => toTruth(fact(sympify(e), name));

/** e is real (SymPy is_real): true, false or 'unknown'. */
export const isReal = (e: ExprLike): Truth => factTruth(e, 'real');
/** e is positive (SymPy is_positive). */
export const isPositive = (e: ExprLike): Truth => factTruth(e, 'positive');
/** e is negative (SymPy is_negative). */
export const isNegative = (e: ExprLike): Truth => factTruth(e, 'negative');
/** e is nonnegative (SymPy is_nonnegative). */
export const isNonnegative = (e: ExprLike): Truth => factTruth(e, 'nonnegative');
/** e is nonzero (SymPy is_nonzero). */
export const isNonzero = (e: ExprLike): Truth => factTruth(e, 'nonzero');
/** e is zero (SymPy is_zero). */
export const isZero = (e: ExprLike): Truth => factTruth(e, 'zero');
/** e is an integer (SymPy is_integer). */
export const isIntegerValued = (e: ExprLike): Truth => factTruth(e, 'integer');
/** e is irrational (SymPy is_irrational). */
export const isIrrational = (e: ExprLike): Truth => factTruth(e, 'irrational');
/** e is algebraic (SymPy is_algebraic). */
export const isAlgebraic = (e: ExprLike): Truth => factTruth(e, 'algebraic');
/** e is a complex number (SymPy is_complex). */
export const isComplex = (e: ExprLike): Truth => factTruth(e, 'complex');
/** e is finite (SymPy is_finite). */
export const isFinite = (e: ExprLike): Truth => factTruth(e, 'finite');
/** e is a prime integer (SymPy is_prime). */
export const isPrime = (e: ExprLike): Truth => factTruth(e, 'prime');
/** e is nonpositive (SymPy is_nonpositive). */
export const isNonpositive = (e: ExprLike): Truth => factTruth(e, 'nonpositive');
/** e is an even integer (SymPy is_even). */
export const isEven = (e: ExprLike): Truth => factTruth(e, 'even');
/** e is an odd integer (SymPy is_odd). */
export const isOdd = (e: ExprLike): Truth => factTruth(e, 'odd');
/** e is a nonzero imaginary number (SymPy is_imaginary). */
export const isImaginary = (e: ExprLike): Truth => factTruth(e, 'imaginary');
/** e is hermitian (SymPy is_hermitian). */
export const isHermitian = (e: ExprLike): Truth => factTruth(e, 'hermitian');
/** e is antihermitian (SymPy is_antihermitian). */
export const isAntihermitian = (e: ExprLike): Truth => factTruth(e, 'antihermitian');
/** e is real or infinite, and negative (SymPy is_extended_negative). */
export const isExtendedNegative = (e: ExprLike): Truth => factTruth(e, 'extended_negative');
/** e is real or infinite, and positive (SymPy is_extended_positive). */
export const isExtendedPositive = (e: ExprLike): Truth => factTruth(e, 'extended_positive');
/** e is a point of the Riemann surface of the logarithm (SymPy is_polar). */
export const isPolar = (e: ExprLike): Truth => factTruth(e, 'polar');
/** e is composite: a positive integer with a divisor other than 1 and itself (SymPy is_composite). */
export const isComposite = (e: ExprLike): Truth => factTruth(e, 'composite');
/** e is real or infinite and not positive (SymPy is_extended_nonpositive). */
export const isExtendedNonpositive = (e: ExprLike): Truth => factTruth(e, 'extended_nonpositive');
/** e is real or infinite and not zero (SymPy is_extended_nonzero). */
export const isExtendedNonzero = (e: ExprLike): Truth => factTruth(e, 'extended_nonzero');
/** e is a real number that is not an integer (SymPy is_noninteger). */
export const isNoninteger = (e: ExprLike): Truth => factTruth(e, 'noninteger');
/** e is a transcendental number (SymPy is_transcendental). */
export const isTranscendental = (e: ExprLike): Truth => factTruth(e, 'transcendental');
/** e commutes under multiplication (SymPy is_commutative). */
export const isCommutative = (e: ExprLike): Truth => factTruth(e, 'commutative');

/** A finite singular point of the table: an integer, I, -I or -1/E. */
function singularPoint(p: string): Expr {
  const sign = p.startsWith('-') ? -1 : 1;
  const body = sign < 0 ? p.slice(1) : p;
  const value = body === 'I' ? I : body === '1/E' ? pow(E, -1) : sympify(Number(body));
  return sign < 0 ? mul(-1, value) : value;
}

/**
 * SymPy `f.is_singular(a)`: whether `a` is an essential singularity or a branch point of the
 * function `f` (`sin`, `log`, ... or its name), or the function is not holomorphic anywhere
 * (`Abs`, `re`); 'unknown' for a function without recorded singularities.
 */
export function isSingular(f: Head | string, aIn: ExprLike): Truth {
  const name = typeof f === 'string' ? f : headName(f);
  // symjs names the absolute value abs (SymPy class Abs)
  const points = name === undefined ? undefined : SINGULARITIES[name === 'abs' ? 'Abs' : name];
  if (points === undefined) return 'unknown';
  if (typeof points === 'boolean') return points;
  const a = sympify(aIn);
  // SymPy fuzzy_or: true when one is true, false when all are false
  let unknown = false;
  for (const p of points) {
    const t = p === 'zoo' ? factTruth(a, 'infinite') : factTruth(sub(a, singularPoint(p)), 'zero');
    if (t === true) return true;
    if (t === 'unknown') unknown = true;
  }
  return unknown ? 'unknown' : false;
}


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


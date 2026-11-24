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

/**
 * Tests whether the expression is real.
 *
 * @param e - The input expression.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 * @see SymPy `sympy.core.expr.Expr.is_real`
 */
export const isReal = (e: ExprLike): Truth => factTruth(e, 'real');
/**
 * Tests whether the expression is positive.
 *
 * @param e - The input expression.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 * @see SymPy `sympy.core.expr.Expr.is_positive`
 */
export const isPositive = (e: ExprLike): Truth => factTruth(e, 'positive');
/**
 * Tests whether the expression is negative.
 *
 * @param e - The input expression.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 * @see SymPy `sympy.core.expr.Expr.is_negative`
 */
export const isNegative = (e: ExprLike): Truth => factTruth(e, 'negative');
/**
 * Tests whether the expression is nonnegative.
 *
 * @param e - The input expression.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 * @see SymPy `sympy.core.expr.Expr.is_nonnegative`
 */
export const isNonnegative = (e: ExprLike): Truth => factTruth(e, 'nonnegative');
/**
 * Tests whether the expression is nonzero.
 *
 * @param e - The input expression.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 * @see SymPy `sympy.core.expr.Expr.is_nonzero`
 */
export const isNonzero = (e: ExprLike): Truth => factTruth(e, 'nonzero');
/**
 * Tests whether the expression is zero.
 *
 * @param e - The input expression.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 * @see SymPy `sympy.core.expr.Expr.is_zero`
 */
export const isZero = (e: ExprLike): Truth => factTruth(e, 'zero');
/**
 * Tests whether the expression is an integer.
 *
 * @param e - The input expression.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 * @see SymPy `sympy.core.expr.Expr.is_integer`
 */
export const isIntegerValued = (e: ExprLike): Truth => factTruth(e, 'integer');
/**
 * Tests whether the expression is irrational.
 *
 * @param e - The input expression.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 * @see SymPy `sympy.core.expr.Expr.is_irrational`
 */
export const isIrrational = (e: ExprLike): Truth => factTruth(e, 'irrational');
/**
 * Tests whether the expression is algebraic.
 *
 * @param e - The input expression.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 * @see SymPy `sympy.core.expr.Expr.is_algebraic`
 */
export const isAlgebraic = (e: ExprLike): Truth => factTruth(e, 'algebraic');
/**
 * Tests whether the expression is a complex number.
 *
 * @param e - The input expression.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 * @see SymPy `sympy.core.expr.Expr.is_complex`
 */
export const isComplex = (e: ExprLike): Truth => factTruth(e, 'complex');
/**
 * Tests whether the expression is finite.
 *
 * @param e - The input expression.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 * @see SymPy `sympy.core.expr.Expr.is_finite`
 */
export const isFinite = (e: ExprLike): Truth => factTruth(e, 'finite');
/**
 * Tests whether the expression is a prime integer.
 *
 * @param e - The input expression.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 * @see SymPy `sympy.core.expr.Expr.is_prime`
 */
export const isPrime = (e: ExprLike): Truth => factTruth(e, 'prime');
/**
 * Tests whether the expression is nonpositive.
 *
 * @param e - The input expression.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 * @see SymPy `sympy.core.expr.Expr.is_nonpositive`
 */
export const isNonpositive = (e: ExprLike): Truth => factTruth(e, 'nonpositive');
/**
 * Tests whether the expression is an even integer.
 *
 * @param e - The input expression.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 * @see SymPy `sympy.core.expr.Expr.is_even`
 */
export const isEven = (e: ExprLike): Truth => factTruth(e, 'even');
/**
 * Tests whether the expression is an odd integer.
 *
 * @param e - The input expression.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 * @see SymPy `sympy.core.expr.Expr.is_odd`
 */
export const isOdd = (e: ExprLike): Truth => factTruth(e, 'odd');
/**
 * Tests whether the expression is a nonzero imaginary number.
 *
 * @param e - The input expression.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 * @see SymPy `sympy.core.expr.Expr.is_imaginary`
 */
export const isImaginary = (e: ExprLike): Truth => factTruth(e, 'imaginary');
/**
 * Tests whether the expression is hermitian.
 *
 * @param e - The input expression.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 * @see SymPy `sympy.core.expr.Expr.is_hermitian`
 */
export const isHermitian = (e: ExprLike): Truth => factTruth(e, 'hermitian');
/**
 * Tests whether the expression is antihermitian.
 *
 * @param e - The input expression.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 * @see SymPy `sympy.core.expr.Expr.is_antihermitian`
 */
export const isAntihermitian = (e: ExprLike): Truth => factTruth(e, 'antihermitian');
/**
 * Tests whether the expression is real or infinite, and negative.
 *
 * @param e - The input expression.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 * @see SymPy `sympy.core.expr.Expr.is_extended_negative`
 */
export const isExtendedNegative = (e: ExprLike): Truth => factTruth(e, 'extended_negative');
/**
 * Tests whether the expression is real or infinite, and positive.
 *
 * @param e - The input expression.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 * @see SymPy `sympy.core.expr.Expr.is_extended_positive`
 */
export const isExtendedPositive = (e: ExprLike): Truth => factTruth(e, 'extended_positive');
/**
 * Tests whether the expression is a point of the Riemann surface of the logarithm.
 *
 * @param e - The input expression.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 * @see SymPy `sympy.core.expr.Expr.is_polar`
 */
export const isPolar = (e: ExprLike): Truth => factTruth(e, 'polar');
/**
 * Tests whether the expression is composite.
 *
 * @param e - The input expression.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 * @see SymPy `sympy.core.expr.Expr.is_composite`
 */
export const isComposite = (e: ExprLike): Truth => factTruth(e, 'composite');
/**
 * Tests whether the expression is real or infinite and not positive.
 *
 * @param e - The input expression.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 * @see SymPy `sympy.core.expr.Expr.is_extended_nonpositive`
 */
export const isExtendedNonpositive = (e: ExprLike): Truth => factTruth(e, 'extended_nonpositive');
/**
 * Tests whether the expression is real or infinite and not zero.
 *
 * @param e - The input expression.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 * @see SymPy `sympy.core.expr.Expr.is_extended_nonzero`
 */
export const isExtendedNonzero = (e: ExprLike): Truth => factTruth(e, 'extended_nonzero');
/**
 * Tests whether the expression is a real number that is not an integer.
 *
 * @param e - The input expression.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 * @see SymPy `sympy.core.expr.Expr.is_noninteger`
 */
export const isNoninteger = (e: ExprLike): Truth => factTruth(e, 'noninteger');
/**
 * Tests whether the expression is a transcendental number.
 *
 * @param e - The input expression.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 * @see SymPy `sympy.core.expr.Expr.is_transcendental`
 */
export const isTranscendental = (e: ExprLike): Truth => factTruth(e, 'transcendental');
/**
 * Tests whether the expression commutes under multiplication.
 *
 * @param e - The input expression.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 * @see SymPy `sympy.core.expr.Expr.is_commutative`
 */
export const isCommutative = (e: ExprLike): Truth => factTruth(e, 'commutative');

/** A finite singular point of the table: an integer, I, -I or -1/E. */
function singularPoint(p: string): Expr {
  const sign = p.startsWith('-') ? -1 : 1;
  const body = sign < 0 ? p.slice(1) : p;
  const value = body === 'I' ? I : body === '1/E' ? pow(E, -1) : sympify(Number(body));
  return sign < 0 ? mul(-1, value) : value;
}

/**
 * Whether `a` is an essential singularity or a branch point of the
 * function `f` (`sin`, `log`, ... or its name), or the function is not holomorphic anywhere
 * (`Abs`, `re`); 'unknown' for a function without recorded singularities.
 *
 * @param f - The function or expression to transform.
 * @param aIn - The point to test.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 * @see SymPy `sympy.core.function.Function.is_singular`
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
 * The values of the Wilds making pattern equal to expr,
 * or NoMatch.
 *
 * @param expr - The input expression.
 * @param pattern - The pattern containing the wildcards to bind.
 * @param opts - Set `old` to use algebraic matching.
 * @returns The wildcard bindings, or `NoMatch`.
 * @see SymPy `sympy.core.basic.Basic.match`
 * @example
 * ```ts
 * import { Wild, ex, match } from '@symjs/symjs';
 *
 * match(ex`x`, new Wild('p')); // => {p_: x}
 * ```
 */
export function match(expr: ExprLike, pattern: ExprLike, opts: { old?: boolean } = {}): Map<Sym, Expr> | NoMatchResult {
  return orNoMatch(matchImpl(expr, pattern, opts));
}

/**
 * The values of the Wilds making pattern equal to expr
 * (pattern.matches(expr) is expr.match(pattern)), or NoMatch.
 *
 * @param pattern - The pattern containing the wildcards to bind.
 * @param expr - The input expression.
 * @param opts - Set `old` to use algebraic matching.
 * @returns The wildcard bindings, or `NoMatch`.
 * @see SymPy `sympy.core.basic.Basic.matches`
 * @example
 * ```ts
 * import { Wild, ex, matches } from '@symjs/symjs';
 *
 * matches(new Wild('p'), ex`x`); // => {p_: x}
 * ```
 */
export function matches(pattern: ExprLike, expr: ExprLike, opts: { old?: boolean } = {}): Map<Sym, Expr> | NoMatchResult {
  return match(expr, pattern, opts);
}

/**
 * The additive order term O(...) of e, or NoMatch when there is none.
 *
 * @param e - The input expression.
 * @returns The additive order term, or `NoMatch`.
 * @see SymPy `sympy.core.expr.Expr.getO`
 */
export function getO(e: ExprLike): Expr | NoMatchResult {
  return orNoMatch(M.getO(e));
}

/**
 * Extracts `c` as a factor of `e` and returns the remaining quotient, or `NoMatch` if extraction fails.
 *
 * @param e - The input expression.
 * @param c - The factor to remove.
 * @returns The remaining quotient, or `NoMatch` when extraction fails.
 * @see SymPy `sympy.core.expr.Expr.extract_multiplicatively`
 * @example
 * ```ts
 * import { ex, extractMultiplicatively } from '@symjs/symjs';
 *
 * extractMultiplicatively(ex`2*x*y`, ex`x`); // => 2*y
 * ```
 */
export function extractMultiplicatively(e: ExprLike, c: ExprLike): Expr | NoMatchResult {
  return orNoMatch(M.extractMultiplicatively(e, c));
}
/**
 * Subtracts `c` from `e` when the matching numeric coefficients move toward zero without changing
 * sign. Returns `NoMatch` when extraction fails.
 *
 * @param e - The input expression.
 * @param c - The term to subtract.
 * @returns The remaining difference, or `NoMatch` when extraction fails.
 * @see SymPy `sympy.core.expr.Expr.extract_additively`
 * @example
 * ```ts
 * import { ex, extractAdditively } from '@symjs/symjs';
 *
 * extractAdditively(ex`2*x + 3`, ex`x + 1`); // => x + 2
 * ```
 */
export function extractAdditively(e: ExprLike, c: ExprLike): Expr | NoMatchResult {
  return orNoMatch(M.extractAdditively(e, c));
}
/**
 * The coefficient of x in e, or NoMatch when e is not c*x.
 *
 * @param e - The input expression.
 * @param x - The factor whose coefficient to extract.
 * @returns The coefficient of the factor, or `NoMatch`.
 * @see SymPy `sympy.core.expr.Expr.as_coefficient`
 * @example
 * ```ts
 * import { asCoefficient, ex } from '@symjs/symjs';
 *
 * asCoefficient(ex`E`, ex`E`); // => 1
 * asCoefficient(ex`2*E`, ex`E`); // => 2
 * ```
 */
export function asCoefficient(e: ExprLike, x: ExprLike): Expr | NoMatchResult {
  return orNoMatch(M.asCoefficient(e, x));
}
/**
 * Tests whether an expression is meromorphic in a variable at a point.
 *
 * @param e - The input expression.
 * @param x - The complex variable.
 * @param a - The point to test.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 * @see SymPy `sympy.core.expr.Expr.is_meromorphic`
 * @example
 * ```ts
 * import { ex, isMeromorphic } from '@symjs/symjs';
 *
 * isMeromorphic(ex`log(x)`, ex`x`, 0); // => False
 * isMeromorphic(ex`log(x)`, ex`x`, -1); // => True
 * ```
 */
export function isMeromorphic(e: ExprLike, x: Expr, a: ExprLike): Truth {
  return toTruth(M.isMeromorphic(e, x, a));
}

export { NoMatch };


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

/**
 * Recognize a pair of trigonometric terms, or return NoMatch.
 *
 * @param a - The first operand.
 * @param b - The second operand.
 * @param two - Whether to match products of two trigonometric functions.
 * @returns The factored trigonometric components, or `NoMatch`.
 * @see SymPy `sympy.simplify.fu.trig_split`
 * @example
 * ```ts
 * import { ex, isNoMatch, trigSplit } from '@symjs/symjs';
 *
 * isNoMatch(trigSplit(ex`cos(x)`, ex`sin(x)`)); // => True
 * ```
 */
export function trigSplit(a: Expr, b: Expr, two = false): [Expr, number, number, Expr, Expr, boolean] | NoMatchResult {
  return orNoMatch(trigSplitImpl(a, b, two));
}

/**
 * Split g*(f + s), with s = +/-1, or return NoMatch.
 *
 * @remarks
 * For `as_f_sign_1(x + 1)`, SymPy displays `(1, x, 1)`. For `as_f_sign_1(x - 1)`, SymPy displays `(1, x, -1)`.
 * @param e - The input expression.
 * @returns The common factor, expression and sign, or `NoMatch`.
 * @see SymPy `sympy.simplify.fu.as_f_sign_1`
 * @example
 * ```ts
 * import { asFSign1, ex } from '@symjs/symjs';
 *
 * asFSign1(ex`x + 1`); // => [1, x, 1]
 * asFSign1(ex`x - 1`); // => [1, x, -1]
 * ```
 */
export function asFSign1(e: Expr): [Expr, Expr, Expr] | NoMatchResult {
  return orNoMatch(asFSign1Impl(e));
}

/**
 * Denest a biquadratic square root, or return NoMatch.
 *
 * @param expr - The input expression.
 * @param a - The part of the radicand independent of the inner square root.
 * @param b - The coefficient of the inner square root.
 * @param r - The inner radicand.
 * @param d2 - The discriminant `a**2 - b**2*r`.
 * @returns The denested root, or `NoMatch`.
 * @see SymPy `sympy.simplify.sqrtdenest.sqrt_biquadratic_denest`
 * @example
 * ```ts
 * import { Pow, ex, sqrtBiquadraticDenest } from '@symjs/symjs';
 *
 * const a = ex`5*sqrt(2) + 8`, b = ex`2*sqrt(2) + 4`, r = ex`2 + sqrt(2)`;
 * const z = new Pow(ex`${a} + ${b}*sqrt(${r})`, ex`1/2`);
 * sqrtBiquadraticDenest(z, a, b, r, ex`${a}**2 - ${b}**2*${r}`); // => sqrt(2) + sqrt(sqrt(2) + 2) + 2
 * ```
 */
export function sqrtBiquadraticDenest(expr: Pow, a: Expr, b: Expr, r: Expr, d2: Expr): Expr | NoMatchResult {
  return orNoMatch(sqrtBiquadraticDenestImpl(expr, a, b, r, d2));
}

/**
 * Simplifies the successive-term ratio `f(k + 1)/f(k)` to a rational function of `k`,
 * returning `NoMatch` when `f` is not hypergeometric in `k`.
 *
 * @param f - The function or expression to transform.
 * @param k - The index.
 * @returns The simplified ratio of successive terms, or `NoMatch`.
 * @see SymPy `sympy.simplify.simplify.hypersimp`
 */
export function hypersimp(f: ExprLike, k: Expr): Expr | NoMatchResult {
  return orNoMatch(hypersimpImpl(f, k));
}

/**
 * The expression with its variables separated; with
 * `dict`, {symbol: factor, coeff: rest}, or NoMatch when it does not separate.
 * `symbols: null` groups the entire expression under the coeff key.
 *
 * @param e - The input expression.
 * @param opts - `symbols` selects the variables, `dict` requests the factor map and `force` relaxes power-splitting assumptions.
 * @returns The matching result, or `NoMatch` when the required form is absent.
 * @see SymPy `sympy.simplify.simplify.separatevars`
 * @example
 * ```ts
 * import { ex, separatevars } from '@symjs/symjs';
 *
 * separatevars(ex`(x*y)**y`); // => (x*y)**y
 * separatevars(ex`-3*x**2 + x*y + x`); // => -x*(3*x - y - 1)
 * ```
 */
export function separatevars(e: ExprLike, opts: { symbols?: readonly Sym[] | null; dict: true; force?: boolean }): Map<Sym | 'coeff', Expr> | NoMatchResult;
export function separatevars(e: ExprLike, opts?: { symbols?: readonly Sym[] | null; dict?: false; force?: boolean }): Expr;
export function separatevars(e: ExprLike, opts: { symbols?: readonly Sym[] | null; dict?: boolean; force?: boolean } = {}): Expr | Map<Sym | 'coeff', Expr> | NoMatchResult {
  return orNoMatch(separatevarsImpl(e, opts));
}

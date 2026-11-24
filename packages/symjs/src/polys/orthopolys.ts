// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/orthopolys.py and named_poly of
// polys/polytools.py), Copyright (c) 2006-2023 SymPy Development Team,
// BSD 3-Clause License (see LICENSE).

/**
 * @file The orthogonal polynomials of a given degree as expressions or Poly
 * objects (SymPy jacobi_poly, gegenbauer_poly, chebyshevt_poly,
 * chebyshevu_poly, hermite_poly, hermite_prob_poly, legendre_poly and
 * laguerre_poly).
 */

import type { Expr, ExprLike } from '../core/nodes';
import { Dummy } from '../core/nodes';
import { sympify } from '../core/ops';
import {
  type Coeffs,
  chebyshevtCoeffs,
  chebyshevuCoeffs,
  coeffsExpr,
  gegenbauerCoeffs,
  hermiteCoeffs,
  hermiteProbCoeffs,
  jacobiCoeffs,
  laguerreCoeffs,
  legendreCoeffs,
} from '../functions/special/orthocoeffs';
import { Poly } from './sympoly';
import { constructDomain } from './constructor';

/** Options of the polynomial generators. */
export interface NamedPolyOptions {
  /** Return a Poly instead of an expression. */
  polys?: boolean;
}

/** The result of a polynomial generator: a Poly with `{ polys: true }`, else an expression. */
export type NamedPolyResult<O extends NamedPolyOptions> = O extends { polys: true } ? Poly : Expr;

/**
 * SymPy named_poly: the polynomial of index n in x, or in a dummy variable
 * (a PurePoly) when x is not given.
 */
function namedPoly(n: number, gen: (n: number) => Coeffs, name: string, x: ExprLike | undefined, opts: NamedPolyOptions, field = true, parameters: readonly ExprLike[] = []): Expr | Poly {
  if (!Number.isInteger(n) || n < 0) throw new RangeError(`Cannot generate ${name} of index ${n}`);
  const v = x === undefined ? new Dummy('x') : sympify(x);
  const cs = gen(n);
  const e = coeffsExpr(cs, v);
  if (!opts.polys) return e;
  const domain = field ? constructDomain(parameters, { field: true })[0] : 'ZZ';
  return Poly.from(e, [v], { pure: x === undefined, domain });
}

/**
 * The Jacobi polynomial P_n^(a,b)(x).
 *
 * @param n - Nonnegative index of the polynomial family.
 * @param a - First shape parameter.
 * @param b - Second Jacobi parameter.
 * @param x - Variable or evaluation point of the polynomial.
 * @param opts - Set `polys` to return a polynomial object.
 * @returns The polynomial as an expression, or a `Poly` with `polys: true`.
 * @throws RangeError when the index is not a nonnegative integer.
 * @see SymPy `sympy.polys.orthopolys.jacobi_poly`
 */
export function jacobiPoly<O extends NamedPolyOptions = Record<never, never>>(n: number, a: ExprLike, b: ExprLike, x?: ExprLike, opts?: O): NamedPolyResult<O>;
export function jacobiPoly(n: number, a: ExprLike, b: ExprLike, x?: ExprLike, opts: NamedPolyOptions = {}): Expr | Poly {
  return namedPoly(n, (k) => jacobiCoeffs(k, sympify(a), sympify(b)), 'Jacobi polynomial', x, opts, true, [a, b]);
}

/**
 * The Gegenbauer polynomial C_n^(a)(x).
 *
 * @param n - Nonnegative index of the polynomial family.
 * @param a - Parameter of the polynomial family.
 * @param x - Variable or evaluation point of the polynomial.
 * @param opts - Set `polys` to return a polynomial object.
 * @returns The polynomial as an expression, or a `Poly` with `polys: true`.
 * @throws RangeError when the index is not a nonnegative integer.
 * @see SymPy `sympy.polys.orthopolys.gegenbauer_poly`
 */
export function gegenbauerPoly<O extends NamedPolyOptions = Record<never, never>>(n: number, a: ExprLike, x?: ExprLike, opts?: O): NamedPolyResult<O>;
export function gegenbauerPoly(n: number, a: ExprLike, x?: ExprLike, opts: NamedPolyOptions = {}): Expr | Poly {
  return namedPoly(n, (k) => gegenbauerCoeffs(k, sympify(a)), 'Gegenbauer polynomial', x, opts, true, [a]);
}

/**
 * The Chebyshev polynomial of the first kind T_n(x).
 *
 * @param n - Nonnegative index of the polynomial family.
 * @param x - Variable or evaluation point of the polynomial.
 * @param opts - Set `polys` to return a polynomial object.
 * @returns The polynomial as an expression, or a `Poly` with `polys: true`.
 * @throws RangeError when the index is not a nonnegative integer.
 * @see SymPy `sympy.polys.orthopolys.chebyshevt_poly`
 */
export function chebyshevtPoly<O extends NamedPolyOptions = Record<never, never>>(n: number, x?: ExprLike, opts?: O): NamedPolyResult<O>;
export function chebyshevtPoly(n: number, x?: ExprLike, opts: NamedPolyOptions = {}): Expr | Poly {
  return namedPoly(n, chebyshevtCoeffs, 'Chebyshev polynomial of the first kind', x, opts, false);
}

/**
 * The Chebyshev polynomial of the second kind U_n(x).
 *
 * @param n - Nonnegative index of the polynomial family.
 * @param x - Variable or evaluation point of the polynomial.
 * @param opts - Set `polys` to return a polynomial object.
 * @returns The polynomial as an expression, or a `Poly` with `polys: true`.
 * @throws RangeError when the index is not a nonnegative integer.
 * @see SymPy `sympy.polys.orthopolys.chebyshevu_poly`
 */
export function chebyshevuPoly<O extends NamedPolyOptions = Record<never, never>>(n: number, x?: ExprLike, opts?: O): NamedPolyResult<O>;
export function chebyshevuPoly(n: number, x?: ExprLike, opts: NamedPolyOptions = {}): Expr | Poly {
  return namedPoly(n, chebyshevuCoeffs, 'Chebyshev polynomial of the second kind', x, opts, false);
}

/**
 * The physicist's Hermite polynomial H_n(x).
 *
 * @param n - Nonnegative index of the polynomial family.
 * @param x - Variable or evaluation point of the polynomial.
 * @param opts - Set `polys` to return a polynomial object.
 * @returns The polynomial as an expression, or a `Poly` with `polys: true`.
 * @throws RangeError when the index is not a nonnegative integer.
 * @see SymPy `sympy.polys.orthopolys.hermite_poly`
 */
export function hermitePoly<O extends NamedPolyOptions = Record<never, never>>(n: number, x?: ExprLike, opts?: O): NamedPolyResult<O>;
export function hermitePoly(n: number, x?: ExprLike, opts: NamedPolyOptions = {}): Expr | Poly {
  return namedPoly(n, hermiteCoeffs, 'Hermite polynomial', x, opts, false);
}

/**
 * The probabilist's Hermite polynomial He_n(x).
 *
 * @param n - Nonnegative index of the polynomial family.
 * @param x - Variable or evaluation point of the polynomial.
 * @param opts - Set `polys` to return a polynomial object.
 * @returns The polynomial as an expression, or a `Poly` with `polys: true`.
 * @throws RangeError when the index is not a nonnegative integer.
 * @see SymPy `sympy.polys.orthopolys.hermite_prob_poly`
 */
export function hermiteProbPoly<O extends NamedPolyOptions = Record<never, never>>(n: number, x?: ExprLike, opts?: O): NamedPolyResult<O>;
export function hermiteProbPoly(n: number, x?: ExprLike, opts: NamedPolyOptions = {}): Expr | Poly {
  return namedPoly(n, hermiteProbCoeffs, "probabilist's Hermite polynomial", x, opts, false);
}

/**
 * The Legendre polynomial P_n(x).
 *
 * @param n - Nonnegative index of the polynomial family.
 * @param x - Variable or evaluation point of the polynomial.
 * @param opts - Set `polys` to return a polynomial object.
 * @returns The polynomial as an expression, or a `Poly` with `polys: true`.
 * @throws RangeError when the index is not a nonnegative integer.
 * @see SymPy `sympy.polys.orthopolys.legendre_poly`
 */
export function legendrePoly<O extends NamedPolyOptions = Record<never, never>>(n: number, x?: ExprLike, opts?: O): NamedPolyResult<O>;
export function legendrePoly(n: number, x?: ExprLike, opts: NamedPolyOptions = {}): Expr | Poly {
  return namedPoly(n, legendreCoeffs, 'Legendre polynomial', x, opts);
}

/**
 * The generalized Laguerre polynomial L_n^(alpha)(x).
 *
 * @param n - Nonnegative index of the polynomial family.
 * @param x - Variable or evaluation point of the polynomial.
 * @param alpha - Laguerre parameter.
 * @param opts - Set `polys` to return a polynomial object.
 * @returns The polynomial as an expression, or a `Poly` with `polys: true`.
 * @throws RangeError when the index is not a nonnegative integer.
 * @see SymPy `sympy.polys.orthopolys.laguerre_poly`
 */
export function laguerrePoly<O extends NamedPolyOptions = Record<never, never>>(n: number, x?: ExprLike, alpha?: ExprLike, opts?: O): NamedPolyResult<O>;
export function laguerrePoly(n: number, x?: ExprLike, alpha: ExprLike = 0, opts: NamedPolyOptions = {}): Expr | Poly {
  return namedPoly(n, (k) => laguerreCoeffs(k, sympify(alpha)), 'Laguerre polynomial', x, opts, true, [alpha]);
}

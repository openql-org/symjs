// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import type { Sym } from '../core/nodes';
import type { Poly } from '../polys/sympoly';
import { KPoly } from './rischpoly';
import { orderAt as polynomialOrder, orderAtOo as infinityOrder } from './rde';

/**
 * Computes the multiplicity of an irreducible polynomial factor.
 *
 * @param a - The polynomial whose multiplicity is measured.
 * @param p - The irreducible factor.
 * @param t - The polynomial generator.
 * @returns The multiplicity of the factor, or infinity for zero.
 * @throws RangeError when the proposed factor is constant.
 * @see SymPy `sympy.integrals.rde.order_at`
 */
export function orderAt(a: Poly, p: Poly, t: Sym): number {
  const factor = KPoly.of(p.asExpr(), t);
  if (factor.degree < 1) throw new RangeError('orderAt: a nonconstant polynomial factor is required');
  return polynomialOrder(KPoly.of(a.asExpr(), t), factor, t);
}

/**
 * Computes the order of vanishing of a rational function at infinity.
 *
 * @param a - The numerator polynomial.
 * @param d - The denominator polynomial.
 * @param t - The polynomial generator.
 * @returns The denominator degree minus the numerator degree.
 * @throws RangeError when the denominator is zero.
 * @see SymPy `sympy.integrals.rde.order_at_oo`
 */
export function orderAtOo(a: Poly, d: Poly, t: Sym): number {
  const denominator = KPoly.of(d.asExpr(), t);
  if (denominator.isZero) throw new RangeError('orderAtOo: denominator must be nonzero');
  return infinityOrder(KPoly.of(a.asExpr(), t), denominator);
}

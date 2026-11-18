// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import type { Sym } from '../core/nodes';
import type { Poly } from '../polys/sympoly';
import { KPoly } from './rischpoly';
import { orderAt as polynomialOrder, orderAtOo as infinityOrder } from './rde';

/** The multiplicity of an irreducible polynomial p in a; Infinity for zero. */
export function orderAt(a: Poly, p: Poly, t: Sym): number {
  const factor = KPoly.of(p.asExpr(), t);
  if (factor.degree < 1) throw new RangeError('orderAt: a nonconstant polynomial factor is required');
  return polynomialOrder(KPoly.of(a.asExpr(), t), factor, t);
}

/** Order of vanishing at infinity of the rational function a/d. */
export function orderAtOo(a: Poly, d: Poly, t: Sym): number {
  const denominator = KPoly.of(d.asExpr(), t);
  if (denominator.isZero) throw new RangeError('orderAtOo: denominator must be nonzero');
  return infinityOrder(KPoly.of(a.asExpr(), t), denominator);
}

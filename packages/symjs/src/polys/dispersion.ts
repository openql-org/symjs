// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0, polys/dispersion.py, Copyright (c) 2006-2023
// SymPy Development Team, BSD 3-Clause License (see LICENSE).

import type { Expr, ExprLike } from '../core/nodes';
import { Rational, S } from '../core/nodes';
import { add, mul, pow } from '../core/ops';
import { cancel } from '../simplify/rational';
import { Poly } from './sympoly';

/**
 * Finds nonnegative shifts for which the two polynomials share a nonconstant factor.
 *
 * @param p - Polynomial to operate on.
 * @param q - Polynomial to shift. Defaults to the first polynomial.
 * @param x - Polynomial generator.
 * @returns The dispersion set.
 * @throws RangeError when the polynomial is not univariate or the generators differ.
 * @see SymPy `sympy.polys.dispersion.dispersionset`
 * @example
 * ```ts
 * import { dispersionset, ex } from '@symjs/symjs';
 *
 * dispersionset(ex`x**2 - 9`); // => {0, 6}
 * dispersionset(ex`x**4 - 3*x**2 + 1`, ex`x**4 - 12*x**3 + 51*x**2 - 90*x + 55`); // => {2, 3, 4}
 * ```
 */
export function dispersionset(p: Poly | ExprLike, q: Poly | ExprLike = p, x?: Expr): Set<bigint> {
  const f = p instanceof Poly ? p : Poly.from(p, x === undefined ? undefined : [x]);
  const g = q instanceof Poly ? q : Poly.from(q, x === undefined ? undefined : [x]);
  if (f.gens.length !== 1 || g.gens.length !== 1) throw new RangeError('Polynomials need to be univariate');
  if (f.gens[0]?.key !== g.gens[0]?.key) throw new RangeError('Polynomials must have the same generator');
  if (f.degree() < 1 || g.degree() < 1) return new Set([0n]);
  const fs = f.factorList()[1], gs = q === p ? fs : g.factorList()[1];
  const shifts = new Set<bigint>();
  for (const [s] of fs) for (const [t] of gs) {
    const n = s.degree();
    if (n !== t.degree() || s.LC().key !== t.LC().key) continue;
    const alpha = cancel(mul(add(s.coeffMonomial([n-1]), mul(-1,t.coeffMonomial([n-1]))), pow(mul(n,t.LC()),-1)));
    if (!(alpha instanceof Rational) || !alpha.isInteger || alpha.isNegative || shifts.has(alpha.p)) continue;
    if (n > 1 && !s.sub(t.shift(alpha)).isZero) continue;
    shifts.add(alpha.p);
  }
  return shifts;
}

/**
 * Finds the largest dispersion shift or negative infinity when there is none.
 *
 * @param p - Polynomial to operate on.
 * @param q - Polynomial to shift. Defaults to the first polynomial.
 * @param x - Polynomial generator.
 * @returns The greatest shift in the dispersion set, or negative infinity for an empty set.
 * @see SymPy `sympy.polys.dispersion.dispersion`
 * @example
 * ```ts
 * import { dispersion, ex } from '@symjs/symjs';
 *
 * dispersion(ex`x**2 - 9`); // => 6
 * dispersion(ex`x**4 - 3*x**2 + 1`, ex`x**4 - 12*x**3 + 51*x**2 - 90*x + 55`); // => 4
 * ```
 */
export function dispersion(p: Poly | ExprLike, q: Poly | ExprLike = p, x?: Expr): Expr {
  const shifts = dispersionset(p,q,x);
  let largest = -1n;
  for (const shift of shifts) if (shift > largest) largest = shift;
  return largest < 0n ? S.NegativeInfinity : Rational.of(largest);
}

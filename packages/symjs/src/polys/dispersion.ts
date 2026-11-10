// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0, polys/dispersion.py, Copyright (c) 2006-2023
// SymPy Development Team, BSD 3-Clause License (see LICENSE).

import type { Expr, ExprLike } from '../core/nodes';
import { Rational, S } from '../core/nodes';
import { add, mul, pow } from '../core/ops';
import { cancel } from '../simplify/rational';
import { Poly } from './sympoly';

/** Nonnegative integer shifts a for which gcd(p(x),q(x+a)) has positive degree. */
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

/** Largest dispersion shift; negative infinity when the dispersion set is empty. */
export function dispersion(p: Poly | ExprLike, q: Poly | ExprLike = p, x?: Expr): Expr {
  const shifts = dispersionset(p,q,x);
  let largest = -1n;
  for (const shift of shifts) if (shift > largest) largest = shift;
  return largest < 0n ? S.NegativeInfinity : Rational.of(largest);
}

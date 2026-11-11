// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
/** Factors obtained from the explicit roots of a univariate polynomial. */
import type { Expr, ExprLike } from '../core/nodes';
import { Sym } from '../core/nodes';
import { add, mul } from '../core/ops';
import { cast } from '../core/guard';
import { ordered } from '../core/match';
import { roots } from './poly';
import { Poly } from './sympoly';

/** Linear root factors, with a residual factor when explicit roots are incomplete. */
export function rootFactors(f: Poly, x?: Sym): Poly[];
export function rootFactors(f: ExprLike, x?: Sym): Expr[];
export function rootFactors(f: Poly | ExprLike, x?: Sym): Poly[] | Expr[] {
  const p = f instanceof Poly ? f : Poly.from(f, x === undefined ? undefined : [x]);
  if (p.gens.length !== 1) throw new RangeError('root_factors requires a univariate polynomial');
  const gen = cast(p.gen, Sym);
  const zeros = ordered(roots(p.asExpr(), gen, { skipQuintic: true }));
  const factors = zeros.map((r) => Poly.from(add(gen, mul(-1, r)), [gen]));
  if (factors.length === 0) factors.push(p);
  else if (factors.length < p.degree()) factors.push(p.quo(factors.reduce((a,b) => a.mul(b))));
  return f instanceof Poly ? factors : factors.map((factor) => factor.asExpr());
}

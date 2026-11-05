// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 solvers/bivariate.py, BSD-3-Clause; see LICENSE.

/**
 * @file SymPy `bivariate_type`: recognize a polynomial in x and y as a
 * polynomial P(u) of one composite u(x, y) (x*y, a*x + b*y, a*x*y + b*y).
 * The other functions of `sympy/solvers/bivariate.py` (the Lambert-W
 * solver `_solve_lambert`, `_filtered_gens`, ...) are private helpers of
 * `solve` in `solvers/solve.ts`.
 */

import type { Expr, ExprLike, Sym } from '../core/nodes';
import { Add, Dummy } from '../core/nodes';
import { add, mul, pow, root } from '../core/ops';
import { subs, xreplace } from '../core/traverse';
import { NoMatch, type NoMatchResult } from '../core/truth';
import { isZero } from '../core/assumptions';
import { Poly } from '../polys/sympoly';
import { mexpand } from '../simplify/fu';

const freeOf = (e: Expr, x: Sym, y: Sym): boolean => !e.has(x) && !e.has(y);

/** The composite of bivariate_type for a Poly in the dummies x and y (SymPy's call with first=False). */
function bivariateCore(p: Poly, x0: Sym, y0: Sym): [Expr, Expr, Dummy] | undefined {
  let [x, y] = [x0, y0];
  const u = new Dummy('u', { positive: true });
  const f = p.asExpr();

  // f(x*y)
  const terms = f instanceof Add ? f.args : [f];
  const parts = terms.map((a) => mexpand(subs(a, [[x, mul(u, pow(y, -1))]])));
  if (parts.every((a) => freeOf(a, x, y))) return [mul(x, y), add(...parts), u];

  const ok = (v: Sym, c: Expr): Expr | undefined => {
    const e = mexpand(subs(f, [[v, c]]));
    return freeOf(e, x, y) ? e : undefined;
  };
  const d = p.degree(x);
  if (p.degree(y) !== d) return undefined;

  // f(a*x + b*y)
  const a1 = root(p.coeffMonomial([d, 0]), d);
  const b1 = root(p.coeffMonomial([0, d]), d);
  const lin = ok(x, mul(add(u, mul(-1, b1, y)), pow(a1, -1)));
  if (lin !== undefined) return [add(mul(a1, x), mul(b1, y)), lin, u];

  // f(a*x*y + b*y), then f(a*x*y + b*x)
  const swapped = (m: readonly number[]): number[] => (x === x0 ? [...m] : [...m].reverse());
  for (let itry = 0; itry < 2; itry++) {
    const a = root(p.coeffMonomial(swapped([d, d])), d);
    const b = root(p.coeffMonomial(swapped([0, d])), d);
    // (SymPy divides by a zero coefficient and then finds no match)
    if (isZero(a) !== true) {
      const e = ok(x, mul(add(u, mul(-1, b, y)), pow(a, -1), pow(y, -1)));
      if (e !== undefined) return [add(mul(a, x, y), mul(b, y)), e, u];
    }
    [x, y] = [y, x];
  }
  return undefined;
}

/**
 * SymPy bivariate_type: if the polynomial f in x and y is P(u(x, y)) for
 * u = x*y, a*x + b*y, a*x*y + b*y or a*x*y + b*x, returns u(x, y), P(u) and
 * the positive dummy u; otherwise NoMatch.
 */
export function bivariateType(f: ExprLike, x: Sym, y: Sym): [Expr, Expr, Dummy] | NoMatchResult {
  const e = Poly.from(f, [x, y]).asExpr();
  const _x = new Dummy();
  const _y = new Dummy();
  const rv = bivariateCore(Poly.from(xreplace(e, [[x, _x], [y, _y]]), [_x, _y]), _x, _y);
  if (rv === undefined) return NoMatch;
  const reps = [[_x, x], [_y, y]] as const;
  return [xreplace(rv[0], reps), xreplace(rv[1], reps), rv[2]];
}

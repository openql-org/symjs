// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file powsimp(): combine powers with a common base (x**a*x**b -> x**(a + b)).
 */

import { Expr, ExprLike, Mul } from '../core/nodes';
import { add, asBaseExp, mul, pow, sympify } from '../core/ops';
import { mapBottomUp } from '../core/traverse';

/** Combine factors with equal bases by adding their exponents. */
export function powsimp(ex: ExprLike): Expr {
  return mapBottomUp(sympify(ex), (e) => {
    if (!(e instanceof Mul)) return e;
    const groups = new Map<string, { base: Expr; exps: Expr[] }>();
    const order: string[] = [];
    for (const f of e.args) {
      if (f.isNumber) {
        groups.set(`#${order.length}`, { base: f, exps: [] });
        order.push(`#${order.length}`);
        continue;
      }
      const [b, x] = asBaseExp(f);
      const g = groups.get(b.key);
      if (g) g.exps.push(x);
      else {
        groups.set(b.key, { base: b, exps: [x] });
        order.push(b.key);
      }
    }
    if (groups.size === e.args.length) return e;
    return mul(
      ...order.map((k) => {
        const g = groups.get(k)!;
        return g.exps.length === 0 ? g.base : pow(g.base, add(...g.exps));
      }),
    );
  });
}

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file series(): power series expansion with an Order term, SymPy style.
 */

import { Expr, ExprLike, Order, Rational, Special, Sym, impl } from '../core/nodes';
import { add, mul, pow, sympify } from '../core/ops';
import { subs } from '../core/traverse';
import { log } from '../functions/elementary';
import { Expander } from './puiseux';

/**
 * O(expr) for x -> x0. Like SymPy, the argument is reduced to its leading
 * power: O(x + x**2) = O(x), O(cos(x)) = O(1), O(cos(x), x, pi/2) = O(x - pi/2).
 */
export function O(ex: ExprLike, x?: Sym, x0: ExprLike = 0): Expr {
  const e = sympify(ex);
  const p = sympify(x0);
  const syms = [...e.freeSymbols()];
  const v = x ?? (syms.length === 1 ? syms[0] : undefined);
  const atZero = p instanceof Rational && p.isZero;
  if (v === undefined || p instanceof Special) {
    return new Order(x === undefined || atZero ? [e] : [e, x, p]);
  }
  let reduced: Expr = e;
  try {
    const t = new Sym('_o');
    const lead = new Expander(t).leading(subs(e, [[v, add(p, t)]]));
    if (!lead.c.has(t)) {
      const base = atZero ? v : add(v, mul(-1, p));
      reduced = pow(base, lead.e);
    }
  } catch {
    // keep the expression as given
  }
  return atZero ? new Order([reduced]) : new Order([reduced, v, p]);
}

/**
 * Series expansion of e about x = x0 up to O((x - x0)**n). Like SymPy, an
 * exact (finite) expansion is returned without an Order term.
 */
export function series(ex: ExprLike, x: Sym, x0x: ExprLike = 0, n = 6): Expr {
  const e = sympify(ex);
  const x0 = sympify(x0x);
  if (x0 instanceof Special) throw new Error('series: expansion at infinity is not supported yet');
  if (!e.has(x)) return e;
  const t = new Sym('_s');
  const ex0 = new Expander(t);
  const shifted = subs(e, [[x, add(x0, t)]]);
  const ps = ex0.ser(shifted, Rational.of(n));
  const base = x0 instanceof Rational && x0.isZero ? x : add(x, mul(-1, x0));
  const back = (c: Expr) => subs(c, [[ex0.L, log(base)]]);
  const terms = ps.terms.map((term) => mul(back(term.c), pow(base, term.e)));
  const body = add(...terms);
  if (ps.order.value >= 1e5) return body;
  const ord = x0 instanceof Rational && x0.isZero ? new Order([pow(x, ps.order)]) : new Order([pow(base, ps.order), x, x0]);
  return add(body, ord);
}

impl.series = series;


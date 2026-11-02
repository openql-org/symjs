// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file series(): power series expansion with an Order term, SymPy style.
 */

import { Add, Expr, ExprLike, Fn, Order, Pow, Rational, S, Special, Sym, impl } from '../core/nodes';
import { add, mul, neg, pow, sympify } from '../core/ops';
import { mapBottomUp, xreplace as subs } from '../core/traverse';
import { log, sin } from '../functions/elementary';
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
  if (v !== undefined && p instanceof Special && p.name === 'oo' && syms.length === 1) {
    // leading behaviour at infinity: substitute x = 1/t, t -> 0+
    try {
      const t = new Sym('_o', { positive: true });
      const lead = new Expander(t).leading(subs(e, [[v, pow(t, -1)]]));
      if (!lead.c.has(t)) return new Order([pow(v, neg(lead.e)), v, p]);
    } catch {
      // keep the expression as given
    }
  }
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
export function series(ex: ExprLike, x: Sym, x0x: ExprLike = 0, n = 6, dir: '+' | '-' = '+'): Expr {
  // sinc(u) = sin(u)/u has a removable singularity at u = 0
  const e = mapBottomUp(sympify(ex), (t) => (t instanceof Fn && t.name === 'sinc' ? mul(sin(t.args[0]!), pow(t.args[0]!, -1)) : t));
  const x0 = sympify(x0x);
  if (x0 instanceof Special) throw new Error('series: expansion at infinity is not supported yet');
  if (!e.has(x)) return e;
  const t = new Sym('_s');
  const ex0 = new Expander(t);
  // from the left: x = x0 - t with t -> 0+, written in powers of (x0 - x)
  const shifted = subs(e, [[x, dir === '-' ? add(x0, mul(-1, t)) : add(x0, t)]]);
  const ps = ex0.ser(shifted, Rational.of(n));
  const base = dir === '-' ? add(x0, mul(-1, x)) : x0 instanceof Rational && x0.isZero ? x : add(x, mul(-1, x0));
  const back = (c: Expr) => subs(c, [[ex0.L, log(base)]]);
  const terms = ps.terms.map((term) => mul(back(term.c), pow(base, term.e)));
  const body = add(...terms);
  if (ps.order.value >= 1e5) return body;
  const lin = x0 instanceof Rational && x0.isZero ? x : add(x, mul(-1, x0));
  const ord = x0 instanceof Rational && x0.isZero ? new Order([pow(x, ps.order)]) : new Order([pow(lin, ps.order), x, x0]);
  return add(body, ord);
}

impl.series = series;
impl.leadterm = (e, x) => leadterm(e, x);

/** Leading term c*x**e of e as x -> 0 (SymPy leadterm): [c, e]. */
export function leadterm(ex: ExprLike, x: Sym): [Expr, Expr] {
  const e = sympify(ex);
  if (!e.has(x)) return [e, S.Zero];
  const t = new Sym('_s');
  const exp0 = new Expander(t);
  const l = exp0.leading(subs(e, [[x, t]]));
  const c = subs(l.c, [[exp0.L, log(x)]]);
  return [c, l.e];
}

/** SymPy as_leading_term(x). */
export function asLeadingTerm(ex: ExprLike, x: Sym): Expr {
  const [c, e] = leadterm(ex, x);
  return mul(c, pow(x, e));
}

/** Order of the O term in a sum, or undefined (SymPy getn). */
export function getn(ex: ExprLike): Expr | undefined {
  const e = sympify(ex);
  const o = (e instanceof Add ? e.args : [e]).find((a) => a instanceof Order) as Order | undefined;
  if (!o) return undefined;
  const b = o.args[0]!;
  if (b instanceof Pow) return b.exp;
  if (b instanceof Sym) return S.One;
  return undefined;
}


/** Leading terms of a sum as x -> 0 with their order terms (SymPy extract_leading_order). */
export function extractLeadingOrder(ex: ExprLike, x: Sym): [Expr, Expr][] {
  const e = sympify(ex);
  const terms = e instanceof Add ? e.args : [e];
  const orders = terms.map((t) => leadterm(t, x)[1]);
  const minO = orders.reduce((m, o) => ((o as Rational).value < (m as Rational).value ? o : m));
  return terms.filter((_, i) => orders[i]!.key === minO.key).map((t) => [t, new Order([t.has(x) ? t : S.One])]);
}

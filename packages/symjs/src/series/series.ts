// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file series(): power series expansion with an Order term, SymPy style.
 */

import { NotImplementedError } from '../core/errors';
import type { Expr, ExprLike } from '../core/nodes';
import { Add, Fn, Order, Pow, Rational, S, Special, Sym, impl } from '../core/nodes';
import { add, exp, mul, neg, pow, sympify } from '../core/ops';
import { Mul } from '../core/nodes';
import { expandMul } from '../simplify/expand';
import { mapBottomUp, xreplace as subs } from '../core/traverse';
import { log, sin } from '../functions/elementary';
import { Expander } from './puiseux';

/**
 * O(expr) for x -> x0. Like SymPy, the argument is reduced to its leading
 * power: O(x + x**2) = O(x), O(cos(x)) = O(1), O(cos(x), x, pi/2) = O(x - pi/2).
 */
export function O(ex: ExprLike, xIn?: Sym | readonly Sym[], x0: ExprLike = 0): Expr {
  const e = sympify(ex);
  const p = sympify(x0);
  const syms = [...e.freeSymbols()];
  const vars = Array.isArray(xIn) ? (xIn as readonly Sym[]) : xIn === undefined && syms.length > 1 ? (sortSyms(syms)) : undefined;
  if (vars && vars.length > 1) return orderMulti(e, vars, p);
  const x: Sym | undefined = Array.isArray(xIn) ? (xIn as readonly Sym[])[0] : (xIn as Sym | undefined);
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

function sortSyms(xs: Sym[]): Sym[] {
  return [...xs].sort((a, b) => (a.name < b.name ? -1 : a.name > b.name ? 1 : 0));
}

/**
 * Order term in several variables at 0 or oo: the terms of lowest (at 0) or
 * highest (at oo) total degree, without their coefficients (SymPy Order).
 */
function orderMulti(e: Expr, vars: readonly Sym[], p: Expr): Expr {
  const atZero = p instanceof Rational && p.isZero;
  const atOo = p instanceof Special && p.name === 'oo';
  let reduced = e;
  if (atZero || atOo) {
    const terms = expandMul(e) instanceof Add ? expandMul(e).args : [expandMul(e)];
    const deg = (t: Expr): number | undefined => {
      let d = 0;
      for (const f of t instanceof Mul ? t.args : [t]) {
        if (vars.some((v) => v.key === f.key)) d += 1;
        else if (f instanceof Pow && vars.some((v) => v.key === f.base.key) && f.exp instanceof Rational) d += f.exp.value;
        else if (f.freeSymbols().size && [...f.freeSymbols()].some((s) => vars.some((v) => v.key === s.key))) return undefined;
      }
      return d;
    };
    const ds = terms.map(deg);
    if (ds.every((d) => d !== undefined)) {
      const target = atZero ? Math.min(...(ds)) : Math.max(...(ds));
      const strip = (t: Expr) => mul(...(t instanceof Mul ? t.args : [t]).filter((f) => !(f instanceof Rational || f.freeSymbols().size === 0)));
      reduced = add(...terms.filter((_, i) => ds[i] === target).map(strip));
    }
  }
  return new Order([reduced, ...vars, p]);
}

/**
 * Series expansion of e about x = x0 up to O((x - x0)**n). Like SymPy, an
 * exact (finite) expansion is returned without an Order term.
 */
/**
 * Series at +oo or -oo (SymPy series(f, x, oo, n)): x = sign/t with t -> 0+,
 * the expansion in t written back in x, with O(x**(-n), (x, oo)).
 */
function seriesAtInfinity(e: Expr, x: Sym, sign: 1 | -1, n: number): Expr {
  const t = new Sym('_t_inf', { positive: true });
  const st = series(subs(e, [[x, mul(sign, pow(t, -1))]]), t, 0, n);
  const back = (u: Expr) => subs(u, [[t, mul(sign, pow(x, -1))]]);
  const terms = st instanceof Add ? st.args : [st];
  const out: Expr[] = [];
  let order: Expr | undefined;
  for (const u of terms) {
    if (u instanceof Order) {
      const lead = u.args[0]!;
      const k = lead instanceof Pow && lead.base.key === t.key ? lead.exp : lead.key === t.key ? S.One : undefined;
      order = k === undefined ? undefined : new Order([pow(x, neg(k)), x, sign === 1 ? S.Infinity : S.NegativeInfinity]);
    } else out.push(back(u));
  }
  if (!order) return add(...out);
  // the Order at infinity must not absorb the terms (they are larger there): smallest terms first, like SymPy
  const body = add(...out);
  const parts = (body instanceof Add ? body.args : [body]).filter((u) => !(u instanceof Rational && u.isZero));
  const deg = (u: Expr): number => {
    let d = 0;
    for (const f of u instanceof Mul ? u.args : [u]) {
      if (f.key === x.key) d += 1;
      else if (f instanceof Pow && f.base.key === x.key && f.exp instanceof Rational) d += f.exp.toNumber();
    }
    return d;
  };
  parts.sort((a, b) => deg(a) - deg(b));
  return new Add([...parts, order]);
}

export function series(ex: ExprLike, x: Sym, x0x: ExprLike = 0, n = 6, dir: '+' | '-' = '+', opts: { logx?: Expr } = {}): Expr {
  // sinc(u) = sin(u)/u has a removable singularity at u = 0
  let e = mapBottomUp(sympify(ex), (t) => (t instanceof Fn && t.name === 'sinc' ? mul(sin(t.args[0]!), pow(t.args[0]!, -1)) : t));
  const x00 = sympify(x0x);
  const atZero = x00 instanceof Rational && x00.isZero;
  if (opts.logx && atZero) {
    // SymPy logx: log(x) stands for the given symbol; x**c = exp(c*log(x)) for symbolic c
    e = mapBottomUp(e, (t) => (t instanceof Pow && t.base.key === x.key && !(t.exp instanceof Rational) && !t.exp.has(x) ? exp(mul(t.exp, log(x))) : t));
    e = subs(e, [[log(x), opts.logx]]);
    if (!e.has(x)) return e;
  }
  // x**c with symbolic c is its own expansion at 0
  if (atZero && e instanceof Pow && e.base.key === x.key && !(e.exp instanceof Rational) && !e.exp.has(x)) return e;
  const x0 = sympify(x0x);
  if (x0 instanceof Special && (x0.name === 'oo' || x0.name === '-oo')) return seriesAtInfinity(e, x, x0.name === 'oo' ? 1 : -1, n);
  if (x0 instanceof Special) throw new NotImplementedError('series: expansion at this point is not supported');
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
  const o = (e instanceof Add ? e.args : [e]).find((a) => a instanceof Order);
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

/** SymPy Expr.taylor_term(n, x): the n-th term of the Maclaurin series, f^(n)(0)*x**n/n!. */
export function taylorTerm(eIn: ExprLike, n: number, x: Sym): Expr {
  const e = sympify(eIn);
  let fact = 1n;
  for (let i = 2n; i <= BigInt(n); i++) fact *= i;
  return mul(subs(impl.diff(e, x, n), [[x, S.Zero]]), pow(x, n), Rational.of(1n, fact));
}

/**
 * SymPy Expr.aseries(x, n, hir): asymptotic expansion at x -> oo in the most
 * rapidly varying decaying exponential w = exp(-b*x). Without hir only the
 * leading term in w is kept and its coefficient is expanded in 1/x; with hir
 * the terms up to w**n. Expressions without exponentials give their series
 * at infinity; growing exponentials are returned unchanged.
 */
export function aseries(ex: ExprLike, x: Sym, n = 6, hir = false): Expr {
  const e = sympify(ex);
  const rates: Rational[] = [];
  let growing = false as boolean; // set inside a callback
  let other = false as boolean;
  const walk = (u: Expr) => {
    if (u instanceof Pow && u.base === S.E && u.exp.has(x)) {
      const c = expandMul(mul(u.exp, pow(x, -1)));
      if (c instanceof Rational) {
        if (c.isPositive) growing = true;
        else rates.push(c);
      } else other = true;
    }
    u.args.forEach(walk);
  };
  walk(e);
  if (growing || other) return e;
  if (!rates.length) return series(e, x, S.Infinity, n);
  const b = rates.reduce((m, r) => (Math.abs(r.toNumber()) < Math.abs(m.toNumber()) ? r : m));
  const w = new Sym('_w_as', { positive: true });
  // exp(c*x) = w**(c/b)
  const replaced = mapBottomUp(e, (u) => (u instanceof Pow && u.base === S.E && u.exp.has(x) ? pow(w, mul(expandMul(mul(u.exp, pow(x, -1))), pow(b, -1))) : u));
  const sw = series(replaced, w, 0, hir ? n : 3);
  const terms = sw instanceof Add ? sw.args : [sw];
  const byPower = new Map<number, Expr[]>();
  for (const t of terms) {
    if (t instanceof Order) continue;
    let k = 0;
    const cs: Expr[] = [];
    for (const f of t instanceof Mul ? t.args : [t]) {
      if (f.key === w.key) k += 1;
      else if (f instanceof Pow && f.base.key === w.key && f.exp instanceof Rational) k += f.exp.toNumber();
      else cs.push(f);
    }
    byPower.set(k, [...(byPower.get(k) ?? []), mul(...cs)]);
  }
  const ks = [...byPower.keys()].sort((a, c) => a - c);
  if (!ks.length) return e;
  const wx = (k: number) => exp(mul(k, b, x));
  if (!hir) {
    const k = ks[0]!;
    const coeff = series(add(...byPower.get(k)!), x, S.Infinity, n);
    return mul(coeff, wx(k));
  }
  const parts = ks.filter((k) => k < n).sort((a, c) => c - a).map((k) => mul(add(...byPower.get(k)!), wx(k)));
  return new Add([...parts, new Order([wx(n), x, S.Infinity])]);
}

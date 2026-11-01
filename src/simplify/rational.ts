// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Rational-function manipulation: fraction, together, cancel.
 */

import { Add, Constant, Expr, Fn, impl, ExprLike, Mul, Pow, Rational, Sym, isNum } from '../core/nodes';
import { add, mul, pow, splitCoeff, sympify } from '../core/ops';
import { freeSymbols, rebuild } from '../core/traverse';
import { divExact, mgcd } from '../polys/mpoly';
import { UPoly } from '../polys/poly';
import { expandMul as expand } from './expand';
import { isNegative, isPositive } from '../core/assumptions';

const negExponent = (x: Expr): boolean => {
  // SymPy fraction: exponents known to be negative go to the denominator
  if (isNegative(x) === true) return true;
  if (isPositive(x) === true) return false;
  const [c] = splitCoeff(x);
  return c.isNegative;
};

/** Split e into [numerator, denominator]. */
export function fraction(ex: ExprLike): [Expr, Expr] {
  const e = sympify(ex);
  const factors = e instanceof Mul ? e.args : [e];
  const num: Expr[] = [];
  const den: Expr[] = [];
  for (const f of factors) {
    if (f instanceof Rational) {
      num.push(Rational.of(f.p));
      den.push(Rational.of(f.q));
    } else if (f instanceof Pow && negExponent(f.exp)) {
      den.push(pow(f.base, mul(-1, f.exp)));
    } else {
      num.push(f);
    }
  }
  return [mul(...num), mul(...den)];
}

/** Combine a sum of fractions over a common denominator (recursively). */
export function together(ex: ExprLike, opts: { deep?: boolean } = {}): Expr {
  const deep = opts.deep ?? false;
  // SymPy _together: gcd_terms over the recursively combined terms of every sum
  const go = (e: Expr): Expr => {
    if (e.args.length === 0) return e;
    const isExp = e instanceof Pow && e.base instanceof Constant && e.base.name === 'E';
    if ((e instanceof Fn || isExp) && !deep) return e;
    if (e instanceof Add) return impl.gcdTermsOf!(e.args.map(go));
    if (e instanceof Pow) return pow(go(e.base), deep ? go(e.exp) : e.exp);
    const args = e.args.map(go);
    return args.every((a, i) => a === e.args[i]) ? e : rebuild(e, args);
  };
  return go(sympify(ex));
}

/**
 * Put e into the form p/q with expanded p, q and cancel common factors.
 * Polynomial GCD cancellation is performed for univariate rational functions.
 */
export function cancel(ex: ExprLike): Expr {
  const e = together(sympify(ex));
  let [n, d] = fraction(e);
  n = expand(n);
  d = expand(d);
  if (d instanceof Rational && d.isOne) return n;
  const syms = new Map<string, Sym>();
  for (const s of [...freeSymbols(n), ...freeSymbols(d)]) syms.set(s.key, s);
  if (syms.size === 1) {
    const x = [...syms.values()][0]!;
    const pn = UPoly.fromExpr(n, x);
    const pd = UPoly.fromExpr(d, x);
    if (pn && pd) {
      const g = pn.gcd(pd);
      let qn = g.degree > 0 ? pn.divmod(g)[0] : pn;
      let qd = g.degree > 0 ? pd.divmod(g)[0] : pd;
      // normalize: monic denominator
      const lc = qd.lc;
      qn = qn.scale(Rational.of(lc.q, lc.p));
      qd = qd.scale(Rational.of(lc.q, lc.p));
      if (qd.degree === 0) return qn.toExpr(x);
      return mul(qn.toExpr(x), pow(qd.toExpr(x), -1));
    }
  }
  if (isNum(d)) return expand(mul(n, pow(d, -1)));
  if (syms.size > 1) {
    const vars = [...syms.values()].sort((a, b) => (a.name < b.name ? -1 : a.name > b.name ? 1 : 0));
    try {
      const g = mgcd(n, d, vars);
      if (!(g instanceof Rational)) {
        const nn = divExact(n, g, vars);
        const dd = divExact(d, g, vars);
        if (nn !== undefined && dd !== undefined) {
          n = nn;
          d = dd;
        }
      }
    } catch {
      // not polynomial: keep as is
    }
    if (d instanceof Rational) return expand(mul(n, pow(d, -1)));
  }
  return mul(n, pow(d, -1));
}

impl.fraction = (e) => fraction(e);

/** SymPy ratsimp: polynomial part plus a cancelled remainder over a single denominator. */
export function ratsimp(ex: ExprLike): Expr {
  const c = cancel(sympify(ex));
  const [f, g] = fraction(c);
  if (!g.freeSymbols().size) return c;
  const gens = [...new Map([...f.freeSymbols(), ...g.freeSymbols()].map((s) => [s.key, s])).values()];
  const pf = polyDivide(f, g, gens);
  if (!pf) return c;
  const [q, r] = pf;
  return add(q, cancel(mul(r, pow(g, -1))));
}

/** Multivariate division of f by g in lex order: [quotient, remainder]. */
function polyDivide(f: Expr, g: Expr, gens: readonly Expr[]): [Expr, Expr] | undefined {
  return impl.polyReduce ? impl.polyReduce(f, g, gens) : undefined;
}

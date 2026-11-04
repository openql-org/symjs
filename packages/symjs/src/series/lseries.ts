// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Lazy series (SymPy Expr.lseries) and Expr.dir (the direction of
 * approach). SymPy has them as Expr methods (sympy/core/expr.py); they are
 * here because they build on series and limits.
 */

import type { Expr, ExprLike, Sym } from '../core/nodes';
import { Add, Dummy, Mul, Order, Pow, Rational, S, Special } from '../core/nodes';
import { add, mul, neg, pow, sub, sympify } from '../core/ops';
import { subs } from '../core/traverse';
import { diff } from '../calculus/diff';
import { log } from '../functions/elementary/elementary';
import { leadterm, series } from './series';
import { limit } from './limits';

const isZeroExpr = (e: Expr): boolean => e instanceof Rational && e.isZero;
const isOrder = (e: Expr): boolean => e instanceof Order;

/**
 * The terms of the series of e about x0 up to order n, lowest order first:
 * computed in t = x - x0 and written back in x - x0.
 */
export function seriesTerms(e: Expr, x: Sym, x0: Expr, n: number, dir: '+' | '-'): { terms: Expr[]; exact: boolean } {
  const t = new Dummy('t');
  const atZero = isZeroExpr(x0);
  const et = atZero ? subs(e, [[x, t]]) : subs(e, [[x, add(x0, t)]]);
  const s = series(et, t, 0, n, dir);
  const parts = s instanceof Add ? s.args : [s];
  const terms = parts.filter((p) => !isOrder(p));
  // each term is c*t**e or c*(-t)**e (from the left) with c free of t but for log(t) or log(-t)
  // (leadterm would search the leading term of t**2000/2 to too small an order)
  const deg = (p: Expr): number => {
    for (const f of p instanceof Mul ? p.args : [p]) {
      if (f.key === t.key) return 1;
      if (f instanceof Pow && f.exp instanceof Rational && (f.base.key === t.key || f.base.key === neg(t).key)) return f.exp.value;
    }
    return 0;
  };
  const back = (p: Expr): Expr => subs(p, [[t, atZero ? x : sub(x, x0)]]);
  return { terms: [...terms].sort((a, b) => deg(a) - deg(b)).map(back), exact: !parts.some(isOrder) };
}

/**
 * SymPy Expr.lseries: the terms of the series of e about x0, lazily (an
 * iterator that computes more terms as they are requested).
 */
export function* lseries(ex: ExprLike, x: Sym, x0: ExprLike = 0, dir: '+' | '-' = '+'): Generator<Expr, void, undefined> {
  const e = sympify(ex);
  const p = sympify(x0);
  let n = 6;
  let done = 0;
  for (;;) {
    const { terms, exact } = seriesTerms(e, x, p, n, dir);
    for (const t of terms.slice(done)) yield t;
    done = Math.max(done, terms.length);
    if (exact || n > 4096) return;
    n *= 2;
  }
}

/**
 * SymPy Expr.dir(x, cdir): the direction in which e approaches its value at
 * x = 0 when x approaches 0 from the direction cdir.
 */
export function dir(ex: ExprLike, x: Sym, cdir: ExprLike): Expr {
  let arg = sympify(ex);
  if (isZeroExpr(arg)) return S.Zero;
  let minexp = 0;
  let coeff: Expr = S.Zero;
  while (!isZeroExpr(arg)) {
    minexp++;
    arg = diff(arg, x);
    coeff = subs(arg, [[x, 0]]);
    if (coeff instanceof Special && coeff.name === 'nan') coeff = limit(arg, x, 0);
    if (coeff instanceof Special && coeff.name === 'zoo') {
      try {
        coeff = leadterm(arg, x)[0];
        // a leading coefficient with log(x) is not a direction (SymPy raises and takes the limit)
        if (coeff.has(log(x))) coeff = limit(arg, x, 0);
      } catch {
        coeff = limit(arg, x, 0);
      }
    }
    if (!isZeroExpr(coeff)) break;
  }
  return mul(coeff, pow(sympify(cdir), minexp));
}

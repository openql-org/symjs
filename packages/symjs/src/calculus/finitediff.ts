// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Finite difference approximations (SymPy finite_diff_weights and
 * Derivative.as_finite_difference).
 */

import type { Derivative, Expr, ExprLike } from '../core/nodes';
import { Rational, S, Sym } from '../core/nodes';
import { at, cast, defined } from '../core/guard';
import { add, mul, pow, sympify } from '../core/ops';
import { xreplace } from '../core/traverse';
import { derivative as impl_derivative } from '../core/undef';

/** Fornberg weights: delta[m][n][nu] for derivative order m using the first n+1 points. */
export function finiteDiffWeights(order: number, xs: readonly Expr[], x0: ExprLike = 1): Expr[][][] {
  const X0 = sympify(x0);
  const M = order;
  const N = xs.length - 1;
  const delta: Expr[][][] = Array.from({ length: M + 1 }, () => Array.from({ length: N + 1 }, () => Array.from({ length: N + 1 }, () => S.Zero as Expr)));
  // delta[m][n] as a checked row
  const row = (m: number, n: number): Expr[] => at(at(delta, m), n);
  row(0, 0)[0] = S.One;
  let c1: Expr = S.One;
  for (let n = 1; n <= N; n++) {
    let c2: Expr = S.One;
    const xn = at(xs, n);
    for (let nu = 0; nu < n; nu++) {
      const c3 = add(xn, mul(-1, at(xs, nu)));
      c2 = mul(c2, c3);
      if (n <= M) row(n, n - 1)[nu] = S.Zero;
      for (let m = 0; m <= Math.min(n, M); m++) {
        const prev = m > 0 ? at(row(m - 1, n - 1), nu) : S.Zero;
        row(m, n)[nu] = mul(add(mul(add(xn, mul(-1, X0)), at(row(m, n - 1), nu)), mul(-m, prev)), pow(c3, -1));
      }
    }
    for (let m = 0; m <= Math.min(n, M); m++) {
      const prev = m > 0 ? at(row(m - 1, n - 1), n - 1) : S.Zero;
      row(m, n)[n] = mul(c1, pow(c2, -1), add(mul(m, prev), mul(-1, add(at(xs, n - 1), mul(-1, X0)), at(row(m, n - 1), n - 1))));
    }
    c1 = c2;
  }
  return delta;
}

const isPointList = (p: ExprLike | readonly ExprLike[]): p is readonly ExprLike[] => Array.isArray(p);

/**
 * Approximate a derivative of an undefined function by finite differences
 * (SymPy Derivative.as_finite_difference). `points` is a step size or the
 * list of sample points.
 */
export function asFiniteDifference(d: Derivative, points: ExprLike | readonly ExprLike[] = 1, x0?: ExprLike, wrt?: Sym): Expr {
  const vc = d.variableCount;
  const [v, order] = defined(wrt ? vc.find(([w]) => w.key === wrt.key) : vc[0], 'differentiation variable');
  const x = cast(v, Sym, 'differentiation variable');
  const X0 = x0 === undefined ? x : sympify(x0);
  let pts: Expr[];
  if (isPointList(points)) pts = points.map(sympify);
  else {
    // a step depending on x (e.g. dx(x)) is taken at x0 (SymPy)
    const h = xreplace(sympify(points), [[x, X0]]);
    pts = [];
    if (order % 2 === 0) for (let i = -order / 2; i <= order / 2; i++) pts.push(add(X0, mul(h, i)));
    else for (let i = -order; i <= order; i += 2) pts.push(add(X0, mul(h, Rational.of(i, 2))));
  }
  const w = at(at(finiteDiffWeights(order, pts, X0), order), pts.length - 1);
  // remaining derivatives (other variables) stay on the function
  const rest = vc.filter(([u]) => u.key !== x.key);
  const base = rest.length ? impl_derivative(d.expr, rest) : d.expr;
  return add(...pts.map((p, i) => mul(at(w, i), xreplace(base, [[x, p]]))));
}


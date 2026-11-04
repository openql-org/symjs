// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Finite difference approximations (SymPy finite_diff_weights and
 * Derivative.as_finite_difference, apply_finite_diff and differentiate_finite).
 */

import type { Expr, ExprLike, Sym } from '../core/nodes';
import { Derivative, Rational, S, UndefFn } from '../core/nodes';
import { at } from '../core/guard';
import { SubsNode } from '../core/subsnode';
import { add, mul, pow, sympify } from '../core/ops';
import { freeSymbols, rebuild, subs } from '../core/traverse';
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
 * SymPy apply_finite_diff(order, x_list, y_list, x0): the finite difference
 * approximation at x0 of the derivative of the given order of the function
 * with the values y_list at the points x_list.
 */
export function applyFiniteDiff(order: number, xList: readonly ExprLike[], yList: readonly ExprLike[], x0: ExprLike = 0): Expr {
  if (xList.length !== yList.length) throw new RangeError('x_list and y_list not equal in length.');
  const N = xList.length - 1;
  const w = at(at(finiteDiffWeights(order, xList.map(sympify), x0), order), N);
  return add(...yList.map((y, nu) => mul(at(w, nu), y)));
}

/** The variables of a derivative with their multiplicity, in the order of first appearance. */
const variableList = (d: Derivative): Expr[] => d.variableCount.flatMap(([v, n]) => Array.from({ length: n }, () => v));

/** Derivative(expr, (v, n), ...) without the zero counts (Derivative(expr) is expr). */
function derivativeOf(expr: Expr, vc: readonly [Expr, number][]): Expr {
  const nz = vc.filter(([, n]) => n > 0);
  return nz.length ? impl_derivative(expr, nz) : expr;
}

/** SymPy _as_finite_diff: every Derivative in e replaced by its finite difference. */
function asFiniteDiff(e: Expr, points: ExprLike | readonly ExprLike[], x0: ExprLike | undefined, wrt: Expr | undefined): Expr {
  if (!(e instanceof Derivative)) {
    if (e.args.length === 0) return e;
    return rebuild(e, e.args.map((a) => asFiniteDiff(a, points, x0, wrt)));
  }
  if (wrt === undefined) {
    let d: Expr = e;
    let old: Expr | undefined;
    for (const v of variableList(e)) {
      if (old?.key === v.key) continue;
      d = asFiniteDiff(d, points, x0, v);
      old = v;
    }
    return d;
  }
  const vars = variableList(e);
  const order = vars.filter((v) => v.key === wrt.key).length;
  const X0 = x0 === undefined ? wrt : sympify(x0);
  let pts: Expr[];
  if (isPointList(points)) pts = points.map(sympify);
  else {
    // a step depending on wrt (e.g. dx(x)) is taken at x0
    const p0 = sympify(points);
    const h = p0 instanceof UndefFn && p0.args.some((a) => a.key === wrt.key) ? subs(p0, [[wrt, X0]]) : p0;
    pts = [];
    if (order % 2 === 0) for (let i = -order / 2; i <= order / 2; i++) pts.push(add(X0, mul(h, i)));
    else for (let i = -order; i <= order; i += 2) pts.push(add(X0, mul(h, Rational.of(i, 2))));
  }
  if (pts.length < order + 1) throw new RangeError(`Too few points for order ${order}`);
  const others: [Expr, number][] = [[wrt, 0]];
  const seen = new Set<string>([wrt.key]);
  for (const v of vars) {
    if (seen.has(v.key)) continue;
    seen.add(v.key);
    others.push([v, vars.filter((u) => u.key === v.key).length]);
  }
  return applyFiniteDiff(order, pts, pts.map((p) => derivativeOf(subs(e.expr, [[wrt, p]]), others)), X0);
}

/**
 * Approximate a derivative by finite differences (SymPy
 * Derivative.as_finite_difference). `points` is a step size or the list of
 * sample points; without `wrt`, every variable of the derivative in turn.
 */
export function asFiniteDifference(d: Derivative, points: ExprLike | readonly ExprLike[] = 1, x0?: ExprLike, wrt?: Sym): Expr {
  return asFiniteDiff(d, points, x0, wrt);
}

/** The Subs nodes of e replaced by finite differences at their points. */
function replaceSubs(e: Expr, points: ExprLike | readonly ExprLike[], wrt: Sym | undefined): Expr {
  const args = e.args.map((a) => replaceSubs(a, points, wrt));
  const r = args.length ? rebuild(e, args) : e;
  if (r instanceof SubsNode) return asFiniteDiff(r.expr, points, at(r.point, 0), at(r.variables, 0));
  return r;
}

/**
 * SymPy differentiate_finite(expr, *symbols, points, x0, wrt): the
 * derivative of expr with respect to the symbols (a symbol and a count, or
 * several symbols), with every derivative replaced by a finite difference.
 */
export function differentiateFinite(ex: ExprLike, symbols: readonly (Sym | number)[] = [], opts: { points?: ExprLike | readonly ExprLike[]; x0?: ExprLike; wrt?: Sym } = {}): Expr {
  const e = sympify(ex);
  const points = opts.points ?? 1;
  const vc: [Expr, number][] = [];
  for (const s of symbols) {
    if (typeof s === 'number') {
      const lastVc = vc[vc.length - 1];
      if (lastVc === undefined) throw new RangeError('differentiate_finite: a count must follow a symbol');
      lastVc[1] += s - 1;
    } else vc.push([s, 1]);
  }
  // no symbols: the derivative with respect to the only free symbol
  if (vc.length === 0) {
    const free = [...freeSymbols(e)];
    if (free.length === 0) return S.Zero;
    if (free.length > 1) throw new RangeError(`Since there is more than one variable in the expression, the variable(s) of differentiation must be supplied to differentiate ${e.toString()}`);
    vc.push([at(free, 0), 1]);
  }
  const D = derivativeOf(e, vc);
  return replaceSubs(asFiniteDiff(D, points, opts.x0, opts.wrt), points, opts.wrt);
}

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Symbolic differentiation.
 */

import { isReal } from '../core/assumptions';
import { piecewise } from '../core/logic';
import { Add, Constant, Derivative, Dummy, Expr, ExprLike, Fn, Integral, Mul, Piecewise, Pow, S, Sym, UndefFn, impl, isNum } from '../core/nodes';
import { derivative } from '../core/undef';
import { add, mul, pow, sympify } from '../core/ops';
import { xreplace } from '../core/traverse';
import { abs, conjugate, cos, cosh, im as fnIm, log, re as fnRe, sin, sinh, tan, tanh } from '../functions/elementary';

/**
 * Partial derivatives of multi-argument functions: fnPartials[name](args, i)
 * is d f(args) / d args[i]. special.ts registers entries.
 */
export const fnPartials: Partial<Record<Fn['name'], (args: readonly Expr[], i: number) => Expr>> = {};

/** Derivative of f(u) with respect to u, for each known function. */
const fnDerivative: Partial<Record<Fn['name'], (u: Expr) => Expr>> = {
  sin: (u) => cos(u),
  cos: (u) => mul(-1, sin(u)),
  tan: (u) => add(1, pow(tan(u), 2)),
  asin: (u) => pow(add(1, mul(-1, pow(u, 2))), S.NegHalf),
  acos: (u) => mul(-1, pow(add(1, mul(-1, pow(u, 2))), S.NegHalf)),
  atan: (u) => pow(add(1, pow(u, 2)), -1),
  sinh: (u) => cosh(u),
  cosh: (u) => sinh(u),
  tanh: (u) => add(1, mul(-1, pow(tanh(u), 2))),
  log: (u) => pow(u, -1),
};

function d(e: Expr, x: Expr): Expr {
  if (e.key === x.key) return S.One;
  if (isNum(e) || e instanceof Constant || e instanceof Sym) return S.Zero;
  if (!e.has(x)) return S.Zero;

  if (e instanceof Add) return add(...e.args.map((a) => d(a, x)));

  if (e instanceof Mul) {
    const terms: Expr[] = [];
    for (let i = 0; i < e.args.length; i++) {
      const di = d(e.args[i]!, x);
      if (di.key === S.Zero.key) continue;
      terms.push(mul(...e.args.map((a, j) => (j === i ? di : a))));
    }
    return add(...terms);
  }

  if (e instanceof Pow) {
    const [b, n] = e.args;
    const db = d(b, x);
    const dn = d(n, x);
    // d(b^n) = b^n * (n' log b + n b'/b)
    if (dn.key === S.Zero.key) return mul(n, pow(b, add(n, -1)), db);
    if (b instanceof Constant && b.name === 'E') return mul(e, dn);
    return mul(e, add(mul(dn, log(b)), mul(n, db, pow(b, -1))));
  }

  if (e instanceof Fn && fnPartials[e.name]) {
    const partial = fnPartials[e.name]!;
    const terms: Expr[] = [];
    e.args.forEach((a, i) => {
      const da = d(a, x);
      if (!(da instanceof Expr && da.key === S.Zero.key)) terms.push(mul(partial(e.args, i), da));
    });
    return add(...terms);
  }
  if (e instanceof Fn) {
    const u = e.args[0]!;
    const du = d(u, x);
    if (e.name === 'conjugate') return conjugate(du);
    // re/im are linear; valid for differentiation w.r.t. a real variable
    if (e.name === 're') return fnRe(du);
    if (e.name === 'im') return fnIm(du);
    if (e.name === 'abs') {
      if (isReal(u)) return mul(u, pow(abs(u), -1), du);
      throw new Error('diff: derivative of abs() of a non-real argument is not supported');
    }
    const f = fnDerivative[e.name];
    if (!f) throw new Error(`diff: unknown derivative for ${e.name}`);
    return mul(f(u), du);
  }
  if (e instanceof UndefFn) {
    // chain rule over the arguments; only direct dependence is represented
    const terms: Expr[] = [];
    for (const a of e.args) {
      if (!a.has(x)) continue;
      if (a.key === x.key) terms.push(derivative(e, [[x, 1]]));
      else throw new Error('diff: derivative of an undefined function of a composite argument is not supported');
    }
    return add(...terms);
  }
  if (e instanceof Derivative) {
    if (e.expr instanceof UndefFn && e.expr.args.some((a) => a.key === x.key)) return derivative(e, [[x, 1]]);
    return S.Zero;
  }
  if (e instanceof Piecewise) return piecewise(...e.pairs.map(([v, c]) => [d(v, x), c] as const));
  if (e instanceof Integral && !e.limits && e.variable.key === x.key) return e.integrand;
  throw new Error(`diff: unsupported expression ${e.toString()}`);
}

/** n-th derivative of e with respect to x. */
export function diff(ex: ExprLike, x: Expr, n = 1): Expr {
  if (!Number.isInteger(n) || n < 0) throw new RangeError('diff: order must be a non-negative integer');
  let e = sympify(ex);
  if (!(x instanceof Sym)) {
    // differentiate with respect to an expression such as f(x): treat it as a symbol
    const t = new Dummy('xi');
    const r = diff(xreplace(e, [[x, t]]), t, n);
    return xreplace(r, [[t, x]]);
  }
  for (let i = 0; i < n; i++) e = d(e, x);
  return e;
}

impl.diff = diff;

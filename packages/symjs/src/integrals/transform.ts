// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Change of variables in integrals (SymPy Integral.transform).
 */

import { Dummy, Expr, ExprLike, Integral, Rational, S, Sym, impl } from '../core/nodes';
import { Sum, doitConcrete } from '../concrete/summations';
import { isNonNegative } from '../core/assumptions';
import { FiniteSet as FiniteSetClass } from '../sets/sets';
import { singularities } from '../solvers/inequalities';
import { limit } from '../series/limits';
import { integrate } from './integrate';
import { add, mul, pow, sympify } from '../core/ops';
import { some, subs } from '../core/traverse';
import { diff } from '../calculus/diff';
import { solve } from '../solvers/solve';

/**
 * Substitute x = g(u) in the integral (SymPy Integral.transform(x, (g, u))).
 * Passing only a symbol u performs the plain renaming x = u. Limits are
 * mapped by solving g(u) = limit, which must have a unique solution.
 */
export function transformIntegral(integral: Integral, x: Sym, gIn: ExprLike, uIn?: Sym): Integral {
  const g = sympify(gIn);
  const u = uIn ?? (g instanceof Sym ? g : undefined);
  if (!u) throw new Error('transform: the new variable must be given');
  if (integral.variable.key !== x.key) throw new Error('transform: x is not the integration variable');
  const f = mul(subs(integral.integrand, [[x, g]]), diff(g, u));
  const lim = integral.limits;
  if (!lim) return new Integral([f, u]);
  const mapLimit = (a: Expr): Expr => {
    const sols = solve(add(g, mul(-1, a)), u);
    if (sols.length !== 1) throw new Error('transform: the substitution is not invertible on the limits');
    return sols[0]!;
  };
  return new Integral([f, u, mapLimit(lim[0]), mapLimit(lim[1])]);
}

/** Cauchy principal value of a definite integral (SymPy Integral.principal_value). */
export function principalValue(integral: Integral): Expr {
  const lim = integral.limits;
  const x = integral.variable;
  if (!lim || !(x instanceof Sym)) throw new Error('principal_value: a definite integral is required');
  const [a, b] = lim;
  if (a.key === b.key) return S.Zero;
  const f = integral.integrand;
  const inRange = (s: Expr) => {
    const lo = add(s, mul(-1, a));
    const hi = add(b, mul(-1, s));
    return isNonNegative(lo) === true && isNonNegative(hi) === true;
  };
  const sing = singularities(f, x);
  const points = sing instanceof FiniteSetClass ? sing.args.filter(inRange) : [];
  for (const s of points) {
    if (s.key === a.key || s.key === b.key) throw new Error('principal_value: singularity at an end point');
  }
  const F = integrate(f, x);
  if (some(F, (e) => e instanceof Integral)) return integral;
  let I: Expr =
    a.key === S.NegativeInfinity.key && b.key === S.Infinity.key
      ? limit(add(F, mul(-1, subs(F, [[x, mul(-1, x)]]))), x, S.Infinity)
      : add(limit(F, x, b, '-'), mul(-1, limit(F, x, a, '+')));
  const r = new Dummy('r', { positive: true });
  for (const s of points) {
    I = add(I, limit(add(subs(F, [[x, add(s, mul(-1, r))]]), mul(-1, subs(F, [[x, add(s, r)]]))), r, 0, '+'));
  }
  return I;
}

/**
 * SymPy Integral.as_sum(n, method): the Riemann sum approximating a definite
 * integral with n intervals ('left', 'right', 'midpoint' or 'trapezoid').
 * With a symbolic n, or with `evaluate: false`, the result keeps a Sum.
 */
export function asSum(integral: Integral, n: ExprLike, method: 'left' | 'right' | 'midpoint' | 'trapezoid' = 'midpoint', opts: { evaluate?: boolean } = {}): Expr {
  const lim = integral.limits;
  if (!lim) throw new Error('as_sum: a definite integral is required');
  const N = sympify(n);
  const [a, b] = lim;
  const x = integral.variable;
  const f = integral.integrand;
  const dx = mul(add(b, mul(-1, a)), pow(N, -1));
  const k = new Dummy('k', { integer: true, positive: true });
  const at = (p: Expr) => subs(f, [[x, p]]);
  let body: Expr;
  let extra: Expr = S.Zero;
  let upper: Expr = N;
  // points written like SymPy: a + k*dx - dx/2 for the midpoint rule
  if (method === 'left') body = at(add(a, mul(k, dx), mul(-1, dx)));
  else if (method === 'right') body = at(add(a, mul(k, dx)));
  else if (method === 'midpoint') body = at(add(a, mul(k, dx), mul(S.NegHalf, dx)));
  else {
    // trapezoid: (f(a) + f(b))/2 + the inner points
    extra = mul(add(at(a), at(b)), S.Half);
    body = at(add(a, mul(k, dx)));
    upper = add(N, -1);
  }
  const evaluate = opts.evaluate !== false;
  if (evaluate && N instanceof Rational) {
    const M = Number(N.p) - (method === 'trapezoid' ? 1 : 0);
    const terms = Array.from({ length: M }, (_, j) => subs(body, [[k, Rational.of(j + 1)]]));
    return mul(dx, add(extra, ...terms));
  }
  const s = Sum(body, [k, 1, upper]);
  return mul(dx, add(extra, evaluate ? doitConcrete(s as never) : s));
}

/** SymPy Curve(functions, (t, a, b)): a parametric curve. */
export class Curve {
  readonly functions: Expr[];
  constructor(
    functions: readonly ExprLike[],
    readonly limits: readonly [Sym, Expr, Expr],
  ) {
    this.functions = functions.map(sympify);
  }
  toString(): string {
    return `Curve((${this.functions.map(String).join(', ')}), (${this.limits.map(String).join(', ')}))`;
  }
}

/** SymPy line_integrate(field, curve, vars): the integral of field along the curve with respect to arc length. */
export function lineIntegrate(field: ExprLike, curve: Curve, vars: readonly Sym[]): Expr {
  const [t0, a, b] = curve.limits;
  if (vars.length !== curve.functions.length) throw new Error('line_integrate: the curve and the variables differ in dimension');
  // the parameter is real
  const t = new Dummy(t0.name, { real: true });
  const fs = curve.functions.map((g) => subs(g, [[t0, t]]));
  const f = subs(sympify(field), vars.map((v, i) => [v, fs[i]!] as [Expr, Expr]));
  const speed = pow(add(...fs.map((g) => pow(diff(g, t), 2))), S.Half);
  return integrate(impl.simplify(mul(f, impl.simplify(speed))), t, [a, b]);
}

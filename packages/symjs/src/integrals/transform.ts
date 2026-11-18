// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Change of variables in integrals (SymPy Integral.transform).
 */

import type { Expr, ExprLike } from '../core/nodes';
import { Dummy, Integral, Rational, S, Sym, impl } from '../core/nodes';
import { Concrete, Sum, doitConcrete } from '../concrete/summations';
import { at, cast, first } from '../core/guard';
import { isNonNegative, isPositive } from '../core/assumptions';
import { fact } from '../core/exprfacts';
import { NotImplementedError } from '../core/errors';
import { FiniteSet as FiniteSetClass } from '../sets/sets';
import { singularities } from '../solvers/inequalities';
import { limit } from '../series/limits';
import { integrate } from './integrate';
import { add, mul, pow, sympify } from '../core/ops';
import { freeSymbols, some, subs } from '../core/traverse';
import { sign } from '../functions/special/special';
import { diff } from '../calculus/diff';
import { solve } from '../solvers/solve';
import { cancel } from '../simplify/rational';
import { simplify } from '../simplify/simplify';

/**
 * Substitute x = g(u) in the integral (SymPy Integral.transform(x, (g, u))).
 * Passing only a symbol u performs the plain renaming x = u; without u the
 * new variable is the only free symbol of g. Limits are mapped through the
 * inverse u = G(x), solved like SymPy with u and x taken positive (the root
 * of x = u**2 is sqrt(x)); a limit where G is infinite or undefined is
 * reached by a limit. Reversed limits are swapped and the integrand negated.
 */
export function transformIntegral(integral: Integral, x: Expr, gIn: ExprLike, uIn?: Sym): Integral {
  const g = sympify(gIn);
  if (!(x instanceof Sym)) {
    if (!(g instanceof Sym) || uIn !== undefined) throw new RangeError('transform: an expression for the old variable requires a new symbol');
    const variable = cast(integral.variable, Sym);
    const jacobian = diff(x, variable);
    if (jacobian.equals(S.Zero)) throw new RangeError('transform: substitution has zero Jacobian');
    const quotient = cancel(mul(integral.integrand, pow(jacobian, -1)));
    let transformed = subs(quotient, [[x, g]]);
    if (transformed.has(variable)) {
      const inverses = solve(add(x, mul(-1, g)), variable);
      const candidates = inverses.map((root) => simplify(subs(quotient, [[variable, root]])));
      transformed = first(candidates);
      if (candidates.some((f) => !simplify(add(f, mul(-1, transformed))).equals(S.Zero))) throw new RangeError('transform: inverse branches give different integrands');
    }
    const limits = integral.limits;
    return new Integral(limits === undefined ? [transformed, g] : [transformed, g, ...limits.map((p) => subs(x, [[variable, p]]))]);
  }
  const free = [...freeSymbols(g)].filter((s) => s instanceof Sym);
  if (!uIn && free.length !== 1) throw new RangeError('transform: the new variable must be given');
  const u = uIn ?? first(free);
  if (!free.some((s) => s.key === u.key)) throw new RangeError('transform: the new variable must occur in the mapping');
  if (integral.variable.key !== x.key) throw new TypeError('transform: x is not the integration variable');
  let f = mul(subs(integral.integrand, [[x, g]]), diff(g, u));
  const lim = integral.limits;
  if (!lim && integral.args.length !== 3) return new Integral([f, u]);
  // the inverse G(d) of x = g(u), solved for positive u and x first
  const d = new Dummy('d', { positive: true });
  const pu = isPositive(u) === undefined ? new Dummy(u.name, { positive: true }) : u;
  const inverse = solve(add(subs(g, [[u, pu]]), mul(-1, d)), pu);
  if (inverse.length === 0) throw new RangeError('transform: no solution of x = g(u) for u');
  const atLimit = (a: Expr, b: Expr): Expr => {
    const vals = new Map<string, Expr>();
    for (const G of inverse) {
      const v = subs(G, [[d, a]]);
      // G is undefined or infinite at a finite limit: approach it from the side of the other limit
      const w = v === S.NaN || (fact(v, 'finite') === false && fact(a, 'finite') === true) ? limit(mul(sign(b), G), d, a) : v;
      vals.set(w.key, w);
    }
    if (vals.size !== 1) throw new RangeError('transform: the substitution does not give a unique limit');
    return first([...vals.values()]);
  };
  if (!lim) return new Integral([f, u, atLimit(at(integral.args, 2), S.One)]);
  let a = atLimit(lim[0], lim[1]);
  let b = atLimit(lim[1], lim[0]);
  if (isPositive(add(a, mul(-1, b))) === true) {
    [a, b] = [b, a];
    f = mul(-1, f);
  }
  return new Integral([f, u, a, b]);
}

/** Cauchy principal value of a definite integral (SymPy Integral.principal_value). */
export function principalValue(integral: Integral): Expr {
  const lim = integral.limits;
  const x = integral.variable;
  if (!lim || !(x instanceof Sym)) throw new TypeError('principal_value: a definite integral is required');
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
    if (s.key === a.key || s.key === b.key) throw new RangeError('principal_value: singularity at an end point');
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
  if (integral.integrand instanceof Integral) throw new NotImplementedError('as_sum: multidimensional integrals are not supported');
  const lim = integral.limits;
  if (!lim) throw new TypeError('as_sum: a definite integral is required');
  const N = sympify(n);
  const [a, b] = lim;
  if (fact(a, 'finite') === false || fact(b, 'finite') === false) throw new RangeError('as_sum: a finite interval is required');
  if (fact(N, 'positive') === false || fact(N, 'integer') === false || fact(N, 'finite') === false) throw new RangeError('as_sum: n must be a positive integer');
  if (!['left', 'right', 'midpoint', 'trapezoid'].includes(method)) throw new RangeError('as_sum: unknown method');
  const x = integral.variable;
  const f = integral.integrand;
  const dx = mul(add(b, mul(-1, a)), pow(N, -1));
  const k = new Dummy('k', { integer: true, positive: true });
  const atPoint = (p: Expr) => subs(f, [[x, p]]);
  let body: Expr;
  let extra: Expr = S.Zero;
  let upper: Expr = N;
  // points written like SymPy: a + k*dx - dx/2 for the midpoint rule
  if (method === 'left') body = atPoint(add(a, mul(add(k, -1), dx)));
  else if (method === 'right') body = atPoint(add(a, mul(k, dx)));
  else if (method === 'midpoint') body = atPoint(add(a, mul(k, dx), mul(S.NegHalf, dx)));
  else {
    // trapezoid: (f(a) + f(b))/2 + the inner points
    extra = mul(add(atPoint(a), atPoint(b)), S.Half);
    body = atPoint(add(a, mul(k, dx)));
    upper = add(N, -1);
  }
  const evaluate = opts.evaluate !== false;
  if (evaluate && N instanceof Rational) {
    const M = Number(N.p) - (method === 'trapezoid' ? 1 : 0);
    const terms = Array.from({ length: M }, (_, j) => subs(body, [[k, Rational.of(j + 1)]]));
    return mul(dx, add(extra, ...terms));
  }
  const s = Sum(body, [k, 1, upper]);
  return mul(dx, add(extra, evaluate ? doitConcrete(cast(s, Concrete, 'Sum')) : s));
}

/**
 * A parametric curve as line_integrate takes it: the coordinate functions
 * and the limits (t, a, b) (SymPy Curve, see '@symjs/symjs/geometry').
 */
export interface ParametricCurve {
  readonly functions: Iterable<Expr>;
  readonly limits: Iterable<Expr>;
}

/** SymPy line_integrate(field, curve, vars): the integral of field along the curve with respect to arc length. */
export function lineIntegrate(field: ExprLike, curve: ParametricCurve, vars: readonly Sym[]): Expr {
  const limits = [...curve.limits];
  const functions = [...curve.functions];
  const t0 = cast(at(limits, 0), Sym, 'the curve parameter');
  const [a, b] = [at(limits, 1), at(limits, 2)];
  if (vars.length !== functions.length) throw new RangeError('line_integrate: the curve and the variables differ in dimension');
  // the parameter is real
  const t = new Dummy(t0.name, { real: true });
  const fs = functions.map((g) => subs(g, [[t0, t]]));
  const f = subs(
    sympify(field),
    vars.map((v, i): [Expr, Expr] => [v, at(fs, i)]),
  );
  const speed = pow(add(...fs.map((g) => pow(diff(g, t), 2))), S.Half);
  return integrate(impl.simplify(mul(f, impl.simplify(speed))), t, [a, b]);
}

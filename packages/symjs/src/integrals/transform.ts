// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Change of variables in integrals (SymPy Integral.transform).
 */

import { Dummy, Expr, ExprLike, Integral, S, Sym } from '../core/nodes';
import { isNonNegative } from '../core/assumptions';
import { FiniteSet as FiniteSetClass } from '../sets/sets';
import { singularities } from '../solvers/inequalities';
import { limit } from '../series/limits';
import { integrate } from './integrate';
import { add, mul, sympify } from '../core/ops';
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

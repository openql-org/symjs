// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy `gammasimp` and `combsimp` (the integer-shift part): factorials,
 * binomials and rising/falling factorials are written with Gamma, and in
 * each product Gamma factors whose arguments differ by integers are combined
 * into polynomial factors, e.g. gamma(x + 3)/gamma(x + 1) = (x + 1)*(x + 2).
 */

import { Expr, ExprLike, Fn, Mul, Pow, Rational, Sym } from '../core/nodes';
import { polyCoefficients } from '../polys/poly';
import { powsimp } from './powsimp';
import { cancel, fraction } from './rational';
import { add, mul, pow, sympify } from '../core/ops';
import { mapBottomUp } from '../core/traverse';
import { fn } from '../functions/elementary';
import { expand } from './expand';
import { factor } from '../polys/sympoly';

const MAX_SHIFT = 50;
const gamma = (x: Expr) => fn('gamma', [x]);
const hasGamma = (e: Expr): boolean => (e instanceof Fn && e.name === 'gamma') || e.args.some(hasGamma);

/** factorial, binomial, rf, ff written with gamma. */
function toGamma(e: Expr): Expr {
  return mapBottomUp(e, (x) => {
    if (!(x instanceof Fn)) return x;
    const [a, b] = x.args;
    switch (x.name) {
      case 'factorial':
        return gamma(add(a!, 1));
      case 'binomial':
        return mul(gamma(add(a!, 1)), pow(gamma(add(b!, 1)), -1), pow(gamma(add(a!, mul(-1, b!), 1)), -1));
      case 'rf':
        return mul(gamma(add(a!, b!)), pow(gamma(a!), -1));
      case 'ff':
        return mul(gamma(add(a!, 1)), pow(gamma(add(a!, mul(-1, b!), 1)), -1));
      default:
        return x;
    }
  });
}

/** Combine the Gamma factors of one product whose arguments differ by integers. */
function combineProduct(e: Expr): Expr {
  if (!(e instanceof Mul)) return e;
  const rest: Expr[] = [];
  const gs: [Expr, number][] = []; // gamma argument, integer exponent
  for (const f of e.args) {
    const [b, n] = f instanceof Pow && f.exp instanceof Rational && f.exp.isInteger ? [f.base, Number(f.exp.p)] : [f, 1];
    if (b instanceof Fn && b.name === 'gamma') gs.push([b.args[0]!, n]);
    else rest.push(f);
  }
  if (gs.length < 2) return e;
  // classes of arguments differing by integers, each with its smallest member
  const classes: { base: Expr; members: [number, number][] }[] = [];
  for (const [a, n] of gs) {
    let placed = false;
    for (const c of classes) {
      const d = expand(add(a, mul(-1, c.base)));
      if (d instanceof Rational && d.isInteger && Math.abs(Number(d.p)) <= MAX_SHIFT) {
        let k = Number(d.p);
        if (k < 0) {
          // new smallest member: shift the existing offsets
          c.members = c.members.map(([o, m]) => [o - k, m]);
          c.base = a;
          k = 0;
        }
        c.members.push([k, n]);
        placed = true;
        break;
      }
    }
    if (!placed) classes.push({ base: a, members: [[0, n]] });
  }
  if (classes.length === gs.length) return e;
  const out = [...rest];
  for (const { base, members } of classes) {
    // only ratios are combined (SymPy keeps factorial(n)*factorial(n + 1))
    if (!(members.some(([, n]) => n > 0) && members.some(([, n]) => n < 0))) {
      for (const [k, n] of members) out.push(pow(gamma(add(base, k)), n));
      continue;
    }
    let total = 0;
    for (const [k, n] of members) {
      total += n;
      // gamma(base + k) = gamma(base) * base*(base + 1)*...*(base + k - 1)
      for (let i = 0; i < k; i++) out.push(pow(add(base, i), n));
    }
    if (total) out.push(pow(gamma(base), total));
  }
  return mul(...out);
}

/** SymPy `gammasimp`: combine Gamma functions whose arguments differ by integers. */
export function gammasimp(exIn: ExprLike): Expr {
  const ex = sympify(exIn);
  const g = mapBottomUp(toGamma(ex), combineProduct);
  if (hasGamma(g)) return g;
  try {
    return factor(g);
  } catch {
    return g;
  }
}

/**
 * SymPy `combsimp`: simplify combinatorial expressions (factorials,
 * binomials, rising and falling factorials). The expression is returned
 * unchanged when Gamma factors remain and none could be combined.
 */
export function combsimp(exIn: ExprLike): Expr {
  const ex = sympify(exIn);
  const g = toGamma(ex);
  const c = mapBottomUp(g, combineProduct);
  if (hasGamma(c)) return c.key === g.key ? ex : c;
  try {
    return factor(c);
  } catch {
    return c;
  }
}

/**
 * SymPy hypersimp(f, k): the term ratio f(k + 1)/f(k) simplified, when it is
 * a rational function of k (f is hypergeometric); undefined otherwise.
 */
export function hypersimp(fIn: ExprLike, k: Expr): Expr | undefined {
  const f = sympify(fIn);
  const ratio = mul(f.subs(k, add(k, 1)), pow(f, -1));
  let r = combsimp(ratio);
  try {
    r = factor(cancel(powsimp(r)));
  } catch {
    // keep the combined ratio
  }
  const [n, d] = fraction(r);
  const isPoly = (e: Expr) => !e.has(k) || polyCoefficients(expand(e), k as Sym) !== undefined;
  return isPoly(n) && isPoly(d) ? r : undefined;
}

/** SymPy Expr.is_hypergeometric(k). */
export function isHypergeometric(f: ExprLike, k: Expr): boolean {
  return hypersimp(f, k) !== undefined;
}

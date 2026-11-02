// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy `gammasimp` and `combsimp` (the integer-shift part): factorials,
 * binomials and rising/falling factorials are written with Gamma, and in
 * each product Gamma factors whose arguments differ by integers are combined
 * into polynomial factors, e.g. gamma(x + 3)/gamma(x + 1) = (x + 1)*(x + 2).
 */

import type { Expr, ExprLike } from '../core/nodes';
import { Add, Dummy, Fn, Mul, Pow, Rational, S, Sym } from '../core/nodes';
import { polyCoefficients } from '../polys/poly';
import { powsimp } from './powsimp';
import { cancel, fraction } from './rational';
import { add, couldExtractMinusSign, mul, pow, sympify } from '../core/ops';
import { countOps, mapBottomUp, xreplace } from '../core/traverse';
import { at, first, pair } from '../core/guard';
import { isIntegerQ, isNegative as isNegativeQ, isZero as isZeroQ } from '../core/assumptions';
import { fn } from '../functions/elementary';
import { expand } from './expand';
import { factor } from '../polys/sympoly';

const MAX_SHIFT = 50;
const gamma = (x: Expr) => fn('gamma', [x]);
const hasGamma = (e: Expr): boolean => (e instanceof Fn && e.name === 'gamma') || e.args.some(hasGamma);

/** x <= 0 is known (SymPy (x <= 0) == True). */
const knownNonPositive = (x: Expr): boolean => (x instanceof Rational ? x.p <= 0n : isNegativeQ(x) === true || isZeroQ(x) === true);
/** x < 0 is known. */
const knownNegative = (x: Expr): boolean => (x instanceof Rational ? x.p < 0n : isNegativeQ(x) === true);

/**
 * factorial, binomial, rf and ff written with gamma (SymPy rewrite(gamma,
 * piecewise=False)): rf(x, k) for x <= 0 and ff(x, k) for x < 0 use the
 * reflected form, so that rf(0, k) does not become gamma(k)/gamma(0) = 0.
 */
export function toGamma(e: Expr): Expr {
  return mapBottomUp(e, (x) => {
    if (!(x instanceof Fn)) return x;
    switch (x.name) {
      case 'factorial':
        return gamma(add(first(x.args), 1));
      case 'binomial': {
        const [a, b] = pair(x.args);
        return mul(gamma(add(a, 1)), pow(gamma(add(b, 1)), -1), pow(gamma(add(a, mul(-1, b), 1)), -1));
      }
      case 'rf': {
        const [a, b] = pair(x.args);
        if (knownNonPositive(a)) return mul(pow(-1, b), gamma(add(1, mul(-1, a))), pow(gamma(add(1, mul(-1, a), mul(-1, b))), -1));
        return mul(gamma(add(a, b)), pow(gamma(a), -1));
      }
      case 'ff': {
        const [a, b] = pair(x.args);
        if (knownNegative(a)) return mul(pow(-1, b), gamma(add(b, mul(-1, a))), pow(gamma(mul(-1, a)), -1));
        return mul(gamma(add(a, 1)), pow(gamma(add(a, mul(-1, b), 1)), -1));
      }
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
    if (b instanceof Fn && b.name === 'gamma') gs.push([first(b.args), n]);
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
/**
 * The reflection formula in a product: gamma(a)**e*gamma(b)**e with a + b an
 * integer n becomes (pi/sin(pi*a) * gamma(b)/gamma(1 - a))**e, the last
 * ratio being a polynomial (gamma(1 - z)*gamma(1 + z) = pi*z/sin(pi*z)).
 */
function reflect(e: Expr): Expr {
  if (!(e instanceof Mul)) return e;
  const fs = [...e.args];
  const gam = (f: Expr): [Expr, Expr] | undefined => {
    const [b, k] = f instanceof Pow ? [f.base, f.exp] : [f, Rational.of(1n)];
    return b instanceof Fn && b.name === 'gamma' && k instanceof Rational && (k.p === 1n || k.p === -1n) && k.q === 1n ? [first(b.args), k] : undefined;
  };
  for (let i = 0; i < fs.length; i++) {
    const gi = gam(at(fs, i));
    if (!gi) continue;
    for (let j = i + 1; j < fs.length; j++) {
      const gj = gam(at(fs, j));
      if (!gj || gj[1].key !== gi[1].key) continue;
      const n = add(gi[0], gj[0]);
      if (!(n instanceof Rational && n.q === 1n) || isIntegerQ(gi[0]) === true) continue;
      // a: the argument that does not look negated, so that sin(pi*a) reads naturally
      const a = couldExtractMinusSign(gi[0]) ? gj[0] : gi[0];
      const k = Number(n.p) - 1;
      // gamma(b)/gamma(1 - a) with b = (1 - a) + k
      const w = add(1, mul(-1, a));
      let ratio: Expr = S.One;
      if (k > 0) for (let t = 0; t < k; t++) ratio = mul(ratio, add(w, t));
      else for (let t = 1; t <= -k; t++) ratio = mul(ratio, pow(add(w, -t), -1));
      // sin(pi*(a0 + m)) = (-1)**m*sin(pi*a0) for the integer part m of a
      const m = a instanceof Add && a.args[0] instanceof Rational && a.args[0].q === 1n ? a.args[0] : S.Zero;
      const a0 = add(a, mul(-1, m));
      const sgn = m instanceof Rational && m.p % 2n !== 0n ? -1 : 1;
      const pair = mul(sgn, S.Pi, pow(fn('sin', [mul(S.Pi, a0)]), -1), ratio);
      const rest = fs.filter((_, m) => m !== i && m !== j);
      return reflect(mul(...rest, pow(pair, gi[1])));
    }
  }
  return e;
}

export function gammasimp(exIn: ExprLike): Expr {
  const ex = sympify(exIn);
  const g = mapBottomUp(mapBottomUp(toGamma(ex), combineProduct), reflect);
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
  if (hasGamma(c)) {
    if (c.key === g.key && countOps(g) >= countOps(ex)) return ex;
    // as_comb: Gamma of an integer is written as a factorial again
    return mapBottomUp(c, (x) => (x instanceof Fn && x.name === 'gamma' && isIntegerQ(first(x.args)) === true ? fn('factorial', [add(first(x.args), -1)]) : x));
  }
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
  return isPolyIn(n, k) && isPolyIn(d, k) ? r : undefined;
}

/** Is e a polynomial in k (k need not be a symbol: it is replaced by a dummy first)? */
function isPolyIn(e: Expr, k: Expr): boolean {
  if (!e.has(k)) return true;
  if (k instanceof Sym) return polyCoefficients(expand(e), k) !== undefined;
  const d = new Dummy('k');
  return polyCoefficients(xreplace(expand(e), [[k, d]]), d) !== undefined;
}

/** SymPy Expr.is_hypergeometric(k). */
export function isHypergeometric(f: ExprLike, k: Expr): boolean {
  return hypersimp(f, k) !== undefined;
}

/** SymPy hypersimilar(f, g, k): is f/g a rational function of k (after combinatorial simplification)? */
export function hypersimilar(f: ExprLike, g: ExprLike, k: Expr): boolean {
  const r = combsimp(mul(sympify(f), pow(sympify(g), -1)));
  const [n, d] = fraction(cancel(r));
  return isPolyIn(n, k) && isPolyIn(d, k);
}

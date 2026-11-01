// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Rational-function manipulation: fraction, together, cancel.
 */

import { Add, Expr, ExprLike, Mul, Pow, Rational, S, Sym, isNum } from '../core/nodes';
import { numAdd, numCmp, numNeg } from '../core/num';
import { lcm } from '../core/numbers';
import { add, asBaseExp, mul, pow, splitCoeff, sympify } from '../core/ops';
import { freeSymbols, mapBottomUp } from '../core/traverse';
import { Poly } from '../polys/poly';
import { expand } from './expand';

const negExponent = (x: Expr): boolean => {
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
export function together(ex: ExprLike): Expr {
  return mapBottomUp(sympify(ex), (e) => {
    if (!(e instanceof Add)) return e;
    const parts = e.args.map(fraction);
    if (parts.every(([, d]) => d instanceof Rational && d.isOne)) return e;

    // common denominator: numeric lcm and the maximal power of each base
    let numericDen = 1n;
    const bases = new Map<string, { base: Expr; exp: Rational }>();
    const factorize = (d: Expr): { n: bigint; pows: Map<string, { base: Expr; exp: Expr }> } => {
      const pows = new Map<string, { base: Expr; exp: Expr }>();
      let n = 1n;
      for (const f of d instanceof Mul ? d.args : [d]) {
        if (f instanceof Rational) n *= f.p;
        else {
          const [b, x] = asBaseExp(f);
          // only rational exponents can be compared; otherwise treat the whole factor as a base
          if (x instanceof Rational) pows.set(b.key, { base: b, exp: x });
          else pows.set(f.key, { base: f, exp: S.One });
        }
      }
      return { n, pows };
    };
    const decomposed = parts.map(([, d]) => factorize(d));
    for (const { n, pows } of decomposed) {
      numericDen = lcm(numericDen, n);
      for (const [k, { base, exp }] of pows) {
        const r = exp instanceof Rational ? exp : S.One;
        const cur = bases.get(k);
        if (!cur || numCmp(r, cur.exp) > 0) bases.set(k, { base, exp: r });
      }
    }
    const numerators = parts.map(([n], i) => {
      const { n: dn, pows } = decomposed[i]!;
      const factors: Expr[] = [Rational.of(numericDen / dn)];
      for (const [k, { base, exp }] of bases) {
        const own = pows.get(k)?.exp;
        const ownR = own instanceof Rational ? own : own ? S.One : S.Zero;
        factors.push(pow(base, numAdd(exp, numNeg(ownR))));
      }
      return mul(n, ...factors);
    });
    const D = mul(Rational.of(numericDen), ...[...bases.values()].map(({ base, exp }) => pow(base, exp)));
    return mul(expand(add(...numerators)), pow(D, -1));
  });
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
    const pn = Poly.fromExpr(n, x);
    const pd = Poly.fromExpr(d, x);
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
  return mul(n, pow(d, -1));
}

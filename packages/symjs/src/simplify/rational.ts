// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Rational-function manipulation: fraction, together, cancel.
 */

import type { Expr, ExprLike, Sym } from '../core/nodes';
import { Add, Constant, Fn, impl, Mul, Pow, Rational, isNum } from '../core/nodes';
import { add, mul, pow, splitCoeff, sympify } from '../core/ops';
import { freeSymbols, rebuild } from '../core/traverse';
import { divExact, mgcd } from '../polys/mpoly';
import { UPoly, polyHooks } from '../polys/poly';
import { expandMul as expand } from './expand';
import { isNegative, isPositive } from '../core/assumptions';
import { InvariantError } from '../core/errors';
import { first } from '../core/guard';

const negExponent = (x: Expr): boolean => {
  // SymPy fraction: exponents known to be negative go to the denominator
  if (isNegative(x) === true) return true;
  if (isPositive(x) === true) return false;
  const [c] = splitCoeff(x);
  return c.isNegative;
};

/** Split e into [numerator, denominator]. */
export function fraction(ex: ExprLike, opts: { exact?: boolean } = {}): [Expr, Expr] {
  const e = sympify(ex);
  const factors = e instanceof Mul ? e.args : [e];
  const num: Expr[] = [];
  const den: Expr[] = [];
  for (const f of factors) {
    if (f instanceof Rational) {
      num.push(Rational.of(f.p));
      den.push(Rational.of(f.q));
    } else if (opts.exact && f instanceof Pow) {
      // SymPy exact=True: only exponents known to be negative, symbolic ones stay in the numerator
      const ex = f.exp;
      const negative = ex instanceof Rational ? ex.isNegative : isNegative(ex) === true;
      if (negative && ex instanceof Rational && ex.p === -1n && ex.q === 1n) den.push(f.base);
      else if (negative && ex.freeSymbols().size === 0) den.push(pow(f.base, mul(-1, ex)));
      else num.push(f);
    } else if (f instanceof Pow && negExponent(f.exp)) {
      den.push(pow(f.base, mul(-1, f.exp)));
    } else {
      num.push(f);
    }
  }
  if (opts.exact) {
    // SymPy Mul(*numer, evaluate=not exact): the factors as they are (2*(x + 1) stays)
    const raw = (xs: Expr[]): Expr => {
      const ys = xs.filter((y) => !(y instanceof Rational && y.p === 1n && y.q === 1n));
      return ys.length === 0 ? Rational.of(1n) : ys.length === 1 ? first(ys) : new Mul(ys);
    };
    return [raw(num), raw(den)];
  }
  return [mul(...num), mul(...den)];
}

/** Combine a sum of fractions over a common denominator (recursively). */
export function together(ex: ExprLike, opts: { deep?: boolean } = {}): Expr {
  const deep = opts.deep ?? false;
  // SymPy _together: gcd_terms over the recursively combined terms of every sum
  const go = (e: Expr): Expr => {
    if (e.args.length === 0) return e;
    const isExp = e instanceof Pow && e.base instanceof Constant && e.base.name === 'E';
    if ((e instanceof Fn || isExp) && !deep) return e;
    if (e instanceof Add) {
      if (impl.gcdTermsOf === undefined) throw new InvariantError('impl.gcdTermsOf is not registered');
      return impl.gcdTermsOf(e.args.map(go));
    }
    if (e instanceof Pow) return pow(go(e.base), deep ? go(e.exp) : e.exp);
    const args = e.args.map(go);
    return args.every((a, i) => a === e.args[i]) ? e : rebuild(e, args);
  };
  return go(sympify(ex));
}

/**
 * Put e into the form p/q with expanded p, q and cancel common factors.
 * Polynomial GCD cancellation is performed for univariate rational functions.
 */
/** sqrt(g) times a sum: the square root of the gcd of the integer radicands of every term. */
function radicalContent(e: Expr): [Expr, Expr] | undefined {
  if (!(e instanceof Add)) return undefined;
  let g = 0n;
  const gcd = (a: bigint, b: bigint): bigint => (b === 0n ? a : gcd(b, a % b));
  for (const t of e.args) {
    let radicand: bigint | undefined;
    for (const f of t instanceof Mul ? t.args : [t]) {
      if (f instanceof Pow && f.base instanceof Rational && f.base.q === 1n && f.exp instanceof Rational && f.exp.p === 1n && f.exp.q === 2n) {
        radicand = f.base.p;
        break;
      }
    }
    if (radicand === undefined) return undefined;
    g = gcd(g, radicand);
  }
  if (g <= 1n) return undefined;
  const sg = pow(Rational.of(g), Rational.of(1n, 2n));
  return [sg, expand(mul(e, pow(sg, -1)))];
}

function radicalContentRatio(n: Expr, d: Expr): Expr | undefined {
  const a = radicalContent(n);
  const b = radicalContent(d);
  if (!a || !b || a[1].key !== b[1].key) return undefined;
  return impl.radsimp ? impl.radsimp(mul(a[0], pow(b[0], -1))) : mul(a[0], pow(b[0], -1));
}

export function cancel(ex: ExprLike): Expr {
  const e = together(sympify(ex));
  let [n, d] = fraction(e);
  n = expand(n);
  d = expand(d);
  if (d instanceof Rational && d.isOne) return n;
  // a common square root content: (sqrt(3) + sqrt(15)*A)/(sqrt(2) + sqrt(10)*A) = sqrt(6)/2
  const rc = radicalContentRatio(n, d);
  if (rc) return rc;
  const syms = new Map<string, Sym>();
  for (const s of [...freeSymbols(n), ...freeSymbols(d)]) syms.set(s.key, s);
  if (syms.size === 1) {
    const x = first([...syms.values()]);
    const pn = UPoly.fromExpr(n, x);
    const pd = UPoly.fromExpr(d, x);
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
  if (syms.size > 1) {
    const vars = [...syms.values()].sort((a, b) => (a.name < b.name ? -1 : a.name > b.name ? 1 : 0));
    try {
      const g = mgcd(n, d, vars);
      if (!(g instanceof Rational)) {
        const nn = divExact(n, g, vars);
        const dd = divExact(d, g, vars);
        if (nn !== undefined && dd !== undefined) {
          n = nn;
          d = dd;
        }
      }
    } catch {
      // not polynomial: keep as is
    }
    if (d instanceof Rational) return expand(mul(n, pow(d, -1)));
  }
  return mul(n, pow(d, -1));
}

impl.fraction = (e) => fraction(e);

/** SymPy ratsimp: polynomial part plus a cancelled remainder over a single denominator. */
export function ratsimp(ex: ExprLike): Expr {
  const c = cancel(sympify(ex));
  const [f, g] = fraction(c);
  if (!g.freeSymbols().size) return c;
  const gens = [...new Map([...f.freeSymbols(), ...g.freeSymbols()].map((s) => [s.key, s])).values()];
  const pf = polyDivide(f, g, gens);
  if (!pf) return c;
  const [q, r] = pf;
  return add(q, cancel(mul(r, pow(g, -1))));
}

/** Multivariate division of f by g in lex order: [quotient, remainder]. */
function polyDivide(f: Expr, g: Expr, gens: readonly Expr[]): [Expr, Expr] | undefined {
  return impl.polyReduce ? impl.polyReduce(f, g, gens) : undefined;
}

polyHooks.cancel = (e) => cancel(e);

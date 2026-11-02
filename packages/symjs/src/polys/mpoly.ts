// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Multivariate polynomial arithmetic on expanded expressions:
 * exact division, pseudo-remainders, content and GCD (recursive primitive PRS),
 * and a heuristic multivariate factorization.
 */

import { InvariantError, PolynomialError } from '../core/errors';
import { at, defined } from '../core/guard';
import type { Expr, Sym } from '../core/nodes';
import { Add, Mul, Rational, S } from '../core/nodes';
import { numMul } from '../core/num';
import { gcd as igcd, lcm as ilcm } from '../core/numbers';
import { add, mul, pow } from '../core/ops';
import { freeSymbols } from '../core/traverse';
import { expandMul as expand } from '../simplify/expand';
import { polyCoefficients } from './poly';

const isZeroE = (e: Expr) => e instanceof Rational && e.isZero;

/** Degree of e in x (polynomial assumed), -1 for zero. */
export function degreeIn(e: Expr, x: Sym): number {
  if (isZeroE(e)) return -1;
  const pc = polyCoefficients(e, x);
  if (!pc) throw new PolynomialError('degreeIn: not a polynomial');
  return Math.max(...pc.keys());
}

function coeffsIn(e: Expr, x: Sym): Map<number, Expr> {
  const pc = polyCoefficients(e, x);
  if (!pc) throw new PolynomialError('not a polynomial');
  return pc;
}

/** Leading coefficient in x. */
export function lcIn(e: Expr, x: Sym): Expr {
  const pc = coeffsIn(e, x);
  return pc.get(Math.max(...pc.keys())) ?? S.Zero;
}

/** gcd of two rationals: gcd(numerators)/lcm(denominators). */
function rationalGcd(a: Rational, b: Rational): Rational {
  if (a.isZero) return Rational.of(b.p < 0n ? -b.p : b.p, b.q);
  if (b.isZero) return Rational.of(a.p < 0n ? -a.p : a.p, a.q);
  return Rational.of(igcd(a.p, b.p), ilcm(a.q, b.q));
}

/** Numeric content of an expanded polynomial (gcd of its rational coefficients). */
function numericContent(e: Expr): Rational {
  let g: Rational = S.Zero;
  for (const t of e instanceof Add ? e.args : [e]) {
    const c = t instanceof Mul && t.args[0] instanceof Rational ? t.args[0] : t instanceof Rational ? t : S.One;
    g = rationalGcd(g, c);
  }
  return g.isZero ? S.One : g;
}

/** b**k for a rational b and a nonnegative integer k (a Rational). */
function powRat(b: Rational, k: number): Rational {
  const r = pow(b, k);
  if (!(r instanceof Rational)) throw new InvariantError('power of a rational is not a Rational');
  return r;
}

/** Exact quotient f/g in Q[vars], or undefined when g does not divide f. */
export function divExact(f0: Expr, g0: Expr, vars: readonly Sym[]): Expr | undefined {
  const f = expand(f0);
  const g = expand(g0);
  if (isZeroE(g)) throw new RangeError('division by zero polynomial');
  if (isZeroE(f)) return S.Zero;
  const [x, ...rest] = vars;
  if (x === undefined) return expand(mul(f, pow(g, -1)));
  const dg = degreeIn(g, x);
  if (dg === 0) {
    // divide every coefficient
    const pc = coeffsIn(f, x);
    const out: Expr[] = [];
    for (const [k, c] of pc) {
      const q = divExact(c, g, rest);
      if (q === undefined) return undefined;
      out.push(mul(q, pow(x, k)));
    }
    return expand(add(...out));
  }
  let r = f;
  const q: Expr[] = [];
  const lg = lcIn(g, x);
  for (let guard = 0; guard < 1000 && !isZeroE(r); guard++) {
    const dr = degreeIn(r, x);
    if (dr < dg) return undefined;
    const c = divExact(lcIn(r, x), lg, rest);
    if (c === undefined) return undefined;
    const term = mul(c, pow(x, dr - dg));
    q.push(term);
    r = expand(add(r, mul(-1, term, g)));
  }
  return isZeroE(r) ? expand(add(...q)) : undefined;
}

/** Pseudo-remainder of a by b in x. */
export function prem(a0: Expr, b: Expr, x: Sym): Expr {
  let r = expand(a0);
  const db = degreeIn(b, x);
  const lb = lcIn(b, x);
  for (let guard = 0; guard < 1000 && !isZeroE(r); guard++) {
    const dr = degreeIn(r, x);
    if (dr < db) break;
    r = expand(add(mul(lb, r), mul(-1, lcIn(r, x), pow(x, dr - db), b)));
  }
  return r;
}

/** Content of f with respect to x: gcd of its coefficients (polynomials in the other variables). */
export function contentIn(f: Expr, x: Sym, rest: readonly Sym[]): Expr {
  let g: Expr = S.Zero;
  for (const c of coeffsIn(f, x).values()) g = mgcd(g, c, rest);
  return g;
}

/** Sign normalization: make the leading coefficient (lex order in vars) positive. */
function normalizeSign(e: Expr, vars: readonly Sym[]): Expr {
  let c = e;
  for (const v of vars) {
    if (!c.has(v)) continue;
    c = lcIn(c, v);
  }
  const lead = c instanceof Add ? at(c.args, -1) : c;
  const k = lead instanceof Mul && lead.args[0] instanceof Rational ? lead.args[0] : lead instanceof Rational ? lead : S.One;
  return k.isNegative ? expand(mul(-1, e)) : e;
}

/** GCD of two polynomials in Q[vars] (with integer content), normalized with a positive leading coefficient. */
export function mgcd(f0: Expr, g0: Expr, vars: readonly Sym[]): Expr {
  const f = expand(f0);
  const g = expand(g0);
  if (isZeroE(f)) return normalizeSign(g, vars);
  if (isZeroE(g)) return normalizeSign(f, vars);
  const live = vars.filter((v) => f.has(v) || g.has(v));
  const [x, ...rest] = live;
  if (x === undefined) {
    if (f instanceof Rational && g instanceof Rational) return rationalGcd(f, g);
    return rationalGcd(numericContent(f), numericContent(g));
  }
  if (!f.has(x)) return mgcd(f, contentIn(g, x, rest), rest);
  if (!g.has(x)) return mgcd(contentIn(f, x, rest), g, rest);
  const cf = contentIn(f, x, rest);
  const cg = contentIn(g, x, rest);
  const c = mgcd(cf, cg, rest);
  let a = defined(divExact(f, cf, live), 'f / content');
  let b = defined(divExact(g, cg, live), 'g / content');
  if (degreeIn(a, x) < degreeIn(b, x)) [a, b] = [b, a];
  for (let guard = 0; guard < 200 && !isZeroE(b) && degreeIn(b, x) > 0; guard++) {
    const r = prem(a, b, x);
    a = b;
    if (isZeroE(r)) {
      b = S.Zero;
      break;
    }
    b = divExact(r, contentIn(r, x, rest), live) ?? r;
  }
  const g1 = isZeroE(b) ? defined(divExact(a, contentIn(a, x, rest), live), 'primitive part') : S.One;
  return normalizeSign(expand(mul(c, g1)), live);
}

/** lcm of two polynomials. */
export function mlcm(f: Expr, g: Expr, vars: readonly Sym[]): Expr {
  const d = mgcd(f, g, vars);
  return normalizeSign(expand(mul(defined(divExact(f, d, vars), 'f / gcd'), g)), vars);
}

/** Sorted generator list for a set of expressions (alphabetical by name). */
export function varsOf(...es: Expr[]): Sym[] {
  const m = new Map<string, Sym>();
  for (const e of es) for (const s of freeSymbols(e)) m.set(s.key, s);
  return [...m.values()].sort((a, b) => (a.name < b.name ? -1 : a.name > b.name ? 1 : 0));
}

/**
 * Factor a multivariate polynomial: numeric content, contents with respect to
 * each variable, univariate factors and quadratics with a perfect-square
 * discriminant. Returns [content, [factor, multiplicity][]].
 */
export function mfactorList(f0: Expr, vars: readonly Sym[], uniFactor: (e: Expr, x: Sym) => [Rational, [Expr, number][]]): [Rational, [Expr, number][]] {
  const f = expand(f0);
  if (f instanceof Rational) return [f, []];
  const live = vars.filter((v) => f.has(v));
  const out: [Expr, number][] = [];
  let content: Rational = S.One;
  const push = (g: Expr, k: number) => {
    const e = out.find(([h]) => h.key === g.key);
    if (e) e[1] += k;
    else out.push([g, k]);
  };
  const rec = (pIn: Expr, k: number) => {
    let p = pIn;
    p = expand(p);
    if (p instanceof Rational) {
      content = numMul(content, powRat(p, k));
      return;
    }
    const lv = live.filter((v) => p.has(v));
    if (lv.length === 1) {
      const [c, fs] = uniFactor(p, at(lv, 0));
      content = numMul(content, powRat(c, k));
      for (const [g, m] of fs) push(g, m * k);
      return;
    }
    // monomial factors and contents
    for (const v of lv) {
      const cv = contentIn(p, v, lv.filter((u) => u !== v));
      if (!(cv instanceof Rational) && cv.freeSymbols().size > 0) {
        rec(cv, k);
        rec(defined(divExact(p, cv, lv), 'p / content'), k);
        return;
      }
      // powers of v dividing every term
      const pc = coeffsIn(p, v);
      const low = Math.min(...pc.keys());
      if (low > 0) {
        push(v, low * k);
        rec(defined(divExact(p, pow(v, low), lv), 'p / monomial'), k);
        return;
      }
    }
    // numeric content
    const nc = numericContent(p);
    if (!nc.isOne) {
      content = numMul(content, powRat(nc, k));
      rec(expand(mul(p, pow(nc, -1))), k);
      return;
    }
    // quadratic in some variable with a square discriminant
    for (const v of lv) {
      if (degreeIn(p, v) !== 2) continue;
      const pc = coeffsIn(p, v);
      const a = pc.get(2) ?? S.Zero;
      const b = pc.get(1) ?? S.Zero;
      const c = pc.get(0) ?? S.Zero;
      const disc = expand(add(pow(b, 2), mul(-4, a, c)));
      const s = polySqrt(disc, lv, uniFactor);
      if (s === undefined) continue;
      // p = (2a v + b - s)(2a v + b + s) / (4a); make both factors primitive
      const prim = (h: Expr): Expr => {
        let g = expand(h);
        const cv = contentIn(g, v, lv.filter((u) => u !== v));
        g = divExact(g, cv, lv) ?? g;
        const nc = numericContent(g);
        return expand(mul(g, pow(nc, -1)));
      };
      const g1 = prim(add(mul(2, a, v), b, mul(-1, s)));
      const g2 = prim(add(mul(2, a, v), b, s));
      const ratio = divExact(p, expand(mul(g1, g2)), lv);
      if (!(ratio instanceof Rational)) continue;
      content = numMul(content, powRat(ratio, k));
      rec(g1, k);
      rec(g2, k);
      return;
    }
    const q = normalizeSign(p, lv);
    // keep the sign removed by the normalization in the content
    if (q.key !== p.key && k % 2 === 1) content = numMul(content, S.NegOne);
    push(q, k);
  };
  rec(f, 1);
  return [content, out];
}

/** Square root of a polynomial if it is a perfect square. */
function polySqrt(e: Expr, vars: readonly Sym[], uniFactor: (e: Expr, x: Sym) => [Rational, [Expr, number][]]): Expr | undefined {
  if (e instanceof Rational) {
    const r = pow(e, S.Half);
    return r instanceof Rational ? r : undefined;
  }
  const [c, fs] = mfactorList(e, vars, uniFactor);
  if (fs.some(([, k]) => k % 2 !== 0)) return undefined;
  const sc = pow(c, S.Half);
  if (!(sc instanceof Rational)) return undefined;
  return expand(mul(sc, ...fs.map(([g, k]) => pow(g, k / 2))));
}


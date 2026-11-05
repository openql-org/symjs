// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Multivariate polynomial arithmetic on expanded expressions:
 * exact division, pseudo-remainders, content and GCD (recursive primitive PRS),
 * and a heuristic multivariate factorization.
 */

import { PolynomialError } from '../core/errors';
import { at, defined, expectType, getOrThrow } from '../core/guard';
import type { Expr } from '../core/nodes';
import { Add, Mul, Pow, Rational, S } from '../core/nodes';
import { numMul } from '../core/num';
import { gcd as igcd, lcm as ilcm } from '../core/numbers';
import { add, mul, pow } from '../core/ops';
import { expandMul as expand } from '../simplify/expand';
import { UPoly, polyCoefficients } from './poly';
import { xreplace } from '../core/traverse';
import type { ZPoly } from './wang';
import { wangFactor, zpoly } from './wang';
import { heuGcd } from './euclidtools';

const isZeroE = (e: Expr) => e instanceof Rational && e.isZero;

/** Degree of e in x (polynomial assumed), -1 for zero. */
export function degreeIn(e: Expr, x: Expr): number {
  return Math.max(-1, ...coeffsIn(e, x).keys());
}

function coeffsIn(e: Expr, x: Expr): Map<number, Expr> {
  const pc = polyCoefficients(e, x);
  if (!pc) throw new PolynomialError('not a polynomial');
  return pc;
}

/** Leading coefficient in x of a nonzero polynomial. */
export function lcIn(e: Expr, x: Expr): Expr {
  const pc = coeffsIn(e, x);
  return getOrThrow(pc, Math.max(...pc.keys()));
}

/** gcd of two rationals, b nonzero: gcd(numerators)/lcm(denominators). */
function rationalGcd(a: Rational, b: Rational): Rational {
  if (a.isZero) return Rational.of(b.p < 0n ? -b.p : b.p, b.q);
  return Rational.of(igcd(a.p, b.p), ilcm(a.q, b.q));
}

/** Numeric content of a nonzero expanded polynomial (gcd of its rational coefficients, all nonzero). */
function numericContent(e: Expr): Rational {
  let g: Rational = S.Zero;
  for (const t of e instanceof Add ? e.args : [e]) {
    const c = t instanceof Mul && t.args[0] instanceof Rational ? t.args[0] : t instanceof Rational ? t : S.One;
    g = rationalGcd(g, c);
  }
  return g;
}

/** b**k for a rational b and a nonnegative integer k. */
const powRat = (b: Rational, k: number): Rational => Rational.of(b.p ** BigInt(k), b.q ** BigInt(k));

/** Exact quotient f/g in Q[vars], or undefined when g does not divide f. */
export function divExact(f0: Expr, g0: Expr, vars: readonly Expr[]): Expr | undefined {
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
  // each step cancels the leading term of r, so its degree in x decreases
  while (!isZeroE(r)) {
    const dr = degreeIn(r, x);
    if (dr < dg) return undefined;
    const c = divExact(lcIn(r, x), lg, rest);
    if (c === undefined) return undefined;
    const term = mul(c, pow(x, dr - dg));
    q.push(term);
    r = expand(add(r, mul(-1, term, g)));
  }
  return expand(add(...q));
}

/**
 * Division with remainder of multivariate polynomials over a field, recursively in the main
 * variable (SymPy dmp_ff_div): the leading coefficient of the remainder is divided by that of g
 * in the other variables, and the division stops when that has a remainder.
 */
export function ffDiv(f0: Expr, g0: Expr, vars: readonly Expr[]): [Expr, Expr] {
  const f = expand(f0);
  const g = expand(g0);
  if (isZeroE(g)) throw new RangeError('division by zero polynomial');
  const [x, ...rest] = vars;
  if (x === undefined) return [expand(mul(f, pow(g, -1))), S.Zero];
  const dg = degreeIn(g, x);
  let dr = degreeIn(f, x);
  const q: Expr[] = [];
  let r = f;
  const lg = lcIn(g, x);
  while (dr >= dg) {
    const [c, R] = ffDiv(lcIn(r, x), lg, rest);
    if (!isZeroE(R)) break;
    const t = mul(c, pow(x, dr - dg));
    q.push(t);
    // the leading term of r cancels, so the degree decreases
    r = expand(add(r, mul(-1, t, g)));
    dr = degreeIn(r, x);
  }
  return [expand(add(...q)), r];
}

/** Pseudo-remainder of a by b in x. */
export function prem(a0: Expr, b: Expr, x: Expr): Expr {
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
export function contentIn(f: Expr, x: Expr, rest: readonly Expr[]): Expr {
  let g: Expr = S.Zero;
  for (const c of coeffsIn(f, x).values()) g = mgcd(g, c, rest);
  return g;
}

/** Sign normalization: make the leading coefficient (lex order in vars) positive. */
function normalizeSign(e: Expr, vars: readonly Expr[]): Expr {
  let c = e;
  for (const v of vars) {
    if (!c.has(v)) continue;
    c = lcIn(c, v);
  }
  const lead = c instanceof Add ? at(c.args, -1) : c;
  const k = lead instanceof Mul && lead.args[0] instanceof Rational ? lead.args[0] : lead instanceof Rational ? lead : S.One;
  return k.isNegative ? expand(mul(-1, e)) : e;
}

/**
 * An expanded polynomial with rational coefficients in vars as [F, d] with F an integer polynomial
 * and d a positive integer, e = F/d; undefined when a term has another factor.
 */
function toZZ(e: Expr, vars: readonly Expr[]): [ZPoly, bigint] | undefined {
  const index = new Map(vars.map((v, i) => [v.key, i]));
  const ts: [number[], Rational][] = [];
  let den = 1n;
  for (const t of e instanceof Add ? e.args : [e]) {
    const m = vars.map(() => 0);
    let c: Rational = S.One;
    for (const f of t instanceof Mul ? t.args : [t]) {
      if (f instanceof Rational) {
        c = f;
        continue;
      }
      const [b, k] = f instanceof Pow && f.exp instanceof Rational && f.exp.isInteger && f.exp.p > 0n ? [f.base, Number(f.exp.p)] : [f, 1];
      const i = index.get(b.key);
      if (i === undefined) return undefined;
      m[i] = at(m, i) + k;
    }
    den = ilcm(den, c.q);
    ts.push([m, c]);
  }
  return [zpoly(ts.map(([m, c]) => [m, (c.p * den) / c.q] as const)), den];
}

/**
 * gcd(f, g) of expanded nonzero polynomials with rational coefficients by the heuristic GCD, with
 * the cofactors f/gcd and g/gcd; the gcd as mgcd normalizes it. Undefined when the coefficients
 * are not rational or the heuristic fails (`start` is the first evaluation point of heuGcd, for tests).
 */
export function heuGcdCofactors(f: Expr, g: Expr, vars: readonly Expr[], start?: bigint): [Expr, Expr, Expr] | undefined {
  const zf = toZZ(f, vars);
  const zg = zf && toZZ(g, vars);
  if (!zf || !zg) return undefined;
  const r = heuGcd(zf[0], zg[0], vars.length, start);
  if (!r) return undefined;
  const [h, cff, cfg] = r;
  let ch = 0n;
  for (const t of h.values()) ch = igcd(ch, t.c);
  const rg = rationalGcd(numericContent(f), numericContent(g));
  // f = h*cff/df = ch*prim(h)*cff/df, and the gcd is rg*prim(h)
  const prim = fromZPoly(new Map([...h].map(([k, t]) => [k, { e: t.e, c: t.c / ch }])), vars);
  const scale = (d: bigint, p: ZPoly): Expr => expand(mul(Rational.of(ch, d), pow(rg, -1), fromZPoly(p, vars)));
  return [expand(mul(rg, prim)), scale(zf[1], cff), scale(zg[1], cfg)];
}

/** GCD of two polynomials in Q[vars] (with integer content), normalized with a positive leading coefficient. */
export function mgcd(f0: Expr, g0: Expr, vars: readonly Expr[]): Expr {
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
  // SymPy dmp_gcd over ZZ and QQ: the heuristic GCD first, the remainder sequence when it fails
  const heu = heuGcdCofactors(f, g, live);
  if (heu) return heu[0];
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
    b = defined(divExact(r, contentIn(r, x, rest), live), 'primitive part');
  }
  const g1 = isZeroE(b) ? defined(divExact(a, contentIn(a, x, rest), live), 'primitive part') : S.One;
  return normalizeSign(expand(mul(c, g1)), live);
}

/** lcm of two polynomials. */
export function mlcm(f: Expr, g: Expr, vars: readonly Expr[]): Expr {
  const d = mgcd(f, g, vars);
  return normalizeSign(expand(mul(defined(divExact(f, d, vars), 'f / gcd'), g)), vars);
}

/**
 * Factor a multivariate polynomial: numeric content, contents with respect to
 * each variable, univariate factors and quadratics with a perfect-square
 * discriminant. Returns [content, [factor, multiplicity][]].
 */
export function mfactorList(f0: Expr, vars: readonly Expr[], uniFactor: (e: Expr, x: Expr) => [Rational, [Expr, number][]]): [Rational, [Expr, number][]] {
  const f = expand(f0);
  if (f instanceof Rational) return [f, []];
  const live = vars.filter((v) => f.has(v));
  const out: [Expr, number][] = [];
  let content: Rational = S.One;
  // the factors found on different branches are distinct: contents and primitive parts are
  // coprime, and a square in any variable is split off by the square-free decomposition first
  const push = (g: Expr, k: number) => {
    out.push([g, k]);
  };
  const rec = (pIn: Expr, k: number) => {
    // never a constant: contents and factors taken out keep a variable
    const p = expand(pIn);
    const lv = live.filter((v) => p.has(v));
    if (lv.length === 1) {
      const [c, fs] = uniFactor(p, at(lv, 0));
      content = numMul(content, powRat(c, k));
      for (const [g, m] of fs) push(g, m * k);
      return;
    }
    // monomial factors
    for (const v of lv) {
      // powers of v dividing every term
      const low = Math.min(...coeffsIn(p, v).keys());
      if (low > 0) {
        push(v, low * k);
        rec(defined(divExact(p, pow(v, low), lv), 'p / monomial'), k);
        return;
      }
    }
    // the content in the main variable (SymPy dmp_primitive): Wang's algorithm needs a primitive polynomial
    const [x0, ...others] = lv;
    // (the gcd of the coefficients, the shortest first, stopping at a constant)
    const cs = [...coeffsIn(p, defined(x0, 'main variable')).values()].sort((u, w) => termCount(u) - termCount(w));
    let cv: Expr = S.Zero;
    for (const c of cs) {
      cv = mgcd(cv, c, others);
      if (cv instanceof Rational) break;
    }
    if (!(cv instanceof Rational)) {
      rec(cv, k);
      rec(defined(divExact(p, cv, lv), 'p / content'), k);
      return;
    }
    // numeric content
    const nc = numericContent(p);
    if (!nc.isOne) {
      content = numMul(content, powRat(nc, k));
      rec(expand(mul(p, pow(nc, -1))), k);
      return;
    }
    // square-free decomposition (Yun) in the first variable of p
    const sqf = squareFreeParts(p, lv);
    if (sqf.length > 1 || at(sqf, 0)[1] > 1) {
      const prod = expand(mul(...sqf.map(([g, i]) => pow(g, i))));
      const ratio = expectType(divExact(p, prod, lv), (r): r is Rational => r instanceof Rational, 'square-free ratio');
      content = numMul(content, powRat(ratio, k));
      for (const [g, i] of sqf) rec(g, k * i);
      return;
    }
    // irreducible factors over ZZ (Wang's EEZ algorithm) of the primitive square-free p
    const lcFactor = (lc: ZPoly): [bigint, ZPoly[]] => {
      const [c, fs] = mfactorList(fromZPoly(lc, lv), lv, uniFactor);
      return [c.p, fs.map(([g]) => toZPoly(g, lv))];
    };
    const gs = wangFactor(toZPoly(p, lv), lv.length, lcFactor).map((g) => normalizeSign(fromZPoly(g, lv), lv));
    // p and the product of its primitive factors differ by a sign
    const ratio = expectType(divExact(p, expand(mul(...gs)), lv), (r): r is Rational => r instanceof Rational, 'factor ratio');
    content = numMul(content, powRat(ratio, k));
    for (const g of gs) push(g, k);
  };
  rec(f, 1);
  return [content, out];
}

const termCount = (e: Expr): number => (e instanceof Add ? e.args.length : 1);

/** Derivative of a polynomial in x. */
function diffIn(e: Expr, x: Expr): Expr {
  return add(...[...coeffsIn(e, x)].map(([k, c]) => mul(k, c, pow(x, k - 1))));
}

/**
 * Square-free decomposition of a primitive polynomial without a monomial
 * content (Yun's algorithm in the first variable): [(a_i, i)] with p equal
 * to prod a_i**i up to a rational factor, each a_i of positive degree in it.
 */
function squareFreeParts(p: Expr, vars: readonly Expr[]): [Expr, number][] {
  const x = defined(vars.find((v) => p.has(v)), 'main variable');
  // an image at integer values of the other variables of the same degree that is square-free
  // proves p square-free (a square factor keeps its degree in the image), without the gcd
  const others = vars.filter((v) => v !== x);
  const image = defined(UPoly.fromExpr(xreplace(p, others.map((v, i): [Expr, Expr] => [v, Rational.of(2 * i + 3)])), x), 'image');
  const sqf = image.squareFree();
  if (image.degree === degreeIn(p, x) && sqf.length === 1 && at(sqf, 0)[1] === 1) return [[p, 1]];
  const dp = diffIn(p, x);
  const c = mgcd(p, dp, vars);
  if (degreeIn(c, x) <= 0) return [[p, 1]];
  let w = defined(divExact(p, c, vars), 'p / gcd');
  let y = defined(divExact(dp, c, vars), "p' / gcd");
  const out: [Expr, number][] = [];
  for (let i = 1; degreeIn(w, x) > 0; i++) {
    const z = expand(add(y, mul(-1, diffIn(w, x))));
    const g = mgcd(w, z, vars);
    if (degreeIn(g, x) > 0) out.push([g, i]);
    w = defined(divExact(w, g, vars), 'w / g');
    y = defined(divExact(z, g, vars), 'z / g');
  }
  return out;
}

/** An expanded polynomial with integer coefficients as a sparse polynomial in vars. */
function toZPoly(e: Expr, vars: readonly Expr[]): ZPoly {
  const out: [number[], bigint][] = [];
  const walk = (c: Expr, i: number, exps: number[]): void => {
    if (i === vars.length) {
      out.push([exps, expectType(c, (r): r is Rational => r instanceof Rational && r.q === 1n, 'integer coefficient').p]);
      return;
    }
    for (const [k, ci] of coeffsIn(c, at(vars, i))) walk(ci, i + 1, [...exps, k]);
  };
  walk(e, 0, []);
  return zpoly(out);
}

const fromZPoly = (f: ZPoly, vars: readonly Expr[]): Expr => add(...[...f.values()].map((t) => mul(Rational.of(t.c), ...vars.map((v, i) => pow(v, at(t.e, i))))));

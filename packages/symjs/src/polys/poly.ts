// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Univariate polynomials over the rationals, coefficient extraction and root finding.
 */

import { NotImplementedError, PolynomialError } from '../core/errors';
import { isNegative, isNonZero, isPositive, isReal } from '../core/assumptions';
import { Eq, piecewise } from '../core/logic';
import { ExprMap } from '../core/exprmap';
import type { Expr, ExprLike, Sym } from '../core/nodes';
import { Add, Dummy, Mul, Pow, Rational, S, compareExpr, impl } from '../core/nodes';
import { zassenhaus } from './zassenhaus';
import { numCmp } from '../core/num';
import { at, defined, first, getOrThrow, last } from '../core/guard';
import { countOps, ordered } from '../core/match';
import { gcd as gcdBig, lcm } from '../core/numbers';
import { add, mul, pow, sqrt, sympify } from '../core/ops';
import { freeSymbols } from '../core/traverse';
import { expand as expandHints, expandMul as expand } from '../simplify/expand';
import { decomposePower, factorTerms } from '../simplify/exprtools';

/** cancel, registered by simplify/rational (which imports this module). @internal */
export const polyHooks: { cancel?: (e: Expr) => Expr; factorList?: (e: Expr) => [Expr, [Expr, number][]] } = {};
const cancel = (e: Expr): Expr => defined(polyHooks.cancel, 'cancel hook')(e);
/** factor, registered by polys/sympoly (loaded with this module by every entry point). */
const factorE = (e: Expr): Expr => defined(impl.factor?.(e), 'factor hook');

/**
 * Coefficients of e as a polynomial in x (degree -> coefficient expression),
 * or undefined if e is not polynomial in x.
 */
export function polyCoefficients(ex: ExprLike, x: Expr): Map<number, Expr> | undefined {
  const e = expand(sympify(ex));
  const out = new Map<number, Expr>();
  const terms = e instanceof Add ? e.args : [e];
  for (const t of terms) {
    const factors = t instanceof Mul ? t.args : [t];
    let deg = 0;
    const rest: Expr[] = [];
    for (const f of factors) {
      if (f.key === x.key) deg += 1;
      else if (f instanceof Pow && f.base.key === x.key && f.exp instanceof Rational && f.exp.isInteger && f.exp.p > 0n) {
        deg += Number(f.exp.p);
      } else if (f.has(x)) return undefined;
      else rest.push(f);
    }
    out.set(deg, add(out.get(deg) ?? S.Zero, mul(...rest)));
  }
  for (const [k, v] of [...out]) if (v instanceof Rational && v.isZero) out.delete(k);
  return out;
}

const R = (n: bigint | number, d: bigint | number = 1n) => Rational.of(n, d);

// Exact rational arithmetic (the Rational cases of core/num, typed as Rational).
const qAdd = (a: Rational, b: Rational): Rational => (a.q === b.q ? Rational.of(a.p + b.p, a.q) : Rational.of(a.p * b.q + b.p * a.q, a.q * b.q));
const qMul = (a: Rational, b: Rational): Rational => (a.isOne ? b : b.isOne ? a : Rational.of(a.p * b.p, a.q * b.q));
const qNeg = (a: Rational): Rational => Rational.of(-a.p, a.q);
/** 1/a for a nonzero a (leading coefficients and scale factors). */
const qInv = (a: Rational): Rational => Rational.of(a.q, a.p);
/** a**n for n >= 0. */
function qPowInt(a: Rational, n: bigint): Rational {
  return Rational.of(a.p ** n, a.q ** n);
}

/** Dense univariate polynomial with rational coefficients (index = degree). */
export class UPoly {
  readonly coeffs: readonly Rational[];

  constructor(coeffs: readonly Rational[]) {
    const c = [...coeffs];
    while (c.at(-1)?.isZero) c.pop();
    this.coeffs = c;
  }

  static fromExpr(e: ExprLike, x: Expr): UPoly | undefined {
    const m = polyCoefficients(e, x);
    if (!m) return undefined;
    const deg = Math.max(-1, ...m.keys());
    const cs: Rational[] = [];
    for (let i = 0; i <= deg; i++) {
      const v = m.get(i) ?? S.Zero;
      if (!(v instanceof Rational)) return undefined;
      cs.push(v);
    }
    return new UPoly(cs);
  }

  get degree(): number {
    return this.coeffs.length - 1;
  }
  get isZero(): boolean {
    return this.coeffs.length === 0;
  }
  get lc(): Rational {
    return this.coeffs[this.coeffs.length - 1] ?? S.Zero;
  }

  toExpr(x: Expr): Expr {
    return add(...this.coeffs.map((c, i) => mul(c, pow(x, i))));
  }

  add(o: UPoly): UPoly {
    const n = Math.max(this.coeffs.length, o.coeffs.length);
    const out: Rational[] = [];
    for (let i = 0; i < n; i++) out.push(qAdd(this.coeffs[i] ?? S.Zero, o.coeffs[i] ?? S.Zero));
    return new UPoly(out);
  }
  scale(k: Rational): UPoly {
    return new UPoly(this.coeffs.map((c) => qMul(c, k)));
  }
  sub(o: UPoly): UPoly {
    return this.add(o.scale(S.NegOne));
  }
  mul(o: UPoly): UPoly {
    if (this.isZero || o.isZero) return new UPoly([]);
    const out: Rational[] = Array.from({ length: this.coeffs.length + o.coeffs.length - 1 }, () => S.Zero);
    this.coeffs.forEach((a, i) =>
      o.coeffs.forEach((b, j) => {
        out[i + j] = qAdd(at(out, i + j), qMul(a, b));
      }),
    );
    return new UPoly(out);
  }

  divmod(d: UPoly): [UPoly, UPoly] {
    if (d.isZero) throw new RangeError('Polynomial division by zero');
    let r: UPoly = this;
    const q: Rational[] = Array.from({ length: Math.max(0, this.degree - d.degree + 1) }, () => S.Zero);
    const inv = qInv(d.lc);
    while (!r.isZero && r.degree >= d.degree) {
      const k = r.degree - d.degree;
      const c = qMul(r.lc, inv);
      q[k] = c;
      const shifted = new UPoly([...Array.from({ length: k }, () => S.Zero), ...d.coeffs.map((x) => qMul(x, c))]);
      r = r.sub(shifted);
    }
    return [new UPoly(q), r];
  }

  monic(): UPoly {
    return this.isZero ? this : this.scale(qInv(this.lc));
  }

  gcd(o: UPoly): UPoly {
    let a: UPoly = this;
    let b: UPoly = o;
    while (!b.isZero) [a, b] = [b, a.divmod(b)[1]];
    return a.monic();
  }

  derivative(): UPoly {
    return new UPoly(this.coeffs.slice(1).map((c, i) => qMul(c, R(i + 1))));
  }

  evalAt(x: Rational): Rational {
    return this.coeffs.reduceRight<Rational>((acc, c) => qAdd(qMul(acc, x), c), S.Zero);
  }

  /** Square-free decomposition (Yun): returns [factor, multiplicity][] of monic factors. */
  squareFree(): [UPoly, number][] {
    const out: [UPoly, number][] = [];
    if (this.degree <= 0) return out;
    const f = this.monic();
    let a = f.gcd(f.derivative());
    let b = f.divmod(a)[0];
    let c = f.derivative().divmod(a)[0];
    let d = c.sub(b.derivative());
    let i = 1;
    while (b.degree > 0) {
      a = b.gcd(d);
      if (a.degree > 0) out.push([a, i]);
      b = b.divmod(a)[0];
      c = d.divmod(a)[0];
      d = c.sub(b.derivative());
      i++;
    }
    return out;
  }

  /**
   * Rational roots (without multiplicity): the linear factors over ZZ of the
   * square-free parts (no enumeration of the divisors of the leading and
   * constant coefficients, which explodes for coefficients with many prime factors).
   */
  rationalRoots(): Rational[] {
    const roots: Rational[] = [];
    for (const [p] of this.squareFree()) {
      const den = p.coeffs.reduce((l, c) => lcm(l, c.q), 1n);
      for (const g of zassenhaus(p.coeffs.map((c) => (c.p * den) / c.q))) {
        if (g.length === 2) roots.push(R(-first(g), last(g)));
      }
    }
    return roots.sort((a, b) => numCmp(a, b));
  }

  /**
   * Factor over Q as content * prod(factor^multiplicity) with monic
   * irreducible factors, the linear ones first (by their roots).
   */
  factor(): { content: Rational; factors: [UPoly, number][] } {
    if (this.isZero) return { content: S.Zero, factors: [] };
    const content = this.lc;
    const factors: [UPoly, number][] = [];
    for (const [p, m] of this.squareFree()) {
      // full factorization over ZZ (Zassenhaus); the linear factors first, by their roots
      const den = p.coeffs.reduce((l, c) => lcm(l, c.q), 1n);
      const gs = zassenhaus(p.coeffs.map((c) => (c.p * den) / c.q)).map((g) => new UPoly(g.map((c) => Rational.of(c, last(g)))));
      const root = (g: UPoly) => qNeg(first(g.coeffs));
      for (const g of gs.filter((h) => h.degree === 1).sort((u, v) => numCmp(root(u), root(v)))) factors.push([g, m]);
      for (const g of gs.filter((h) => h.degree > 1)) factors.push([g, m]);
    }
    return { content, factors };
  }
}

/**
 * sqrt(d) with square factors moved outside, ignoring the sign of the
 * extracted factor (valid inside a +/- pair), like SymPy's roots_quadratic:
 * sqrt(-t**2) -> I*t.
 */
function sqrtRemoveSquares(d: Expr): Expr {
  if (!(d instanceof Mul || d instanceof Pow)) return sqrt(d);
  const outside: Expr[] = [];
  const inside: Expr[] = [];
  for (const f of d instanceof Mul ? d.args : [d]) {
    if (f instanceof Pow && f.exp instanceof Rational && f.exp.isInteger && f.exp.p % 2n === 0n) {
      outside.push(pow(f.base, Rational.of(f.exp.p / 2n)));
    } else inside.push(f);
  }
  if (outside.length === 0) return sqrt(d);
  return mul(...outside, sqrt(mul(...inside)));
}

/** Roots of a quadratic a x^2 + b x + c (symbolic coefficients allowed). */
/** SymPy roots_cubic (Cardano) for x**3 + a*x**2 + b*x + c with rational coefficients. */
function cubicRoots(lc: Rational, c2: Rational, c1: Rational, c0: Rational): Expr[] {
  const a = qMul(c2, qInv(lc));
  const b = qMul(c1, qInv(lc));
  const c = qMul(c0, qInv(lc));
  const third = Rational.of(1n, 3n);
  const cbrt = (x: Expr) => pow(x, third);
  // only irreducible cubics reach here: c != 0 and q != 0 (a zero q leaves the factor x + a/3)
  const p = qAdd(b, qNeg(qMul(qMul(a, a), third)));
  const q = qAdd(qAdd(c, qNeg(qMul(qMul(a, b), third))), qMul(qMul(Rational.of(2n), qPowInt(a, 3n)), Rational.of(1n, 27n)));
  const pon3 = mul(p, third);
  const aon3 = mul(a, third);
  let u1: Expr | undefined;
  const pz = p.isZero;
  if (pz) {
    u1 = q.isPositive ? neg(cbrt(q)) : cbrt(neg(q));
  } else if (q.isNegative) {
    u1 = neg(cbrt(add(mul(-1, q, Rational.of(1n, 2n)), sqrt(add(mul(pow(q, 2), Rational.of(1n, 4n)), pow(pon3, 3))))));
  }
  const coeff = mul(S.I, sqrt(3), Rational.of(1n, 2n));
  if (u1 === undefined) {
    const uks = [S.One, add(Rational.of(-1n, 2n), coeff), add(Rational.of(-1n, 2n), neg(coeff))];
    const D0 = add(pow(a, 2), mul(-3, b));
    const D1 = add(mul(2, pow(a, 3)), mul(-9, a, b), mul(27, c));
    const C = cbrt(mul(add(D1, sqrt(add(pow(D1, 2), mul(-4, pow(D0, 3))))), Rational.of(1n, 2n)));
    return uks.map((uk) => mul(-1, third, add(a, mul(uk, C), mul(D0, pow(C, -1), pow(uk, -1)))));
  }
  const u2 = mul(u1, add(Rational.of(-1n, 2n), coeff));
  const u3 = mul(u1, add(Rational.of(-1n, 2n), neg(coeff)));
  if (pz) return [u1, u2, u3].map((u) => add(u, neg(aon3)));
  return [u1, u2, u3].map((u) => add(neg(u), mul(pon3, pow(u, -1)), neg(aon3)));
}

const neg = (e: Expr): Expr => mul(-1, e);
const isZeroE = (e: Expr): boolean => e instanceof Rational && e.isZero;

/** SymPy roots_binomial: roots of a*x**n + b in SymPy's order. */
function binomialRoots(a: Rational, b: Rational, n: number): Expr[] {
  const base = qMul(qNeg(b), qInv(a));
  let alpha: Expr = pow(base, Rational.of(1n, BigInt(n)));
  alpha = expandHints(alpha, { complex: true });
  const negB = base.isNegative;
  const big = negB && even(n) && qAdd(base, S.One).isPositive;
  return binomialOrder(n, negB, big).map((k) => expand(mul(alpha, unitRoot(k, n))));
}

/** The k of the roots alpha*exp(2*pi*I*k/n) in SymPy's roots_binomial order. */
function binomialOrder(n: number, negB: boolean, big: boolean): number[] {
  let ks: number[] = [];
  let imax = Math.floor(n / 2);
  if (even(n)) {
    ks.push(imax);
    imax -= 1;
  }
  if (!negB) ks.push(0);
  for (let i = imax; i > 0; i--) {
    if (negB) ks.push(i, -i);
    else ks.push(-i, i);
  }
  if (negB) {
    ks.push(0);
    if (big) {
      const out: number[] = [];
      for (let i = 0; i < ks.length; i += 2) out.push(...ks.slice(i, i + 2).reverse());
      ks = out;
    }
  }
  return ks;
}

const even = (n: number): boolean => n % 2 === 0;

/** exp(2*pi*I*k/n) as cos + I*sin. */
function unitRoot(k: number, n: number): Expr {
  const ang = mul(Rational.of(BigInt(2 * k), BigInt(n)), S.Pi);
  return add(defined(impl.cos?.(ang), 'cos'), mul(S.I, defined(impl.sin?.(ang), 'sin')));
}

function quadraticRoots(a: Expr, b: Expr, c: Expr): [Expr, Expr] {
  const disc = expand(add(pow(b, 2), mul(-4, a, c)));
  const s = sqrtRemoveSquares(disc);
  const inv2a = pow(mul(2, a), -1);
  return [expand(mul(add(mul(-1, b), mul(-1, s)), inv2a)), expand(mul(add(mul(-1, b), s), inv2a))];
}

/**
 * Roots of a polynomial equation e = 0 in x, listed with multiplicity.
 * Supports: any degree with rational coefficients (via rational roots and
 * quadratic factors), degree <= 2 with symbolic coefficients.
 */
/**
 * SymPy `roots(f, x)`: the roots with their multiplicities. With
 * `{ multiple: true }` a list with each root repeated by its multiplicity
 * (SymPy `roots(f, x, multiple=True)`). With `{ skipQuintic: true }` the roots
 * of irreducible factors of degree 5 or more are omitted, as SymPy does.
 */
export function rootsDict(ex: ExprLike, x: Sym, opts: { multiple: true; skipQuintic?: boolean }): Expr[];
export function rootsDict(ex: ExprLike, x: Sym, opts?: { multiple?: false; skipQuintic?: boolean }): ExprMap<number>;
export function rootsDict(ex: ExprLike, x: Sym, opts: { multiple?: boolean; skipQuintic?: boolean } = {}): ExprMap<number> | Expr[] {
  const m = new ExprMap<number>();
  for (const r of roots(ex, x, opts)) m.set(r, (m.get(r) ?? 0) + 1);
  if (!opts.multiple) return m;
  // SymPy: the roots in ordered() order, each repeated by its multiplicity
  return ordered([...m.keys()]).flatMap((r) => Array.from({ length: getOrThrow(m, r) }, () => r));
}

/** Roots repeated by multiplicity (the list form used internally). */
export function roots(ex: ExprLike, x: Sym, opts: { skipQuintic?: boolean } = {}): Expr[] {
  const coeffs = polyCoefficients(ex, x);
  if (!coeffs) throw new PolynomialError('roots: expression is not a polynomial in the given symbol');
  const deg = Math.max(-1, ...coeffs.keys());
  if (deg <= 0) return [];
  const p = UPoly.fromExpr(ex, x);
  if (p && deg >= 2 && p.coeffs.filter((c) => !c.isZero).length === 2 && !first(p.coeffs).isZero) {
    return binomialRoots(at(p.coeffs, deg), first(p.coeffs), deg);
  }
  if (p) {
    const out: Expr[] = [];
    for (const [f, m] of p.factor().factors) {
      let rs: Expr[];
      const [c0 = S.Zero, c1 = S.Zero, c2 = S.Zero, c3 = S.Zero] = f.coeffs;
      if (f.degree === 1) rs = [qMul(qNeg(c0), qInv(c1))];
      else if (f.degree === 2) rs = quadraticRoots(c2, c1, c0);
      else if (f.degree === 3) rs = cubicRoots(c3, c2, c1, c0);
      else if (opts.skipQuintic && f.degree >= 5) continue; // SymPy roots() omits roots it cannot express in radicals
      else throw new NotImplementedError(`roots: cannot solve irreducible factor of degree ${f.degree}`);
      for (const r of rs) for (let i = 0; i < m; i++) out.push(r);
    }
    return out;
  }
  // Normalize by the leading coefficient; this often yields rational coefficients.
  const lead = defined(coeffs.get(deg), 'leading coefficient');
  const normalized = new Map([...coeffs].map(([k, v]) => [k, cancel(mul(v, pow(lead, -1)))] as const));
  if ([...normalized.values()].every((v) => v instanceof Rational)) {
    return roots(add(...[...normalized].map(([k, v]) => mul(v, pow(x, k)))), x);
  }
  const get = (k: number) => normalized.get(k) ?? S.Zero;
  // factor out x^k for zero low-order coefficients
  let low = 0;
  while (!normalized.has(low)) low++;
  // SymPy lists the roots at zero last
  const zeros: Expr[] = Array.from({ length: low }, () => S.Zero);
  const effDeg = deg - low;
  // SymPy roots(): a polynomial that factors over its coefficient ring is solved factor by factor
  if (coeffs.size > 2 && effDeg > 1) {
    const split = splitFactors(add(...[...coeffs].map(([k, v]) => mul(v, pow(x, k - low)))), x);
    if (split) return [...split.flatMap(([f, k]) => roots(f, x, opts).flatMap((r) => Array.from({ length: k }, () => r))), ...zeros];
  }
  if (effDeg === 1) {
    // SymPy roots_linear: over a polynomial ring the root is factored (x/(y - 1), not -x/(1 - y))
    const r = expand(mul(-1, get(low), pow(get(low + 1), -1)));
    // factor() over a polynomial ring, simplify() over EX
    if (!freeSymbols(r).size) return [r, ...zeros];
    return [isCompositeDomain([...coeffs.values()]) ? factorE(r) : simplifyEX(r), ...zeros];
  }
  if (effDeg === 2) {
    const orig = (k: number) => coeffs.get(k) ?? S.Zero;
    return [...symbolicQuadraticRoots(orig(low + 2), orig(low + 1), orig(low)), ...zeros];
  }
  // SymPy roots(): a binomial a*x**n + b by roots_binomial
  if (normalized.size === 2) return [...symbolicBinomialRoots(get(low), effDeg), ...zeros];
  if (effDeg === 3) return [...symbolicCubicRoots(get(low + 2), get(low + 1), get(low)), ...zeros];
  // a polynomial in x**2 (SymPy's decomposition f = g(x**2)): the square roots of the roots of g
  if ([...normalized.keys()].every((k) => (k - low) % 2 === 0)) {
    const g = add(...[...normalized].map(([k, v]) => mul(v, pow(x, (k - low) / 2))));
    return [...roots(g, x, opts).flatMap((r) => [neg(sqrt(r)), sqrt(r)]), ...zeros];
  }
  if (effDeg === 4) return [...symbolicQuarticRoots(get(low + 3), get(low + 2), get(low + 1), get(low), opts), ...zeros];
  throw new NotImplementedError(`roots: symbolic polynomials of degree ${effDeg} are not supported`);
}

/** Eq(p, 0) in SymPy's canonical form inside Piecewise: Eq(-a**2/12 - 1, 0) -> Eq(a**2, -12). */
function canonicalEq(p: Expr): Expr {
  const terms = p instanceof Add ? p.args : [p];
  const c0 = add(...terms.filter((t) => t instanceof Rational));
  const rest = terms.filter((t) => !(t instanceof Rational));
  const coeffOf = (t: Expr): Rational => (t instanceof Mul && t.args[0] instanceof Rational ? t.args[0] : S.One);
  const lead = coeffOf(first(rest));
  let g = 0n;
  let l = 1n;
  const gcd = (u: bigint, v: bigint): bigint => (v === 0n ? (u < 0n ? -u : u) : gcd(v, u % v));
  for (const t of rest) {
    const c = coeffOf(t);
    g = gcd(g, c.p);
    l = (l / gcd(l, c.q)) * c.q;
  }
  const k = Rational.of(lead.isNegative ? -g : g, l);
  return Eq(expand(mul(add(...rest), pow(k, -1))), mul(-1, c0, pow(k, -1)));
}

/**
 * SymPy roots_quartic for the monic x**4 + a*x**3 + b*x**2 + c*x + d with
 * symbolic coefficients (d is nonzero: the roots at zero are split off before):
 * the quasisymmetric case, the biquadratic and depressed-cubic cases, the
 * Descartes-Euler method with a rational resolvent root, else Ferrari's method,
 * with a Piecewise on p = 0 when its sign is not known.
 */
function symbolicQuarticRoots(a: Expr, b: Expr, c: Expr, d: Expr, opts: { skipQuintic?: boolean }): Expr[] {
  const y = new Dummy('y');
  const rootsOf = (cs: Expr[]): Expr[] => roots(add(...cs.map((k, i) => mul(k, pow(y, cs.length - 1 - i)))), y, opts);
  if (!isZeroE(a) && expand(pow(mul(c, pow(a, -1)), 2)).key === expand(d).key) {
    const m = mul(c, pow(a, -1));
    const [z1, z2] = symbolicQuadraticRoots(S.One, a, add(b, mul(-2, m)));
    return [...symbolicQuadraticRoots(S.One, neg(z1), m), ...symbolicQuadraticRoots(S.One, neg(z2), m)];
  }
  const a2 = pow(a, 2);
  const e = add(b, mul(Rational.of(-3n, 8n), a2));
  const f = expand(add(c, mul(a, add(mul(a2, Rational.of(1n, 8n)), mul(b, Rational.of(-1n, 2n))))));
  const aon4 = mul(a, Rational.of(1n, 4n));
  const g = expand(add(d, mul(-1, aon4, add(mul(a, add(mul(3, a2, Rational.of(1n, 64n)), mul(b, Rational.of(-1n, 4n)))), c))));
  const shift = (rs: Expr[]): Expr[] => rs.map((t) => add(t, neg(aon4)));
  if (isZeroE(f)) {
    const [y1, y2] = rootsOf([S.One, e, g]).map((t) => sqrt(t));
    return shift([neg(defined(y1, 'root')), neg(defined(y2, 'root')), defined(y1, 'root'), defined(y2, 'root')]);
  }
  if (isZeroE(g)) return shift([S.Zero, ...rootsOf([S.One, S.Zero, e, f])]);
  // Descartes-Euler: a rational nonzero root R of 64*R**3 + 32*e*R**2 + (4*e**2 - 16*g)*R - f**2
  const res = [Rational.of(64), mul(32, e), expand(add(mul(4, pow(e, 2)), mul(-16, g))), expand(neg(pow(f, 2)))];
  if (res.every((k) => k instanceof Rational)) {
    const up = UPoly.fromExpr(add(...res.map((k, i) => mul(k, pow(y, 3 - i)))), y);
    const rs = defined(up, 'resolvent').rationalRoots().filter((r) => !r.isZero);
    if (rs.length) {
      const R = last(rs);
      const c1 = sqrt(R);
      const B = mul(-1, f, c1, pow(mul(4, R), -1));
      const A = add(neg(R), mul(e, Rational.of(-1n, 2n)));
      const c2 = sqrt(add(A, B));
      const c3 = sqrt(add(A, neg(B)));
      return [add(c1, neg(c2), neg(aon4)), add(neg(c1), neg(c3), neg(aon4)), add(neg(c1), c3, neg(aon4)), add(c1, c2, neg(aon4))];
    }
  }
  // Ferrari
  const p = expand(add(mul(Rational.of(-1n, 12n), pow(e, 2)), neg(g)));
  const q = add(mul(Rational.of(-1n, 108n), pow(e, 3)), mul(e, g, Rational.of(1n, 3n)), mul(Rational.of(-1n, 8n), pow(f, 2)));
  const third = Rational.of(1n, 3n);
  const ans = (yy: Expr): Expr[] => {
    const w = sqrt(add(e, mul(2, yy)));
    const arg1 = add(mul(3, e), mul(2, yy));
    const arg2 = mul(2, f, pow(w, -1));
    const out: Expr[] = [];
    for (const sg of [-1, 1]) {
      const r = sqrt(neg(add(arg1, mul(sg, arg2))));
      for (const t of [-1, 1]) out.push(add(mul(add(mul(sg, w), mul(-t, r)), Rational.of(1n, 2n)), neg(aon4)));
    }
    return out;
  };
  const y1 = add(mul(e, Rational.of(-5n, 6n)), neg(pow(q, third)));
  if (isZeroE(p)) return ans(y1);
  const u = pow(add(mul(-1, q, Rational.of(1n, 2n)), sqrt(add(mul(pow(q, 2), Rational.of(1n, 4n)), mul(pow(p, 3), Rational.of(1n, 27n))))), third);
  const y2 = add(mul(e, Rational.of(-5n, 6n)), u, mul(-1, p, pow(mul(3, u), -1)));
  if (isNonZero(p) === true) return ans(y2);
  const a1s = ans(y1);
  const cond = canonicalEq(p);
  return ans(y2).map((r2, i) => piecewise([at(a1s, i), cond], [r2, true]));
}


/**
 * SymPy simplify() of a root over EX, as far as it matters here: together()
 * (which pulls out common factors) unless the simplified form is shorter.
 */
function simplifyEX(r: Expr): Expr {
  const tog = r instanceof Add ? commonFactor(r) : combineExp(r);
  const simp = impl.simplify(r);
  // a rearrangement of the same terms (-(a + b) for -a - b) is not shorter for SymPy
  const cands = expand(simp).key === expand(r).key ? [tog, r] : [tog, r, simp];
  return cands.reduce((best, c) => (countOps(c) < countOps(best) ? c : best));
}

/** A product with the powers of E combined (SymPy powsimp(combine='exp')). */
function combineExp(r: Expr): Expr {
  if (!(r instanceof Mul)) return r;
  const isExp = (t: Expr): t is Pow => t instanceof Pow && t.base.key === S.E.key;
  const exps = r.args.filter(isExp);
  if (exps.length < 2) return r;
  return mul(...r.args.filter((t) => !isExp(t)), pow(S.E, add(...exps.map((t) => t.exp))));
}

/** A sum with the factors common to all its terms pulled out (SymPy gcd_terms). */
function commonFactor(r: Add): Expr {
  const powers = (t: Expr): Map<string, [Expr, number]> => {
    const m = new Map<string, [Expr, number]>();
    for (const f of t instanceof Mul ? t.args : [t]) {
      if (f instanceof Rational) continue;
      const [b, k] = f instanceof Pow && f.exp instanceof Rational && f.exp.isInteger ? [f.base, Number(f.exp.p)] : [f, 1];
      m.set(b.key, [b, k]);
    }
    return m;
  };
  const maps = r.args.map(powers);
  const common: Expr[] = [];
  for (const [key, [b, k]] of first(maps)) {
    const ks = maps.map((m) => m.get(key)?.[1]);
    if (ks.some((v) => v === undefined)) continue;
    common.push(pow(b, Math.min(k, ...ks.map((v) => defined(v, 'exponent')))));
  }
  if (!common.length) return r;
  const c = mul(...common);
  return mul(c, add(...r.args.map((t) => mul(t, pow(c, -1)))));
}

/**
 * Whether SymPy's construct_domain gives a polynomial ring or a fraction field
 * for the coefficients (not EX): no generator is an algebraic number and no two
 * generators share a symbol.
 */
function isCompositeDomain(cs: readonly Expr[]): boolean {
  const gens = new Map<string, Expr>();
  const visit = (t: Expr): void => {
    if (t instanceof Rational || t.key === S.I.key) return;
    if (t instanceof Add || t instanceof Mul) return t.args.forEach(visit);
    if (t instanceof Pow && t.exp instanceof Rational && t.exp.isInteger) return visit(t.base);
    const [g] = decomposePower(t);
    gens.set(g.key, g);
  };
  // the generators of the expanded coefficients (exp(x - y) -> exp(x), exp(-y))
  cs.forEach((c) => visit(expandHints(c)));
  const seen = new Set<string>();
  for (const g of gens.values()) {
    const syms = [...freeSymbols(g)].map((v) => v.key);
    if (!syms.length && g instanceof Pow) return false;
    if (syms.some((k) => seen.has(k))) return false;
    for (const k of syms) seen.add(k);
  }
  return true;
}

/**
 * The factors containing x of factor(e) with their multiplicities (SymPy
 * Poly(f).factor_list() in roots), or undefined when e does not split.
 */
function splitFactors(e: Expr, x: Sym): [Expr, number][] | undefined {
  // (registered by polys/sympoly, loaded with this module by every entry point)
  const out = defined(polyHooks.factorList, 'factor_list hook')(e)[1].filter(([f]) => f.has(x));
  return out.length > 1 || (out.length === 1 && at(out, 0)[1] > 1) ? out : undefined;
}

/** SymPy roots_binomial for x**n + c with a symbolic c (in SymPy's order). */
function symbolicBinomialRoots(c: Expr, n: number): Expr[] {
  const base = neg(c);
  const alpha = pow(base, Rational.of(1n, BigInt(n)));
  const negB = isNegative(base) === true;
  const big = negB && even(n) && isPositive(add(base, S.One)) === true;
  return binomialOrder(n, negB, big).map((k) => expand(mul(alpha, unitRoot(k, n))));
}

/** SymPy roots_quadratic over a polynomial ring (coefficients factored). */
function symbolicQuadraticRoots(a: Expr, b: Expr, c: Expr): [Expr, Expr] {
  const ex = !isCompositeDomain([a, b, c]);
  // c = 0 does not occur: the roots at zero are split off before
  if (isZeroE(b)) {
    const q = mul(-1, c, pow(a, -1));
    const r = sqrtRemoveSquares(ex ? simplifyEX(q) : factorE(q));
    return [neg(r), r];
  }
  if (ex) return quadraticRootsEX(a, b, c);
  const A = mul(2, a);
  const B = factorE(mul(-1, b, pow(A, -1)));
  const D = mul(sqrtRemoveSquares(factorE(expand(add(pow(b, 2), mul(-4, a, c))))), pow(A, -1));
  const r0 = add(B, neg(D));
  const r1 = add(B, D);
  return isNegative(a) === true ? [r1, r0] : [r0, r1];
}

/** SymPy roots_quadratic over EX: the discriminant and -b/(2a) simplified, the roots expanded. */
function quadraticRootsEX(a: Expr, b: Expr, c: Expr): [Expr, Expr] {
  const A = mul(2, a);
  const B = simplifyEX(mul(-1, b, pow(A, -1)));
  const D = factorTerms(mul(sqrtRemoveSquares(simplifyEX(add(pow(b, 2), mul(-4, a, c)))), pow(A, -1)));
  const r0 = add(B, neg(D));
  const r1 = add(B, D);
  return isNegative(a) === true ? [r1, r0] : [expand(r0), expand(r1)];
}

/** SymPy roots_cubic (Cardano) for the monic x**3 + a*x**2 + b*x + c with symbolic coefficients. */
function symbolicCubicRoots(a: Expr, b: Expr, c: Expr): Expr[] {
  const third = Rational.of(1n, 3n);
  // (expanded: a cubic with the root -a/3 that factor() does not split has q = 0)
  const p = expand(add(b, mul(-1, pow(a, 2), third)));
  const q = expand(add(c, mul(-1, a, b, third), mul(2, pow(a, 3), Rational.of(1n, 27n))));
  const coeff = mul(S.I, sqrt(3), Rational.of(1n, 2n));
  const uks = [S.One, add(Rational.of(-1n, 2n), coeff), add(Rational.of(-1n, 2n), neg(coeff))];
  if (isZeroE(p) || isZeroE(q) || (isReal(q) === true && isNegative(q) === true)) {
    // the cases with u1 (SymPy): x**3 + a*x**2 + ... with p = 0, q = 0 or q < 0
    const pon3 = mul(p, third);
    const aon3 = mul(a, third);
    if (isZeroE(q)) {
      const r = sqrtRemoveSquares(neg(p));
      return [neg(r), S.Zero, r].map((t) => add(t, neg(aon3)));
    }
    const u1 = isZeroE(p)
      ? isPositive(q) === true
        ? neg(pow(q, third))
        : pow(neg(q), third)
      : neg(pow(add(mul(-1, q, Rational.of(1n, 2n)), sqrt(add(mul(pow(q, 2), Rational.of(1n, 4n)), pow(pon3, 3)))), third));
    const us = [u1, mul(u1, at(uks, 1)), mul(u1, at(uks, 2))];
    if (isZeroE(p)) return us.map((u) => add(u, neg(aon3)));
    return us.map((u) => add(neg(u), mul(pon3, pow(u, -1)), neg(aon3)));
  }
  const D0 = add(pow(a, 2), mul(-3, b));
  const D1 = add(mul(2, pow(a, 3)), mul(-9, a, b), mul(27, c));
  const C = pow(mul(add(D1, sqrt(add(pow(D1, 2), mul(-4, pow(D0, 3))))), Rational.of(1n, 2n)), third);
  return uks.map((uk) => mul(-1, third, add(a, mul(uk, C), mul(D0, pow(C, -1), pow(uk, -1)))));
}

/**
 * Factor a univariate polynomial with rational coefficients, SymPy style:
 * content times primitive integer factors, kept as an unevaluated product
 * (e.g. `2*(x + 1)`, `(x - 1)*(2*x + 1)`).
 */
export function factorPoly(ex: ExprLike, x: Sym): Expr {
  const e = sympify(ex);
  const p = UPoly.fromExpr(e, x);
  if (!p || p.degree <= 0) return e;
  const { content: lc, factors } = p.factor();
  let content: Rational = lc;
  const parts: Expr[] = [];
  for (const [f, m] of factors) {
    // scale the monic factor to a primitive integer polynomial
    let d = 1n;
    for (const c of f.coeffs) d = lcm(d, c.q);
    const ints = f.coeffs.map((c) => (c.p * d) / c.q);
    let g = 0n;
    for (const v of ints) g = gcdBig(g, v);
    const scale = Rational.of(d, g); // f * scale is primitive
    const prim = f.scale(scale);
    content = qMul(content, qPowInt(qInv(scale), BigInt(m)));
    parts.push(pow(prim.toExpr(x), m));
  }
  parts.sort(compareExpr);
  if (parts.length === 1 && content.isOne) return first(parts);
  return new Mul(content.isOne ? parts : [content, ...parts]);
}

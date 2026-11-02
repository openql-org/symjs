// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Univariate polynomials over the rationals, coefficient extraction and root finding.
 */

import { NotImplementedError, PolynomialError } from '../core/errors';
import { ExprMap } from '../core/exprmap';
import type { Expr, ExprLike, Sym } from '../core/nodes';
import { Add, Mul, Pow, Rational, S, compareExpr, impl } from '../core/nodes';
import { zassenhaus } from './zassenhaus';
import { numCmp } from '../core/num';
import { at, defined, first, last } from '../core/guard';
import { factorInt, gcd as gcdBig, lcm } from '../core/numbers';
import { add, mul, pow, sqrt, sympify } from '../core/ops';
import { freeSymbols } from '../core/traverse';
import { expandMul as expand } from '../simplify/expand';

/**
 * Coefficients of e as a polynomial in x (degree -> coefficient expression),
 * or undefined if e is not polynomial in x.
 */
/** cancel, registered by simplify/rational (which imports this module). @internal */
export const polyHooks: { cancel: (e: Expr) => Expr } = { cancel: (e) => e };
const cancel = (e: Expr): Expr => polyHooks.cancel(e);

export function polyCoefficients(ex: ExprLike, x: Sym): Map<number, Expr> | undefined {
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
function qInv(a: Rational): Rational {
  if (a.isZero) throw new RangeError('Division by zero');
  return Rational.of(a.q, a.p);
}
function qPowInt(a: Rational, n: bigint): Rational {
  if (n >= 0n) return Rational.of(a.p ** n, a.q ** n);
  if (a.isZero) throw new RangeError('Division by zero: 0 raised to a negative power');
  return Rational.of(a.q ** -n, a.p ** -n);
}

/** Dense univariate polynomial with rational coefficients (index = degree). */
export class UPoly {
  readonly coeffs: readonly Rational[];

  constructor(coeffs: readonly Rational[]) {
    const c = [...coeffs];
    while (c.at(-1)?.isZero) c.pop();
    this.coeffs = c;
  }

  static fromExpr(e: ExprLike, x: Sym): UPoly | undefined {
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
        out[i + j] = qAdd(out[i + j] ?? S.Zero, qMul(a, b));
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

  /** Rational roots (without multiplicity). */
  rationalRoots(): Rational[] {
    if (this.degree <= 0) return [];
    // scale to integer coefficients
    let den = 1n;
    for (const c of this.coeffs) den = lcm(den, c.q);
    const ints = this.coeffs.map((c) => (c.p * den) / c.q);
    const roots: Rational[] = [];
    let lo = 0;
    while (ints[lo] === 0n) lo++;
    if (lo > 0) roots.push(S.Zero);
    const a0 = at(ints, lo);
    const an = last(ints);
    if (ints.length - 1 === lo) return roots;
    const divisors = (nIn: bigint): bigint[] => {
      let n = nIn;
      n = n < 0n ? -n : n;
      let ds = [1n];
      for (const [p, k] of factorInt(n)) {
        const next: bigint[] = [];
        for (const d of ds) {
          let m = 1n;
          for (let i = 0n; i <= k; i++) {
            next.push(d * m);
            m *= p;
          }
        }
        ds = next;
      }
      return ds;
    };
    const seen = new Set<string>();
    for (const p of divisors(a0)) {
      for (const q of divisors(an)) {
        for (const s of [1n, -1n]) {
          const r = R(s * p, q);
          if (seen.has(r.key)) continue;
          seen.add(r.key);
          if (this.evalAt(r).isZero) roots.push(r);
        }
      }
    }
    return roots.sort((a, b) => numCmp(a, b));
  }

  /**
   * Factor over Q as content * prod(factor^multiplicity). Linear factors from
   * rational roots are split off; remaining factors are returned as they are
   * (they may still be reducible over Q).
   */
  factor(): { content: Rational; factors: [UPoly, number][] } {
    if (this.isZero) return { content: S.Zero, factors: [] };
    const content = this.lc;
    const factors: [UPoly, number][] = [];
    for (const [p, m] of this.squareFree()) {
      let rest = p;
      for (const r of p.rationalRoots()) {
        const lin = new UPoly([qNeg(r), S.One]);
        factors.push([lin, m]);
        rest = rest.divmod(lin)[0];
      }
      if (rest.degree > 1) {
        // the remaining part has no rational roots: full factorization over ZZ (Zassenhaus)
        const den = rest.coeffs.reduce((l, c) => (l * c.q) / gcdBig(l, c.q), 1n);
        const ints = rest.coeffs.map((c) => (c.p * den) / c.q);
        for (const g of zassenhaus(ints)) {
          const lcg = last(g);
          factors.push([new UPoly(g.map((c) => Rational.of(c, lcg))), m]);
        }
      } else if (rest.degree > 0) factors.push([rest, m]);
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
  if (c.isZero) {
    const [x1, x2] = quadraticRoots(S.One, a, b);
    return [x1, S.Zero, x2];
  }
  const p = qAdd(b, qNeg(qMul(qMul(a, a), third)));
  const q = qAdd(qAdd(c, qNeg(qMul(qMul(a, b), third))), qMul(qMul(Rational.of(2n), qPowInt(a, 3n)), Rational.of(1n, 27n)));
  const pon3 = mul(p, third);
  const aon3 = mul(a, third);
  let u1: Expr | undefined;
  const pz = p.isZero;
  const qz = q.isZero;
  if (pz) {
    if (qz) return [neg(aon3), neg(aon3), neg(aon3)];
    u1 = q.isPositive ? neg(cbrt(q)) : cbrt(neg(q));
  } else if (qz) {
    const [y1, y2] = quadraticRoots(S.One, S.Zero, p);
    return [y1, S.Zero, y2].map((t) => add(t, neg(aon3)));
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

/** SymPy roots_binomial: roots of a*x**n + b in SymPy's order. */
function binomialRoots(a: Rational, b: Rational, n: number): Expr[] {
  const base = qMul(qNeg(b), qInv(a));
  let alpha: Expr = pow(base, Rational.of(1n, BigInt(n)));
  alpha = impl.expandComplex ? impl.expandComplex(alpha) : alpha;
  const negB = base.isNegative;
  const even = n % 2 === 0;
  const big = negB && even && qAdd(base, S.One).isPositive;
  let ks: number[] = [];
  let imax = Math.floor(n / 2);
  if (even) {
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
  return ks.map((k) => {
    const ang = mul(Rational.of(BigInt(2 * k), BigInt(n)), S.Pi);
    const zeta = add(defined(impl.cos?.(ang), 'cos'), mul(S.I, defined(impl.sin?.(ang), 'sin')));
    return expand(mul(alpha, zeta));
  });
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
  const rs = roots(ex, x, opts);
  if (opts.multiple) return rs;
  const m = new ExprMap<number>();
  for (const r of rs) m.set(r, (m.get(r) ?? 0) + 1);
  return m;
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
  const zeros: Expr[] = Array.from({ length: low }, () => S.Zero);
  const effDeg = deg - low;
  if (effDeg === 1) {
    // SymPy roots_linear: over a polynomial ring the root is factored (x/(y - 1), not -x/(1 - y))
    const r = expand(mul(-1, get(low), pow(get(low + 1), -1)));
    if (freeSymbols(r).size && impl.factor) {
      try {
        return [...zeros, impl.factor(r)];
      } catch {
        return [...zeros, r];
      }
    }
    return [...zeros, r];
  }
  if (effDeg === 2) {
    // x**2 + c: +-sqrt(-c) (SymPy roots_quadratic with b = 0)
    if (!normalized.has(low + 1)) {
      const r = sqrtRemoveSquares(expand(mul(-1, get(low), pow(get(low + 2), -1))));
      return [...zeros, mul(-1, r), r];
    }
    return [...zeros, ...quadraticRoots(get(low + 2), get(low + 1), get(low))];
  }
  throw new NotImplementedError(`roots: symbolic polynomials of degree ${effDeg} are not supported`);
}

/** Distinct solutions of e = 0 for x (polynomial equations only). */
export function solve(ex: ExprLike, x: Sym): Expr[] {
  const seen = new Set<string>();
  const out: Expr[] = [];
  for (const r of roots(ex, x)) {
    if (!seen.has(r.key)) {
      seen.add(r.key);
      out.push(r);
    }
  }
  return out;
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
  const [only] = parts;
  if (parts.length === 1 && only !== undefined && content.isOne) return only;
  return new Mul(content.isOne ? parts : [content, ...parts]);
}

/** Factor an expression (currently: univariate polynomials with rational coefficients). */
export function factor(ex: ExprLike): Expr {
  const e = sympify(ex);
  const syms = [...freeSymbols(e)];
  const [x] = syms;
  if (syms.length !== 1 || x === undefined) return e;
  return factorPoly(e, x);
}

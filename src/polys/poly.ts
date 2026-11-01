// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Univariate polynomials over the rationals, coefficient extraction and root finding.
 */

import { Add, Expr, ExprLike, Mul, Pow, Rational, S, Sym, compareExpr } from '../core/nodes';
import { numAdd, numCmp, numInv, numMul, numNeg, numPowInt } from '../core/num';
import { factorInt, gcd as gcdBig, lcm } from '../core/numbers';
import { add, mul, pow, sqrt, sympify } from '../core/ops';
import { freeSymbols } from '../core/traverse';
import { expand } from '../simplify/expand';
import { cancel } from '../simplify/rational';

/**
 * Coefficients of e as a polynomial in x (degree -> coefficient expression),
 * or undefined if e is not polynomial in x.
 */
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

/** Dense univariate polynomial with rational coefficients (index = degree). */
export class Poly {
  readonly coeffs: readonly Rational[];

  constructor(coeffs: readonly Rational[]) {
    const c = [...coeffs];
    while (c.length > 0 && c[c.length - 1]!.isZero) c.pop();
    this.coeffs = c;
  }

  static fromExpr(e: ExprLike, x: Sym): Poly | undefined {
    const m = polyCoefficients(e, x);
    if (!m) return undefined;
    const deg = Math.max(-1, ...m.keys());
    const cs: Rational[] = [];
    for (let i = 0; i <= deg; i++) {
      const v = m.get(i) ?? S.Zero;
      if (!(v instanceof Rational)) return undefined;
      cs.push(v);
    }
    return new Poly(cs);
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

  add(o: Poly): Poly {
    const n = Math.max(this.coeffs.length, o.coeffs.length);
    const out: Rational[] = [];
    for (let i = 0; i < n; i++) out.push(numAdd(this.coeffs[i] ?? S.Zero, o.coeffs[i] ?? S.Zero) as Rational);
    return new Poly(out);
  }
  scale(k: Rational): Poly {
    return new Poly(this.coeffs.map((c) => numMul(c, k) as Rational));
  }
  sub(o: Poly): Poly {
    return this.add(o.scale(S.NegOne));
  }
  mul(o: Poly): Poly {
    if (this.isZero || o.isZero) return new Poly([]);
    const out: Rational[] = Array.from({ length: this.coeffs.length + o.coeffs.length - 1 }, () => S.Zero);
    this.coeffs.forEach((a, i) =>
      o.coeffs.forEach((b, j) => {
        out[i + j] = numAdd(out[i + j]!, numMul(a, b)) as Rational;
      }),
    );
    return new Poly(out);
  }

  divmod(d: Poly): [Poly, Poly] {
    if (d.isZero) throw new RangeError('Polynomial division by zero');
    let r: Poly = this;
    const q: Rational[] = Array.from({ length: Math.max(0, this.degree - d.degree + 1) }, () => S.Zero);
    const inv = numInv(d.lc) as Rational;
    while (!r.isZero && r.degree >= d.degree) {
      const k = r.degree - d.degree;
      const c = numMul(r.lc, inv) as Rational;
      q[k] = c;
      const shifted = new Poly([...Array.from({ length: k }, () => S.Zero), ...d.coeffs.map((x) => numMul(x, c) as Rational)]);
      r = r.sub(shifted);
    }
    return [new Poly(q), r];
  }

  monic(): Poly {
    return this.isZero ? this : this.scale(numInv(this.lc) as Rational);
  }

  gcd(o: Poly): Poly {
    let a: Poly = this;
    let b: Poly = o;
    while (!b.isZero) [a, b] = [b, a.divmod(b)[1]];
    return a.monic();
  }

  derivative(): Poly {
    return new Poly(this.coeffs.slice(1).map((c, i) => numMul(c, R(i + 1)) as Rational));
  }

  evalAt(x: Rational): Rational {
    let acc: Rational = S.Zero;
    for (let i = this.coeffs.length - 1; i >= 0; i--) acc = numAdd(numMul(acc, x), this.coeffs[i]!) as Rational;
    return acc;
  }

  /** Square-free decomposition (Yun): returns [factor, multiplicity][] of monic factors. */
  squareFree(): [Poly, number][] {
    const out: [Poly, number][] = [];
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
    const a0 = ints[lo]!;
    const an = ints[ints.length - 1]!;
    if (ints.length - 1 === lo) return roots;
    const divisors = (n: bigint): bigint[] => {
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
  factor(): { content: Rational; factors: [Poly, number][] } {
    if (this.isZero) return { content: S.Zero, factors: [] };
    const content = this.lc;
    const factors: [Poly, number][] = [];
    for (const [p, m] of this.squareFree()) {
      let rest = p;
      for (const r of p.rationalRoots()) {
        const lin = new Poly([numNeg(r) as Rational, S.One]);
        factors.push([lin, m]);
        rest = rest.divmod(lin)[0];
      }
      if (rest.degree > 0) factors.push([rest, m]);
    }
    return { content, factors };
  }
}

/** Roots of a quadratic a x^2 + b x + c (symbolic coefficients allowed). */
function quadraticRoots(a: Expr, b: Expr, c: Expr): Expr[] {
  const disc = expand(add(pow(b, 2), mul(-4, a, c)));
  const s = sqrt(disc);
  const inv2a = pow(mul(2, a), -1);
  return [expand(mul(add(mul(-1, b), mul(-1, s)), inv2a)), expand(mul(add(mul(-1, b), s), inv2a))];
}

/**
 * Roots of a polynomial equation e = 0 in x, listed with multiplicity.
 * Supports: any degree with rational coefficients (via rational roots and
 * quadratic factors), degree <= 2 with symbolic coefficients.
 */
export function roots(ex: ExprLike, x: Sym): Expr[] {
  const coeffs = polyCoefficients(ex, x);
  if (!coeffs) throw new Error('roots: expression is not a polynomial in the given symbol');
  const deg = Math.max(-1, ...coeffs.keys());
  if (deg <= 0) return [];
  const p = Poly.fromExpr(ex, x);
  if (p) {
    const out: Expr[] = [];
    for (const [f, m] of p.factor().factors) {
      let rs: Expr[];
      if (f.degree === 1) rs = [numMul(numNeg(f.coeffs[0]!), numInv(f.coeffs[1]!))];
      else if (f.degree === 2) rs = quadraticRoots(f.coeffs[2]!, f.coeffs[1]!, f.coeffs[0]!);
      else throw new Error(`roots: cannot solve irreducible factor of degree ${f.degree}`);
      for (const r of rs) for (let i = 0; i < m; i++) out.push(r);
    }
    return out;
  }
  // Normalize by the leading coefficient; this often yields rational coefficients.
  const lead = coeffs.get(deg)!;
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
  if (effDeg === 1) return [...zeros, expand(mul(-1, get(low), pow(get(low + 1), -1)))];
  if (effDeg === 2) return [...zeros, ...quadraticRoots(get(low + 2), get(low + 1), get(low))];
  throw new Error(`roots: symbolic polynomials of degree ${effDeg} are not supported`);
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
  const p = Poly.fromExpr(e, x);
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
    content = numMul(content, numPowInt(numInv(scale) as Rational, BigInt(m))) as Rational;
    parts.push(pow(prim.toExpr(x), m));
  }
  parts.sort(compareExpr);
  if (parts.length === 1 && content.isOne) return parts[0]!;
  return new Mul(content.isOne ? parts : [content, ...parts]);
}

/** Factor an expression (currently: univariate polynomials with rational coefficients). */
export function factor(ex: ExprLike): Expr {
  const e = sympify(ex);
  const syms = [...freeSymbols(e)];
  if (syms.length !== 1) return e;
  return factorPoly(e, syms[0]!);
}

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/puiseux.py), Copyright (c) 2006-2023 SymPy
// Development Team, BSD 3-Clause License (see LICENSE).

/** Sparse finite Puiseux polynomials with exact rational (possibly negative) exponents. */
import { lcm } from '../core/numbers';
import { NoMatch, type NoMatchResult } from '../core/truth';
import { at, first } from '../core/guard';
import { NotImplementedError } from '../core/errors';
import type { ExprLike } from '../core/nodes';
import { Add, Expr, Mul, Pow, Rational } from '../core/nodes';
import { add, mul, pow, sympify } from '../core/ops';
import { str } from '../printing/str';
import { groundEq, groundIsZero, groundQuo, groundStr } from './compatibility';
import type { Domain } from './domains';
import type { DomainLike, RingSymbols } from './rings';
import { PolyElement, PolyRing } from './rings';

export type PuiseuxMonom = readonly Rational[];
export type PuiseuxTerm = readonly [readonly ExprLike[], ExprLike];

/** @internal Exact exponents never pass through floating-point arithmetic. */
export function rationalExponent(e: ExprLike): Rational {
  const r = sympify(e);
  if (!(r instanceof Rational)) throw new TypeError('a Puiseux exponent must be rational');
  return r;
}
/** @internal */
export const addExponents = (a: Rational, b: Rational): Rational => Rational.of(a.p * b.q + b.p * a.q, a.q * b.q);
/** @internal */
export const multiplyExponents = (a: Rational, b: Rational): Rational => Rational.of(a.p * b.p, a.q * b.q);
/** @internal */
export const compareExponents = (a: Rational, b: Rational): number => {
  const d = a.p * b.q - b.p * a.q;
  return d < 0n ? -1 : d > 0n ? 1 : 0;
};
const monomKey = (m: PuiseuxMonom): string => m.map((e) => e.key).join(',');

/** A ring of finite sums of rational powers of its generators (SymPy PuiseuxRing). */
export class PuiseuxRing {
  readonly polyRing: PolyRing;
  readonly domain: Domain;
  readonly symbols: readonly Expr[];
  readonly ngens: number;
  readonly gens: readonly PuiseuxPoly[];
  readonly zeroMonom: PuiseuxMonom;

  constructor(symbols: RingSymbols, domain: DomainLike) {
    this.polyRing = new PolyRing(symbols, domain);
    this.domain = this.polyRing.domain;
    this.symbols = this.polyRing.symbols;
    this.ngens = this.polyRing.ngens;
    this.zeroMonom = this.symbols.map(() => Rational.of(0));
    this.gens = this.polyRing.gens.map((p) => this.fromPoly(p));
  }
  toString(): string {
    return `PuiseuxRing((${this.symbols.map((s) => str(s)).join(', ')}${this.ngens === 1 ? ',' : ''}), ${String(this.domain)})`;
  }
  equals(other: unknown): boolean {
    return other instanceof PuiseuxRing && this.polyRing.equals(other.polyRing);
  }
  /** Multiply rational exponent vectors componentwise as monomials. */
  monomialMul(a: readonly ExprLike[], b: readonly ExprLike[]): Rational[] {
    return a.map((e, i) => addExponents(rationalExponent(e), rationalExponent(at(b, i))));
  }
  get zero(): PuiseuxPoly { return this.fromDict([]); }
  get one(): PuiseuxPoly { return this.groundNew(this.domain.one); }
  fromPoly(p: PolyElement): PuiseuxPoly { return new PuiseuxPoly(p.setRing(this.polyRing), this); }
  fromDict(terms: Iterable<PuiseuxTerm>): PuiseuxPoly { return new PuiseuxPoly(terms, this); }
  fromInt(n: number | bigint): PuiseuxPoly { return this.groundNew(n); }
  domainNew(value: ExprLike): Expr { return this.polyRing.domainNew(value); }
  groundNew(value: ExprLike): PuiseuxPoly { return this.fromDict([[this.zeroMonom, value]]); }
  ringNew(value: PuiseuxPoly | PolyElement | ExprLike | ReadonlyMap<readonly ExprLike[], ExprLike>): PuiseuxPoly {
    if (value instanceof PuiseuxPoly) {
      if (!this.equals(value.ring)) throw new RangeError('cannot combine different Puiseux rings');
      return value;
    }
    if (value instanceof PolyElement) return this.fromPoly(value);
    if (value instanceof Map) return this.fromDict(value);
    if (typeof value === 'string') throw new NotImplementedError('parsing ring elements from strings');
    if (value instanceof Expr || typeof value === 'number' || typeof value === 'bigint') return this.fromExpr(value);
    throw new TypeError('expected a Puiseux polynomial, a term map or an expression');
  }
  fromExpr(value: ExprLike): PuiseuxPoly {
    const visit = (e: Expr): PuiseuxPoly => {
      const i = this.symbols.findIndex((s) => s.key === e.key);
      if (i >= 0) return at(this.gens, i);
      if (!this.symbols.some((s) => e.has(s))) return this.groundNew(e);
      if (e instanceof Add) return e.args.reduce((p, a) => p.add(visit(a)), this.zero);
      if (e instanceof Mul) return e.args.reduce((p, a) => p.mul(visit(a)), this.one);
      if (e instanceof Pow && e.exp instanceof Rational) return visit(e.base).pow(e.exp);
      return this.groundNew(e);
    };
    return visit(sympify(value));
  }
  index(x: PuiseuxPoly): number {
    const i = this.gens.findIndex((g) => g.equals(x));
    if (i < 0) throw new RangeError('expected a generator of this Puiseux ring');
    return i;
  }
}

/** An immutable sparse Puiseux polynomial; exponents are stored directly as reduced rationals. */
export class PuiseuxPoly {
  readonly ring: PuiseuxRing;
  private readonly data: ReadonlyMap<string, readonly [PuiseuxMonom, Expr]>;

  /** Integer polynomial, denominator monomial and exponent denominators of the normalized representation. */
  private representation(): { poly: PolyElement; monom: bigint[]; ns: bigint[] } {
    const terms = this.terms();
    const ns = this.ring.symbols.map((_, i) => terms.reduce((n, [m]) => lcm(n, at(m, i).q), 1n));
    const integerMonoms = terms.map(([m]) => m.map((e, i) => e.p * at(ns, i) / e.q));
    const shifts = ns.map((_, i) => integerMonoms.length === 0 ? 0n : -integerMonoms.reduce((minimum, m) => at(m, i) < minimum ? at(m, i) : minimum, at(first(integerMonoms), i)));
    const monom = shifts.some((e) => e > 0n) ? shifts : ns.map(() => 0n);
    const poly = this.ring.polyRing.fromDict(terms.map(([, c], j) => [at(integerMonoms, j).map((v, i) => Number(v + at(monom, i))), c]));
    return { poly, monom, ns };
  }
  get poly(): PolyElement { return this.representation().poly; }
  get monom(): readonly bigint[] | NoMatchResult {
    const m = this.representation().monom;
    return m.some((e) => e !== 0n) ? m : NoMatch;
  }
  get ns(): readonly bigint[] | NoMatchResult {
    const ns = this.representation().ns;
    return ns.some((e) => e !== 1n) ? ns : NoMatch;
  }

  constructor(poly: PolyElement | Iterable<PuiseuxTerm>, ring: PuiseuxRing) {
    this.ring = ring;
    const terms = poly instanceof PolyElement ? poly.setRing(ring.polyRing).listterms() : poly;
    const data = new Map<string, readonly [PuiseuxMonom, Expr]>();
    for (const [m0, c0] of terms) {
      if (m0.length !== ring.ngens) throw new RangeError('wrong number of Puiseux exponents');
      const m = m0.map(rationalExponent);
      const k = monomKey(m);
      const c = ring.domainNew(c0);
      const prev = data.get(k);
      const value = prev ? ring.domain.add(prev[1], c) : c;
      if (groundIsZero(ring.domain, value)) data.delete(k);
      else data.set(k, [m, value]);
    }
    this.data = data;
  }
  static fromDict(terms: Iterable<PuiseuxTerm>, ring: PuiseuxRing): PuiseuxPoly { return ring.fromDict(terms); }
  get length(): number { return this.data.size; }
  get isZero(): boolean { return this.length === 0; }
  get isTerm(): boolean { return this.length === 1; }
  get isOne(): boolean { return this.equals(this.ring.one); }
  get(monom: readonly ExprLike[]): Expr { return this.data.get(monomKey(monom.map(rationalExponent)))?.[1] ?? this.ring.domain.zero; }
  /** Iterate over the exponent vectors, as over the keys of a sparse polynomial. */
  *[Symbol.iterator](): IterableIterator<PuiseuxMonom> { yield* this.monoms(); }
  terms(): [PuiseuxMonom, Expr][] { return [...this.data.values()].map(([m, c]) => [[...m], c]); }
  monoms(): PuiseuxMonom[] { return this.terms().map(([m]) => m); }
  toDict(): Map<PuiseuxMonom, Expr> { return new Map(this.terms()); }
  equals(other: unknown): boolean {
    if (other instanceof PolyElement) return this.ring.polyRing.equals(other.ring) && this.equals(this.ring.fromPoly(other));
    if (other instanceof Expr || typeof other === 'number' || typeof other === 'bigint') {
      return this.length <= 1 && groundEq(this.get(this.ring.zeroMonom), sympify(other)) && (this.isZero || first(this.monoms()).every((e) => e.isZero));
    }
    if (!(other instanceof PuiseuxPoly)) return false;
    return this.ring.equals(other.ring) && this.length === other.length && this.terms().every(([m, c]) => groundEq(c, other.get(m)));
  }
  add(other: PuiseuxPoly | ExprLike): PuiseuxPoly {
    return this.ring.fromDict([...this.terms(), ...this.ring.ringNew(other).terms()]);
  }
  neg(): PuiseuxPoly { return this.ring.fromDict(this.terms().map(([m, c]) => [m, this.ring.domain.neg(c)])); }
  sub(other: PuiseuxPoly | ExprLike): PuiseuxPoly { return this.add(this.ring.ringNew(other).neg()); }
  mul(other: PuiseuxPoly | ExprLike): PuiseuxPoly {
    const q = this.ring.ringNew(other);
    return this.ring.fromDict(this.terms().flatMap(([m, c]) => q.terms().map(([n, d]): PuiseuxTerm => [m.map((e, i) => addExponents(e, at(n, i))), this.ring.domain.mul(c, d)])));
  }
  pow(exponent: ExprLike): PuiseuxPoly {
    const n = rationalExponent(exponent);
    if (!n.isInteger || n.isNegative) {
      if (!this.isTerm) throw new RangeError('only terms can be inverted or raised to fractional powers');
      const [m, c] = first(this.terms());
      if (!n.isInteger && !groundEq(c, this.ring.domain.one)) throw new RangeError('only monomials can be raised to a rational power');
      if (n.isNegative && !this.ring.domain.isField && !groundEq(c, this.ring.domain.one)) throw new RangeError('cannot invert a non-unit coefficient');
      const coefficient = n.isInteger ? groundQuo(this.ring.domain, this.ring.domain.one, this.ring.domainNew(pow(c, -n.p))) : this.ring.domain.one;
      return this.ring.fromDict([[m.map((e) => multiplyExponents(e, n)), coefficient]]);
    }
    let k = n.p;
    let result = this.ring.one;
    let factor: PuiseuxPoly = this;
    while (k > 0n) {
      if (k & 1n) result = result.mul(factor);
      k >>= 1n;
      if (k) factor = factor.mul(factor);
    }
    return result;
  }
  truediv(other: PuiseuxPoly | ExprLike): PuiseuxPoly {
    if (!(other instanceof PuiseuxPoly)) {
      const d = this.ring.domainNew(other);
      if (groundIsZero(this.ring.domain, d)) throw new RangeError('division by zero');
      // SymPy converts the reciprocal into the domain before multiplying,
      // so even (2*x)/2 cannot be formed over ZZ through a scalar divisor.
      return this.mul(this.ring.domain.isField ? groundQuo(this.ring.domain, this.ring.domain.one, d) : this.ring.domainNew(pow(d, -1)));
    }
    const q = this.ring.ringNew(other);
    if (!q.isTerm) throw new RangeError('only terms can be inverted');
    const [n, d] = first(q.terms());
    if (!this.ring.domain.isField && !groundEq(d, this.ring.domain.one)) throw new RangeError('cannot invert a non-unit coefficient');
    return this.ring.fromDict(this.terms().map(([m, c]) => [m.map((e, i) => addExponents(e, multiplyExponents(at(n, i), Rational.of(-1)))), groundQuo(this.ring.domain, c, d)]));
  }
  diff(x: PuiseuxPoly): PuiseuxPoly {
    const i = this.ring.index(x);
    return this.ring.fromDict(this.terms().filter(([m]) => !at(m, i).isZero).map(([m, c]) => [m.map((e, j) => j === i ? addExponents(e, Rational.of(-1)) : e), this.ring.domain.mul(c, this.ring.domainNew(at(m, i)))]));
  }
  asExpr(): Expr {
    return add(...this.terms().map(([m, c]) => mul(this.ring.domain.toSympy(c), ...m.map((e, i) => pow(at(this.ring.symbols, i), e)))));
  }
  toString(): string {
    const terms = this.terms().sort(([a], [b]) => {
      // Distinct map entries always differ in at least one exponent.
      return first(a.map((e, i) => compareExponents(e, at(b, i))).filter((c) => c !== 0));
    });
    return terms.map(([m, c]) => {
      const monom = m.flatMap((e, i) => e.isZero ? [] : [e.isOne ? str(at(this.ring.symbols, i)) : `${str(at(this.ring.symbols, i))}**${e.isInteger && e.isPositive ? str(e) : `(${str(e)})`}`]).join('*');
      if (!monom) return groundStr(this.ring.domain, c);
      return groundEq(c, this.ring.domain.one) ? monom : `${groundStr(this.ring.domain, c)}*${monom}`;
    }).join(' + ') || '0';
  }
}

/** Construct a Puiseux ring and its generators (SymPy puiseux_ring). */
export function puiseuxRing(symbols: RingSymbols, domain: DomainLike): [PuiseuxRing, ...PuiseuxPoly[]] {
  const ring = new PuiseuxRing(symbols, domain);
  return [ring, ...ring.gens];
}

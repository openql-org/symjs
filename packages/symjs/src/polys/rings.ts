// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/rings.py), Copyright (c) 2006-2023 SymPy
// Development Team, BSD 3-Clause License (see LICENSE).

/**
 * @file Sparse polynomial rings (SymPy `sympy.polys.rings`): `PolyRing`
 * K[x_1, ..., x_n] over a ground domain with a monomial order, and its
 * elements `PolyElement`, maps from exponent vectors to nonzero ground
 * coefficients. `ring`, `xring`, `vring` and `sring` construct rings.
 */

import { ExactQuotientFailed, NotImplementedError, PolynomialError } from '../core/errors';
import { at, first } from '../core/guard';
import type { ExprLike } from '../core/nodes';
import { Add, Expr, Mul, Pow, Rational, Sym } from '../core/nodes';
import { expandSymbolNames } from '../core/numberutils';
import { add, mul, pow, sympify } from '../core/ops';
import { gcd as igcd } from '../core/numbers';
import { multinomialCoefficients } from '../ntheory/multinomial';
import type { IntLike } from '../ntheory/intutil';
import { PREC, str } from '../printing/str';
import { expand } from '../simplify/expand';
import {
  IPolys,
  canonicalUnit,
  groundAbs,
  groundConvert,
  groundDenom,
  groundEq,
  groundGcd,
  groundIsNegative,
  groundIsZero,
  groundLcm,
  groundPow,
  groundPrecedence,
  groundQuo,
  groundRem,
  groundRing,
  groundStr,
  hasAssocRing,
  intArg,
} from './compatibility';
import type { Monom } from './compatibility';
import type { Domain } from './domains';
import { CoercionFailed, EX, FractionField, IntegerRing, PolynomialRing as PolynomialDomain, QQ, RR, ZZ } from './domains';
import type { MonomialOrdering } from './orderings';
import { grevlex, grlex, igrevlex, igrlex, ilex, lex } from './orderings';
import { GeneratorsError, MultivariatePolynomialError } from './polyerrors';
import { Poly, inferDomain, sortGens } from './sympoly';

export type { Monom } from './compatibility';

/** The generators of a ring: a string of names ('x,y' or 'x y'), a symbol or a sequence of them. */
export type RingSymbols = string | Expr | readonly (string | Expr)[];
/** A ground domain or its name (ZZ, QQ, RR, EX, ZZ[a,b], QQ(a), ...). */
export type DomainLike = Domain | string;
/** A monomial order or its name (lex, grlex, grevlex, ilex, ...). */
export type OrderLike = MonomialOrdering | string;

const ORDERS: Readonly<Record<string, MonomialOrdering>> = { lex, grlex, grevlex, ilex, igrlex, igrevlex };

const mkey = (m: Monom): string => m.join(',');

/** SymPy _parse_symbols. */
function parseSymbols(symbols: RingSymbols): Expr[] {
  if (typeof symbols === 'string') return expandSymbolNames(symbols).map((n) => new Sym(n));
  if (symbols instanceof Expr) return [symbols];
  if (symbols.every((s) => typeof s === 'string')) return symbols.flatMap((s) => expandSymbolNames(s).map((n) => new Sym(n)));
  if (symbols.every((s) => s instanceof Expr)) return [...symbols];
  throw new GeneratorsError('expected a string, Symbol or expression or a non-empty sequence of strings, Symbols or expressions');
}

/** A domain from its name (SymPy Domain option). */
export function parseDomain(d: DomainLike): Domain {
  if (typeof d !== 'string') return d;
  const grounds: Record<string, Domain> = { ZZ, QQ, RR, EX, Z: ZZ, Q: QQ, R: RR };
  const g = grounds[d];
  if (g) return g;
  const m = /^(ZZ|QQ)([[(])(.+)[\])]$/.exec(d.replace(/\s/g, ''));
  if (m) {
    const K = at(m, 1) === 'QQ' ? QQ : ZZ;
    const syms = at(m, 3).split(',').map((n) => new Sym(n));
    return at(m, 2) === '[' ? K.polyRing(...syms) : K.fracField(...syms);
  }
  throw new PolynomialError(`expected a valid domain specification, got ${d}`);
}

function parseOrder(o: OrderLike): MonomialOrdering {
  if (typeof o !== 'string') return o;
  const r = ORDERS[o];
  if (!r) throw new PolynomialError(`supported monomial orderings are 'lex', 'grlex' and 'grevlex', got '${o}'`);
  return r;
}

/**
 * A multivariate polynomial ring K[x_1, ..., x_n] with sparse elements
 * (SymPy PolyRing). Rings with the same generators, domain and order are
 * equal.
 */
export class PolyRing extends IPolys<PolyElement> {
  readonly symbols: readonly Expr[];
  readonly ngens: number;
  readonly domain: Domain;
  readonly order: MonomialOrdering;
  readonly zeroMonom: Monom;
  readonly gens: readonly PolyElement[];
  /** The identity of the ring (generators, domain and order). */
  readonly key: string;

  constructor(symbols: RingSymbols, domain: DomainLike = ZZ, order: OrderLike = lex) {
    super();
    this.symbols = parseSymbols(symbols);
    this.ngens = this.symbols.length;
    this.domain = parseDomain(domain);
    this.order = parseOrder(order);
    const shared = this.domain.symbols.filter((s) => this.symbols.some((t) => t.key === s.key));
    if (shared.length) throw new GeneratorsError("polynomial ring and it's ground domain share generators");
    this.zeroMonom = new Array<number>(this.ngens).fill(0);
    this.key = `${this.symbols.map((s) => s.key).join(';')}|${this.domain.toString()}|${this.order.toString()}`;
    this.gens = this.symbols.map((_, i) => new PolyElement(this, [[this.monomialBasis(i), this.domain.one]]));
  }

  toString(): string {
    return `Polynomial ring in ${this.symbols.map((s) => str(s)).join(', ')} over ${this.domain.toString()} with ${this.order.toString()} order`;
  }

  /** The rings have the same generators, domain and order (SymPy ==). */
  equals(other: unknown): boolean {
    return other instanceof PolyRing && other.key === this.key;
  }

  /** The ring with other generators, domain or order (SymPy clone). */
  clone(opts: { symbols?: RingSymbols; domain?: DomainLike; order?: OrderLike } = {}): PolyRing {
    return new PolyRing(opts.symbols ?? this.symbols, opts.domain ?? this.domain, opts.order ?? this.order);
  }

  /** The exponent vector of the i-th generator (SymPy monomial_basis). */
  monomialBasis(i: IntLike): number[] {
    const m = new Array<number>(this.ngens).fill(0);
    m[intArg(i)] = 1;
    return m;
  }

  get zero(): PolyElement {
    return new PolyElement(this, []);
  }

  get one(): PolyElement {
    return new PolyElement(this, [[this.zeroMonom, this.domain.one]]);
  }

  /** e is an element of this ring (SymPy is_element). */
  isElement(e: unknown): boolean {
    return e instanceof PolyElement && e.ring.key === this.key;
  }

  /** A value as an element of the ground domain (SymPy domain_new). */
  domainNew(element: ExprLike | PolyElement): Expr {
    if (element instanceof PolyElement) {
      if (element.isGround) return element.const();
      throw new CoercionFailed(`cannot convert ${element.toString()} to ${this.domain.toString()}`);
    }
    return groundConvert(this.domain, element);
  }

  /** The constant polynomial c (SymPy ground_new). */
  groundNew(coeff: ExprLike | PolyElement): PolyElement {
    return this.termNew(this.zeroMonom, coeff);
  }

  /** The term c*x**monom (SymPy term_new). */
  termNew(monom: Monom, coeff: ExprLike | PolyElement): PolyElement {
    const c = this.domainNew(coeff);
    return new PolyElement(this, groundIsZero(this.domain, c) ? [] : [[monom, c]]);
  }

  /**
   * An element of this ring (SymPy ring_new, R(element)): a polynomial of
   * this ring, a map or list of terms, a dense list, an expression or a
   * ground value.
   */
  ringNew(element: PolyElement | ReadonlyMap<Monom, ExprLike> | readonly unknown[] | ExprLike): PolyElement {
    if (element instanceof PolyElement) {
      if (this.isElement(element)) return element;
      if (element.ring.ngens === this.ngens && element.ring.symbols.every((s, i) => s.key === at(this.symbols, i).key)) return this.fromTerms(element.listterms());
      throw new NotImplementedError('conversion');
    }
    if (element instanceof Map) return this.fromDict(element);
    if (Array.isArray(element)) {
      const list: readonly unknown[] = element;
      return list.every(isTermPair) ? this.fromTerms(list.filter(isTermPair)) : this.fromList(list);
    }
    if (typeof element === 'string') throw new NotImplementedError('parsing');
    if (element instanceof Expr) return this.fromExpr(element);
    if (typeof element === 'number' || typeof element === 'bigint') return this.groundNew(element);
    throw new TypeError('expected a polynomial, terms, a dense list or an expression');
  }

  /** An element from a map of exponent vectors to coefficients (SymPy from_dict). */
  fromDict(element: ReadonlyMap<Monom, ExprLike> | Iterable<readonly [Monom, ExprLike]>): PolyElement {
    return this.fromTerms(element instanceof Map ? [...element] : element);
  }

  /** An element from (exponent vector, coefficient) pairs; repeated monomials are added (SymPy from_terms). */
  fromTerms(terms: Iterable<readonly [Monom, ExprLike]>): PolyElement {
    const K = this.domain;
    const map = new Map<string, [Monom, Expr]>();
    for (const [m, c0] of terms) {
      if (m.length !== this.ngens) throw new PolynomialError(`expected a monomial of length ${this.ngens}`);
      const c = c0 instanceof Expr && !(c0 instanceof Rational) ? c0 : groundConvert(K, c0);
      const k = mkey(m);
      const prev = map.get(k);
      map.set(k, [[...m], prev ? K.add(prev[1], c) : c]);
    }
    return new PolyElement(this, [...map.values()].filter(([, c]) => !groundIsZero(K, c)));
  }

  /** An element from a dense recursive list, highest degree first (SymPy from_list). */
  fromList(element: readonly unknown[]): PolyElement {
    const out: [Monom, ExprLike][] = [];
    const walk = (r: unknown, level: number, prefix: number[]): void => {
      if (level === this.ngens) {
        if (!(r instanceof Expr || typeof r === 'number' || typeof r === 'bigint')) throw new PolynomialError('from_list: a dense list nested more deeply than the generators');
        out.push([prefix, r]);
        return;
      }
      if (!Array.isArray(r)) throw new PolynomialError('from_list: a dense list nested less deeply than the generators');
      const list: readonly unknown[] = r;
      list.forEach((x, i) => walk(x, level + 1, [...prefix, list.length - 1 - i]));
    };
    walk(element, 0, []);
    return this.fromTerms(out);
  }

  /** An element from an expression in the generators (SymPy from_expr). */
  fromExpr(expr: ExprLike): PolyElement {
    const rebuild = (e: Expr): PolyElement => {
      const i = this.symbols.findIndex((s) => s.key === e.key);
      if (i >= 0) return at(this.gens, i);
      if (e instanceof Add) return e.args.map(rebuild).reduce((a, b) => a.add(b));
      if (e instanceof Mul) return e.args.map(rebuild).reduce((a, b) => a.mul(b));
      if (e instanceof Pow && e.exp instanceof Rational && e.exp.isInteger && e.exp.p > 1n) return rebuild(e.base).pow(Number(e.exp.p));
      return this.groundNew(e);
    };
    try {
      return rebuild(sympify(expr));
    } catch {
      throw new RangeError(`expected an expression convertible to a polynomial in ${this.toString()}, got ${str(sympify(expr))}`);
    }
  }

  /** The index of a generator given as an element, an index, a name or undefined (SymPy index). */
  index(gen?: PolyElement | IntLike | string): number {
    if (gen === undefined) return this.ngens ? 0 : -1;
    if (typeof gen === 'string') {
      const i = this.symbols.findIndex((s) => s instanceof Sym && s.name === gen);
      if (i < 0) throw new RangeError(`invalid generator: ${gen}`);
      return i;
    }
    if (gen instanceof PolyElement) {
      const i = this.isElement(gen) ? this.gens.findIndex((g) => g.equals(gen)) : -1;
      if (i < 0) throw new RangeError(`invalid generator: ${gen.toString()}`);
      return i;
    }
    const i = intArg(gen);
    if (i >= 0 && i < this.ngens) return i;
    if (i >= -this.ngens && i <= -1) return -i - 1;
    throw new RangeError(`invalid generator index: ${i}`);
  }

  /** The ring without the given generators, or the domain when none remain (SymPy drop). */
  drop(...gens: (PolyElement | IntLike | string)[]): PolyRing | Domain {
    const idx = new Set(gens.map((g) => this.index(g)));
    const symbols = this.symbols.filter((_, i) => !idx.has(i));
    return symbols.length ? this.clone({ symbols }) : this.domain;
  }

  /** The ring with the generators start..end, or the domain when none remain (SymPy R[start:end]). */
  slice(start: number, end?: number): PolyRing | Domain {
    const symbols = this.symbols.slice(start, end);
    return symbols.length ? this.clone({ symbols }) : this.domain;
  }

  /** The ring over the ground domain of a composite domain (SymPy to_ground). */
  toGround(): PolyRing {
    const K = this.domain;
    if (K instanceof PolynomialDomain || K instanceof FractionField) return this.clone({ domain: groundOfSymbolic(K) });
    throw new PolynomialError(`${K.toString()} is not a composite domain`);
  }

  get isUnivariate(): boolean {
    return this.ngens === 1;
  }

  get isMultivariate(): boolean {
    return this.ngens > 1;
  }

  /** The sum of polynomials or nested sequences of them (SymPy add). */
  add(...objs: (PolyElement | ExprLike | Iterable<PolyElement | ExprLike>)[]): PolyElement {
    let p = this.zero;
    for (const o of objs) p = isIterable(o) ? p.add(this.add(...o)) : p.add(o);
    return p;
  }

  /** The product of polynomials or nested sequences of them (SymPy mul). */
  mul(...objs: (PolyElement | ExprLike | Iterable<PolyElement | ExprLike>)[]): PolyElement {
    let p = this.one;
    for (const o of objs) p = isIterable(o) ? p.mul(this.mul(...o)) : p.mul(o);
    return p;
  }

  /** The ring without the given generators over a domain that contains them (SymPy drop_to_ground). */
  dropToGround(...gens: (PolyElement | IntLike | string)[]): PolyRing {
    const idx = new Set(gens.map((g) => this.index(g)));
    const symbols = this.symbols.filter((_, i) => !idx.has(i));
    if (!symbols.length) return this;
    const dropped = this.symbols.filter((_, i) => idx.has(i));
    return this.clone({ symbols, domain: this.domain.polyRing(...dropped.map(asSym)) });
  }

  /** The ring with the generators of both rings (SymPy compose). */
  compose(other: PolyRing): PolyRing {
    if (this.equals(other)) return this;
    return this.addGens(other.symbols);
  }

  /** The ring with the given symbols added to its generators, sorted as SymPy's set union (SymPy add_gens). */
  addGens(symbols: readonly Expr[]): PolyRing {
    const all = new Map<string, Expr>();
    for (const s of [...this.symbols, ...symbols]) all.set(s.key, s);
    return this.clone({ symbols: sortGens([...all.values()]) });
  }

  /** The elementary symmetric polynomial of degree n in the generators (SymPy symmetric_poly). */
  symmetricPoly(n: IntLike): PolyElement {
    const k = intArg(n);
    if (k < 0 || k > this.ngens) throw new RangeError(`Cannot generate symmetric polynomial of order ${k} for ${this.gens.map(String).join(', ')}`);
    if (!k) return this.one;
    let poly = this.zero;
    for (const s of subsetsOf(this.ngens, k)) poly = poly.add(this.termNew(this.zeroMonom.map((_, i) => (s.includes(i) ? 1 : 0)), this.domain.one));
    return poly;
  }

  /** The ring without the i-th generator (of a ring with several). */
  dropGen(i: number): PolyRing {
    return this.clone({ symbols: this.symbols.filter((_, j) => j !== i) });
  }

  // ---- IPolys plumbing -----------------------------------------------------

  withDomain(K: Domain): PolyRing {
    return this.clone({ domain: K });
  }

  protected moveTo(f: PolyElement, R: IPolys<PolyElement>): PolyElement {
    return R.fromTerms(f.listterms());
  }

  protected dropRing(j: number): PolyRing | Domain {
    return this.drop(j);
  }
}

function isPairs<T>(x: unknown): x is readonly (readonly [GenLike, T])[] {
  return Array.isArray(x);
}

function isMapArg(x: unknown): x is ReadonlyMap<PolyElement, PolyElement | ExprLike> {
  return x instanceof Map;
}

function isExprList(x: unknown): x is readonly ExprLike[] {
  return Array.isArray(x);
}

const isTermPair = (t: unknown): t is readonly [Monom, ExprLike] => Array.isArray(t) && t.length === 2 && Array.isArray(t[0]);

function isIterable(o: unknown): o is Iterable<PolyElement | ExprLike> {
  return typeof o === 'object' && o !== null && !(o instanceof PolyElement) && !(o instanceof Expr) && Symbol.iterator in o;
}

function asSym(e: Expr): Sym {
  if (e instanceof Sym) return e;
  throw new PolynomialError(`${str(e)} is not a symbol`);
}

/** The numeric ground of K[a, ...] or K(a, ...). */
function groundOfSymbolic(K: Domain): Domain {
  return K.ground === 'QQ' ? QQ : K.ground === 'RR' ? RR : K.ground === 'EX' ? EX : ZZ;
}

/** The k-element subsets of 0..n-1 in SymPy's order. */
function subsetsOf(n: number, k: number): number[][] {
  const out: number[][] = [];
  const rec = (start: number, cur: number[]): void => {
    if (cur.length === k) {
      out.push(cur);
      return;
    }
    for (let i = start; i < n; i++) rec(i + 1, [...cur, i]);
  };
  rec(0, []);
  return out;
}

/** The generator argument of an element method (an element, an index or a name). */
export type GenLike = PolyElement | IntLike | string;

/**
 * An element of a polynomial ring (SymPy PolyElement): a map from
 * exponent vectors to nonzero coefficients of the ground domain. Elements are
 * immutable.
 */
export class PolyElement {
  readonly ring: PolyRing;
  private readonly map: ReadonlyMap<string, readonly [Monom, Expr]>;

  constructor(ring: PolyRing, terms: Iterable<readonly [Monom, Expr]>) {
    this.ring = ring;
    const m = new Map<string, readonly [Monom, Expr]>();
    for (const [e, c] of terms) if (!groundIsZero(ring.domain, c)) m.set(mkey(e), [e, c]);
    this.map = m;
  }

  private get K(): Domain {
    return this.ring.domain;
  }

  private make(terms: Iterable<readonly [Monom, Expr]>): PolyElement {
    return new PolyElement(this.ring, terms);
  }

  /** The number of terms. */
  get length(): number {
    return this.map.size;
  }

  /** The coefficient of an exponent vector (zero when absent). */
  get(monom: Monom): Expr {
    return this.map.get(mkey(monom))?.[1] ?? this.K.zero;
  }

  /** The polynomial as a map of exponent vectors to coefficients (SymPy to_dict). */
  toDict(): Map<Monom, Expr> {
    return new Map(this.listterms());
  }

  /** The element in another ring with the same or reordered generators (SymPy set_ring). */
  setRing(newRing: PolyRing): PolyElement {
    if (this.ring.equals(newRing)) return this;
    const pos = this.ring.symbols.map((s) => newRing.symbols.findIndex((t) => t.key === s.key));
    const terms: [Monom, Expr][] = [];
    for (const [m, c] of this.listterms()) {
      const e = new Array<number>(newRing.ngens).fill(0);
      m.forEach((k, i) => {
        const j = at(pos, i);
        if (j < 0) {
          if (k) throw new GeneratorsError(`unable to drop generators ${str(at(this.ring.symbols, i))}`);
        } else e[j] = k;
      });
      terms.push([e, newRing.domainNew(this.K.toSympy(c))]);
    }
    return newRing.fromTerms(terms);
  }

  /** The polynomial as an expression in the generators (or the given symbols) (SymPy as_expr). */
  asExpr(...symbols: Expr[]): Expr {
    const syms = symbols.length ? symbols : this.ring.symbols;
    if (syms.length !== this.ring.ngens) throw new RangeError(`Wrong number of symbols, expected ${this.ring.ngens} got ${syms.length}`);
    return add(...this.terms().map(([m, c]) => mul(this.K.toSympy(c), ...m.map((k, i) => pow(at(syms, i), k)))));
  }

  /** The lcm of the coefficient denominators and the polynomial multiplied by it (SymPy clear_denoms). */
  clearDenoms(): [Expr, PolyElement] {
    const K = this.K;
    if (!K.isField || !hasAssocRing(K)) return [K.one, this];
    let common: Expr = Rational.of(1);
    for (const [, c] of this.listterms()) common = groundLcm(ZZ, common, groundDenom(c));
    return [common, this.mulGround(common)];
  }

  /** Equality with a polynomial of the same ring or a ground value (SymPy ==). */
  equals(other: unknown): boolean {
    if (other instanceof PolyElement) {
      if (!this.ring.isElement(other)) return this.isZero && other.isZero;
      if (other.length !== this.length) return false;
      return this.listterms().every(([m, c]) => groundEq(other.get(m), c));
    }
    if (other instanceof Expr || typeof other === 'number' || typeof other === 'bigint') {
      if (this.length > 1) return false;
      const v = sympify(other);
      return groundEq(this.const(), v) && (this.isZero || this.isGround);
    }
    return false;
  }

  /** The polynomial without the generator, which must not occur (SymPy drop). */
  drop(gen: GenLike): PolyElement | Expr {
    const i = this.ring.index(gen);
    if (this.ring.ngens === 1) {
      if (this.isGround) return this.const();
      throw new RangeError(`Cannot drop ${String(gen)}`);
    }
    const R = this.ring.dropGen(i);
    if (this.listmonoms().some((m) => at(m, i) !== 0)) throw new RangeError(`Cannot drop ${String(gen)}`);
    return R.fromTerms(this.listterms().map(([m, c]) => [[...m.slice(0, i), ...m.slice(i + 1)], c] as const));
  }

  /** The polynomial over the ring without the generator, with the generator moved into the domain (SymPy drop_to_ground). */
  dropToGround(gen: GenLike): PolyElement {
    if (this.ring.ngens === 1) throw new RangeError('Cannot drop only generator to ground');
    const i = this.ring.index(gen);
    const R = this.ring.dropToGround(i);
    const g = at(this.ring.symbols, i);
    return R.fromTerms(this.listterms().map(([m, c]) => [[...m.slice(0, i), ...m.slice(i + 1)], R.domain.fromSympy(mul(this.K.toSympy(c), pow(g, at(m, i))))] as const));
  }

  /** The dense recursive representation (SymPy to_dense). */
  toDense(): unknown[] {
    const build = (terms: [Monom, Expr][], level: number): unknown[] | Expr => {
      if (level === this.ring.ngens) return terms.length ? first(terms)[1] : this.K.zero;
      const deg = Math.max(-1, ...terms.map(([m]) => at(m, level)));
      const out: unknown[] = [];
      for (let k = deg; k >= 0; k--) out.push(build(terms.filter(([m]) => at(m, level) === k), level + 1));
      return out;
    };
    const r = build(this.listterms(), 0);
    return Array.isArray(r) ? r : [r];
  }

  toString(): string {
    const K = this.K;
    if (this.isZero) return groundStr(K, K.zero);
    const parts: string[] = [];
    for (const [expv, coeff] of this.terms()) {
      const negative = groundIsNegative(K, coeff);
      parts.push(negative ? ' - ' : ' + ');
      let scoeff: string;
      if (expv.every((e) => e === 0)) {
        scoeff = groundStr(K, coeff);
        if (negative && scoeff.startsWith('-')) scoeff = scoeff.slice(1);
      } else {
        const c = negative ? K.neg(coeff) : coeff;
        if (groundEq(c, K.one)) scoeff = '';
        else {
          const s = groundStr(K, c);
          scoeff = groundPrecedence(K, c) < PREC.MUL ? `(${s})` : s;
        }
      }
      const sexpv: string[] = [];
      expv.forEach((e, i) => {
        if (!e) return;
        const s0 = at(this.ring.symbols, i);
        const sym = s0 instanceof Sym ? str(s0) : `(${str(s0)})`;
        sexpv.push(e === 1 ? sym : e < 0 ? `${sym}**(${e})` : `${sym}**${e}`);
      });
      if (scoeff) sexpv.unshift(scoeff);
      parts.push(sexpv.join('*'));
    }
    const head = first(parts);
    parts.shift();
    if (head === ' - ') parts.unshift('-');
    return parts.join('');
  }

  // ---- predicates ------------------------------------------------------------

  get isGenerator(): boolean {
    return this.ring.gens.some((g) => g.equals(this));
  }
  get isGround(): boolean {
    return this.isZero || (this.length === 1 && this.map.has(mkey(this.ring.zeroMonom)));
  }
  get isMonomial(): boolean {
    return this.isZero || (this.length === 1 && groundEq(this.LC, this.K.one));
  }
  get isTerm(): boolean {
    return this.length <= 1;
  }
  get isNegative(): boolean {
    return groundIsNegative(this.K, this.LC);
  }
  get isPositive(): boolean {
    return !this.isZero && !this.isNegative;
  }
  get isNonnegative(): boolean {
    return !this.isNegative;
  }
  get isNonpositive(): boolean {
    return this.isZero || this.isNegative;
  }
  get isZero(): boolean {
    return this.map.size === 0;
  }
  get isOne(): boolean {
    return this.equals(this.ring.one);
  }
  get isMonic(): boolean {
    return groundEq(this.LC, this.K.one);
  }
  get isPrimitive(): boolean {
    return groundEq(this.content(), this.K.one);
  }
  get isLinear(): boolean {
    return this.listmonoms().every((m) => m.reduce((s, e) => s + e, 0) <= 1);
  }
  get isQuadratic(): boolean {
    return this.listmonoms().every((m) => m.reduce((s, e) => s + e, 0) <= 2);
  }
  get isSquarefree(): boolean {
    return this.ring.ngens === 0 || this.ring.dmpSqfP(this);
  }
  get isIrreducible(): boolean {
    return this.ring.ngens === 0 || this.ring.dmpIrreducibleP(this);
  }
  get isCyclotomic(): boolean {
    if (!this.ring.isUnivariate) throw new MultivariatePolynomialError('cyclotomic polynomial');
    return this.ring.dupCyclotomicP(this);
  }

  // ---- arithmetic ------------------------------------------------------------

  /** -f. */
  neg(): PolyElement {
    return this.make(this.listterms().map(([m, c]) => [m, this.K.neg(c)] as const));
  }

  /** The other operand as an element of this ring (a polynomial of the ring or a ground value). */
  private coerce(o: PolyElement | ExprLike): PolyElement {
    if (o instanceof PolyElement) {
      if (this.ring.isElement(o)) return o;
      if (o.isGround && o.ring.ngens === 0) return this.ring.groundNew(o.const());
      throw new PolynomialError(`cannot combine elements of ${this.ring.toString()} and ${o.ring.toString()}`);
    }
    return this.ring.groundNew(o);
  }

  /** f + g. */
  add(o: PolyElement | ExprLike): PolyElement {
    const g = this.coerce(o);
    const K = this.K;
    const m = new Map(this.map);
    for (const [k, [e, c]] of g.map) {
      const p = m.get(k);
      m.set(k, [e, p ? K.add(p[1], c) : c]);
    }
    return this.make(m.values());
  }

  /** f - g. */
  sub(o: PolyElement | ExprLike): PolyElement {
    return this.add(this.coerce(o).neg());
  }

  /** f*g. */
  mul(o: PolyElement | ExprLike): PolyElement {
    const g = this.coerce(o);
    const K = this.K;
    const m = new Map<string, [Monom, Expr]>();
    for (const [e1, c1] of this.map.values()) {
      for (const [e2, c2] of g.map.values()) {
        const e = e1.map((a, i) => a + at(e2, i));
        const k = mkey(e);
        const p = m.get(k);
        const c = K.mul(c1, c2);
        m.set(k, [e, p ? K.add(p[1], c) : c]);
      }
    }
    return this.make(m.values());
  }

  /** f**n for a nonnegative integer n (SymPy __pow__). */
  pow(n: IntLike): PolyElement {
    const k = intArg(n, 'exponent');
    if (k < 0) throw new RangeError(`exponent must be a non-negative integer, got ${k}`);
    if (k === 0) {
      if (this.isZero) throw new RangeError('0**0');
      return this.ring.one;
    }
    if (this.length === 1) {
      const [e, c] = first(this.listterms());
      return this.make([[e.map((a) => a * k), groundEq(c, this.K.one) ? c : groundPow(this.K, c, k)]]);
    }
    if (k === 1) return this;
    if (k === 2) return this.square();
    if (k === 3) return this.mul(this.square());
    if (this.length <= 5) return this.powMultinomial(k);
    return this.powGeneric(k);
  }

  private powGeneric(n0: number): PolyElement {
    let p = this.ring.one;
    let c: PolyElement = this;
    let n = n0;
    for (;;) {
      if (n & 1) {
        p = p.mul(c);
        n -= 1;
        if (!n) break;
      }
      c = c.square();
      n = Math.floor(n / 2);
    }
    return p;
  }

  private powMultinomial(n: number): PolyElement {
    const terms = this.listterms();
    const out: [Monom, Expr][] = [];
    for (const [ks, coeff] of multinomialCoefficients(terms.length, n)) {
      let monom: number[] = [...this.ring.zeroMonom];
      let c: Expr = Rational.of(coeff);
      ks.forEach((k, i) => {
        if (!k) return;
        const [e, a] = at(terms, i);
        monom = monom.map((x, j) => x + at(e, j) * Number(k));
        c = this.K.mul(c, groundPow(this.K, a, Number(k)));
      });
      out.push([monom, c]);
    }
    return this.ring.fromTerms(out);
  }

  /** f**2 (SymPy square). */
  square(): PolyElement {
    return this.mul(this);
  }

  /** The leading term division of SymPy _term_div: the quotient term, or undefined when it does not divide. */
  private termDiv(a: readonly [Monom, Expr], b: readonly [Monom, Expr]): [Monom, Expr] | undefined {
    const K = this.K;
    const monom = a[0].map((x, i) => x - at(b[0], i));
    if (monom.some((x) => x < 0)) return undefined;
    if (!K.isField && !groundIsZero(K, groundRem(K, a[1], b[1]))) return undefined;
    return [monom, groundQuo(K, a[1], b[1])];
  }

  /**
   * Division by a polynomial or a list of polynomials ([CLO] p. 64): the
   * quotients and the remainder with f = sum(q_i*g_i) + r (SymPy div).
   */
  div(fv: PolyElement): [PolyElement, PolyElement];
  div(fv: readonly PolyElement[]): [PolyElement[], PolyElement];
  div(fv: PolyElement | readonly PolyElement[]): [PolyElement | PolyElement[], PolyElement] {
    const single = fv instanceof PolyElement;
    const gs = single ? [fv] : [...fv];
    if (gs.some((g) => g.isZero)) throw new RangeError('polynomial division');
    for (const g of gs) if (!g.ring.equals(this.ring)) throw new RangeError('self and f must have the same ring');
    const qv = gs.map(() => this.ring.zero);
    let p: PolyElement = this;
    let r = this.ring.zero;
    const lts = gs.map((g) => g.LT);
    while (!p.isZero) {
      const lt = p.LT;
      let divided = false;
      for (let i = 0; i < gs.length && !divided; i++) {
        const t = this.termDiv(lt, at(lts, i));
        if (t) {
          qv[i] = at(qv, i).add(this.make([t]));
          p = p.sub(at(gs, i).mulTerm(t));
          divided = true;
        }
      }
      if (!divided) {
        r = r.add(this.make([lt]));
        p = p.sub(this.make([lt]));
      }
    }
    return single ? [at(qv, 0), r] : [qv, r];
  }

  /** The remainder of the division by one or more polynomials (SymPy rem). */
  rem(G: PolyElement | readonly PolyElement[]): PolyElement {
    return G instanceof PolyElement ? this.div(G)[1] : this.div(G)[1];
  }

  /** The quotient (SymPy quo). */
  quo(G: PolyElement | readonly PolyElement[]): PolyElement | PolyElement[] {
    return G instanceof PolyElement ? this.div(G)[0] : this.div(G)[0];
  }

  /** The exact quotient (SymPy exquo); ExactQuotientFailed when the remainder is not zero. */
  exquo(G: PolyElement): PolyElement {
    const [q, r] = this.div(G);
    if (!r.isZero) throw new ExactQuotientFailed(`${G.toString()} does not divide ${this.toString()}`);
    return q;
  }

  /** (f // g, f % g) for a polynomial or a ground value (SymPy divmod). */
  divmod(o: PolyElement | ExprLike): [PolyElement, PolyElement] {
    if (o instanceof PolyElement) return this.div(this.coerce(o));
    const c = this.ring.domainNew(o);
    return [this.quoGround(c), this.remGround(c)];
  }

  /** f // g (SymPy floordiv). */
  floordiv(o: PolyElement | ExprLike): PolyElement {
    return this.divmod(o)[0];
  }

  /** f % g (SymPy mod). */
  mod(o: PolyElement | ExprLike): PolyElement {
    return this.divmod(o)[1];
  }

  /** f / g: the exact quotient by a polynomial, the quotient by a ground value (SymPy truediv). */
  truediv(o: PolyElement | ExprLike): PolyElement {
    if (o instanceof PolyElement && !o.isGround) return this.exquo(this.coerce(o));
    const c = o instanceof PolyElement ? o.const() : this.ring.domainNew(o);
    if (groundIsZero(this.K, c)) throw new RangeError('polynomial division');
    return this.quoGround(c);
  }

  // ---- degrees and terms -----------------------------------------------------

  /** The degree in x (the first generator by default); -Infinity for zero (SymPy degree). */
  degree(x?: GenLike): number {
    const i = this.ring.index(x);
    if (this.isZero) return -Infinity;
    if (i < 0) return 0;
    return Math.max(...this.listmonoms().map((m) => at(m, i)));
  }

  /** The degrees in all generators (SymPy degrees). */
  degrees(): number[] {
    return this.ring.zeroMonom.map((_, i) => this.degree(i));
  }

  /** The tail degree in x (SymPy tail_degree). */
  tailDegree(x?: GenLike): number {
    const i = this.ring.index(x);
    if (this.isZero) return -Infinity;
    if (i < 0) return 0;
    return Math.min(...this.listmonoms().map((m) => at(m, i)));
  }

  /** The tail degrees in all generators (SymPy tail_degrees). */
  tailDegrees(): number[] {
    return this.ring.zeroMonom.map((_, i) => this.tailDegree(i));
  }

  private orderCmp(a: Monom, b: Monom): number {
    return this.ring.order.compare(a, b);
  }

  /** The leading exponent vector in the order of the ring; the zero vector for zero (SymPy leading_expv). */
  leadingExpv(): Monom {
    let best: Monom | undefined;
    for (const m of this.listmonoms()) if (best === undefined || this.orderCmp(m, best) > 0) best = m;
    return best ?? this.ring.zeroMonom;
  }

  /** The coefficient of a monomial (an element with one monomial term) or of 1 (SymPy coeff). */
  coeff(element: PolyElement | ExprLike): Expr {
    if (!(element instanceof PolyElement)) {
      if (sympify(element).key === Rational.of(1).key) return this.get(this.ring.zeroMonom);
      throw new RangeError(`expected a monomial, got ${str(sympify(element))}`);
    }
    if (this.ring.isElement(element) && element.length === 1) {
      const [m, c] = first(element.listterms());
      if (groundEq(c, this.K.one)) return this.get(m);
    }
    throw new RangeError(`expected a monomial, got ${element.toString()}`);
  }

  /** The constant coefficient (SymPy const). */
  const(): Expr {
    return this.get(this.ring.zeroMonom);
  }

  /** The leading coefficient (SymPy LC). */
  get LC(): Expr {
    return this.get(this.leadingExpv());
  }

  /** The leading exponent vector (SymPy LM). */
  get LM(): Monom {
    return this.leadingExpv();
  }

  /** The leading monomial as an element (SymPy leading_monom). */
  leadingMonom(): PolyElement {
    if (this.isZero) return this.ring.zero;
    return this.make([[this.leadingExpv(), this.K.one]]);
  }

  /** The leading term (exponent vector, coefficient) (SymPy LT). */
  get LT(): readonly [Monom, Expr] {
    const e = this.leadingExpv();
    return [e, this.get(e)];
  }

  /** The leading term as an element (SymPy leading_term). */
  leadingTerm(): PolyElement {
    return this.make([this.LT]);
  }

  /** The terms sorted by a monomial order, largest first (SymPy terms). */
  terms(order?: OrderLike): [Monom, Expr][] {
    const O = order === undefined ? this.ring.order : parseOrder(order);
    return this.listterms().sort((a, b) => O.compare(b[0], a[0]));
  }

  /** The coefficients sorted by a monomial order (SymPy coeffs). */
  coeffs(order?: OrderLike): Expr[] {
    return this.terms(order).map(([, c]) => c);
  }

  /** The exponent vectors sorted by a monomial order (SymPy monoms). */
  monoms(order?: OrderLike): Monom[] {
    return this.terms(order).map(([m]) => m);
  }

  /** The terms in no particular order (SymPy listterms). */
  listterms(): [Monom, Expr][] {
    return [...this.map.values()].map(([m, c]) => [m, c]);
  }

  /** The coefficients in no particular order (SymPy listcoeffs). */
  listcoeffs(): Expr[] {
    return [...this.map.values()].map(([, c]) => c);
  }

  /** The exponent vectors in no particular order (SymPy listmonoms). */
  listmonoms(): Monom[] {
    return [...this.map.values()].map(([m]) => m);
  }

  // ---- ground operations -----------------------------------------------------

  /** The gcd of the coefficients (SymPy content). */
  content(): Expr {
    const K = this.K;
    return this.listcoeffs().reduce((g, c) => groundGcd(K, g, c), K.zero);
  }

  /** The content and the primitive part (SymPy primitive). */
  primitive(): [Expr, PolyElement] {
    const c = this.content();
    if (groundIsZero(this.K, c)) return [c, this];
    return [c, this.quoGround(c)];
  }

  /** f divided by its leading coefficient (SymPy monic). */
  monic(): PolyElement {
    return this.isZero ? this : this.quoGround(this.LC);
  }

  /** c*f (SymPy mul_ground). */
  mulGround(x: ExprLike): PolyElement {
    const c = this.ring.domainNew(x);
    if (groundIsZero(this.K, c)) return this.ring.zero;
    return this.make(this.listterms().map(([m, a]) => [m, this.K.mul(a, c)] as const));
  }

  /** f*x**monom (SymPy mul_monom). */
  mulMonom(monom: Monom): PolyElement {
    return this.make(this.listterms().map(([m, c]) => [m.map((a, i) => a + at(monom, i)), c] as const));
  }

  /** f*c*x**monom (SymPy mul_term). */
  mulTerm(term: readonly [Monom, ExprLike]): PolyElement {
    const [monom, c0] = term;
    const c = this.ring.domainNew(c0);
    if (this.isZero || groundIsZero(this.K, c)) return this.ring.zero;
    return this.make(this.listterms().map(([m, a]) => [m.map((x, i) => x + at(monom, i)), this.K.mul(a, c)] as const));
  }

  /** The coefficients divided by x; over a ring, the terms with a remainder are dropped (SymPy quo_ground). */
  quoGround(x: ExprLike): PolyElement {
    const K = this.K;
    const c = this.ring.domainNew(x);
    if (groundIsZero(K, c)) throw new RangeError('polynomial division');
    if (this.isZero || groundEq(c, K.one)) return this;
    if (K.isField) return this.make(this.listterms().map(([m, a]) => [m, K.quo(a, c)] as const));
    return this.make(this.listterms().filter(([, a]) => groundIsZero(K, groundRem(K, a, c))).map(([m, a]) => [m, groundQuo(K, a, c)] as const));
  }

  /** f divided by c*x**monom, dropping the terms that do not divide (SymPy quo_term). */
  quoTerm(term: readonly [Monom, ExprLike]): PolyElement {
    const [monom, c0] = term;
    const c = this.ring.domainNew(c0);
    if (groundIsZero(this.K, c)) throw new RangeError('polynomial division');
    if (this.isZero) return this.ring.zero;
    if (monom.every((e) => e === 0)) return this.quoGround(c);
    const out: [Monom, Expr][] = [];
    for (const t of this.listterms()) {
      const q = this.termDiv(t, [monom, c]);
      if (q) out.push(q);
    }
    return this.make(out);
  }

  /** The coefficients modulo p, in the symmetric range over ZZ (SymPy trunc_ground). */
  truncGround(p: ExprLike): PolyElement {
    const K = this.K;
    const q = this.ring.domainNew(p);
    const half = groundQuo(K, q, Rational.of(2));
    return this.make(
      this.listterms().map(([m, c]) => {
        const r = groundRem(K, c, q);
        return [m, K instanceof IntegerRing && greater(r, half) ? K.sub(r, q) : r] as const;
      }),
    );
  }

  /** The coefficients modulo p (SymPy rem_ground, the same as trunc_ground). */
  remGround(p: ExprLike): PolyElement {
    return this.truncGround(p);
  }

  /** The gcd of the contents of f and g and both divided by it (SymPy extract_ground). */
  extractGround(g: PolyElement): [Expr, PolyElement, PolyElement] {
    const c = groundGcd(this.K, this.content(), g.content());
    return [c, this.quoGround(c), g.quoGround(c)];
  }

  /** The largest absolute value of a coefficient (SymPy max_norm). */
  maxNorm(): Expr {
    return this.ring.dupMaxNorm(this);
  }

  /** The sum of the absolute values of the coefficients (SymPy l1_norm). */
  l1Norm(): Expr {
    const K = this.K;
    return this.listcoeffs().reduce((s, c) => K.add(s, groundAbs(K, c)), K.zero);
  }

  /** The exponents divided by their gcds in each generator, for f and the given polynomials (SymPy deflate). */
  deflate(...G: PolyElement[]): [number[], PolyElement[]] {
    const polys = [this, ...G];
    const J = this.ring.zeroMonom.map(() => 0);
    for (const p of polys) for (const m of p.listmonoms()) m.forEach((e, i) => (J[i] = Number(igcd(BigInt(at(J, i)), BigInt(e)))));
    const K = J.map((b) => b || 1);
    if (K.every((b) => b === 1)) return [K, polys];
    return [K, polys.map((p) => p.make(p.listterms().map(([m, c]) => [m.map((e, i) => e / at(K, i)), c] as const)))];
  }

  /** The exponents multiplied by J (SymPy inflate). */
  inflate(J: readonly IntLike[]): PolyElement {
    const k = J.map((j) => intArg(j));
    return this.make(this.listterms().map(([m, c]) => [m.map((e, i) => e * at(k, i)), c] as const));
  }

  /** The lcm (SymPy lcm). */
  lcm(g: PolyElement): PolyElement {
    const K = this.K;
    let f: PolyElement = this;
    let h = g;
    let c: Expr = K.one;
    if (!K.isField) {
      let fc: Expr;
      let gc: Expr;
      [fc, f] = f.primitive();
      [gc, h] = h.primitive();
      c = groundLcm(K, fc, gc);
    }
    const l = f.mul(h).exquo(f.gcd(h));
    return K.isField ? l.monic() : l.mulGround(c);
  }

  /** The gcd (SymPy gcd). */
  gcd(g: PolyElement): PolyElement {
    return this.cofactors(g)[0];
  }

  /** The gcd and the cofactors f/gcd and g/gcd (SymPy cofactors). */
  cofactors(g: PolyElement): [PolyElement, PolyElement, PolyElement] {
    const R = this.ring;
    if (this.isZero && g.isZero) return [R.zero, R.zero, R.zero];
    if (this.isZero) return g.isNonnegative ? [g, R.zero, R.one] : [g.neg(), R.zero, R.one.neg()];
    if (g.isZero) return this.isNonnegative ? [this, R.one, R.zero] : [this.neg(), R.one.neg(), R.zero];
    if (this.length === 1) return this.gcdMonom(g);
    if (g.length === 1) {
      const [h, cfg, cff] = g.gcdMonom(this);
      return [h, cff, cfg];
    }
    const [J, fg] = this.deflate(g);
    const [h, cff, cfg] = R.dmpInnerGcd(at(fg, 0), at(fg, 1));
    return [h.inflate(J), cff.inflate(J), cfg.inflate(J)];
  }

  private gcdMonom(g: PolyElement): [PolyElement, PolyElement, PolyElement] {
    const K = this.K;
    const [mf, cf] = first(this.listterms());
    let mg0: number[] = [...mf];
    let cg0 = cf;
    for (const [m, c] of g.listterms()) {
      mg0 = mg0.map((e, i) => Math.min(e, at(m, i)));
      cg0 = groundGcd(K, cg0, c);
    }
    const h = this.make([[mg0, cg0]]);
    const cff = this.make([[mf.map((e, i) => e - at(mg0, i)), groundQuo(K, cf, cg0)]]);
    const cfg = this.make(g.listterms().map(([m, c]) => [m.map((e, i) => e - at(mg0, i)), groundQuo(K, c, cg0)] as const));
    return [h, cff, cfg];
  }

  /** f/g with the common factors cancelled: (p, q) with a canonical denominator (SymPy cancel). */
  cancel(g: PolyElement): [PolyElement, PolyElement] {
    const R = this.ring;
    const K = this.K;
    if (this.isZero) return [this, R.one];
    let p: PolyElement;
    let q: PolyElement;
    if (!(K.isField && hasAssocRing(K))) [, p, q] = this.cofactors(g);
    else {
      const ZR = R.clone({ domain: groundRing(K) });
      const [cq, f1] = this.clearDenoms();
      const [cp, g1] = g.clearDenoms();
      [, p, q] = f1.setRing(ZR).cofactors(g1.setRing(ZR));
      const c = groundGcd(ZZ, cp, cq);
      p = p.setRing(R).mulGround(groundQuo(ZZ, cp, c));
      q = q.setRing(R).mulGround(groundQuo(ZZ, cq, c));
    }
    const u = q.canonicalUnit();
    if (groundEq(u, K.one)) return [p, q];
    return [p.mulGround(u), q.mulGround(u)];
  }

  /** The canonical unit of the leading coefficient (SymPy canonical_unit). */
  canonicalUnit(): Expr {
    return canonicalUnit(this.K, this.LC);
  }

  /** The partial derivative in x (SymPy diff). */
  diff(x: GenLike): PolyElement {
    const i = this.ring.index(x);
    return this.make(
      this.listterms()
        .filter(([m]) => at(m, i) !== 0)
        .map(([m, c]) => [m.map((e, j) => (j === i ? e - 1 : e)), this.ring.domainNew(this.K.mul(c, Rational.of(at(m, i))))] as const),
    );
  }

  /** f evaluated at values for its first generators (SymPy __call__). */
  call(...values: ExprLike[]): PolyElement | Expr {
    if (!(values.length > 0 && values.length <= this.ring.ngens)) throw new RangeError(`expected at least 1 and at most ${this.ring.ngens} values, got ${values.length}`);
    return this.evaluate(values.map((v, i) => [at(this.ring.gens, i), v] as const));
  }

  /** f with x = a, in the ring without x; with a list of pairs, all of them in turn (SymPy evaluate). */
  evaluate(x: GenLike | readonly (readonly [GenLike, ExprLike])[], a?: ExprLike): PolyElement | Expr {
    if (isPairs(x)) {
      const pairs = x;
      if (!pairs.length) return this;
      const [X, v] = first(pairs);
      const rest = pairs.slice(1);
      const f = this.evaluate(X, v);
      if (!rest.length || !(f instanceof PolyElement)) return f;
      const ix = this.ring.index(X);
      // the remaining generators in the ring without X (SymPy Y.drop(X))
      return f.evaluate(rest.map(([Y, w]) => {
        const iy = this.ring.index(Y);
        return [iy > ix ? iy - 1 : iy, w] as const;
      }));
    }
    const i = this.ring.index(x);
    const K = this.K;
    const v = this.ring.domainNew(a ?? 0);
    if (this.ring.ngens === 1) return this.listterms().reduce((s, [m, c]) => K.add(s, K.mul(c, groundPow(K, v, first(m)))), K.zero);
    const R = this.ring.dropGen(i);
    return R.fromTerms(this.listterms().map(([m, c]) => [[...m.slice(0, i), ...m.slice(i + 1)], K.mul(c, groundPow(K, v, at(m, i)))] as const));
  }

  /** f with x = a, in the same ring; with a list of pairs, one after the other (SymPy subs). */
  subs(x: GenLike | readonly (readonly [GenLike, ExprLike])[], a?: ExprLike): PolyElement {
    if (isPairs(x)) {
      const pairs = x;
      return pairs.reduce<PolyElement>((f, [X, v]) => f.subs(X, v), this);
    }
    const i = this.ring.index(x);
    const K = this.K;
    const v = this.ring.domainNew(a ?? 0);
    return this.ring.fromTerms(this.listterms().map(([m, c]) => [m.map((e, j) => (j === i ? 0 : e)), K.mul(c, groundPow(K, v, at(m, i)))] as const));
  }

  /**
   * f in terms of the elementary symmetric polynomials (Lauer's algorithm):
   * (p, r, m) with p.compose(m) + r == f, r the part that is not symmetric
   * (SymPy symmetrize).
   */
  symmetrize(): [PolyElement, PolyElement, [PolyElement, PolyElement][]] {
    const R = this.ring;
    const n = R.ngens;
    let f: PolyElement = this;
    if (!n) return [f, R.zero, []];
    const polys = Array.from({ length: n }, (_, i) => R.symmetricPoly(i + 1));
    const weights = Array.from({ length: n }, (_, i) => n - i);
    let symmetric = R.zero;
    while (!f.isZero) {
      let height = -1;
      let best: [Monom, Expr] | undefined;
      for (const [monom, coeff] of f.terms()) {
        if (monom.every((e, i) => i === n - 1 || e >= at(monom, i + 1))) {
          const h = Math.max(...monom.map((e, i) => at(weights, i) * e));
          if (h > height) {
            height = h;
            best = [monom, coeff];
          }
        }
      }
      if (best === undefined) break;
      const [monom, coeff] = best;
      const exps = monom.map((e, i) => e - (monom[i + 1] ?? 0));
      symmetric = symmetric.add(R.termNew(exps, coeff));
      let product = R.groundNew(coeff);
      exps.forEach((e, i) => (product = product.mul(at(polys, i).pow(e))));
      f = f.sub(product);
    }
    return [symmetric, f, R.gens.map((g, i) => [g, at(polys, i)] as [PolyElement, PolyElement])];
  }

  /** f with generators replaced by polynomials, all at once (SymPy compose). */
  compose(x: GenLike | readonly (readonly [GenLike, PolyElement | ExprLike])[] | ReadonlyMap<PolyElement, PolyElement | ExprLike>, a?: PolyElement | ExprLike): PolyElement {
    const R = this.ring;
    let reps: (readonly [GenLike, PolyElement | ExprLike])[];
    if (isPairs<PolyElement | ExprLike>(x)) reps = [...x];
    else if (isMapArg(x)) reps = [...x].sort((p, q) => R.index(p[0]) - R.index(q[0]));
    else if (a !== undefined) reps = [[x, a]];
    else throw new RangeError('expected a generator, value pair a sequence of such pairs');
    const subs = reps.map(([g, v]) => [R.index(g), R.ringNew(v)] as const);
    let poly = R.zero;
    for (const [m0, c] of this.listterms()) {
      const m = [...m0];
      let sub = R.one;
      for (const [i, g] of subs) {
        const n = at(m, i);
        m[i] = 0;
        if (n) sub = sub.mul(g.pow(n));
      }
      poly = poly.add(sub.mulTerm([m, c]));
    }
    return poly;
  }

  /** The coefficient of x**deg as a polynomial in the other generators (SymPy coeff_wrt). */
  coeffWrt(x: GenLike, deg: IntLike): PolyElement {
    const i = this.ring.index(x);
    const d = intArg(deg);
    return this.make(this.listterms().filter(([m]) => at(m, i) === d).map(([m, c]) => [m.map((e, j) => (j === i ? 0 : e)), c] as const));
  }

  /** The pseudo-remainder with respect to x (the first generator by default) (SymPy prem). */
  prem(g: PolyElement, x?: GenLike): PolyElement {
    return this.pdivWith(g, x, false)[1];
  }

  /**
   * Pseudo-division with respect to x: (q, r) with LC(g, x)**(deg(f, x) -
   * deg(g, x) + 1)*f = g*q + r (SymPy pdiv).
   */
  pdiv(g: PolyElement, x?: GenLike): [PolyElement, PolyElement] {
    return this.pdivWith(g, x, true);
  }

  private pdivWith(g: PolyElement, x0: GenLike | undefined, quotient: boolean): [PolyElement, PolyElement] {
    const x = this.ring.index(x0);
    const df = this.degree(x);
    const dg = g.degree(x);
    if (dg < 0) throw new RangeError('polynomial division');
    let q = this.ring.zero;
    let r: PolyElement = this;
    let dr = df;
    if (df < dg) return [q, r];
    let N = df - dg + 1;
    const lcG = g.coeffWrt(x, dg);
    const xp = at(this.ring.gens, x);
    for (;;) {
      const lcR = r.coeffWrt(x, dr);
      const j = dr - dg;
      N -= 1;
      if (quotient) q = q.mul(lcG).add(lcR.mul(xp.pow(j)));
      r = r.mul(lcG).sub(g.mul(lcR).mul(xp.pow(j)));
      dr = r.degree(x);
      if (dr < dg) break;
    }
    const c = lcG.pow(N);
    return [q.mul(c), r.mul(c)];
  }

  /** The pseudo-quotient (SymPy pquo). */
  pquo(g: PolyElement, x?: GenLike): PolyElement {
    return this.pdiv(g, x)[0];
  }

  /** The exact pseudo-quotient; ExactQuotientFailed when the pseudo-remainder is not zero (SymPy pexquo). */
  pexquo(g: PolyElement, x?: GenLike): PolyElement {
    const [q, r] = this.pdiv(g, x);
    if (!r.isZero) throw new ExactQuotientFailed(`${g.toString()} does not divide ${this.toString()}`);
    return q;
  }

  /** The subresultant PRS with respect to x (SymPy subresultants). */
  subresultants(g0: PolyElement, x0?: GenLike): (PolyElement | number)[] {
    const x = this.ring.index(x0);
    let f: PolyElement = this;
    let g = g0;
    let n = f.degree(x);
    let m = g.degree(x);
    if (n < m) {
      [f, g] = [g, f];
      [n, m] = [m, n];
    }
    if (f.isZero) return [0, 0];
    if (g.isZero) return [f, 1];
    const R: PolyElement[] = [f, g];
    let d = n - m;
    let h = f.prem(g, x).mulGround((d + 1) % 2 ? -1 : 1);
    let lc = g.coeffWrt(x, m);
    let c = lc.pow(d).neg();
    while (!h.isZero) {
      const k = h.degree(x);
      R.push(h);
      [f, g, d] = [g, h, m - k];
      m = k;
      const b = lc.neg().mul(c.pow(d));
      h = f.prem(g, x).exquo(b);
      lc = g.coeffWrt(x, k);
      c = d > 1 ? lc.neg().pow(d).exquo(c.pow(d - 1)) : lc.neg();
    }
    return R;
  }

  /** The half extended Euclidean algorithm (SymPy half_gcdex). */
  halfGcdex(g: PolyElement): [PolyElement, PolyElement] {
    return this.ring.dupHalfGcdex(this, g);
  }
  /** The extended Euclidean algorithm (SymPy gcdex). */
  gcdex(g: PolyElement): [PolyElement, PolyElement, PolyElement] {
    return this.ring.dupGcdex(this, g);
  }
  /** The resultant (SymPy resultant). */
  resultant(g: PolyElement): PolyElement | Expr {
    return this.ring.dmpResultant(this, g);
  }
  /** The discriminant (SymPy discriminant). */
  discriminant(): PolyElement | Expr {
    return this.ring.dmpDiscriminant(this);
  }
  /** A functional decomposition (SymPy decompose). */
  decompose(): PolyElement[] {
    if (!this.ring.isUnivariate) throw new MultivariatePolynomialError('polynomial decomposition');
    return this.ring.dupDecompose(this);
  }
  /** f(x + a) (SymPy shift). */
  shift(a: ExprLike): PolyElement {
    if (!this.ring.isUnivariate) throw new MultivariatePolynomialError('shift: use shift_list instead');
    return this.ring.dupShift(this, a);
  }
  /** f(x_0 + a_0, ...) (SymPy shift_list). */
  shiftList(a: readonly ExprLike[]): PolyElement {
    return this.ring.dmpShift(this, a);
  }
  /** The Sturm sequence (SymPy sturm). */
  sturm(): PolyElement[] {
    if (!this.ring.isUnivariate) throw new MultivariatePolynomialError('sturm sequence');
    return this.ring.dupSturm(this);
  }
  /** The greatest factorial factorization (SymPy gff_list). */
  gffList(): [PolyElement, number][] {
    return this.ring.dmpGffList(this);
  }
  /** The square-free part (SymPy sqf_part). */
  sqfPart(): PolyElement {
    return this.ring.dmpSqfPart(this);
  }
  /** The square-free decomposition (SymPy sqf_list). */
  sqfList(all = false): [Expr, [PolyElement, number][]] {
    return this.ring.dmpSqfList(this, all);
  }
  /** The factorization (SymPy factor_list). */
  factorList(): [Expr, [PolyElement, number][]] {
    return this.ring.dmpFactorList(this);
  }
}

/** a > b for rationals. */
const greater = (a: Expr, b: Expr): boolean => a instanceof Rational && b instanceof Rational && a.p * b.q > b.p * a.q;

/**
 * A polynomial ring and its generators: [R, x_1, ..., x_n] (SymPy ring).
 *
 * @example
 * const [R, x, y] = ring('x,y', ZZ);
 * x.add(y).pow(2).toString(); // 'x**2 + 2*x*y + y**2'
 */
export function ring(symbols: RingSymbols, domain: DomainLike = ZZ, order: OrderLike = lex): [PolyRing, ...PolyElement[]] {
  const R = new PolyRing(symbols, domain, order);
  return [R, ...R.gens];
}

/** A polynomial ring and the list of its generators: [R, [x_1, ..., x_n]] (SymPy xring). */
export function xring(symbols: RingSymbols, domain: DomainLike = ZZ, order: OrderLike = lex): [PolyRing, PolyElement[]] {
  const R = new PolyRing(symbols, domain, order);
  return [R, [...R.gens]];
}

/**
 * A polynomial ring (SymPy vring). SymPy also binds the generators in the
 * caller's namespace; JavaScript has none, so they are `R.gens`.
 */
export function vring(symbols: RingSymbols, domain: DomainLike = ZZ, order: OrderLike = lex): PolyRing {
  return new PolyRing(symbols, domain, order);
}

/** Options of sring. */
export interface SringOptions {
  domain?: DomainLike;
  order?: OrderLike;
}

/**
 * A ring for expressions with the generators and the domain derived from
 * them, and the expressions as its elements (SymPy sring): [R, f] for one
 * expression, [R, [f_1, ...]] for a list.
 */
export function sring(exprs: ExprLike, ...rest: (Expr | SringOptions)[]): [PolyRing, PolyElement];
export function sring(exprs: readonly ExprLike[], ...rest: (Expr | SringOptions)[]): [PolyRing, PolyElement[]];
export function sring(exprs: ExprLike | readonly ExprLike[], ...rest: (Expr | SringOptions)[]): [PolyRing, PolyElement | PolyElement[]] {
  const single = !isExprList(exprs);
  const es = (isExprList(exprs) ? [...exprs] : [exprs]).map((e) => expand(sympify(e)));
  const opts: SringOptions = rest.find((r): r is SringOptions => !(r instanceof Expr)) ?? {};
  let gens: Expr[] = rest.filter((r): r is Expr => r instanceof Expr);
  if (!gens.length) {
    const all = new Map<string, Expr>();
    for (const e of es) for (const g of Poly.from(e).gens) all.set(g.key, g);
    gens = sortGens([...all.values()]);
  }
  const polys = es.map((e) => Poly.from(e, gens, opts.domain === undefined ? {} : { domain: String(opts.domain) }));
  const coeffs = polys.flatMap((p) => p.coeffs());
  const domain = opts.domain ?? inferDomain(coeffs);
  const R = new PolyRing(gens, domain, opts.order ?? lex);
  const elems = polys.map((p) => R.fromTerms(p.isZero ? [] : p.terms().map(([m, c]) => [m, R.domainNew(c)] as const)));
  return [R, single ? first(elems) : elems];
}

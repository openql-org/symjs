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
import { at, cast, defined, first } from '../core/guard';
import type { FracField } from './fields';
import type { ExprLike } from '../core/nodes';
import { Add, Constant, Expr, Mul, Pow, Rational, Sym } from '../core/nodes';
import { expandSymbolNames } from '../core/numberutils';
import { add, mul, pow, sympify } from '../core/ops';
import { gcd as igcd } from '../core/numbers';
import { multinomialCoefficients } from '../ntheory/multinomial';
import type { IntLike } from '../ntheory/intutil';
import { PREC, str } from '../printing/str';
import { expand } from '../simplify/expand';
import { fraction, together } from '../simplify/rational';
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
import { AlgebraicField } from './domains/algebraicfield';
import { constructDomain } from './constructor';
import type { MonomialOrdering } from './orderings';
import { grevlex, grlex, igrevlex, igrlex, ilex, lex } from './orderings';
import { GeneratorsError, MultivariatePolynomialError } from './polyerrors';
import { Poly, sortGens } from './sympoly';

export type { Monom } from './compatibility';

/** The fraction-field constructor is registered by polys/fields to avoid an import cycle. @internal */
export const ringHooks: { toField?: (ring: PolyRing) => FracField } = {};

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
  if (Array.isArray(symbols)) {
    if (symbols.every((s) => typeof s === 'string')) return symbols.flatMap((s) => expandSymbolNames(s).map((n) => new Sym(n)));
    if (symbols.every((s) => s instanceof Expr)) return [...symbols];
  }
  throw new GeneratorsError('expected a string, Symbol or expression or a non-empty sequence of strings, Symbols or expressions');
}

/** The ring of a field with an associated ring (SymPy get_ring when has_assoc_Ring): ZZ for QQ, ZZ[X] for ZZ(X); fraction fields over other grounds are not handled. */
function assocRing(K: Domain): Domain | undefined {
  if (K instanceof FractionField) return K.ground === 'ZZ' ? K.getRing() : undefined;
  return K.isField && hasAssocRing(K) ? groundRing(K) : undefined;
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
 * A multivariate polynomial ring K[x_1, ..., x_n] with sparse elements. Rings with the same generators, domain and order are
 * equal.
 *
 * @see SymPy `sympy.polys.rings.PolyRing`
 */
export class PolyRing extends IPolys<PolyElement> {
  /**
   * The symbols naming the generators, in order.
   *
   * @see SymPy `sympy.polys.rings.PolyRing.symbols`
   */
  readonly symbols: readonly Expr[];
  /**
   * The number of generators.
   *
   * @see SymPy `sympy.polys.rings.PolyRing.ngens`
   */
  readonly ngens: number;
  /**
   * The coefficient domain.
   *
   * @see SymPy `sympy.polys.rings.PolyRing.domain`
   */
  readonly domain: Domain;
  /**
   * The monomial order.
   *
   * @see SymPy `sympy.polys.rings.PolyRing.order`
   */
  readonly order: MonomialOrdering;
  /**
   * The all-zero exponent vector.
   *
   * @see SymPy `sympy.polys.rings.PolyRing.zero_monom`
   */
  readonly zeroMonom: Monom;
  /**
   * The ordered generators.
   *
   * @see SymPy `sympy.polys.rings.PolyRing.gens`
   */
  readonly gens: readonly PolyElement[];
  /** The identity of the ring (generators, domain and order). */
  readonly key: string;

  /**
   * Construct a polynomial ring.
   *
   * @param symbols - Symbols naming the generators, in order.
   * @param domain - Coefficient domain.
   * @param order - Monomial order used to compare terms.
   * @throws GeneratorsError when a generator also belongs to the coefficient domain.
   */
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

  /**
   * Formats this object as text.
   *
   * @returns The formatted text.
   * @see SymPy `sympy.polys.rings.PolyRing.__str__`
   */
  toString(): string {
    return `Polynomial ring in ${this.symbols.map((s) => str(s)).join(', ')} over ${this.domain.toString()} with ${this.order.toString()} order`;
  }

  /**
   * Checks whether two rings have the same generators, domain, and monomial order.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns Whether the comparison holds.
   * @see SymPy `sympy.polys.rings.PolyRing.__eq__`
   */
  equals(other: unknown): boolean {
    return other instanceof PolyRing && other.key === this.key;
  }

  /**
   * Copies the ring with the requested generators, coefficient domain, or ordering.
   *
   * @param opts - Controls `symbols` (replacement generator symbols), `domain` (the coefficient domain), `order` (the monomial order).
   * @returns The resulting ring.
   * @see SymPy `sympy.polys.rings.PolyRing.clone`
   */
  clone(opts: { symbols?: RingSymbols; domain?: DomainLike; order?: OrderLike } = {}): PolyRing {
    return new PolyRing(opts.symbols ?? this.symbols, opts.domain ?? this.domain, opts.order ?? this.order);
  }

  /**
   * Forms the rational function field with this ring's generators and coefficient domain.
   *
   * @returns The associated fraction field.
   * @see SymPy `sympy.polys.rings.PolyRing.to_field`
   */
  toField(): FracField {
    return defined(ringHooks.toField, 'fraction field module')(this);
  }

  /**
   * Constructs the unit exponent vector for the chosen generator.
   *
   * @param i - Zero-based index.
   * @returns The generator monomial.
   * @see SymPy `sympy.polys.rings.PolyRing.monomial_basis`
   */
  monomialBasis(i: IntLike): number[] {
    const m = new Array<number>(this.ngens).fill(0);
    m[intArg(i)] = 1;
    return m;
  }

  /**
   * Represents zero in this ring.
   *
   * @returns The additive identity.
   * @see SymPy `sympy.polys.rings.PolyRing.zero`
   */
  get zero(): PolyElement {
    return new PolyElement(this, []);
  }

  /**
   * Represents one in this ring.
   *
   * @returns The multiplicative identity.
   * @see SymPy `sympy.polys.rings.PolyRing.one`
   */
  get one(): PolyElement {
    return new PolyElement(this, [[this.zeroMonom, this.domain.one]]);
  }

  /**
   * Tests whether the value belongs to this ring.
   *
   * @param e - Expression to convert.
   * @returns Whether the operand belongs to this ring or field.
   * @see SymPy `sympy.polys.rings.PolyRing.is_element`
   */
  isElement(e: unknown): boolean {
    return e instanceof PolyElement && e.ring.key === this.key;
  }

  /**
   * Converts the input to the ring's ground domain.
   *
   * @param element - Value to coerce into the domain.
   * @returns The ground element.
   * @throws CoercionFailed when the value cannot be represented in the target domain.
   * @see SymPy `sympy.polys.rings.PolyRing.domain_new`
   */
  domainNew(element: ExprLike | PolyElement): Expr {
    if (element instanceof PolyElement) {
      if (element.isGround) return element.const();
      throw new CoercionFailed(`cannot convert ${element.toString()} to ${this.domain.toString()}`);
    }
    return groundConvert(this.domain, element);
  }

  /**
   * Constructs a constant polynomial from the ground coefficient.
   *
   * @param coeff - Coefficient of the term.
   * @returns The corresponding constant element.
   * @see SymPy `sympy.polys.rings.PolyRing.ground_new`
   */
  groundNew(coeff: ExprLike | PolyElement): PolyElement {
    return this.termNew(this.zeroMonom, coeff);
  }

  /**
   * Builds a polynomial term from a coefficient and an exponent vector.
   *
   * @param monom - Exponent vector of the monomial.
   * @param coeff - Coefficient of the term.
   * @returns The single-term polynomial.
   * @see SymPy `sympy.polys.rings.PolyRing.term_new`
   */
  termNew(monom: Monom, coeff: ExprLike | PolyElement): PolyElement {
    const c = this.domainNew(coeff);
    return new PolyElement(this, groundIsZero(this.domain, c) ? [] : [[monom, c]]);
  }

  /**
   * Constructs a ring element from a polynomial, term collection, dense list, expression, or ground
   * value.
   *
   * @param element - Value to coerce into the domain.
   * @returns The polynomial in this ring.
   * @throws NotImplementedError when the source representation cannot be converted to this ring or the requested input syntax is unsupported.
   * @throws TypeError when the input is not a polynomial, term map, coefficient list or expression.
   * @see SymPy `sympy.polys.rings.PolyRing.ring_new`
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

  /**
   * Builds a polynomial from an exponent-vector-to-coefficient map.
   *
   * @param element - Value to coerce into the domain.
   * @returns The ring element.
   * @see SymPy `sympy.polys.rings.PolyRing.from_dict`
   */
  fromDict(element: ReadonlyMap<Monom, ExprLike> | Iterable<readonly [Monom, ExprLike]>): PolyElement {
    return this.fromTerms(element instanceof Map ? [...element] : element);
  }

  /**
   * Builds the polynomial from term pairs, adding coefficients for repeated monomials.
   *
   * @param terms - Monomial and coefficient pairs.
   * @returns An element from (exponent vector, coefficient) pairs.
   * @throws PolynomialError when the exponent vector has the wrong length.
   * @see SymPy `sympy.polys.rings.PolyRing.from_terms`
   */
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

  /**
   * Converts a recursive dense coefficient list in descending degree order to a ring element.
   *
   * @param element - Value to coerce into the domain.
   * @returns The polynomial.
   * @throws PolynomialError when the coefficient list depth differs from the number of generators.
   * @see SymPy `sympy.polys.rings.PolyRing.from_list`
   */
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

  /**
   * Converts an expression in the ring's generators to polynomial form.
   *
   * @param expr - Expression to convert.
   * @returns The ring element.
   * @throws RangeError when the expression is not polynomial in the specified ring.
   * @see SymPy `sympy.polys.rings.PolyRing.from_expr`
   */
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

  /**
   * Locates a generator by element, position, or name, defaulting to the first generator.
   *
   * @param gen - Generator or its index.
   * @returns The generator index, or −1 for an empty ring when omitted.
   * @throws RangeError when the specified generator or index is invalid.
   * @see SymPy `sympy.polys.rings.PolyRing.index`
   */
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

  /**
   * Removes the specified generators from the ring.
   *
   * @param gens - Polynomial generators in the desired order.
   * @returns The reduced ring or the ground domain if empty.
   * @see SymPy `sympy.polys.rings.PolyRing.drop`
   */
  drop(...gens: (PolyElement | IntLike | string)[]): PolyRing | Domain {
    const idx = new Set(gens.map((g) => this.index(g)));
    const symbols = this.symbols.filter((_, i) => !idx.has(i));
    return symbols.length ? this.clone({ symbols }) : this.domain;
  }

  /**
   * Selects a slice of the ordered generators.
   *
   * @param start - Inclusive starting index.
   * @param end - Exclusive ending index.
   * @returns The resulting ring or the ground domain if empty.
   */
  slice(start: number, end?: number): PolyRing | Domain {
    const symbols = this.symbols.slice(start, end);
    return symbols.length ? this.clone({ symbols }) : this.domain;
  }

  /**
   * Replaces a composite coefficient domain by its own ground domain.
   *
   * @returns The ring over the ground domain.
   * @throws PolynomialError when the coefficient domain is not composite.
   * @see SymPy `sympy.polys.rings.PolyRing.to_ground`
   */
  toGround(): PolyRing {
    const K = this.domain;
    if (K instanceof AlgebraicField) return this.clone({ domain: K.dom });
    if (K instanceof PolynomialDomain || K instanceof FractionField) return this.clone({ domain: groundOfSymbolic(K) });
    throw new PolynomialError(`${K.toString()} is not a composite domain`);
  }

  /**
   * Checks whether there is exactly one generator.
   *
   * @returns True for a univariate ring.
   * @see SymPy `sympy.polys.rings.PolyRing.is_univariate`
   */
  get isUnivariate(): boolean {
    return this.ngens === 1;
  }

  /**
   * Checks whether there are at least two generators.
   *
   * @returns True for a multivariate ring.
   * @see SymPy `sympy.polys.rings.PolyRing.is_multivariate`
   */
  get isMultivariate(): boolean {
    return this.ngens > 1;
  }

  /**
   * Adds the polynomials in the supplied operands, including nested sequences.
   *
   * @param objs - Objects whose rings are to be unified.
   * @returns Their sum.
   * @see SymPy `sympy.polys.rings.PolyRing.add`
   */
  add(...objs: (PolyElement | ExprLike | Iterable<PolyElement | ExprLike>)[]): PolyElement {
    let p = this.zero;
    for (const o of objs) p = isIterable(o) ? p.add(this.add(...o)) : p.add(o);
    return p;
  }

  /**
   * Multiplies the polynomials in the supplied operands, including nested sequences.
   *
   * @param objs - Objects whose rings are to be unified.
   * @returns Their product.
   * @see SymPy `sympy.polys.rings.PolyRing.mul`
   */
  mul(...objs: (PolyElement | ExprLike | Iterable<PolyElement | ExprLike>)[]): PolyElement {
    let p = this.one;
    for (const o of objs) p = isIterable(o) ? p.mul(this.mul(...o)) : p.mul(o);
    return p;
  }

  /**
   * Moves the specified generators from the ring to the coefficient domain.
   *
   * @param gens - Polynomial generators in the desired order.
   * @returns The ring in the remaining generators.
   * @see SymPy `sympy.polys.rings.PolyRing.drop_to_ground`
   */
  dropToGround(...gens: (PolyElement | IntLike | string)[]): PolyRing {
    const idx = new Set(gens.map((g) => this.index(g)));
    const symbols = this.symbols.filter((_, i) => !idx.has(i));
    if (!symbols.length) return this;
    const dropped = this.symbols.filter((_, i) => idx.has(i));
    return this.clone({ symbols, domain: this.domain.polyRing(...dropped.map(asSym)) });
  }

  /**
   * Combines the generators of two polynomial rings.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns The composite ring.
   * @see SymPy `sympy.polys.rings.PolyRing.compose`
   */
  compose(other: PolyRing): PolyRing {
    if (this.equals(other)) return this;
    return this.addGens(other.symbols);
  }

  /**
   * Adjoins the supplied symbols and sorts the combined generator set.
   *
   * @param symbols - Symbols naming the generators, in order.
   * @returns The extended ring.
   * @see SymPy `sympy.polys.rings.PolyRing.add_gens`
   */
  addGens(symbols: readonly Expr[]): PolyRing {
    const all = new Map<string, Expr>();
    for (const s of [...this.symbols, ...symbols]) all.set(s.key, s);
    return this.clone({ symbols: sortGens([...all.values()]) });
  }

  /**
   * Sums all square-free products of `n` distinct generators.
   *
   * @param n - Order of the elementary symmetric polynomial.
   * @returns The elementary symmetric polynomial.
   * @throws RangeError when the requested order is outside the range allowed by the number of generators.
   * @see SymPy `sympy.polys.rings.PolyRing.symmetric_poly`
   */
  symmetricPoly(n: IntLike): PolyElement {
    const k = intArg(n);
    if (k < 0 || k > this.ngens) throw new RangeError(`Cannot generate symmetric polynomial of order ${k} for ${this.gens.map(String).join(', ')}`);
    if (!k) return this.one;
    let poly = this.zero;
    for (const s of subsetsOf(this.ngens, k)) poly = poly.add(this.termNew(this.zeroMonom.map((_, i) => (s.includes(i) ? 1 : 0)), this.domain.one));
    return poly;
  }

  /**
   * Removes the generator at the specified position from a multivariate ring.
   *
   * @param i - Zero-based index.
   * @returns The reduced polynomial ring.
   */
  dropGen(i: number): PolyRing {
    return this.clone({ symbols: this.symbols.filter((_, j) => j !== i) });
  }

  // ---- IPolys plumbing -----------------------------------------------------

  /**
   * Rebuilds the ring over a different coefficient domain while retaining the generators.
   *
   * @param K - Coefficient domain for the polynomial arithmetic.
   * @returns The converted ring.
   * @see SymPy `sympy.polys.rings.PolyRing.clone`
   */
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
 * An element of a polynomial ring: a map from
 * exponent vectors to nonzero coefficients of the ground domain. Elements are
 * immutable.
 *
 * @see SymPy `sympy.polys.rings.PolyElement`
 */
export class PolyElement {
  /**
   * The polynomial ring to which the elements belong.
   *
   * @see SymPy `sympy.polys.rings.PolyElement.ring`
   */
  readonly ring: PolyRing;
  private map: ReadonlyMap<string, readonly [Monom, Expr]>;

  /**
   * Construct a sparse polynomial in the specified ring.
   *
   * @param ring - Polynomial ring supplying the generators and coefficient domain.
   * @param terms - Monomial and coefficient pairs.
   */
  constructor(ring: PolyRing, terms: Iterable<readonly [Monom, Expr]>) {
    this.ring = ring;
    const m = new Map<string, readonly [Monom, Expr]>();
    for (const [e, c] of terms) if (!groundIsZero(ring.domain, c)) m.set(mkey(e), [e, c]);
    this.map = m;
  }

  private get K(): Domain {
    return this.ring.domain;
  }

  /**
   * Represents the element's parent ring as a coefficient domain.
   *
   * @returns The polynomial-ring domain.
   * @see SymPy `sympy.polys.rings.PolyElement.parent`
   */
  parent(): Domain {
    return this.ring.domain.polyRing(...this.ring.symbols.map((s) => cast(s, Sym)));
  }

  private make(terms: Iterable<readonly [Monom, Expr]>): PolyElement {
    return new PolyElement(this.ring, terms);
  }

  /**
   * Counts the polynomial's nonzero terms.
   *
   * @returns The term count.
   */
  get length(): number {
    return this.map.size;
  }

  /**
   * Reads the coefficient associated with an exponent vector.
   *
   * @param monom - Exponent vector of the monomial.
   * @returns The coefficient or zero.
   * @see SymPy `sympy.polys.rings.PolyElement.get`
   */
  get(monom: Monom): Expr {
    return this.map.get(mkey(monom))?.[1] ?? this.K.zero;
  }

  /**
   * Indexes the polynomial coefficients by exponent vector.
   *
   * @returns The term map.
   * @see SymPy `sympy.polys.rings.PolyElement.to_dict`
   */
  toDict(): Map<Monom, Expr> {
    return new Map(this.listterms());
  }

  /**
   * Rewrites the polynomial in a ring with compatible or reordered generators.
   *
   * @param newRing - Target polynomial ring.
   * @returns The converted element.
   * @throws GeneratorsError when the polynomial depends on a generator that would be removed.
   * @see SymPy `sympy.polys.rings.PolyElement.set_ring`
   */
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

  /**
   * Expresses the polynomial in its generators or the supplied symbols.
   *
   * @param symbols - Symbols naming the generators, in order.
   * @returns The symbolic expression.
   * @throws RangeError when the number of replacement symbols differs from the number of generators.
   * @see SymPy `sympy.polys.rings.PolyElement.as_expr`
   */
  asExpr(...symbols: Expr[]): Expr {
    const syms = symbols.length ? symbols : this.ring.symbols;
    if (syms.length !== this.ring.ngens) throw new RangeError(`Wrong number of symbols, expected ${this.ring.ngens} got ${syms.length}`);
    return add(...this.terms().map(([m, c]) => mul(this.K.toSympy(c), ...m.map((k, i) => pow(at(syms, i), k)))));
  }

  /**
   * Clears the denominators of all polynomial coefficients.
   *
   * @returns The common denominator and scaled polynomial.
   * @see SymPy `sympy.polys.rings.PolyElement.clear_denoms`
   */
  clearDenoms(): [Expr, PolyElement] {
    const K = this.K;
    const R = assocRing(K);
    if (R === undefined) return [K.one, this];
    let common: Expr = R.one;
    for (const [, c] of this.listterms()) common = groundLcm(R, common, K instanceof FractionField ? R.fromSympy(fraction(together(c))[1]) : groundDenom(c));
    return [common, this.mulGround(common)];
  }

  /**
   * Tests equality with another polynomial in the ring or with a ground value.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns Whether the comparison holds.
   * @see SymPy `sympy.polys.rings.PolyElement.__eq__`
   */
  equals(other: unknown): boolean {
    if (other instanceof PolyElement) {
      if (!this.ring.isElement(other)) {
        const containsRing = (a: PolyElement, b: PolyElement): boolean => a.K instanceof PolynomialDomain && a.K.dom.equals(b.K)
          && a.K.gens.length === b.ring.ngens && a.K.gens.every((s, i) => s.key === at(b.ring.symbols, i).key);
        if (this.isGround && containsRing(this, other)) return groundEq(this.const(), other.asExpr());
        if (other.isGround && containsRing(other, this)) return groundEq(other.const(), this.asExpr());
        return this.isZero && other.isZero;
      }
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

  /**
   * Drops an unused generator from the polynomial's ring.
   *
   * @param gen - Generator or its index.
   * @returns The polynomial in the remaining generators or its ground value.
   * @throws RangeError when the polynomial depends on a generator that would be removed.
   * @see SymPy `sympy.polys.rings.PolyElement.drop`
   */
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

  /**
   * Moves a generator of the polynomial into the ground domain.
   *
   * @param gen - Generator or its index.
   * @returns The polynomial with the new coefficient domain.
   * @throws RangeError when the only generator would be removed.
   * @see SymPy `sympy.polys.rings.PolyElement.drop_to_ground`
   */
  dropToGround(gen: GenLike): PolyElement {
    if (this.ring.ngens === 1) throw new RangeError('Cannot drop only generator to ground');
    const i = this.ring.index(gen);
    const R = this.ring.dropToGround(i);
    const g = at(this.ring.symbols, i);
    return R.fromTerms(this.listterms().map(([m, c]) => [[...m.slice(0, i), ...m.slice(i + 1)], R.domain.fromSympy(mul(this.K.toSympy(c), pow(g, at(m, i))))] as const));
  }

  /**
   * Expands the sparse term representation into recursive coefficient lists.
   *
   * @returns The dense polynomial.
   * @see SymPy `sympy.polys.rings.PolyElement.to_dense`
   */
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

  /**
   * Formats this object as text.
   *
   * @returns The formatted text.
   * @see SymPy `sympy.polys.rings.PolyElement.__str__`
   */
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
        const sym = s0 instanceof Sym || s0 instanceof Constant ? str(s0) : `(${str(s0)})`;
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

  /**
   * Tests whether the element is one of the ring's generators.
   *
   * @returns True for a generator.
   * @see SymPy `sympy.polys.rings.PolyElement.is_generator`
   */
  get isGenerator(): boolean {
    return this.ring.gens.some((g) => g.equals(this));
  }
  /**
   * Checks that the polynomial is independent of its generators.
   *
   * @returns True for a ground element.
   * @see SymPy `sympy.polys.rings.PolyElement.is_ground`
   */
  get isGround(): boolean {
    return this.isZero || (this.length === 1 && this.map.has(mkey(this.ring.zeroMonom)));
  }
  /**
   * Checks for zero or a single term with coefficient one.
   *
   * @returns The monomial flag.
   * @see SymPy `sympy.polys.rings.PolyElement.is_monomial`
   */
  get isMonomial(): boolean {
    return this.isZero || (this.length === 1 && groundEq(this.LC, this.K.one));
  }
  /**
   * Tests whether the polynomial has at most one nonzero term.
   *
   * @returns True for zero or a single term.
   * @see SymPy `sympy.polys.rings.PolyElement.is_term`
   */
  get isTerm(): boolean {
    return this.length <= 1;
  }
  /**
   * Tests the sign of the leading coefficient for negativity.
   *
   * @returns True for a negative polynomial.
   * @see SymPy `sympy.polys.rings.PolyElement.is_negative`
   */
  get isNegative(): boolean {
    return groundIsNegative(this.K, this.LC);
  }
  /**
   * Tests whether the polynomial has positive sign.
   *
   * @returns True for a positive polynomial.
   * @see SymPy `sympy.polys.rings.PolyElement.is_positive`
   */
  get isPositive(): boolean {
    return !this.isZero && !this.isNegative;
  }
  /**
   * Tests whether the polynomial's sign is zero or positive.
   *
   * @returns The nonnegative flag.
   * @see SymPy `sympy.polys.rings.PolyElement.is_nonnegative`
   */
  get isNonnegative(): boolean {
    return !this.isNegative;
  }
  /**
   * Tests whether the polynomial's sign is zero or negative.
   *
   * @returns The nonpositive flag.
   * @see SymPy `sympy.polys.rings.PolyElement.is_nonpositive`
   */
  get isNonpositive(): boolean {
    return this.isZero || this.isNegative;
  }
  /**
   * Tests for equality with the domain's additive identity.
   *
   * @returns True for zero.
   * @see SymPy `sympy.polys.rings.PolyElement.is_zero`
   */
  get isZero(): boolean {
    return this.map.size === 0;
  }
  /**
   * Tests for equality with the domain's multiplicative identity.
   *
   * @returns True for one.
   * @see SymPy `sympy.polys.rings.PolyElement.is_one`
   */
  get isOne(): boolean {
    return this.equals(this.ring.one);
  }
  /**
   * Tests whether the leading coefficient equals one.
   *
   * @returns True for a monic polynomial.
   * @see SymPy `sympy.polys.rings.PolyElement.is_monic`
   */
  get isMonic(): boolean {
    return groundEq(this.LC, this.K.one);
  }
  /**
   * Tests whether the coefficients have a unit as their GCD.
   *
   * @returns True for a primitive polynomial.
   * @see SymPy `sympy.polys.rings.PolyElement.is_primitive`
   */
  get isPrimitive(): boolean {
    return groundEq(this.content(), this.K.one);
  }
  /**
   * Checks whether the total degree is at most one.
   *
   * @returns The linearity flag.
   * @see SymPy `sympy.polys.rings.PolyElement.is_linear`
   */
  get isLinear(): boolean {
    return this.listmonoms().every((m) => m.reduce((s, e) => s + e, 0) <= 1);
  }
  /**
   * Checks whether the total degree is at most two.
   *
   * @returns The quadratic flag.
   * @see SymPy `sympy.polys.rings.PolyElement.is_quadratic`
   */
  get isQuadratic(): boolean {
    return this.listmonoms().every((m) => m.reduce((s, e) => s + e, 0) <= 2);
  }
  /**
   * Checks whether all irreducible factors have multiplicity one.
   *
   * @returns True for a square-free polynomial.
   * @see SymPy `sympy.polys.rings.PolyElement.is_squarefree`
   */
  get isSquarefree(): boolean {
    return this.ring.ngens === 0 || this.ring.dmpSqfP(this);
  }
  /**
   * Tests for irreducibility over the coefficient domain.
   *
   * @returns True for an irreducible polynomial.
   * @see SymPy `sympy.polys.rings.PolyElement.is_irreducible`
   */
  get isIrreducible(): boolean {
    return this.ring.ngens === 0 || this.ring.dmpIrreducibleP(this);
  }
  /**
   * Tests whether the polynomial is cyclotomic.
   *
   * @returns The cyclotomic flag.
   * @throws MultivariatePolynomialError when the operation requires a univariate polynomial.
   * @see SymPy `sympy.polys.rings.PolyElement.is_cyclotomic`
   */
  get isCyclotomic(): boolean {
    if (!this.ring.isUnivariate) throw new MultivariatePolynomialError('cyclotomic polynomial');
    return this.ring.dupCyclotomicP(this);
  }

  // ---- arithmetic ------------------------------------------------------------

  /**
   * Negates every coefficient of the polynomial.
   *
   * @returns The additive inverse.
   * @see SymPy `sympy.polys.rings.PolyElement.__neg__`
   */
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

  /**
   * Adds the corresponding coefficients of two polynomials.
   *
   * @param o - Operand to combine or compare with this value.
   * @returns The sum polynomial.
   * @see SymPy `sympy.polys.rings.PolyElement.__add__`
   */
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

  /**
   * Subtracts the second polynomial from the first.
   *
   * @param o - Operand to combine or compare with this value.
   * @returns The difference polynomial.
   * @see SymPy `sympy.polys.rings.PolyElement.__sub__`
   */
  sub(o: PolyElement | ExprLike): PolyElement {
    return this.add(this.coerce(o).neg());
  }

  /**
   * Multiplies the two input polynomials.
   *
   * @param o - Operand to combine or compare with this value.
   * @returns The product polynomial.
   * @see SymPy `sympy.polys.rings.PolyElement.__mul__`
   */
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

  /**
   * Raises the polynomial to a nonnegative integer power.
   *
   * @param n - Exponent or degree.
   * @returns The element raised to the specified exponent.
   * @throws RangeError when the exponent is not a nonnegative integer or both base and exponent are zero.
   * @see SymPy `sympy.polys.rings.PolyElement.__pow__`
   */
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

  /**
   * Multiplies the polynomial by itself.
   *
   * @returns The squared polynomial.
   * @see SymPy `sympy.polys.rings.PolyElement.square`
   */
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
   * Divides by one or more polynomials, expressing the dividend as a sum of divisor multiples and a
   * remainder.
   *
   * @param fv - Divisor polynomial or ordered list of divisors.
   * @returns The quotient (one per divisor for a list) and the remainder.
   * @throws RangeError when the divisor is zero or the operands belong to different polynomial rings.
   * @see SymPy `sympy.polys.rings.PolyElement.div`
   */
  div(fv: PolyElement): [PolyElement, PolyElement];
  /**
   * Divides by one or more polynomials, expressing the dividend as a sum of divisor multiples and a
   * remainder.
   *
   * @param fv - Divisor polynomial or ordered list of divisors.
   * @returns The quotient (one per divisor for a list) and the remainder.
   * @throws RangeError when the divisor is zero or the operands belong to different polynomial rings.
   * @see SymPy `sympy.polys.rings.PolyElement.div`
   */
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

  /**
   * Reduces the polynomial by one divisor or a list of divisors.
   *
   * @param G - Divisor polynomial or ordered list of divisors.
   * @returns The polynomial remainder.
   * @see SymPy `sympy.polys.rings.PolyElement.rem`
   */
  rem(G: PolyElement | readonly PolyElement[]): PolyElement {
    return G instanceof PolyElement ? this.div(G)[1] : this.div(G)[1];
  }

  /**
   * Divides the dividend by the divisor and keeps the quotient.
   *
   * @param G - Divisor polynomial or ordered list of divisors.
   * @returns The polynomial quotient.
   * @see SymPy `sympy.polys.rings.PolyElement.quo`
   */
  quo(G: PolyElement | readonly PolyElement[]): PolyElement | PolyElement[] {
    return G instanceof PolyElement ? this.div(G)[0] : this.div(G)[0];
  }

  /**
   * Computes the exact quotient, raising `ExactQuotientFailed` for a nonzero remainder.
   *
   * @param G - Divisor polynomial or ordered list of divisors.
   * @returns The exact quotient.
   * @throws ExactQuotientFailed when the divisor does not divide the dividend exactly.
   * @see SymPy `sympy.polys.rings.PolyElement.exquo`
   */
  exquo(G: PolyElement): PolyElement {
    const [q, r] = this.div(G);
    if (!r.isZero) throw new ExactQuotientFailed(`${G.toString()} does not divide ${this.toString()}`);
    return q;
  }

  /**
   * Divides by a polynomial or ground value with remainder.
   *
   * @param o - Operand to combine or compare with this value.
   * @returns The quotient and remainder.
   * @see SymPy `sympy.polys.rings.PolyElement.__divmod__`
   */
  divmod(o: PolyElement | ExprLike): [PolyElement, PolyElement] {
    if (o instanceof PolyElement) return this.div(this.coerce(o));
    const c = this.ring.domainNew(o);
    return [this.quoGround(c), this.remGround(c)];
  }

  /**
   * Keeps the quotient of polynomial division.
   *
   * @param o - Operand to combine or compare with this value.
   * @returns The polynomial quotient.
   * @see SymPy `sympy.polys.rings.PolyElement.__floordiv__`
   */
  floordiv(o: PolyElement | ExprLike): PolyElement {
    return this.divmod(o)[0];
  }

  /**
   * Keeps the remainder of polynomial division.
   *
   * @param o - Operand to combine or compare with this value.
   * @returns The modulus defining the algebraic extension.
   * @see SymPy `sympy.polys.rings.PolyElement.__mod__`
   */
  mod(o: PolyElement | ExprLike): PolyElement {
    return this.divmod(o)[1];
  }

  /**
   * Computes an exact polynomial quotient or divides by a ground value.
   *
   * @param o - Operand to combine or compare with this value.
   * @returns The quotient of the two elements.
   * @throws RangeError when the divisor is zero.
   * @see SymPy `sympy.polys.rings.PolyElement.__truediv__`
   */
  truediv(o: PolyElement | ExprLike): PolyElement {
    if (o instanceof PolyElement && !o.isGround) return this.exquo(this.coerce(o));
    const c = o instanceof PolyElement ? o.const() : this.ring.domainNew(o);
    if (groundIsZero(this.K, c)) throw new RangeError('polynomial division');
    return this.quoGround(c);
  }

  // ---- degrees and terms -----------------------------------------------------

  /**
   * Computes the degree in the selected generator, defaulting to the first and giving negative infinity
   * for zero.
   *
   * @param x - Polynomial generator.
   * @returns The degree in the selected generator, or `-Infinity` for zero.
   * @see SymPy `sympy.polys.rings.PolyElement.degree`
   */
  degree(x?: GenLike): number {
    const i = this.ring.index(x);
    if (this.isZero) return -Infinity;
    if (i < 0) return 0;
    return Math.max(...this.listmonoms().map((m) => at(m, i)));
  }

  /**
   * Finds the largest exponent in each generator.
   *
   * @returns The degree vector.
   * @see SymPy `sympy.polys.rings.PolyElement.degrees`
   */
  degrees(): number[] {
    return this.ring.zeroMonom.map((_, i) => this.degree(i));
  }

  /**
   * Finds the smallest power of the specified generator among the terms.
   *
   * @param x - Polynomial generator.
   * @returns The tail degree.
   * @see SymPy `sympy.polys.rings.PolyElement.tail_degree`
   */
  tailDegree(x?: GenLike): number {
    const i = this.ring.index(x);
    if (this.isZero) return -Infinity;
    if (i < 0) return 0;
    return Math.min(...this.listmonoms().map((m) => at(m, i)));
  }

  /**
   * Finds the smallest exponent in each generator.
   *
   * @returns The tail degree vector.
   * @see SymPy `sympy.polys.rings.PolyElement.tail_degrees`
   */
  tailDegrees(): number[] {
    return this.ring.zeroMonom.map((_, i) => this.tailDegree(i));
  }

  private orderCmp(a: Monom, b: Monom): number {
    return this.ring.order.compare(a, b);
  }

  /**
   * Selects the leading exponent vector in the ring's order, using the zero vector for the zero
   * polynomial.
   *
   * @returns The leading exponent vector in the order of the ring.
   * @see SymPy `sympy.polys.rings.PolyElement.leading_expv`
   */
  leadingExpv(): Monom {
    let best: Monom | undefined;
    for (const m of this.listmonoms()) if (best === undefined || this.orderCmp(m, best) > 0) best = m;
    return best ?? this.ring.zeroMonom;
  }

  /**
   * Extracts the coefficient of a monomial or of the unit monomial.
   *
   * @param element - Value to coerce into the domain.
   * @returns The selected coefficient.
   * @throws RangeError when the argument is not a monomial.
   * @see SymPy `sympy.polys.rings.PolyElement.coeff`
   */
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

  /**
   * Reads the coefficient of the all-zero exponent vector.
   *
   * @returns The constant term.
   * @see SymPy `sympy.polys.rings.PolyElement.const`
   */
  const(): Expr {
    return this.get(this.ring.zeroMonom);
  }

  /**
   * Extracts the coefficient of the leading term.
   *
   * @returns The leading coefficient.
   * @see SymPy `sympy.polys.rings.PolyElement.LC`
   */
  get LC(): Expr {
    return this.get(this.leadingExpv());
  }

  /**
   * Extracts the exponents of the first term in monomial order.
   *
   * @returns The leading exponent vector.
   * @see SymPy `sympy.polys.rings.PolyElement.LM`
   */
  get LM(): Monom {
    return this.leadingExpv();
  }

  /**
   * Constructs the leading monomial as a ring element.
   *
   * @returns The monic leading monomial.
   * @see SymPy `sympy.polys.rings.PolyElement.leading_monom`
   */
  leadingMonom(): PolyElement {
    if (this.isZero) return this.ring.zero;
    return this.make([[this.leadingExpv(), this.K.one]]);
  }

  /**
   * Selects the highest term in the ring's monomial order.
   *
   * @returns Its exponent vector and coefficient.
   * @see SymPy `sympy.polys.rings.PolyElement.LT`
   */
  get LT(): readonly [Monom, Expr] {
    const e = this.leadingExpv();
    return [e, this.get(e)];
  }

  /**
   * Constructs the highest term as a polynomial in this ring.
   *
   * @returns The leading term polynomial.
   * @see SymPy `sympy.polys.rings.PolyElement.leading_term`
   */
  leadingTerm(): PolyElement {
    return this.make([this.LT]);
  }

  /**
   * Lists terms from largest to smallest in the specified monomial order.
   *
   * @param order - Monomial order used to compare terms.
   * @returns The ordered monomial–coefficient pairs.
   * @see SymPy `sympy.polys.rings.PolyElement.terms`
   */
  terms(order?: OrderLike): [Monom, Expr][] {
    const O = order === undefined ? this.ring.order : parseOrder(order);
    return this.listterms().sort((a, b) => O.compare(b[0], a[0]));
  }

  /**
   * Lists coefficients according to the monomial order of their terms.
   *
   * @param order - Monomial order used to compare terms.
   * @returns The ordered coefficients.
   * @see SymPy `sympy.polys.rings.PolyElement.coeffs`
   */
  coeffs(order?: OrderLike): Expr[] {
    return this.terms(order).map(([, c]) => c);
  }

  /**
   * Lists monomials according to the specified term order.
   *
   * @param order - Monomial order used to compare terms.
   * @returns The ordered exponent vectors.
   * @see SymPy `sympy.polys.rings.PolyElement.monoms`
   */
  monoms(order?: OrderLike): Monom[] {
    return this.terms(order).map(([m]) => m);
  }

  /**
   * Collects the nonzero terms without imposing a monomial order.
   *
   * @returns The monomial–coefficient pairs.
   * @see SymPy `sympy.polys.rings.PolyElement.listterms`
   */
  listterms(): [Monom, Expr][] {
    return [...this.map.values()].map(([m, c]) => [m, c]);
  }

  /**
   * Collects the stored coefficients without imposing a monomial order.
   *
   * @returns The coefficient list.
   * @see SymPy `sympy.polys.rings.PolyElement.listcoeffs`
   */
  listcoeffs(): Expr[] {
    return [...this.map.values()].map(([, c]) => c);
  }

  /**
   * Collects the stored monomials without imposing a monomial order.
   *
   * @returns The exponent vectors.
   * @see SymPy `sympy.polys.rings.PolyElement.listmonoms`
   */
  listmonoms(): Monom[] {
    return [...this.map.values()].map(([m]) => m);
  }

  // ---- ground operations -----------------------------------------------------

  /**
   * Computes the polynomial content as the GCD of its coefficients.
   *
   * @returns The content.
   * @see SymPy `sympy.polys.rings.PolyElement.content`
   */
  content(): Expr {
    const K = this.K;
    return this.listcoeffs().reduce((g, c) => groundGcd(K, g, c), K.zero);
  }

  /**
   * Separates the coefficient GCD from the primitive polynomial.
   *
   * @returns The content and primitive part.
   * @see SymPy `sympy.polys.rings.PolyElement.primitive`
   */
  primitive(): [Expr, PolyElement] {
    const c = this.content();
    if (groundIsZero(this.K, c)) return [c, this];
    return [c, this.quoGround(c)];
  }

  /**
   * Divides by the leading coefficient to normalize the polynomial.
   *
   * @returns The monic polynomial.
   * @see SymPy `sympy.polys.rings.PolyElement.monic`
   */
  monic(): PolyElement {
    return this.isZero ? this : this.quoGround(this.LC);
  }

  /**
   * Multiplies every coefficient by the ground scalar.
   *
   * @param x - Polynomial generator.
   * @returns The scaled polynomial.
   * @see SymPy `sympy.polys.rings.PolyElement.mul_ground`
   */
  mulGround(x: ExprLike): PolyElement {
    const c = this.ring.domainNew(x);
    if (groundIsZero(this.K, c)) return this.ring.zero;
    return this.make(this.listterms().map(([m, a]) => [m, this.K.mul(a, c)] as const));
  }

  /**
   * Multiplies every coefficient by the scalar in place.
   *
   * @param x - Polynomial generator.
   * @returns The updated polynomial.
   * @see SymPy `sympy.polys.rings.PolyElement.imul_num`
   */
  imulNum(x: ExprLike): this {
    this.map = this.mulGround(x).map;
    return this;
  }

  /**
   * Multiplies the polynomial by the supplied monomial.
   *
   * @param monom - Exponent vector of the monomial.
   * @returns The polynomial with the monomial exponents added to each term.
   * @see SymPy `sympy.polys.rings.PolyElement.mul_monom`
   */
  mulMonom(monom: Monom): PolyElement {
    return this.make(this.listterms().map(([m, c]) => [m.map((a, i) => a + at(monom, i)), c] as const));
  }

  /**
   * Multiplies the polynomial by the supplied coefficient and monomial.
   *
   * @param term - Monomial and coefficient of the term.
   * @returns The polynomial multiplied by the term.
   * @see SymPy `sympy.polys.rings.PolyElement.mul_term`
   */
  mulTerm(term: readonly [Monom, ExprLike]): PolyElement {
    const [monom, c0] = term;
    const c = this.ring.domainNew(c0);
    if (this.isZero || groundIsZero(this.K, c)) return this.ring.zero;
    return this.make(this.listterms().map(([m, a]) => [m.map((x, i) => x + at(monom, i)), this.K.mul(a, c)] as const));
  }

  /**
   * Divides coefficients by the ground element, dropping terms with inexact quotients over a ring.
   *
   * @param x - Polynomial generator.
   * @returns The polynomial obtained by dividing its coefficients by the ground element.
   * @throws RangeError when the divisor is zero.
   * @see SymPy `sympy.polys.rings.PolyElement.quo_ground`
   */
  quoGround(x: ExprLike): PolyElement {
    const K = this.K;
    const c = this.ring.domainNew(x);
    if (groundIsZero(K, c)) throw new RangeError('polynomial division');
    if (this.isZero || groundEq(c, K.one)) return this;
    if (K.isField) return this.make(this.listterms().map(([m, a]) => [m, K.quo(a, c)] as const));
    return this.make(this.listterms().filter(([, a]) => groundIsZero(K, groundRem(K, a, c))).map(([m, a]) => [m, groundQuo(K, a, c)] as const));
  }

  /**
   * Divides by the supplied term and drops terms that are not divisible.
   *
   * @param term - Monomial and coefficient of the term.
   * @returns The quotient by the supplied term.
   * @throws RangeError when the divisor is zero.
   * @see SymPy `sympy.polys.rings.PolyElement.quo_term`
   */
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

  /**
   * Reduces coefficients modulo `p`, choosing symmetric residues over the integers.
   *
   * @param p - Modulus for reducing coefficients.
   * @returns The truncated polynomial.
   * @see SymPy `sympy.polys.rings.PolyElement.trunc_ground`
   */
  truncGround(p: ExprLike): PolyElement {
    const K = this.K;
    const q = this.ring.domainNew(p);
    if (K instanceof PolynomialDomain) {
      const ring = new PolyRing(K.gens, K.dom);
      const modulus = ring.fromExpr(q);
      return this.make(this.listterms().map(([m, c]) => {
        const f = ring.fromExpr(c);
        return [m, (modulus.isGround ? f.truncGround(modulus.const()) : f.rem(modulus)).asExpr()] as const;
      }));
    }
    const half = K instanceof IntegerRing ? groundQuo(K, q, Rational.of(2)) : K.zero;
    return this.make(
      this.listterms().map(([m, c]) => {
        const r = groundRem(K, c, q);
        return [m, K instanceof IntegerRing && greater(r, half) ? K.sub(r, q) : r] as const;
      }),
    );
  }

  /**
   * Takes the remainder of each coefficient modulo `p`.
   *
   * @param p - Polynomial to operate on.
   * @returns The reduced polynomial.
   * @see SymPy `sympy.polys.rings.PolyElement.rem_ground`
   */
  remGround(p: ExprLike): PolyElement {
    return this.truncGround(p);
  }

  /**
   * Divides both polynomials by the GCD of their contents.
   *
   * @param g - Second polynomial operand.
   * @returns The shared content and both quotients.
   * @see SymPy `sympy.polys.rings.PolyElement.extract_ground`
   */
  extractGround(g: PolyElement): [Expr, PolyElement, PolyElement] {
    const c = groundGcd(this.K, this.content(), g.content());
    return [c, this.quoGround(c), g.quoGround(c)];
  }

  /**
   * Computes the maximum norm from the polynomial's coefficients.
   *
   * @returns The largest absolute coefficient.
   * @see SymPy `sympy.polys.rings.PolyElement.max_norm`
   */
  maxNorm(): Expr {
    return this.ring.dupMaxNorm(this);
  }

  /**
   * Computes the polynomial's L1 norm.
   *
   * @returns The sum of absolute coefficients.
   * @see SymPy `sympy.polys.rings.PolyElement.l1_norm`
   */
  l1Norm(): Expr {
    const K = this.K;
    return this.listcoeffs().reduce((s, c) => K.add(s, groundAbs(K, c)), K.zero);
  }

  /**
   * Divides exponents by common divisors computed per generator across all inputs.
   *
   * @param G - Other polynomials to deflate by the same exponent factors.
   * @returns The divisor vector and deflated polynomials.
   * @see SymPy `sympy.polys.rings.PolyElement.deflate`
   */
  deflate(...G: PolyElement[]): [number[], PolyElement[]] {
    const polys = [this, ...G];
    const J = this.ring.zeroMonom.map(() => 0);
    for (const p of polys) for (const m of p.listmonoms()) m.forEach((e, i) => (J[i] = Number(igcd(BigInt(at(J, i)), BigInt(e)))));
    const K = J.map((b) => b || 1);
    if (K.every((b) => b === 1)) return [K, polys];
    return [K, polys.map((p) => p.make(p.listterms().map(([m, c]) => [m.map((e, i) => e / at(K, i)), c] as const)))];
  }

  /**
   * Multiplies each generator's exponents by its factor in `J`.
   *
   * @param J - Indices of the generators.
   * @returns The inflated polynomial.
   * @see SymPy `sympy.polys.rings.PolyElement.inflate`
   */
  inflate(J: readonly IntLike[]): PolyElement {
    const k = J.map((j) => intArg(j));
    return this.make(this.listterms().map(([m, c]) => [m.map((e, i) => e * at(k, i)), c] as const));
  }

  /**
   * Finds the least polynomial multiple common to both inputs.
   *
   * @param g - Second polynomial operand.
   * @returns The LCM.
   * @see SymPy `sympy.polys.rings.PolyElement.lcm`
   */
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

  /**
   * Finds the greatest polynomial divisor common to both inputs.
   *
   * @param g - Second polynomial operand.
   * @returns The GCD.
   * @see SymPy `sympy.polys.rings.PolyElement.gcd`
   */
  gcd(g: PolyElement): PolyElement {
    return this.cofactors(g)[0];
  }

  /**
   * Factors the GCD out of the polynomial pair.
   *
   * @param g - Second polynomial operand.
   * @returns The GCD and both quotients.
   * @see SymPy `sympy.polys.rings.PolyElement.cofactors`
   */
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

  /**
   * Cancels common polynomial factors and normalizes the denominator.
   *
   * @param g - Second polynomial operand.
   * @returns The reduced numerator and denominator.
   * @see SymPy `sympy.polys.rings.PolyElement.cancel`
   */
  cancel(g: PolyElement): [PolyElement, PolyElement] {
    const R = this.ring;
    const K = this.K;
    if (this.isZero) return [this, R.one];
    let p: PolyElement;
    let q: PolyElement;
    const Z = assocRing(K);
    if (Z === undefined) [, p, q] = this.cofactors(g);
    else {
      const ZR = R.clone({ domain: Z });
      const [cq, f1] = this.clearDenoms();
      const [cp, g1] = g.clearDenoms();
      [, p, q] = f1.setRing(ZR).cofactors(g1.setRing(ZR));
      const c = groundGcd(Z, cp, cq);
      p = p.setRing(R).mulGround(groundQuo(Z, cp, c));
      q = q.setRing(R).mulGround(groundQuo(Z, cq, c));
    }
    const u = q.canonicalUnit();
    if (groundEq(u, K.one)) return [p, q];
    return [p.mulGround(u), q.mulGround(u)];
  }

  /**
   * Finds the unit that normalizes the leading coefficient.
   *
   * @returns The canonical unit.
   * @see SymPy `sympy.polys.rings.PolyElement.canonical_unit`
   */
  canonicalUnit(): Expr {
    return canonicalUnit(this.K, this.LC);
  }

  /**
   * Differentiates with respect to the specified generator.
   *
   * @param x - Polynomial generator.
   * @returns The partial derivative.
   * @see SymPy `sympy.polys.rings.PolyElement.diff`
   */
  diff(x: GenLike): PolyElement {
    const i = this.ring.index(x);
    return this.make(
      this.listterms()
        .filter(([m]) => at(m, i) !== 0)
        .map(([m, c]) => [m.map((e, j) => (j === i ? e - 1 : e)), this.ring.domainNew(this.K.mul(c, Rational.of(at(m, i))))] as const),
    );
  }

  /**
   * Evaluates the polynomial at values for the leading generators.
   *
   * @param values - Values to substitute, in generator order.
   * @returns Evaluate the rational function at the supplied values.
   * @throws RangeError when the number of evaluation values is outside the range from one to the number of generators.
   * @see SymPy `sympy.polys.rings.PolyElement.__call__`
   */
  call(...values: ExprLike[]): PolyElement | Expr {
    if (!(values.length > 0 && values.length <= this.ring.ngens)) throw new RangeError(`expected at least 1 and at most ${this.ring.ngens} values, got ${values.length}`);
    return this.evaluate(values.map((v, i) => [at(this.ring.gens, i), v] as const));
  }

  /**
   * Substitutes generator values in sequence, removing each specified generator from the ring.
   *
   * @param x - Polynomial generator.
   * @param a - Value to substitute for the chosen generator.
   * @returns The specialized polynomial or ground value.
   * @see SymPy `sympy.polys.rings.PolyElement.evaluate`
   */
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

  /**
   * Substitutes generator values in sequence while retaining the original ring.
   *
   * @param x - Polynomial generator.
   * @param a - First operand.
   * @returns Apply the indicated substitutions to the root sum.
   * @see SymPy `sympy.polys.rings.PolyElement.subs`
   */
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
   * Applies Lauer's algorithm to express the symmetric part in elementary symmetric polynomials.
   *
   * @returns The symmetric expression, remainder, and generator substitutions.
   * @see SymPy `sympy.polys.rings.PolyElement.symmetrize`
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

  /**
   * Substitutes polynomial expressions for the specified generators.
   *
   * @param x - Polynomial generator.
   * @param a - First operand.
   * @returns The polynomial after the specified substitutions.
   * @throws RangeError when the substitutions are not generator and value pairs.
   * @see SymPy `sympy.polys.rings.PolyElement.compose`
   */
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

  /**
   * Collects the terms at the requested degree in one generator.
   *
   * @param x - Polynomial generator.
   * @param deg - Degree to select.
   * @returns The coefficient polynomial in the remaining generators.
   * @see SymPy `sympy.polys.rings.PolyElement.coeff_wrt`
   */
  coeffWrt(x: GenLike, deg: IntLike): PolyElement {
    const i = this.ring.index(x);
    const d = intArg(deg);
    return this.make(this.listterms().filter(([m]) => at(m, i) === d).map(([m, c]) => [m.map((e, j) => (j === i ? 0 : e)), c] as const));
  }

  /**
   * Performs pseudo-division in the main variable and retains the remainder.
   *
   * @param g - Divisor polynomial.
   * @param x - Polynomial generator.
   * @returns The pseudo-remainder.
   * @see SymPy `sympy.polys.rings.PolyElement.prem`
   */
  prem(g: PolyElement, x?: GenLike): PolyElement {
    return this.pdivWith(g, x, false)[1];
  }

  /**
   * Performs pseudo-division in the selected generator.
   *
   * @param g - Divisor polynomial.
   * @param x - Polynomial generator.
   * @returns The pseudo-quotient and pseudo-remainder.
   * @see SymPy `sympy.polys.rings.PolyElement.pdiv`
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

  /**
   * Computes the quotient from polynomial pseudo-division.
   *
   * @param g - Divisor polynomial.
   * @param x - Polynomial generator.
   * @returns The pseudo-quotient.
   * @see SymPy `sympy.polys.rings.PolyElement.pquo`
   */
  pquo(g: PolyElement, x?: GenLike): PolyElement {
    return this.pdiv(g, x)[0];
  }

  /**
   * Performs exact pseudo-division in the main variable.
   *
   * @param g - Divisor polynomial.
   * @param x - Polynomial generator.
   * @returns The exact pseudo-quotient.
   * @throws ExactQuotientFailed when the divisor does not divide the dividend exactly.
   * @see SymPy `sympy.polys.rings.PolyElement.pexquo`
   */
  pexquo(g: PolyElement, x?: GenLike): PolyElement {
    const [q, r] = this.pdiv(g, x);
    if (!r.isZero) throw new ExactQuotientFailed(`${g.toString()} does not divide ${this.toString()}`);
    return q;
  }

  /**
   * Builds the subresultant polynomial remainder sequence in the selected generator.
   *
   * @param g0 - Polynomial divisor.
   * @param x0 - Expansion point.
   * @returns The subresultant polynomials.
   * @see SymPy `sympy.polys.rings.PolyElement.subresultants`
   */
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

  /**
   * Finds a coefficient `s` satisfying `s*f = h` modulo `g` for the GCD `h`.
   *
   * @param g - Second polynomial operand.
   * @returns The pair `[s, h]`.
   * @see SymPy `sympy.polys.rings.PolyElement.half_gcdex`
   */
  halfGcdex(g: PolyElement): [PolyElement, PolyElement] {
    return this.ring.dupHalfGcdex(this, g);
  }
  /**
   * Computes a polynomial GCD and the coefficients of its Bézout identity.
   *
   * @param g - Second polynomial operand.
   * @returns The two Bézout coefficients and GCD.
   * @see SymPy `sympy.polys.rings.PolyElement.gcdex`
   */
  gcdex(g: PolyElement): [PolyElement, PolyElement, PolyElement] {
    return this.ring.dupGcdex(this, g);
  }
  /**
   * Eliminates the polynomial variable by taking the resultant of the inputs.
   *
   * @param g - Second polynomial operand.
   * @returns The resultant with respect to the elimination variable.
   * @see SymPy `sympy.polys.rings.PolyElement.resultant`
   */
  resultant(g: PolyElement): PolyElement | Expr {
    return this.ring.dmpResultant(this, g);
  }
  /**
   * Computes the discriminant of the polynomial.
   *
   * @returns The discriminant value.
   * @see SymPy `sympy.polys.rings.PolyElement.discriminant`
   */
  discriminant(): PolyElement | Expr {
    return this.ring.dmpDiscriminant(this);
  }
  /**
   * Writes the polynomial as a composition of lower-degree polynomials when possible.
   *
   * @returns The components in composition order.
   * @throws MultivariatePolynomialError when the operation requires a univariate polynomial.
   * @see SymPy `sympy.polys.rings.PolyElement.decompose`
   */
  decompose(): PolyElement[] {
    if (!this.ring.isUnivariate) throw new MultivariatePolynomialError('polynomial decomposition');
    return this.ring.dupDecompose(this);
  }
  /**
   * Translates the polynomial's argument by the supplied value.
   *
   * @param a - First operand.
   * @returns The translated polynomial.
   * @throws MultivariatePolynomialError when the operation requires a univariate polynomial.
   * @see SymPy `sympy.polys.rings.PolyElement.shift`
   */
  shift(a: ExprLike): PolyElement {
    if (!this.ring.isUnivariate) throw new MultivariatePolynomialError('shift: use shift_list instead');
    return this.ring.dupShift(this, a);
  }
  /**
   * Translates each generator by its corresponding shift.
   *
   * @param a - First operand.
   * @returns The polynomial translated by one amount for each generator.
   * @see SymPy `sympy.polys.rings.PolyElement.shift_list`
   */
  shiftList(a: readonly ExprLike[]): PolyElement {
    return this.ring.dmpShift(this, a);
  }
  /**
   * Builds the Sturm sequence for the polynomial.
   *
   * @returns The ordered Sturm polynomials.
   * @throws MultivariatePolynomialError when the operation requires a univariate polynomial.
   * @see SymPy `sympy.polys.rings.PolyElement.sturm`
   */
  sturm(): PolyElement[] {
    if (!this.ring.isUnivariate) throw new MultivariatePolynomialError('sturm sequence');
    return this.ring.dupSturm(this);
  }
  /**
   * Computes the greatest factorial factorization of the polynomial.
   *
   * @returns The factors and their factorial lengths.
   * @see SymPy `sympy.polys.rings.PolyElement.gff_list`
   */
  gffList(): [PolyElement, number][] {
    return this.ring.dmpGffList(this);
  }
  /**
   * Removes repeated irreducible factors from the polynomial.
   *
   * @returns The square-free part of the polynomial.
   * @see SymPy `sympy.polys.rings.PolyElement.sqf_part`
   */
  sqfPart(): PolyElement {
    return this.ring.dmpSqfPart(this);
  }
  /**
   * Separates the polynomial into square-free factors by multiplicity.
   *
   * @param all - Include factors of missing multiplicities.
   * @returns The coefficient and factor–multiplicity pairs.
   * @see SymPy `sympy.polys.rings.PolyElement.sqf_list`
   */
  sqfList(all = false): [Expr, [PolyElement, number][]] {
    return this.ring.dmpSqfList(this, all);
  }
  /**
   * Computes the norm of the polynomial over its ground domain.
   *
   * @returns The polynomial norm over the ground domain.
   * @see SymPy `sympy.polys.rings.PolyElement.norm`
   */
  norm(): PolyElement {
    const polynomial = Poly.from(this.asExpr(), this.ring.symbols, { domain: this.K });
    return this.ring.toGround().fromExpr(polynomial.norm().asExpr());
  }
  /**
   * Shifts the polynomial until its norm is square-free over the ground field.
   *
   * @returns The shift, translated polynomial, and norm.
   * @see SymPy `sympy.polys.rings.PolyElement.sqf_norm`
   */
  sqfNorm(): [number[], PolyElement, PolyElement] {
    return this.ring.dmpSqfNorm(this);
  }
  /**
   * Decomposes the polynomial into irreducible factors.
   *
   * @returns The coefficient and factor–multiplicity pairs.
   * @see SymPy `sympy.polys.rings.PolyElement.factor_list`
   */
  factorList(): [Expr, [PolyElement, number][]] {
    return this.ring.dmpFactorList(this);
  }
}

/** a > b for rationals. */
const greater = (a: Expr, b: Expr): boolean => a instanceof Rational && b instanceof Rational && a.p * b.q > b.p * a.q;

/**
 * Constructs a polynomial ring and exposes its generators as individual tuple entries.
 *
 * @param symbols - Symbols naming the generators, in order.
 * @param domain - Coefficient domain.
 * @param order - Monomial order used to compare terms.
 * @returns The tuple `[ring, ...generators]`.
 * @see SymPy `sympy.polys.rings.ring`
 * @example
 * ```ts
 * import { ring, ZZ } from '@symjs/symjs';
 *
 * const [R, x, y] = ring('x,y', ZZ);
 * x.add(y).pow(2).toString(); // => x**2 + 2*x*y + y**2
 * ```
 */
export function ring(symbols: RingSymbols, domain: DomainLike = ZZ, order: OrderLike = lex): [PolyRing, ...PolyElement[]] {
  const R = new PolyRing(symbols, domain, order);
  return [R, ...R.gens];
}

/**
 * Constructs a polynomial ring and collects its generators in a list.
 *
 * @param symbols - Symbols naming the generators, in order.
 * @param domain - Coefficient domain.
 * @param order - Monomial order used to compare terms.
 * @returns The pair `[ring, generators]`.
 * @see SymPy `sympy.polys.rings.xring`
 * @example
 * ```ts
 * import { ZZ, xring } from '@symjs/symjs';
 *
 * xring('x,y,z', ZZ)[1].map(g => g.asExpr()); // => [x, y, z]
 * ```
 */
export function xring(symbols: RingSymbols, domain: DomainLike = ZZ, order: OrderLike = lex): [PolyRing, PolyElement[]] {
  const R = new PolyRing(symbols, domain, order);
  return [R, [...R.gens]];
}

/**
 * Construct a polynomial ring with generators accessible through `gens`.
 *
 * @param symbols - Symbols naming the generators, in order.
 * @param domain - Coefficient domain.
 * @param order - Monomial order used to compare terms.
 * @returns The polynomial ring.
 * @see SymPy `sympy.polys.rings.vring`
 * @example
 * ```ts
 * import { ZZ, vring } from '@symjs/symjs';
 *
 * vring('x,y,z', ZZ).ngens; // => 3
 * ```
 */
export function vring(symbols: RingSymbols, domain: DomainLike = ZZ, order: OrderLike = lex): PolyRing {
  return new PolyRing(symbols, domain, order);
}

/** Options of sring. */
export interface SringOptions {
  /** The coefficient domain. */
  domain?: DomainLike;
  /** The monomial order. */
  order?: OrderLike;
  /** Whether to prefer a field for the coefficients. */
  field?: boolean;
  /** The algebraic extensions to include in the coefficient domain. */
  extension?: boolean;
}

/**
 * Infers a polynomial ring for the input expressions and converts them to elements of that ring.
 *
 * @param exprs - Expressions to convert, with a common generator order.
 * @param rest - Additional generators and polynomial construction options.
 * @returns The ring and the converted element or list.
 * @see SymPy `sympy.polys.rings.sring`
 * @example
 * ```ts
 * import { ex, sring } from '@symjs/symjs';
 *
 * sring(ex`x + 2*y + 3*z`)[1].asExpr(); // => x + 2*y + 3*z
 * ```
 */
export function sring(exprs: ExprLike, ...rest: (Expr | SringOptions)[]): [PolyRing, PolyElement];
/**
 * Infers a polynomial ring for the input expressions and converts them to elements of that ring.
 *
 * @param exprs - Expressions to convert, with a common generator order.
 * @param rest - Additional generators and polynomial construction options.
 * @returns The ring and the converted element or list.
 * @see SymPy `sympy.polys.rings.sring`
 */
export function sring(exprs: readonly ExprLike[], ...rest: (Expr | SringOptions)[]): [PolyRing, PolyElement[]];
export function sring(exprs: ExprLike | readonly ExprLike[], ...rest: (Expr | SringOptions)[]): [PolyRing, PolyElement | PolyElement[]] {
  const single = !isExprList(exprs);
  const es = (isExprList(exprs) ? [...exprs] : [exprs]).map((e) => expand(sympify(e)));
  const opts: SringOptions = rest.find((r): r is SringOptions => !(r instanceof Expr)) ?? {};
  const extension = opts.extension === true ? true : undefined;
  let gens: Expr[] = rest.filter((r): r is Expr => r instanceof Expr);
  if (!gens.length) {
    const all = new Map<string, Expr>();
    for (const e of es) for (const g of Poly.from(e, undefined, { extension }).gens) all.set(g.key, g);
    gens = sortGens([...all.values()]);
  }
  const polys = es.map((e) => Poly.from(e, gens, { domain: opts.domain, extension }));
  const coeffs = polys.flatMap((p) => p.coeffs());
  const domain = opts.domain ?? constructDomain(coeffs, { extension, field: opts.field })[0];
  const R = new PolyRing(gens, domain, opts.order ?? lex);
  const elems = polys.map((p) => R.fromTerms(p.isZero ? [] : p.terms().map(([m, c]) => [m, R.domainNew(c)] as const)));
  return [R, single ? first(elems) : elems];
}

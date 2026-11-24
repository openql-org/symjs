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

/** A vector of rational exponents of a Puiseux monomial. */
export type PuiseuxMonom = readonly Rational[];
/** A rational exponent vector paired with its coefficient. */
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

/**
 * A ring of finite sums of rational powers of its generators.
 *
 * @see SymPy `sympy.polys.puiseux.PuiseuxRing`
 * @example
 * ```ts
 * import { QQ, puiseuxRing } from '@symjs/symjs';
 *
 * const [R, x] = puiseuxRing('x, y', QQ);
 * R.ngens; // => 2
 * ```
 */
export class PuiseuxRing {
  /**
   * The ordinary polynomial ring underlying the Puiseux representation.
   *
   * @see SymPy `sympy.polys.puiseux.PuiseuxRing.poly_ring`
   */
  readonly polyRing: PolyRing;
  /**
   * The coefficient domain.
   *
   * @see SymPy `sympy.polys.puiseux.PuiseuxRing.domain`
   */
  readonly domain: Domain;
  /**
   * The symbols naming the generators, in order.
   *
   * @see SymPy `sympy.polys.puiseux.PuiseuxRing.symbols`
   */
  readonly symbols: readonly Expr[];
  /**
   * The number of generators.
   *
   * @see SymPy `sympy.polys.puiseux.PuiseuxRing.ngens`
   */
  readonly ngens: number;
  /**
   * The ordered generators.
   *
   * @see SymPy `sympy.polys.puiseux.PuiseuxRing.gens`
   */
  readonly gens: readonly PuiseuxPoly[];
  /**
   * The all-zero exponent vector.
   *
   * @see SymPy `sympy.polys.puiseux.PuiseuxRing.zero_monom`
   */
  readonly zeroMonom: PuiseuxMonom;

  /**
   * Construct a Puiseux polynomial ring.
   *
   * @param symbols - Symbols naming the generators, in order.
   * @param domain - Coefficient domain.
   */
  constructor(symbols: RingSymbols, domain: DomainLike) {
    this.polyRing = new PolyRing(symbols, domain);
    this.domain = this.polyRing.domain;
    this.symbols = this.polyRing.symbols;
    this.ngens = this.polyRing.ngens;
    this.zeroMonom = this.symbols.map(() => Rational.of(0));
    this.gens = this.polyRing.gens.map((p) => this.fromPoly(p));
  }
  /**
   * Formats this object as text.
   *
   * @returns The formatted text.
   */
  toString(): string {
    return `PuiseuxRing((${this.symbols.map((s) => str(s)).join(', ')}${this.ngens === 1 ? ',' : ''}), ${String(this.domain)})`;
  }
  /**
   * Checks whether both operands represent the same value.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns Whether the comparison holds.
   * @see SymPy `sympy.polys.puiseux.PuiseuxRing.__eq__`
   */
  equals(other: unknown): boolean {
    return other instanceof PuiseuxRing && this.polyRing.equals(other.polyRing);
  }
  /**
   * Multiplies Puiseux monomials by adding corresponding rational exponents.
   *
   * @param a - First operand.
   * @param b - Second operand.
   * @returns The product exponent vector.
   * @see SymPy `sympy.polys.puiseux.PuiseuxRing.monomial_mul`
   */
  monomialMul(a: readonly ExprLike[], b: readonly ExprLike[]): Rational[] {
    return a.map((e, i) => addExponents(rationalExponent(e), rationalExponent(at(b, i))));
  }
  /**
   * Represents zero in this ring.
   *
   * @returns The additive identity.
   * @see SymPy `sympy.polys.puiseux.PuiseuxRing.zero`
   */
  get zero(): PuiseuxPoly { return this.fromDict([]); }
  /**
   * Represents one in this ring.
   *
   * @returns The multiplicative identity.
   * @see SymPy `sympy.polys.puiseux.PuiseuxRing.one`
   */
  get one(): PuiseuxPoly { return this.groundNew(this.domain.one); }
  /**
   * Embeds a polynomial with ordinary exponents into the Puiseux ring.
   *
   * @param p - Polynomial to operate on.
   * @returns The Puiseux polynomial.
   * @see SymPy `sympy.polys.puiseux.PuiseuxRing.from_poly`
   */
  fromPoly(p: PolyElement): PuiseuxPoly { return new PuiseuxPoly(p.setRing(this.polyRing), this); }
  /**
   * Builds a Puiseux polynomial from its monomial-to-coefficient map.
   *
   * @param terms - Monomial and coefficient pairs.
   * @returns The polynomial in this ring.
   * @see SymPy `sympy.polys.puiseux.PuiseuxRing.from_dict`
   */
  fromDict(terms: Iterable<PuiseuxTerm>): PuiseuxPoly { return new PuiseuxPoly(terms, this); }
  /**
   * Construct a constant polynomial from an integer.
   *
   * @param n - Exponent or degree.
   * @returns The integer as a constant Puiseux polynomial.
   * @see SymPy `sympy.polys.puiseux.PuiseuxRing.from_int`
   */
  fromInt(n: number | bigint): PuiseuxPoly { return this.groundNew(n); }
  /**
   * Converts a value to the coefficient domain.
   *
   * @param value - Value to convert.
   * @returns The ground element.
   * @see SymPy `sympy.polys.puiseux.PuiseuxRing.domain_new`
   */
  domainNew(value: ExprLike): Expr { return this.polyRing.domainNew(value); }
  /**
   * Construct a constant polynomial from a coefficient.
   *
   * @param value - Value to convert.
   * @returns The corresponding constant element.
   * @see SymPy `sympy.polys.puiseux.PuiseuxRing.ground_new`
   */
  groundNew(value: ExprLike): PuiseuxPoly { return this.fromDict([[this.zeroMonom, value]]); }
  /**
   * Converts the input to an element of the polynomial ring.
   *
   * @param value - Value to convert.
   * @returns The ring element.
   * @throws RangeError when the operands have different Puiseux rings.
   * @throws NotImplementedError when the element is supplied as a string.
   * @throws TypeError when the input is not a polynomial, term map or expression.
   */
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
  /**
   * Convert a symbolic expression into a polynomial.
   *
   * @param value - Value to convert.
   * @returns The expression as a Puiseux polynomial.
   */
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
  /**
   * Locates the generator in the ordered list of indeterminates.
   *
   * @param x - Polynomial generator.
   * @returns The generator index.
   * @throws RangeError when the input is not a generator of this ring.
   * @see SymPy `sympy.polys.puiseux.PuiseuxRing.index`
   */
  index(x: PuiseuxPoly): number {
    const i = this.gens.findIndex((g) => g.equals(x));
    if (i < 0) throw new RangeError('expected a generator of this Puiseux ring');
    return i;
  }
}

/**
 * An immutable sparse Puiseux polynomial; exponents are stored directly as reduced rationals.
 *
 * @see SymPy `sympy.polys.puiseux.PuiseuxPoly`
 * @example
 * ```ts
 * import { QQ, ex, puiseuxRing } from '@symjs/symjs';
 *
 * const [R, x] = puiseuxRing('x, y', QQ);
 * x.pow(ex`1/2`).asExpr(); // => sqrt(x)
 * ```
 */
export class PuiseuxPoly {
  /**
   * The polynomial ring to which the elements belong.
   *
   * @see SymPy `sympy.polys.puiseux.PuiseuxPoly.ring`
   */
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
  /**
   * Exposes the polynomial in the internal integer-exponent representation.
   *
   * @returns The underlying polynomial.
   * @see SymPy `sympy.polys.puiseux.PuiseuxPoly.poly`
   */
  get poly(): PolyElement { return this.representation().poly; }
  /**
   * Identifies the monomial shift used to represent the Puiseux powers.
   *
   * @returns The shift vector or `NoMatch`.
   * @see SymPy `sympy.polys.puiseux.PuiseuxPoly.monom`
   */
  get monom(): readonly bigint[] | NoMatchResult {
    const m = this.representation().monom;
    return m.some((e) => e !== 0n) ? m : NoMatch;
  }
  /**
   * Lists the denominators needed to represent each generator's exponents.
   *
   * @returns The denominator vector or `NoMatch` when all are one.
   * @see SymPy `sympy.polys.puiseux.PuiseuxPoly.ns`
   */
  get ns(): readonly bigint[] | NoMatchResult {
    const ns = this.representation().ns;
    return ns.some((e) => e !== 1n) ? ns : NoMatch;
  }

  /**
   * Construct a Puiseux polynomial.
   *
   * @param poly - Polynomial to represent or transform.
   * @param ring - Polynomial ring supplying the generators and coefficient domain.
   * @throws RangeError when the exponent vector has the wrong length.
   */
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
  /**
   * Builds a Puiseux polynomial from its monomial-to-coefficient map.
   *
   * @param terms - Monomial and coefficient pairs.
   * @param ring - Polynomial ring supplying the generators and coefficient domain.
   * @returns The polynomial in this ring.
   * @see SymPy `sympy.polys.puiseux.PuiseuxPoly.from_dict`
   */
  static fromDict(terms: Iterable<PuiseuxTerm>, ring: PuiseuxRing): PuiseuxPoly { return ring.fromDict(terms); }
  /**
   * Counts the terms stored in the polynomial.
   *
   * @returns The term count.
   * @see SymPy `sympy.polys.puiseux.PuiseuxPoly.__len__`
   */
  get length(): number { return this.data.size; }
  /**
   * Tests for equality with the domain's additive identity.
   *
   * @returns True for zero.
   */
  get isZero(): boolean { return this.length === 0; }
  /**
   * Tests whether exactly one nonzero term occurs.
   *
   * @returns True for a single term.
   * @see SymPy `sympy.polys.puiseux.PuiseuxPoly.is_term`
   */
  get isTerm(): boolean { return this.length === 1; }
  /**
   * Tests for equality with the domain's multiplicative identity.
   *
   * @returns True for one.
   */
  get isOne(): boolean { return this.equals(this.ring.one); }
  /**
   * Looks up a monomial in the polynomial.
   *
   * @param monom - Exponent vector of the monomial.
   * @returns Its coefficient or zero.
   */
  get(monom: readonly ExprLike[]): Expr { return this.data.get(monomKey(monom.map(rationalExponent)))?.[1] ?? this.ring.domain.zero; }
  /**
   * Retrieves the coefficient of a stored monomial by its exponents.
   *
   * @param monom - Exponent vector of the monomial.
   * @returns The coefficient at the specified monomial.
   * @throws RangeError when the monomial has no stored coefficient.
   * @see SymPy `sympy.polys.puiseux.PuiseuxPoly.__getitem__`
   */
  getitem(monom: readonly ExprLike[]): Expr {
    const entry = this.data.get(monomKey(monom.map(rationalExponent)));
    if (entry === undefined) throw new RangeError('monomial is not present');
    return entry[1];
  }
  /**
   * Iterate over the exponent vectors of the stored terms.
   *
   * @returns An iterator over the Puiseux monomials.
   * @see SymPy `sympy.polys.puiseux.PuiseuxPoly.__iter__`
   */
  *[Symbol.iterator](): IterableIterator<PuiseuxMonom> { yield* this.monoms(); }
  /**
   * Enumerates the terms of the Puiseux polynomial.
   *
   * @returns The exponent-vector and coefficient pairs.
   * @see SymPy `sympy.polys.puiseux.PuiseuxPoly.terms`
   */
  terms(): [PuiseuxMonom, Expr][] { return [...this.data.values()].map(([m, c]) => [[...m], c]); }
  /**
   * Lists the monomials in the Puiseux polynomial.
   *
   * @returns The exponent vectors.
   * @see SymPy `sympy.polys.puiseux.PuiseuxPoly.monoms`
   */
  monoms(): PuiseuxMonom[] { return this.terms().map(([m]) => m); }
  /**
   * Indexes Puiseux coefficients by their rational exponent vectors.
   *
   * @returns The term map.
   * @see SymPy `sympy.polys.puiseux.PuiseuxPoly.to_dict`
   */
  toDict(): Map<PuiseuxMonom, Expr> { return new Map(this.terms()); }
  /**
   * Checks whether both operands represent the same value.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns Whether the comparison holds.
   * @see SymPy `sympy.polys.puiseux.PuiseuxPoly.__eq__`
   */
  equals(other: unknown): boolean {
    if (other instanceof PolyElement) return this.ring.polyRing.equals(other.ring) && this.equals(this.ring.fromPoly(other));
    if (other instanceof Expr || typeof other === 'number' || typeof other === 'bigint') {
      return this.length <= 1 && groundEq(this.get(this.ring.zeroMonom), sympify(other)) && (this.isZero || first(this.monoms()).every((e) => e.isZero));
    }
    if (!(other instanceof PuiseuxPoly)) return false;
    return this.ring.equals(other.ring) && this.length === other.length && this.terms().every(([m, c]) => groundEq(c, other.get(m)));
  }
  /**
   * Adds the two operands.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns Their sum.
   * @see SymPy `sympy.polys.puiseux.PuiseuxPoly.__add__`
   */
  add(other: PuiseuxPoly | ExprLike): PuiseuxPoly {
    return this.ring.fromDict([...this.terms(), ...this.ring.ringNew(other).terms()]);
  }
  /**
   * Negates the element with respect to addition.
   *
   * @returns The additive inverse.
   * @see SymPy `sympy.polys.puiseux.PuiseuxPoly.__neg__`
   */
  neg(): PuiseuxPoly { return this.ring.fromDict(this.terms().map(([m, c]) => [m, this.ring.domain.neg(c)])); }
  /**
   * Subtracts the second operand from the first.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns Their difference.
   * @see SymPy `sympy.polys.puiseux.PuiseuxPoly.__sub__`
   */
  sub(other: PuiseuxPoly | ExprLike): PuiseuxPoly { return this.add(this.ring.ringNew(other).neg()); }
  /**
   * Multiplies the two operands.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns Their product.
   * @see SymPy `sympy.polys.puiseux.PuiseuxPoly.__mul__`
   */
  mul(other: PuiseuxPoly | ExprLike): PuiseuxPoly {
    const q = this.ring.ringNew(other);
    return this.ring.fromDict(this.terms().flatMap(([m, c]) => q.terms().map(([n, d]): PuiseuxTerm => [m.map((e, i) => addExponents(e, at(n, i))), this.ring.domain.mul(c, d)])));
  }
  /**
   * Raises the element to the requested power.
   *
   * @param exponent - Power to which to raise the base.
   * @returns The exponentiated element.
   * @throws RangeError when a negative or fractional power is requested for a sum of terms or the coefficient does not admit the requested rational power or a coefficient to be inverted is not a unit.
   * @see SymPy `sympy.polys.puiseux.PuiseuxPoly.__pow__`
   */
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
  /**
   * Divides the first element by the second.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns The quotient.
   * @throws RangeError when the divisor is zero or the divisor has more than one term or a coefficient to be inverted is not a unit.
   * @see SymPy `sympy.polys.puiseux.PuiseuxPoly.__truediv__`
   */
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
  /**
   * Differentiates the Puiseux polynomial with respect to the selected generator.
   *
   * @param x - Polynomial generator.
   * @returns The partial derivative.
   * @see SymPy `sympy.polys.puiseux.PuiseuxPoly.diff`
   */
  diff(x: PuiseuxPoly): PuiseuxPoly {
    const i = this.ring.index(x);
    return this.ring.fromDict(this.terms().filter(([m]) => !at(m, i).isZero).map(([m, c]) => [m.map((e, j) => j === i ? addExponents(e, Rational.of(-1)) : e), this.ring.domain.mul(c, this.ring.domainNew(at(m, i)))]));
  }
  /**
   * Expresses the element in terms of its generators.
   *
   * @returns The symbolic expression.
   * @see SymPy `sympy.polys.puiseux.PuiseuxPoly.as_expr`
   */
  asExpr(): Expr {
    return add(...this.terms().map(([m, c]) => mul(this.ring.domain.toSympy(c), ...m.map((e, i) => pow(at(this.ring.symbols, i), e)))));
  }
  /**
   * Formats this object as text.
   *
   * @returns The formatted text.
   */
  toString(): string {
    const terms = this.terms().sort(([a], [b]) => {
      // Distinct map entries always differ in at least one exponent.
      return first(a.map((e, i) => compareExponents(e, at(b, i))).filter((c) => c !== 0));
    });
    return terms.map(([m, c]) => {
      const monom = m.flatMap((e, i) => e.isZero ? [] : [e.isOne ? str(at(this.ring.symbols, i)) : `${str(at(this.ring.symbols, i))}**${e.isInteger && e.isPositive ? str(e) : `(${str(e)})`}`]).join('*');
      if (!monom) return groundStr(this.ring.domain, c);
      return groundEq(c, this.ring.domain.one) ? monom : `${groundStr(this.ring.domain, c)}*${monom}`;
    }).join(' + ');
  }
}

/**
 * Construct a Puiseux ring and its generators.
 *
 * @param symbols - Symbols naming the generators, in order.
 * @param domain - Coefficient domain.
 * @returns The ring followed by its generators.
 * @see SymPy `sympy.polys.puiseux.puiseux_ring`
 * @example
 * ```ts
 * import { QQ, ex, puiseuxRing } from '@symjs/symjs';
 *
 * const [R, x] = puiseuxRing('x, y', QQ);
 * x.pow(ex`1/2`).asExpr(); // => sqrt(x)
 * ```
 */
export function puiseuxRing(symbols: RingSymbols, domain: DomainLike): [PuiseuxRing, ...PuiseuxPoly[]] {
  const ring = new PuiseuxRing(symbols, domain);
  return [ring, ...ring.gens];
}

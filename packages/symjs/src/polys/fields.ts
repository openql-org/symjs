// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/fields.py), Copyright (c) 2006-2023 SymPy
// Development Team, BSD 3-Clause License (see LICENSE).

/** @file Sparse rational function fields and their reduced polynomial fractions. */

import { NotImplementedError } from '../core/errors';
import { at, cast, first } from '../core/guard';
import { asNumerDenom } from '../core/methods';
import type { ExprLike } from '../core/nodes';
import { Add, Expr, Mul, Pow, Rational, Sym } from '../core/nodes';
import { mul, pow, sympify } from '../core/ops';
import type { IntLike } from '../ntheory/intutil';
import { str } from '../printing/str';
import { decomposePower } from '../simplify/exprtools';
import { fraction } from '../simplify/rational';
import { intArg } from './compatibility';
import { CoercionFailed, ZZ } from './domains';
import type { Domain } from './domains';
import { lex } from './orderings';
import type { MonomialOrdering } from './orderings';
import { PolyElement, PolyRing, ringHooks, sring } from './rings';
import type { DomainLike, OrderLike, RingSymbols, SringOptions } from './rings';
import { sortGens } from './sympoly';

/** Values accepted as rational function elements. */
export type FracInput = ExprLike | PolyElement | FracElement;
/** Generator/value pairs for evaluation or substitution. */
export type FracSubstitutions = readonly (readonly [FracElement, ExprLike])[];

/**
 * A multivariate rational function field K(x_1, ..., x_n).
 *
 * @see SymPy `sympy.polys.fields.FracField`
 */
export class FracField {
  /**
   * The polynomial ring to which the elements belong.
   *
   * @see SymPy `sympy.polys.fields.FracField.ring`
   */
  readonly ring: PolyRing;
  /**
   * The symbols naming the generators, in order.
   *
   * @see SymPy `sympy.polys.fields.FracField.symbols`
   */
  readonly symbols: readonly Expr[];
  /**
   * The coefficient domain.
   *
   * @see SymPy `sympy.polys.fields.FracField.domain`
   */
  readonly domain: Domain;
  /**
   * The monomial order.
   *
   * @see SymPy `sympy.polys.fields.FracField.order`
   */
  readonly order: MonomialOrdering;
  /**
   * The number of generators.
   *
   * @see SymPy `sympy.polys.fields.FracField.ngens`
   */
  readonly ngens: number;
  /**
   * The ordered generators.
   *
   * @see SymPy `sympy.polys.fields.FracField.gens`
   */
  readonly gens: readonly FracElement[];

  /**
   * Construct a rational function field.
   *
   * @param symbols - Symbols naming the generators, in order.
   * @param domain - Coefficient domain.
   * @param order - Monomial order used to compare terms.
   */
  constructor(symbols: RingSymbols, domain: DomainLike = ZZ, order: OrderLike = lex) {
    this.ring = new PolyRing(symbols, domain, order);
    this.symbols = this.ring.symbols;
    this.domain = this.ring.domain;
    this.order = this.ring.order;
    this.ngens = this.ring.ngens;
    this.gens = this.ring.gens.map((g) => this.rawNew(g));
  }

  /**
   * The printable representation.
   *
   * @returns The formatted text.
   * @see SymPy `sympy.polys.fields.FracField.__str__`
   */
  toString(): string {
    return `Rational function field in ${this.symbols.map((s) => str(s)).join(', ')} over ${String(this.domain)} with ${String(this.order)} order`;
  }
  /**
   * Whether the operand represents the same value.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns Whether the comparison holds.
   * @see SymPy `sympy.polys.fields.FracField.__eq__`
   */
  equals(other: unknown): boolean {
    return other instanceof FracField && this.ring.equals(other.ring);
  }
  /**
   * True if `element` is an element of this field. False otherwise.
   *
   * @param element - Value to coerce into the domain.
   * @returns Whether the operand belongs to this ring or field.
   * @see SymPy `sympy.polys.fields.FracField.is_element`
   */
  isElement(element: unknown): boolean {
    return element instanceof FracElement && this.equals(element.field);
  }
  /**
   * The position of a generator.
   *
   * @param gen - Generator or its index.
   * @returns The position of a generator.
   * @throws RangeError when the element belongs to a different field.
   * @see SymPy `sympy.polys.fields.FracField.index`
   */
  index(gen: FracElement): number {
    if (!this.isElement(gen)) throw new RangeError('expected an element of this field');
    return this.ring.index(gen.toPoly());
  }
  /**
   * The additive identity.
   *
   * @returns The additive identity.
   * @see SymPy `sympy.polys.fields.FracField.zero`
   */
  get zero(): FracElement { return this.rawNew(this.ring.zero); }
  /**
   * The multiplicative identity.
   *
   * @returns The multiplicative identity.
   * @see SymPy `sympy.polys.fields.FracField.one`
   */
  get one(): FracElement { return this.rawNew(this.ring.one); }

  /**
   * Construct a fraction without cancellation, as in SymPy raw_new.
   *
   * @param numer - Numerator polynomial.
   * @param denom - Denominator polynomial.
   * @returns The fraction with the supplied numerator and denominator.
   * @see SymPy `sympy.polys.fields.FracField.raw_new`
   */
  rawNew(numer: PolyElement, denom: PolyElement = this.ring.one): FracElement {
    return new FracElement(this, numer, denom);
  }
  /**
   * Cancel the common factors and normalize the denominator's unit.
   *
   * @param numer - Numerator polynomial.
   * @param denom - Denominator polynomial.
   * @returns The normalized fraction.
   * @throws RangeError when the denominator is zero.
   * @see SymPy `sympy.polys.fields.FracField.new`
   */
  new(numer: PolyElement, denom: PolyElement = this.ring.one): FracElement {
    const n = numer.setRing(this.ring), d = denom.setRing(this.ring);
    if (d.isZero) throw new RangeError('zero denominator');
    return this.rawNew(...n.cancel(d));
  }
  /**
   * Coerce a value into the coefficient domain.
   *
   * @param element - Value to coerce into the domain.
   * @returns Coerce a value into the coefficient domain.
   * @see SymPy `sympy.polys.fields.FracField.domain_new`
   */
  domainNew(element: ExprLike): Expr { return this.ring.domainNew(element); }

  /**
   * A ground element, including fractions of a non-field ground domain.
   *
   * @param element - Value to coerce into the domain.
   * @returns The corresponding constant element.
   * @see SymPy `sympy.polys.fields.FracField.ground_new`
   */
  groundNew(element: ExprLike): FracElement {
    try { return this.new(this.ring.groundNew(element)); }
    catch (error) {
      if (!(error instanceof CoercionFailed) || this.domain.isField) throw error;
      const e = this.domain.getField().fromSympy(element);
      const [n, d] = fraction(e);
      return this.new(this.ring.groundNew(n), this.ring.groundNew(d));
    }
  }

  /**
   * Convert an element, expression, or [numerator, denominator] polynomial pair.
   *
   * @param element - Value to coerce into the domain.
   * @returns The corresponding element of this fraction field.
   * @throws NotImplementedError when the source and target fraction fields differ or the requested input syntax is unsupported.
   * @see SymPy `sympy.polys.fields.FracField.field_new`
   */
  fieldNew(element: FracInput | string | readonly [PolyElement | ExprLike, PolyElement | ExprLike]): FracElement {
    if (element instanceof FracElement) {
      if (this.isElement(element)) return element;
      if (element.field.symbols.every((s) => this.domain.symbols.some((t) => t.key === s.key))) return this.groundNew(element.asExpr());
      throw new NotImplementedError('conversion between different fields; use setField');
    }
    if (element instanceof PolyElement) return this.fromExpr(element.asExpr());
    if (typeof element === 'string') throw new NotImplementedError('parsing');
    if (element instanceof Expr || typeof element === 'number' || typeof element === 'bigint') return this.fromExpr(element);
    return this.new(this.ring.ringNew(element[0]), this.ring.ringNew(element[1]));
  }

  /**
   * Convert a symbolic rational function to an element of this field.
   *
   * @param expression - Expression to convert.
   * @returns The rational function as a fraction field element.
   * @throws RangeError when the expression cannot be converted to a rational function in this field.
   * @see SymPy `sympy.polys.fields.FracField.from_expr`
   */
  fromExpr(expression: ExprLike): FracElement {
    const rebuild = (e: Expr): FracElement => {
      const i = this.symbols.findIndex((s) => s.key === e.key);
      if (i >= 0) return at(this.gens, i);
      if (e instanceof Add) return e.args.map(rebuild).reduce((a, b) => a.add(b));
      if (e instanceof Mul) return e.args.map(rebuild).reduce((a, b) => a.mul(b));
      if (e instanceof Pow) {
        for (const [j, g] of this.symbols.entries()) {
          if (g instanceof Pow && g.base.key === e.base.key) {
            const q = mul(e.exp, pow(g.exp, -1));
            if (q instanceof Rational && q.isInteger) return at(this.gens, j).pow(q);
          }
        }
        if (e.exp instanceof Rational && e.exp.isInteger) return rebuild(e.base).pow(e.exp);
      }
      const reciprocal = this.symbols.findIndex((s) => s.key === pow(e, -1).key);
      if (reciprocal >= 0) return at(this.gens, reciprocal).pow(-1);
      return this.groundNew(e);
    };
    try { return rebuild(sympify(expression)); }
    catch (error) {
      if (!(error instanceof CoercionFailed)) throw error;
      throw new RangeError(`expected an expression convertible to a rational function in ${String(this)}, got ${str(sympify(expression))}`);
    }
  }

  /**
   * The polynomial ring with the same generators and coefficient domain.
   *
   * @returns The polynomial ring with the same generators and coefficient domain.
   * @see SymPy `sympy.polys.fields.FracField.to_ring`
   */
  toRing(): PolyRing { return this.ring; }
  /**
   * Convert to a fraction-field domain over the same coefficient domain.
   *
   * @returns The coefficient domain corresponding to this fraction field.
   * @throws NotImplementedError when the generators are not symbols.
   * @see SymPy `sympy.polys.fields.FracField.to_domain`
   */
  toDomain(): Domain {
    if (!this.symbols.every((s) => s instanceof Sym)) {
      throw new NotImplementedError('fraction-field domain conversion requires symbol generators');
    }
    return this.domain.fracField(...this.symbols);
  }
}

/**
 * A sparse polynomial fraction. Arithmetic returns reduced fractions.
 *
 * @see SymPy `sympy.polys.fields.FracElement`
 */
export class FracElement {
  /**
   * The numerator polynomial.
   *
   * @see SymPy `sympy.polys.fields.FracElement.numer`
   */
  readonly numer: PolyElement;
  /**
   * The denominator polynomial.
   *
   * @see SymPy `sympy.polys.fields.FracElement.denom`
   */
  readonly denom: PolyElement;
  /**
   * Construct a fraction from polynomial numerator and denominator.
   *
   * @param field - The target coefficient field.
   * @param numer - Numerator polynomial.
   * @param denom - Denominator polynomial.
   * @throws RangeError when the denominator is zero.
   */
  constructor(
    /** The fraction field containing the element. @see SymPy `sympy.polys.fields.FracElement.field` */
    readonly field: FracField, numer: PolyElement, denom: PolyElement = field.ring.one) {
    this.numer = numer.setRing(field.ring);
    this.denom = denom.setRing(field.ring);
    if (this.denom.isZero) throw new RangeError('zero denominator');
  }
  /**
   * Whether the element is zero.
   *
   * @returns Whether the element is zero.
   */
  get isZero(): boolean { return this.numer.isZero; }
  /**
   * The polynomial represented by a fraction with unit denominator.
   *
   * @returns The polynomial represented by a fraction with unit denominator.
   * @throws RangeError when the reduced denominator is not one.
   * @see SymPy `sympy.polys.fields.FracElement.to_poly`
   */
  toPoly(): PolyElement {
    if (!this.denom.equals(1)) throw new RangeError('denominator should be 1');
    return this.numer;
  }
  /**
   * The domain containing the element.
   *
   * @returns The domain containing the element.
   * @see SymPy `sympy.polys.fields.FracElement.parent`
   */
  parent(): Domain { return this.field.toDomain(); }
  /**
   * A copy of this element.
   *
   * @returns A copy of this element.
   * @see SymPy `sympy.polys.fields.FracElement.copy`
   */
  copy(): FracElement { return this.rawNew(this.numer, this.denom); }
  /**
   * Construct a fraction from its numerator and denominator without cancellation.
   *
   * @param numer - Numerator polynomial.
   * @param denom - Denominator polynomial.
   * @returns The fraction with the supplied numerator and denominator.
   * @see SymPy `sympy.polys.fields.FracElement.raw_new`
   */
  rawNew(numer: PolyElement, denom: PolyElement = this.field.ring.one): FracElement { return this.field.rawNew(numer, denom); }
  /**
   * Construct a reduced fraction from its numerator and denominator.
   *
   * @param numer - Numerator polynomial.
   * @param denom - Denominator polynomial.
   * @returns The normalized fraction.
   * @see SymPy `sympy.polys.fields.FracElement.new`
   */
  new(numer: PolyElement, denom: PolyElement): FracElement { return this.field.new(numer, denom); }
  /**
   * Express the fraction in the specified field.
   *
   * @param field - The target coefficient field.
   * @returns Express the fraction in the specified field.
   * @see SymPy `sympy.polys.fields.FracElement.set_field`
   */
  setField(field: FracField): FracElement {
    return this.field.equals(field) ? this : field.new(this.numer.setRing(field.ring), this.denom.setRing(field.ring));
  }
  /**
   * The corresponding symbolic expression.
   *
   * @param symbols - Symbols naming the generators, in order.
   * @returns The symbolic expression.
   * @see SymPy `sympy.polys.fields.FracElement.as_expr`
   */
  asExpr(...symbols: Expr[]): Expr { return mul(this.numer.asExpr(...symbols), pow(this.denom.asExpr(...symbols), -1)); }
  /**
   * Whether the operand represents the same value.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns Whether the comparison holds.
   * @see SymPy `sympy.polys.fields.FracElement.__eq__`
   */
  equals(other: unknown): boolean {
    return other instanceof FracElement && this.field.equals(other.field)
      ? this.numer.equals(other.numer) && this.denom.equals(other.denom)
      : this.denom.equals(1) && this.numer.equals(other);
  }
  /**
   * The printable representation.
   *
   * @returns The formatted text.
   * @see SymPy `sympy.polys.fields.FracElement.__str__`
   */
  toString(): string {
    const n = String(this.numer), d = String(this.denom);
    if (this.denom.equals(1)) return n;
    const numerator = this.numer.length > 1 ? `(${n})` : n;
    const denominator = this.denom.isGenerator || this.denom.isGround ? d : `(${d})`;
    return `${numerator}/${denominator}`;
  }
  /**
   * The additive inverse.
   *
   * @returns The additive inverse.
   * @see SymPy `sympy.polys.fields.FracElement.__neg__`
   */
  neg(): FracElement { return this.rawNew(this.numer.neg(), this.denom); }
  /**
   * The sum of the operands.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns The sum of the operands.
   * @see SymPy `sympy.polys.fields.FracElement.__add__`
   */
  add(other: FracInput): FracElement {
    const g = this.field.fieldNew(other);
    return this.new(this.numer.mul(g.denom).add(g.numer.mul(this.denom)), this.denom.mul(g.denom));
  }
  /**
   * The difference of the operands.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns The difference of the operands.
   * @see SymPy `sympy.polys.fields.FracElement.__sub__`
   */
  sub(other: FracInput): FracElement { return this.add(this.field.fieldNew(other).neg()); }
  /**
   * The product of the operands.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns The product of the operands.
   * @see SymPy `sympy.polys.fields.FracElement.__mul__`
   */
  mul(other: FracInput): FracElement {
    const g = this.field.fieldNew(other);
    return this.new(this.numer.mul(g.numer), this.denom.mul(g.denom));
  }
  /**
   * The quotient of the operands.
   *
   * @param other - Operand to combine or compare with this value.
   * @returns The quotient of the operands.
   * @see SymPy `sympy.polys.fields.FracElement.__truediv__`
   */
  div(other: FracInput): FracElement {
    const g = this.field.fieldNew(other);
    return this.new(this.numer.mul(g.denom), this.denom.mul(g.numer));
  }
  /**
   * The element raised to the specified exponent.
   *
   * @param exponent - Power to which to raise the base.
   * @returns The element raised to the specified exponent.
   * @see SymPy `sympy.polys.fields.FracElement.__pow__`
   */
  pow(exponent: IntLike): FracElement {
    const n = intArg(exponent, 'exponent');
    return n < 0 ? this.rawNew(this.denom.pow(-n), this.numer.pow(-n)) : this.rawNew(this.numer.pow(n), this.denom.pow(n));
  }
  /**
   * Computes partial derivative in `x`.
   *
   * @param gen - Generator or its index.
   * @returns Partial derivative in `x`.
   * @see SymPy `sympy.polys.fields.FracElement.diff`
   */
  diff(gen: FracElement): FracElement {
    const i = this.field.index(gen);
    return this.new(this.numer.diff(i).mul(this.denom).sub(this.numer.mul(this.denom.diff(i))), this.denom.pow(2));
  }

  /**
   * Substitute ground values, keeping the same field.
   *
   * @param gen - Generator or its index.
   * @param value - Value to convert.
   * @returns Apply the indicated substitutions to the root sum.
   * @see SymPy `sympy.polys.fields.FracElement.subs`
   */
  subs(gen: FracElement | FracSubstitutions, value?: ExprLike): FracElement {
    const pairs = this.pairs(gen, value);
    return this.new(this.numer.subs(pairs), this.denom.subs(pairs));
  }
  /**
   * Evaluate ground values and remove their generators from the result field.
   *
   * @param gen - Generator or its index.
   * @param value - Value to convert.
   * @returns Evaluate ground values and remove their generators from the result field.
   * @throws RangeError when the denominator is zero.
   * @see SymPy `sympy.polys.fields.FracElement.evaluate`
   */
  evaluate(gen: FracElement | FracSubstitutions, value?: ExprLike): FracElement | Expr {
    const pairs = this.pairs(gen, value);
    const n = this.numer.evaluate(pairs), d = this.denom.evaluate(pairs);
    if (n instanceof PolyElement) return new FracField(n.ring.symbols, n.ring.domain, n.ring.order).new(n, cast(d, PolyElement));
    // SymPy 1.14 raises AttributeError when the last generator is evaluated
    // (its upstream test is XFAIL). The exact ground quotient is well-defined.
    const denominator = cast(d, Expr);
    if (this.field.domain.isZero(denominator)) throw new RangeError('zero denominator');
    return this.field.domain.quo(n, denominator);
  }
  /**
   * Evaluate the rational function at the supplied values.
   *
   * @param values - Values to substitute, in generator order.
   * @returns Evaluate the rational function at the supplied values.
   * @throws RangeError when the number of evaluation values is outside the range from one to the number of generators.
   * @see SymPy `sympy.polys.fields.FracElement.__call__`
   */
  call(...values: ExprLike[]): FracElement | Expr {
    if (!values.length || values.length > this.field.ngens) throw new RangeError(`expected at least 1 and at most ${this.field.ngens} values`);
    return this.evaluate(values.map((v, i) => [at(this.field.gens, i), v]));
  }
  /**
   * Request composition by substituting a rational function for a generator.
   *
   * @param _gen - Generator or its index.
   * @param _value - Value to convert.
   * @throws NotImplementedError when composition of rational functions is requested.
   * @see SymPy `sympy.polys.fields.FracElement.compose`
   */
  compose(_gen: FracElement, _value: FracInput): never { throw new NotImplementedError('rational function composition'); }

  private pairs(gen: FracElement | FracSubstitutions, value: ExprLike | undefined): (readonly [number, ExprLike])[] {
    if (gen instanceof FracElement) {
      if (value === undefined) throw new TypeError('expected a substitution value');
      return [[this.field.index(gen), value]];
    }
    return gen.map(([g, v]) => [this.field.index(g), v]);
  }
}

/**
 * Construct a field and its generators.
 *
 * @param symbols - Symbols naming the generators, in order.
 * @param domain - Coefficient domain.
 * @param order - Monomial order used to compare terms.
 * @returns The fraction field containing the element.
 * @see SymPy `sympy.polys.fields.field`
 */
export function field(symbols: RingSymbols, domain: DomainLike = ZZ, order: OrderLike = lex): [FracField, ...FracElement[]] {
  const F = new FracField(symbols, domain, order);
  return [F, ...F.gens];
}
/**
 * Construct a field and an array of its generators.
 *
 * @param symbols - Symbols naming the generators, in order.
 * @param domain - Coefficient domain.
 * @param order - Monomial order used to compare terms.
 * @returns The field and an ordered array of its generators.
 * @see SymPy `sympy.polys.fields.xfield`
 */
export function xfield(symbols: RingSymbols, domain: DomainLike = ZZ, order: OrderLike = lex): [FracField, FracElement[]] {
  const F = new FracField(symbols, domain, order);
  return [F, [...F.gens]];
}
/**
 * Construct a rational function field with generators accessible through `gens`.
 *
 * @param symbols - Symbols naming the generators, in order.
 * @param domain - Coefficient domain.
 * @param order - Monomial order used to compare terms.
 * @returns The fraction field.
 * @see SymPy `sympy.polys.fields.vfield`
 */
export function vfield(symbols: RingSymbols, domain: DomainLike = ZZ, order: OrderLike = lex): FracField {
  return new FracField(symbols, domain, order);
}
/**
 * Infer generators and the coefficient domain from numerators and denominators.
 *
 * @param exprs - Expressions to convert, with a common generator order.
 * @param rest - Additional generators and polynomial construction options.
 * @returns The inferred fraction field and its element or array of elements.
 * @see SymPy `sympy.polys.fields.sfield`
 * @remarks SymPy writes the equivalent expression as `(4*x**2 + x*log(x))*exp(1/x)/x**(5/3)`.
 * @example
 * ```ts
 * import { ex, sfield } from '@symjs/symjs';
 *
 * sfield(ex`(4*x**2 + x*log(x))*exp(1/x)/x**(5/3)`)[1].asExpr(); // => (4*x**2*exp(1/x) + x*exp(1/x)*log(x))/x**(5/3)
 * ```
 */
export function sfield(exprs: ExprLike, ...rest: (Expr | SringOptions)[]): [FracField, FracElement];
/**
 * Infer generators and the coefficient domain from numerators and denominators.
 *
 * @param exprs - Expressions to convert, with a common generator order.
 * @param rest - Additional generators and polynomial construction options.
 * @returns The inferred fraction field and its element or array of elements.
 * @see SymPy `sympy.polys.fields.sfield`
 */
export function sfield(exprs: readonly ExprLike[], ...rest: (Expr | SringOptions)[]): [FracField, FracElement[]];
export function sfield(exprs: ExprLike | readonly ExprLike[], ...rest: (Expr | SringOptions)[]): [FracField, FracElement | FracElement[]] {
  const single = exprs instanceof Expr || typeof exprs === 'number' || typeof exprs === 'bigint';
  const es = single ? [exprs] : exprs;
  const [ring, polys] = sring(es.flatMap((e) => asNumerDenom(e)), ...rest);
  // SymPy's polynomial dictionary extraction takes integer powers out of
  // generators: x**(2/3) generates x**(1/3), exp(2*x) generates exp(x).
  const explicit = rest.some((r) => r instanceof Expr);
  const powers = ring.symbols.map((g): [Expr, number] => explicit ? [g, 1] : decomposePower(g));
  const gens = explicit ? ring.symbols : sortGens([...new Map(powers.map(([b]) => [b.key, b])).values()]);
  const F = new FracField(gens, ring.domain, ring.order);
  const convert = (p: PolyElement): PolyElement => F.ring.fromTerms(p.listterms().map(([m,c]) => {
    const monom = gens.map(() => 0);
    powers.forEach(([g, k], i) => { const j = gens.findIndex((h) => h.key === g.key); monom[j] = at(monom, j) + at(m, i)*k; });
    return [monom, c];
  }));
  const values = es.map((_, i) => F.new(convert(at(polys, 2*i)), convert(at(polys, 2*i+1))));
  return [F, single ? first(values) : values];
}

ringHooks.toField = (ring) => new FracField(ring.symbols, ring.domain, ring.order);

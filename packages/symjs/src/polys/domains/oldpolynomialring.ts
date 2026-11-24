// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/domains/old_polynomialring.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause (see LICENSE).

import { NotImplementedError } from '../../core/errors';
import { defined } from '../../core/guard';
import type { Expr, ExprLike, Sym } from '../../core/nodes';
import { mul, pow, sympify } from '../../core/ops';
import { fraction, together } from '../../simplify/rational';
import { str } from '../../printing/str';
import { CoercionFailed, Domain, domainHooks } from '../domains';
import { PolyRing, type OrderLike } from '../rings';
import type { MonomialOrdering } from '../orderings';

/** Polynomial presentation used by module standard bases. @internal */
export interface PolynomialModuleContext {
  readonly polynomialRing: Domain;
  readonly domain: Domain;
  readonly symbols: readonly Sym[];
  readonly order: MonomialOrdering;
  readonly relations: readonly Expr[];
}
const contexts = new WeakMap<Domain, PolynomialModuleContext>();
/** Register a polynomial or quotient presentation. @internal */
export function registerModuleContext(ring: Domain, context: PolynomialModuleContext): void {
  contexts.set(ring, context);
}
/** Polynomial presentation of a supported coefficient ring. @internal */
export function polynomialModuleContext(ring: Domain): PolynomialModuleContext {
  const context = contexts.get(ring);
  if (!context) throw new NotImplementedError(`modules over ${ring.toString()} are not implemented`);
  return context;
}

/**
 * Represents a multivariate polynomial ring with the monomial ordering used for module and ideal
 * operations.
 *
 * @see SymPy `sympy.polys.domains.old_polynomialring.PolynomialRingBase`
 */
export class PolynomialRingBase extends Domain {
  /**
   * Indicates whether the domain supports field arithmetic.
   *
   * @see SymPy `sympy.polys.domains.old_polynomialring.PolynomialRingBase.is_Field`
   */
  readonly isField = false;
  /** The identifier for the underlying coefficient domain. */
  readonly ground;
  /**
   * The monomial order for polynomial comparisons.
   *
   * @see SymPy `sympy.polys.domains.old_polynomialring.PolynomialRingBase.order`
   */
  readonly order: MonomialOrdering;
  private readonly polynomialRing: PolyRing;
  /**
   * Constructs a polynomial ring with ordered generators and a monomial ordering.
   *
   * @param coefficientDomain - Domain of polynomial coefficients.
   * @param symbols - Polynomial generators.
   * @param order - Monomial ordering.
   */
  constructor(
    /** The domain of the polynomial coefficients. */
    readonly coefficientDomain: Domain,
    /**
     * The ordered polynomial generators.
     *
     * @see SymPy `sympy.polys.domains.old_polynomialring.PolynomialRingBase.symbols`
     */
    override readonly symbols: readonly Sym[], order: OrderLike = 'grevlex') {
    super();
    this.ground = coefficientDomain.ground;
    this.polynomialRing = new PolyRing(symbols, coefficientDomain, order);
    this.order = this.polynomialRing.order;
    registerModuleContext(this, { polynomialRing: this, domain: coefficientDomain, symbols, order: this.order, relations: [] });
  }
  /**
   * The underlying coefficient domain.
   *
   * @returns The underlying coefficient domain.
   * @see SymPy `sympy.polys.domains.old_polynomialring.PolynomialRingBase.dom`
   */
  override get dom(): Domain { return this.coefficientDomain; }
  /**
   * Formats the value as text.
   *
   * @returns The printable representation.
   * @see SymPy `sympy.polys.domains.old_polynomialring.PolynomialRingBase.__str__`
   */
  toString(): string {
    return `${this.dom.toString()}[${this.symbols.map(str).join(',')}]${this.order.isGlobal === true ? '' : ` order=${this.order.toString()}`}`;
  }
  /**
   * Compares the two operands for equality.
   *
   * @param other - Value to compare against.
   * @returns Whether the operands are equal.
   * @see SymPy `sympy.polys.domains.old_polynomialring.PolynomialRingBase.__eq__`
   */
  override equals(other: Domain): boolean {
    return other instanceof PolynomialRingBase && this.toString() === other.toString() && this.order.toString() === other.order.toString();
  }
  /**
   * Reduces the expression to the canonical form for this domain.
   *
   * @param e - Expression to represent in this domain.
   * @returns The canonical expression in this domain.
   */
  canon(e: Expr): Expr { return this.fromSympy(e); }
  /**
   * Interprets a symbolic expression in this domain.
   *
   * @param e - Expression to represent in this domain.
   * @returns The expression converted into the domain.
   * @throws CoercionFailed when the value cannot be represented in the target domain.
   * @see SymPy `sympy.polys.domains.old_polynomialring.PolynomialRingBase.from_sympy`
   */
  fromSympy(e: ExprLike): Expr {
    try {
      if (this.order.isGlobal === true) return this.polynomialRing.fromExpr(e).asExpr();
      const [n, d] = fraction(together(sympify(e)));
      const numerator = this.polynomialRing.fromExpr(n), denominator = this.polynomialRing.fromExpr(d);
      if (denominator.isZero) throw new CoercionFailed('denominator is zero');
      const [num, den] = numerator.cancel(denominator);
      if (den.LM.some((k) => k !== 0)) throw new CoercionFailed('denominator is not a local unit');
      return mul(num.asExpr(), pow(den.asExpr(), -1));
    }
    catch {
      throw new CoercionFailed(`cannot convert to ${this.toString()}`);
    }
  }
  /**
   * Finds the field associated with this domain.
   *
   * @returns The associated field.
   * @see SymPy `sympy.polys.domains.old_polynomialring.PolynomialRingBase.get_field`
   */
  getField(): Domain {
    return this.dom.symbols.length ? defined(domainHooks.compositeField, 'composite domains')(this.dom, this.symbols) : this.dom.fracField(...this.symbols);
  }
  /**
   * The ring over another coefficient domain, with the same generators and order.
   *
   * @param K - Coefficient domain for the values.
   * @returns The ring over the replacement domain.
   * @see SymPy `sympy.polys.domains.old_polynomialring.PolynomialRingBase.set_domain`
   */
  setDomain(K: Domain): PolynomialRingBase {
    return new PolynomialRingBase(K, this.symbols, this.order);
  }
  /**
   * The units: the constants that are units of the coefficient domain, and for a local order the
   * elements with such a constant term.
   *
   * @param a - Element on which to operate.
   * @returns Whether the element has a multiplicative inverse.
   * @see SymPy `sympy.polys.domains.old_polynomialring.PolynomialRingBase.is_unit`
   */
  override isUnit(a: unknown): boolean {
    const [n] = fraction(together(this.toSympy(this.convert(a))));
    const p = this.polynomialRing.fromExpr(n);
    if (p.LM.some((degree) => degree !== 0)) return false;
    return this.dom.isUnit(this.dom.convert(p.const()));
  }
  protected override get compositeParts(): readonly [Domain, readonly Sym[]] {
    return [this.dom, this.symbols];
  }
  protected override recompose(K: Domain, gens: readonly Sym[]): Domain {
    return new PolynomialRingBase(K, gens, this.order);
  }
  /**
   * Indicates whether an associated ring is available.
   *
   * @returns Whether the domain has an associated ring.
   * @see SymPy `sympy.polys.domains.old_polynomialring.PolynomialRingBase.has_assoc_Ring`
   */
  override get hasAssocRing(): boolean {
    return true;
  }
  /**
   * Indicates whether operations in this domain use exact arithmetic.
   *
   * @returns Whether arithmetic in the domain is exact.
   * @see SymPy `sympy.polys.domains.old_polynomialring.PolynomialRingBase.is_Exact`
   */
  override get isExact(): boolean {
    return this.dom.isExact;
  }
  /**
   * Finds the exact domain associated with this coefficient domain.
   *
   * @returns The associated exact domain.
   * @see SymPy `sympy.polys.domains.old_polynomialring.PolynomialRingBase.get_exact`
   */
  override getExact(): Domain {
    return this.setDomain(this.dom.getExact());
  }
  /**
   * Checks the characteristic of the coefficient ring.
   *
   * @returns Whether the characteristic is zero.
   * @see SymPy `sympy.polys.domains.old_polynomialring.PolynomialRingBase.has_CharacteristicZero`
   */
  override get hasCharacteristicZero(): boolean {
    return this.dom.hasCharacteristicZero;
  }
  /**
   * Returns the characteristic of the coefficient domain.
   *
   * @returns The characteristic of the coefficient domain.
   * @see SymPy `sympy.polys.domains.old_polynomialring.PolynomialRingBase.characteristic`
   */
  override characteristic(): bigint {
    return this.dom.characteristic();
  }
}

domainHooks.polynomialRing = (K, gens) => new PolynomialRingBase(K, gens);

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/matrices/domainscalar.py), Copyright (c)
// 2006-2023 SymPy Development Team, BSD 3-Clause License (see LICENSE).

/**
 * @file A domain element together with its domain (SymPy DomainScalar),
 * as DomainMatrix indexing and clear_denoms return it.
 */

import { first } from '../../core/guard';
import type { Expr, ExprLike } from '../../core/nodes';
import { Rational } from '../../core/nodes';
import { Domain, ZZ } from '../domains';
import { asInt, type IntLike } from '../../ntheory/intutil';
import { convertFrom, div, domainOfExprs, elemEq, elemRepr, rem } from './domainops';

/**
 * An element of a domain.
 *
 * @see SymPy `sympy.polys.matrices.domainscalar.DomainScalar`
 */
export class DomainScalar {
  /**
   * Pairs a scalar value with the coefficient domain that interprets it.
   *
   * @param element - Element to represent or transform.
   * @param domain - Coefficient domain for the values.
   * @throws TypeError when the domain is not a coefficient domain.
   */
  constructor(
    /**
     * The value in the scalar’s coefficient domain.
     *
     * @see SymPy `sympy.polys.matrices.domainscalar.DomainScalar.element`
     */
    readonly element: Expr,
    /**
     * The coefficient domain.
     *
     * @see SymPy `sympy.polys.matrices.domainscalar.DomainScalar.domain`
     */
    readonly domain: Domain,
  ) {
    if (!(domain instanceof Domain)) throw new TypeError('expected a coefficient domain');
  }
  /**
   * Pairs a scalar with the coefficient domain in which to perform arithmetic.
   *
   * @param element - Element to represent or transform.
   * @param domain - Coefficient domain for the values.
   * @returns The newly constructed element.
   * @see SymPy `sympy.polys.matrices.domainscalar.DomainScalar.new`
   */
  static new(element: Expr, domain: Domain): DomainScalar {
    return new DomainScalar(element, domain);
  }
  /**
   * The scalar of an expression over the domain construct_domain chooses.
   *
   * @param expr - Expression to represent.
   * @returns The expression converted into the domain.
   * @see SymPy `sympy.polys.matrices.domainscalar.DomainScalar.from_sympy`
   */
  static fromSympy(expr: ExprLike): DomainScalar {
    const [domain, elements] = domainOfExprs([expr]);
    return new DomainScalar(first(elements), domain);
  }
  /**
   * Displays the element using its coefficient domain’s representation.
   *
   * @returns The printable representation.
   * @see SymPy `sympy.polys.matrices.domainscalar.DomainScalar.__repr__`
   */
  toString(): string {
    return elemRepr(this.domain, this.element);
  }
  /**
   * Expresses the value using symbolic expression nodes.
   *
   * @returns The corresponding symbolic expression.
   * @see SymPy `sympy.polys.matrices.domainscalar.DomainScalar.to_sympy`
   */
  toSympy(): Expr {
    return this.domain.toSympy(this.element);
  }
  /**
   * The scalar over another domain.
   *
   * @param domain - Destination coefficient domain.
   * @returns The scalar in the requested coefficient domain.
   * @see SymPy `sympy.polys.matrices.domainscalar.DomainScalar.to_domain`
   */
  toDomain(domain: Domain): DomainScalar {
    return new DomainScalar(convertFrom(domain, this.element, this.domain), domain);
  }
  /**
   * Converts the coefficients to the specified domain.
   *
   * @param domain - Coefficient domain for the values.
   * @returns The value over the target domain.
   * @see SymPy `sympy.polys.matrices.domainscalar.DomainScalar.convert_to`
   */
  convertTo(domain: Domain): DomainScalar {
    return this.toDomain(domain);
  }
  /**
   * Both scalars over their unified domain.
   *
   * @param other - Operand to convert to a common module or coefficient domain.
   * @returns The operands over a common domain.
   * @see SymPy `sympy.polys.matrices.domainscalar.DomainScalar.unify`
   */
  unify(other: DomainScalar): [DomainScalar, DomainScalar] {
    const domain = this.domain.unify(other.domain);
    return [this.toDomain(domain), other.toDomain(domain)];
  }
  /**
   * Tests whether this scalar differs from the additive identity.
   *
   * @returns Whether the value differs from zero.
   * @see SymPy `sympy.polys.matrices.domainscalar.DomainScalar.__bool__`
   */
  get isNonzero(): boolean {
    return !this.domain.isZero(this.element);
  }
  /**
   * Adds the other operand to this value.
   *
   * @param other - Addend.
   * @returns The sum of the operands.
   * @see SymPy `sympy.polys.matrices.domainscalar.DomainScalar.__add__`
   */
  add(other: DomainScalar): DomainScalar {
    const [a, b] = this.unify(other);
    return new DomainScalar(a.domain.add(a.element, b.element), a.domain);
  }
  /**
   * Subtracts the other operand from this value.
   *
   * @param other - Value to subtract.
   * @returns The difference in operand order.
   * @see SymPy `sympy.polys.matrices.domainscalar.DomainScalar.__sub__`
   */
  sub(other: DomainScalar): DomainScalar {
    const [a, b] = this.unify(other);
    return new DomainScalar(a.domain.sub(a.element, b.element), a.domain);
  }
  /**
   * Multiplies this value by the factor on its right.
   *
   * @param otherIn - Factor on the right.
   * @returns The product in operand order.
   * @see SymPy `sympy.polys.matrices.domainscalar.DomainScalar.__mul__`
   */
  mul(otherIn: DomainScalar | number | bigint): DomainScalar {
    const other = otherIn instanceof DomainScalar ? otherIn : new DomainScalar(Rational.of(BigInt(otherIn)), ZZ);
    const [a, b] = this.unify(other);
    return new DomainScalar(a.domain.mul(a.element, b.element), a.domain);
  }
  /**
   * Computes the quotient under the division rule of this domain.
   *
   * @param other - Divisor.
   * @returns The quotient under floor division.
   * @see SymPy `sympy.polys.matrices.domainscalar.DomainScalar.__floordiv__`
   */
  floordiv(other: DomainScalar): DomainScalar {
    const [a, b] = this.unify(other);
    return new DomainScalar(div(a.domain, a.element, b.element)[0], a.domain);
  }
  /**
   * Computes the remainder on division by the supplied divisor.
   *
   * @param other - Divisor.
   * @returns The remainder after division.
   * @see SymPy `sympy.polys.matrices.domainscalar.DomainScalar.__mod__`
   */
  mod(other: DomainScalar): DomainScalar {
    const [a, b] = this.unify(other);
    return new DomainScalar(rem(a.domain, a.element, b.element), a.domain);
  }
  /**
   * Divides the scalars over their unified domain and retains the quotient and remainder.
   *
   * @param other - Divisor.
   * @returns The quotient and remainder.
   * @see SymPy `sympy.polys.matrices.domainscalar.DomainScalar.__divmod__`
   */
  divmod(other: DomainScalar): [DomainScalar, DomainScalar] {
    const [a, b] = this.unify(other);
    const [q, r] = div(a.domain, a.element, b.element);
    return [new DomainScalar(q, a.domain), new DomainScalar(r, a.domain)];
  }
  /**
   * An integer power (negative powers in a field).
   *
   * @param exponent - Exponent to which to raise the value.
   * @returns The value raised to the given exponent.
   * @see SymPy `sympy.polys.matrices.domainscalar.DomainScalar.__pow__`
   */
  pow(exponent: IntLike): DomainScalar {
    const n = asInt(exponent, 'exponent');
    const K = this.domain;
    let result = K.one;
    let base = this.element;
    for (let k = n < 0n ? -n : n; k > 0n; k >>= 1n) {
      if (k & 1n) result = K.mul(result, base);
      if (k > 1n) base = K.mul(base, base);
    }
    return new DomainScalar(n < 0n ? K.quo(K.one, result) : result, K);
  }
  /**
   * Applies unary plus to the value.
   *
   * @returns The value with unary plus applied.
   * @see SymPy `sympy.polys.matrices.domainscalar.DomainScalar.__pos__`
   */
  pos(): DomainScalar {
    return this;
  }
  /**
   * Reverses the sign of the value.
   *
   * @returns The additive inverse.
   * @see SymPy `sympy.polys.matrices.domainscalar.DomainScalar.__neg__`
   */
  neg(): DomainScalar {
    return new DomainScalar(this.domain.neg(this.element), this.domain);
  }
  /**
   * Compares the two operands for equality.
   *
   * @param other - Value to compare against.
   * @returns Whether the operands are equal.
   * @see SymPy `sympy.polys.matrices.domainscalar.DomainScalar.__eq__`
   */
  equals(other: unknown): boolean {
    return other instanceof DomainScalar && elemEq(this.element, other.element) && this.domain.equals(other.domain);
  }
  /**
   * Tests for the additive identity.
   *
   * @returns Whether the value equals zero.
   * @see SymPy `sympy.polys.matrices.domainscalar.DomainScalar.is_zero`
   */
  isZero(): boolean {
    return elemEq(this.element, this.domain.zero);
  }
  /**
   * Tests for the multiplicative identity in the scalar’s domain.
   *
   * @returns Whether the value equals one.
   * @see SymPy `sympy.polys.matrices.domainscalar.DomainScalar.is_one`
   */
  isOne(): boolean {
    return elemEq(this.element, this.domain.one);
  }
}

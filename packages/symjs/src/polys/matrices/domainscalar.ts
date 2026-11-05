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
import type { Domain } from '../domains';
import { ZZ } from '../domains';
import { convertFrom, div, domainOfExprs, elemEq, elemRepr, rem } from './domainops';

/** SymPy DomainScalar: an element of a domain. */
export class DomainScalar {
  constructor(
    readonly element: Expr,
    readonly domain: Domain,
  ) {}
  /** A scalar (SymPy DomainScalar.new). */
  static new(element: Expr, domain: Domain): DomainScalar {
    return new DomainScalar(element, domain);
  }
  /** The scalar of an expression over the domain construct_domain chooses. */
  static fromSympy(expr: ExprLike): DomainScalar {
    const [domain, elements] = domainOfExprs([expr]);
    return new DomainScalar(first(elements), domain);
  }
  /** SymPy repr() of the element. */
  toString(): string {
    return elemRepr(this.domain, this.element);
  }
  toSympy(): Expr {
    return this.domain.toSympy(this.element);
  }
  /** The scalar over another domain. */
  toDomain(domain: Domain): DomainScalar {
    return new DomainScalar(convertFrom(domain, this.element, this.domain), domain);
  }
  convertTo(domain: Domain): DomainScalar {
    return this.toDomain(domain);
  }
  /** Both scalars over their unified domain. */
  unify(other: DomainScalar): [DomainScalar, DomainScalar] {
    const domain = this.domain.unify(other.domain);
    return [this.toDomain(domain), other.toDomain(domain)];
  }
  /** Python truth value: a nonzero element. */
  get isNonzero(): boolean {
    return !this.domain.isZero(this.element);
  }
  add(other: DomainScalar): DomainScalar {
    const [a, b] = this.unify(other);
    return new DomainScalar(a.domain.add(a.element, b.element), a.domain);
  }
  sub(other: DomainScalar): DomainScalar {
    const [a, b] = this.unify(other);
    return new DomainScalar(a.domain.sub(a.element, b.element), a.domain);
  }
  /** The product (an integer is a scalar of ZZ). */
  mul(otherIn: DomainScalar | number | bigint): DomainScalar {
    const other = otherIn instanceof DomainScalar ? otherIn : new DomainScalar(Rational.of(BigInt(otherIn)), ZZ);
    const [a, b] = this.unify(other);
    return new DomainScalar(a.domain.mul(a.element, b.element), a.domain);
  }
  /** Floor division (SymPy //). */
  floordiv(other: DomainScalar): DomainScalar {
    const [a, b] = this.unify(other);
    return new DomainScalar(div(a.domain, a.element, b.element)[0], a.domain);
  }
  /** The remainder (SymPy %). */
  mod(other: DomainScalar): DomainScalar {
    const [a, b] = this.unify(other);
    return new DomainScalar(rem(a.domain, a.element, b.element), a.domain);
  }
  /** [quotient, remainder] (SymPy divmod). */
  divmod(other: DomainScalar): [DomainScalar, DomainScalar] {
    const [a, b] = this.unify(other);
    const [q, r] = div(a.domain, a.element, b.element);
    return [new DomainScalar(q, a.domain), new DomainScalar(r, a.domain)];
  }
  /** An integer power (negative powers in a field). */
  pow(n: number): DomainScalar {
    const K = this.domain;
    let r = K.one;
    for (let i = 0; i < Math.abs(n); i++) r = K.mul(r, this.element);
    return new DomainScalar(n < 0 ? K.quo(K.one, r) : r, K);
  }
  pos(): DomainScalar {
    return this;
  }
  neg(): DomainScalar {
    return new DomainScalar(this.domain.neg(this.element), this.domain);
  }
  equals(other: unknown): boolean {
    return other instanceof DomainScalar && elemEq(this.element, other.element) && this.domain.equals(other.domain);
  }
  isZero(): boolean {
    return elemEq(this.element, this.domain.zero);
  }
  isOne(): boolean {
    return elemEq(this.element, this.domain.one);
  }
}

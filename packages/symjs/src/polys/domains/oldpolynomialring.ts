// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/domains/old_polynomialring.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause (see LICENSE).

import { NotImplementedError } from '../../core/errors';
import type { Expr, ExprLike, Sym } from '../../core/nodes';
import { str } from '../../printing/str';
import { CoercionFailed, Domain, domainHooks, QQ, ZZ, RR, EX } from '../domains';
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

/** Multivariate old polynomial ring, with the ordering used by AGCA. */
export class PolynomialRingBase extends Domain {
  readonly isField = false;
  readonly ground;
  readonly order: MonomialOrdering;
  private readonly polynomialRing: PolyRing;
  constructor(readonly coefficientDomain: Domain, override readonly symbols: readonly Sym[], order: OrderLike = 'grevlex') {
    super();
    this.ground = coefficientDomain.ground;
    this.polynomialRing = new PolyRing(symbols, coefficientDomain, order);
    this.order = this.polynomialRing.order;
    registerModuleContext(this, { polynomialRing: this, domain: coefficientDomain, symbols, order: this.order, relations: [] });
  }
  override get dom(): Domain { return this.coefficientDomain; }
  toString(): string {
    return `${this.dom.toString()}[${this.symbols.map(str).join(',')}]${this.order.isGlobal ? '' : ` order=${this.order.toString()}`}`;
  }
  override equals(other: Domain): boolean {
    return other instanceof PolynomialRingBase && this.toString() === other.toString() && this.order.toString() === other.order.toString();
  }
  canon(e: Expr): Expr { return this.polynomialRing.fromExpr(e).asExpr(); }
  fromSympy(e: ExprLike): Expr {
    try { return this.polynomialRing.fromExpr(e).asExpr(); }
    catch {
      if (!this.order.isGlobal) throw new NotImplementedError('fractional representatives of localized polynomial rings are not implemented');
      throw new CoercionFailed(`cannot convert to ${this.toString()}`);
    }
  }
  getField(): Domain {
    if (![QQ, ZZ, RR, EX].includes(this.dom)) throw new NotImplementedError('fraction fields over this coefficient domain are not implemented');
    return this.dom.fracField(...this.symbols);
  }
  /** The ring over another coefficient domain, with the same generators and order (SymPy set_domain). */
  setDomain(K: Domain): PolynomialRingBase {
    return new PolynomialRingBase(K, this.symbols, this.order);
  }
  /**
   * The units (SymPy is_unit): the constants that are units of the coefficient
   * domain, and for a local order the elements with such a constant term.
   */
  override isUnit(a: unknown): boolean {
    const p = this.polynomialRing.fromExpr(this.toSympy(this.convert(a)));
    if (this.order.isGlobal && !p.isGround) return false;
    return this.dom.isUnit(this.dom.convert(p.const()));
  }
  protected override get compositeParts(): readonly [Domain, readonly Sym[]] {
    return [this.dom, this.symbols];
  }
  protected override recompose(K: Domain, gens: readonly Sym[]): Domain {
    return new PolynomialRingBase(K, gens, this.order);
  }
  override get hasAssocRing(): boolean {
    return true;
  }
  override get isExact(): boolean {
    return this.dom.isExact;
  }
  override getExact(): Domain {
    return this.setDomain(this.dom.getExact());
  }
  override get hasCharacteristicZero(): boolean {
    return this.dom.hasCharacteristicZero;
  }
  override characteristic(): bigint {
    return this.dom.characteristic();
  }
}

domainHooks.polynomialRing = (K, gens) => new PolynomialRingBase(K, gens);

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/domains/compositedomain.py,
// polys/domains/polynomialring.py, polys/domains/fractionfield.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License (see LICENSE).

/**
 * @file Polynomial rings K[x, ...] and rational function fields K(x, ...)
 * over coefficient domains other than the numeric grounds: finite fields,
 * CC, algebraic fields, the Gaussian domains and rings over fraction fields
 * (ZZ(z)[x]). Elements are expressions in canonical form, computed with the
 * sparse PolyRing and FracField over the coefficient domain.
 */

import type { Expr, ExprLike, Sym } from '../../core/nodes';
import { sympify } from '../../core/ops';
import { str } from '../../printing/str';
import { CoercionFailed, Domain, domainHooks } from '../domains';
import { FracField } from '../fields';
import { GeneratorsError } from '../polyerrors';
import { PolyRing } from '../rings';

/** Shared parts of the composite domains (SymPy CompositeDomain). */
abstract class CompositeDomain extends Domain {
  readonly ground;
  /** The generators (SymPy symbols). */
  override readonly symbols: readonly Sym[];
  constructor(
    /** The coefficient domain (SymPy domain). */
    readonly domain: Domain,
    symbols: readonly Sym[],
  ) {
    super();
    this.ground = domain.ground;
    this.symbols = symbols;
  }
  /** The generators over the coefficient domain. */
  get gens(): readonly Sym[] {
    return this.symbols;
  }
  /** The coefficient domain (SymPy dom). */
  override get dom(): Domain {
    return this.domain;
  }
  override get hasAssocRing(): boolean {
    return true;
  }
  protected abstract readonly brackets: readonly [string, string];
  toString(): string {
    return `${this.domain.toString()}${this.brackets[0]}${this.symbols.map((s) => str(s)).join(',')}${this.brackets[1]}`;
  }
  /** The element as a canonical expression; throws CoercionFailed. */
  protected abstract element(e: Expr): Expr;
  canon(e: Expr): Expr {
    return this.element(e);
  }
  fromSympy(e: ExprLike): Expr {
    try { return this.element(sympify(e)); }
    catch (error) {
      if (error instanceof RangeError) throw new CoercionFailed(`cannot convert ${str(sympify(e))} to ${this.toString()}`);
      throw error;
    }
  }
  /** The same kind of domain over another coefficient domain (SymPy set_domain). */
  abstract setDomain(K: Domain): Domain;
  override get isExact(): boolean {
    return this.domain.isExact;
  }
  override getExact(): Domain {
    return this.setDomain(this.domain.getExact());
  }
  override get hasCharacteristicZero(): boolean {
    return this.domain.hasCharacteristicZero;
  }
  override characteristic(): bigint {
    return this.domain.characteristic();
  }
  override inject(...symbols: Sym[]): Domain {
    if (symbols.some((s) => this.symbols.some((t) => t.key === s.key))) throw new GeneratorsError(`common generators in (${this.symbols.map((g) => str(g)).join(', ')}) and (${symbols.map((g) => str(g)).join(', ')})`);
    return this.recompose(this.domain, [...this.symbols, ...symbols]);
  }
  override drop(...symbols: Expr[]): Domain {
    const rest = this.symbols.filter((g) => !symbols.some((s) => s.key === g.key));
    const K = this.domain.drop(...symbols);
    return rest.length ? this.recompose(K, rest) : K;
  }
  protected override get compositeParts(): readonly [Domain, readonly Sym[]] {
    return [this.domain, this.symbols];
  }
  protected abstract override recompose(K: Domain, symbols: readonly Sym[]): Domain;
}

/** K[x, ...] over a non-ground coefficient domain (SymPy PolynomialRing). */
export class CompositePolynomialRing extends CompositeDomain {
  readonly isField = false;
  protected readonly brackets = ['[', ']'] as const;
  private readonly ring: PolyRing;
  constructor(domain: Domain, symbols: readonly Sym[]) {
    super(domain, symbols);
    this.ring = new PolyRing([...symbols], domain);
  }
  protected element(e: Expr): Expr {
    return this.ring.fromExpr(e).asExpr();
  }
  getField(): Domain {
    return this.domain.fracField(...this.symbols);
  }
  setDomain(K: Domain): Domain {
    return K.polyRing(...this.symbols);
  }
  /** The units are the units of the coefficient domain (SymPy PolynomialRing.is_unit). */
  override isUnit(a: unknown): boolean {
    const p = this.ring.fromExpr(this.toSympy(this.convert(a)));
    return p.isGround && this.domain.isUnit(this.domain.convert(p.LC));
  }
  /** The canonical unit of the leading coefficient (SymPy PolynomialRing.canonical_unit). */
  override canonicalUnit(a: unknown): unknown {
    const p = this.ring.fromExpr(this.toSympy(this.convert(a)));
    return this.convert(this.domain.toSympy(this.domain.canonicalUnit(this.domain.convert(p.LC))));
  }
  protected recompose(K: Domain, symbols: readonly Sym[]): Domain {
    return K.polyRing(...symbols);
  }
}

/** K(x, ...) over a non-ground coefficient domain (SymPy FractionField). */
export class CompositeFractionField extends CompositeDomain {
  readonly isField = true;
  protected readonly brackets = ['(', ')'] as const;
  private readonly field: FracField;
  constructor(domain: Domain, symbols: readonly Sym[]) {
    super(domain, symbols);
    this.field = new FracField([...symbols], domain);
  }
  protected element(e: Expr): Expr {
    return this.field.fromExpr(e).asExpr();
  }
  getField(): Domain {
    return this;
  }
  override getRing(): Domain {
    return this.domain.polyRing(...this.symbols);
  }
  setDomain(K: Domain): Domain {
    return K.fracField(...this.symbols);
  }
  protected recompose(K: Domain, symbols: readonly Sym[]): Domain {
    return K.fracField(...symbols);
  }
}

domainHooks.compositeRing = (K, gens) => new CompositePolynomialRing(K, gens);
domainHooks.compositeField = (K, gens) => new CompositeFractionField(K, gens);

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
import { CoercionFailed, FractionField, ZZ } from './domains';
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

/** A multivariate rational function field K(x_1, ..., x_n) (SymPy FracField). */
export class FracField {
  readonly ring: PolyRing;
  readonly symbols: readonly Expr[];
  readonly domain: Domain;
  readonly order: MonomialOrdering;
  readonly ngens: number;
  readonly gens: readonly FracElement[];

  constructor(symbols: RingSymbols, domain: DomainLike = ZZ, order: OrderLike = lex) {
    this.ring = new PolyRing(symbols, domain, order);
    this.symbols = this.ring.symbols;
    this.domain = this.ring.domain;
    this.order = this.ring.order;
    this.ngens = this.ring.ngens;
    this.gens = this.ring.gens.map((g) => this.rawNew(g));
  }

  toString(): string {
    return `Rational function field in ${this.symbols.map((s) => str(s)).join(', ')} over ${String(this.domain)} with ${String(this.order)} order`;
  }
  equals(other: unknown): boolean {
    return other instanceof FracField && this.ring.equals(other.ring);
  }
  isElement(element: unknown): boolean {
    return element instanceof FracElement && this.equals(element.field);
  }
  index(gen: FracElement): number {
    if (!this.isElement(gen)) throw new RangeError('expected an element of this field');
    return this.ring.index(gen.toPoly());
  }
  get zero(): FracElement { return this.rawNew(this.ring.zero); }
  get one(): FracElement { return this.rawNew(this.ring.one); }

  /** Construct a fraction without cancellation, as in SymPy raw_new. */
  rawNew(numer: PolyElement, denom: PolyElement = this.ring.one): FracElement {
    return new FracElement(this, numer, denom);
  }
  /** Cancel the common factors and normalize the denominator's unit. */
  new(numer: PolyElement, denom: PolyElement = this.ring.one): FracElement {
    const n = numer.setRing(this.ring), d = denom.setRing(this.ring);
    if (d.isZero) throw new RangeError('zero denominator');
    return this.rawNew(...n.cancel(d));
  }
  domainNew(element: ExprLike): Expr { return this.ring.domainNew(element); }

  /** A ground element, including fractions of a non-field ground domain. */
  groundNew(element: ExprLike): FracElement {
    try { return this.new(this.ring.groundNew(element)); }
    catch (error) {
      if (!(error instanceof CoercionFailed) || this.domain.isField) throw error;
      const e = this.domain.getField().fromSympy(element);
      const [n, d] = fraction(e);
      return this.new(this.ring.groundNew(n), this.ring.groundNew(d));
    }
  }

  /** Convert an element, expression, or [numerator, denominator] polynomial pair. */
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

  /** Rebuild the expression by exact polynomial fraction arithmetic. */
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

  toRing(): PolyRing { return this.ring; }
  /** Convert to the expression-backed domain supported by the existing domain layer. */
  toDomain(): FractionField {
    if (String(this.domain) !== this.domain.ground || this.domain.ground === 'EX' || !this.symbols.every((s) => s instanceof Sym)) {
      throw new NotImplementedError('fraction-field domain conversion requires a basic ground domain and symbol generators');
    }
    return new FractionField(this.domain.ground, this.symbols);
  }
}

/** A sparse polynomial fraction (SymPy FracElement). Arithmetic returns reduced fractions. */
export class FracElement {
  readonly numer: PolyElement;
  readonly denom: PolyElement;
  constructor(readonly field: FracField, numer: PolyElement, denom: PolyElement = field.ring.one) {
    this.numer = numer.setRing(field.ring);
    this.denom = denom.setRing(field.ring);
    if (this.denom.isZero) throw new RangeError('zero denominator');
  }
  get isZero(): boolean { return this.numer.isZero; }
  toPoly(): PolyElement {
    if (!this.denom.equals(1)) throw new RangeError('denominator should be 1');
    return this.numer;
  }
  parent(): FractionField { return this.field.toDomain(); }
  copy(): FracElement { return this.rawNew(this.numer, this.denom); }
  rawNew(numer: PolyElement, denom: PolyElement = this.field.ring.one): FracElement { return this.field.rawNew(numer, denom); }
  new(numer: PolyElement, denom: PolyElement): FracElement { return this.field.new(numer, denom); }
  setField(field: FracField): FracElement {
    return this.field.equals(field) ? this : field.new(this.numer.setRing(field.ring), this.denom.setRing(field.ring));
  }
  asExpr(...symbols: Expr[]): Expr { return mul(this.numer.asExpr(...symbols), pow(this.denom.asExpr(...symbols), -1)); }
  equals(other: unknown): boolean {
    return other instanceof FracElement && this.field.equals(other.field)
      ? this.numer.equals(other.numer) && this.denom.equals(other.denom)
      : this.denom.equals(1) && this.numer.equals(other);
  }
  toString(): string {
    const n = String(this.numer), d = String(this.denom);
    if (this.denom.equals(1)) return n;
    const numerator = this.numer.length > 1 ? `(${n})` : n;
    const denominator = this.denom.isGenerator || this.denom.isGround ? d : `(${d})`;
    return `${numerator}/${denominator}`;
  }
  neg(): FracElement { return this.rawNew(this.numer.neg(), this.denom); }
  add(other: FracInput): FracElement {
    const g = this.field.fieldNew(other);
    return this.new(this.numer.mul(g.denom).add(g.numer.mul(this.denom)), this.denom.mul(g.denom));
  }
  sub(other: FracInput): FracElement { return this.add(this.field.fieldNew(other).neg()); }
  mul(other: FracInput): FracElement {
    const g = this.field.fieldNew(other);
    return this.new(this.numer.mul(g.numer), this.denom.mul(g.denom));
  }
  div(other: FracInput): FracElement {
    const g = this.field.fieldNew(other);
    return this.new(this.numer.mul(g.denom), this.denom.mul(g.numer));
  }
  pow(exponent: IntLike): FracElement {
    const n = intArg(exponent, 'exponent');
    return n < 0 ? this.rawNew(this.denom.pow(-n), this.numer.pow(-n)) : this.rawNew(this.numer.pow(n), this.denom.pow(n));
  }
  diff(gen: FracElement): FracElement {
    const i = this.field.index(gen);
    return this.new(this.numer.diff(i).mul(this.denom).sub(this.numer.mul(this.denom.diff(i))), this.denom.pow(2));
  }

  /** Substitute ground values, keeping the same field. */
  subs(gen: FracElement | FracSubstitutions, value?: ExprLike): FracElement {
    const pairs = this.pairs(gen, value);
    return this.new(this.numer.subs(pairs), this.denom.subs(pairs));
  }
  /** Evaluate ground values and remove their generators from the result field. */
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
  call(...values: ExprLike[]): FracElement | Expr {
    if (!values.length || values.length > this.field.ngens) throw new RangeError(`expected at least 1 and at most ${this.field.ngens} values`);
    return this.evaluate(values.map((v, i) => [at(this.field.gens, i), v]));
  }
  /** SymPy 1.14 leaves rational function composition unimplemented. */
  compose(_gen: FracElement, _value: FracInput): never { throw new NotImplementedError('rational function composition'); }

  private pairs(gen: FracElement | FracSubstitutions, value: ExprLike | undefined): (readonly [number, ExprLike])[] {
    if (gen instanceof FracElement) {
      if (value === undefined) throw new TypeError('expected a substitution value');
      return [[this.field.index(gen), value]];
    }
    return gen.map(([g, v]) => [this.field.index(g), v]);
  }
}

/** Construct a field and its generators (SymPy field). */
export function field(symbols: RingSymbols, domain: DomainLike = ZZ, order: OrderLike = lex): [FracField, ...FracElement[]] {
  const F = new FracField(symbols, domain, order);
  return [F, ...F.gens];
}
/** Construct a field and an array of its generators (SymPy xfield). */
export function xfield(symbols: RingSymbols, domain: DomainLike = ZZ, order: OrderLike = lex): [FracField, FracElement[]] {
  const F = new FracField(symbols, domain, order);
  return [F, [...F.gens]];
}
/** SymPy vfield; JavaScript has no caller namespace, so generators are available as F.gens. */
export function vfield(symbols: RingSymbols, domain: DomainLike = ZZ, order: OrderLike = lex): FracField {
  return new FracField(symbols, domain, order);
}
/** Infer generators and the coefficient domain from numerators and denominators (SymPy sfield). */
export function sfield(exprs: ExprLike, ...rest: (Expr | SringOptions)[]): [FracField, FracElement];
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

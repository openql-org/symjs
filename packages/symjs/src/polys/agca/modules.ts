// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/agca/modules.py), Copyright (c)
// 2006-2023 SymPy Development Team, BSD 3-Clause (see LICENSE).

import { NotImplementedError } from '../../core/errors';
import { at, first, last } from '../../core/guard';
import { Expr, S, type ExprLike } from '../../core/nodes';
import { add, mul, neg, pow } from '../../core/ops';
import { cancel, fraction, together } from '../../simplify/rational';
import type { IntLike } from '../../ntheory/intutil';
import { str } from '../../printing/str';
import { intArg } from '../compatibility';
import { CoercionFailed, type Domain, domainHooks, groundToSympy } from '../domains';
import { polynomialModuleContext, type PolynomialModuleContext } from '../domains/oldpolynomialring';
import { sdmFromVector, sdmToVector, sdmGroebner, sdmNfMora, sdmNfBuchbergerReduced, type Sdm, type SdmOrder } from '../distributedmodules';
import type { ModuleImplementedIdeal } from './ideals';

export type ModuleInput = ModuleElement | readonly ExprLike[] | ExprLike;
const isZero = (e: Expr): boolean => e.key === S.Zero.key;
const zeros = (n: number): Expr[] => Array.from({ length: n }, () => S.Zero);
const units = (n: number): Expr[][] => Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, j) => i === j ? S.One : S.Zero));

/** A vector, or a coset represented by a vector, in a finitely presented module. */
export class ModuleElement {
  readonly data: readonly Expr[];
  constructor(readonly module: Module, data: readonly Expr[]) { this.data = Object.freeze([...data]); }
  toString(): string {
    const relations = this.module.context.relations;
    const suffix = relations.length ? ` + <${relations.map(str).join(', ')}>` : '';
    const vector = `[${this.data.map((e) => str(e) + suffix).join(', ')}]`;
    const ambient = this.module.ambient;
    return ambient instanceof QuotientModule ? `${vector} + ${ambient.killedModule.toString()}` : vector;
  }
  add(other: ModuleInput): ModuleElement {
    const b = this.module.convert(other);
    return this.module.convert(this.data.map((a, i) => add(a, at(b.data, i))));
  }
  neg(): ModuleElement { return this.module.convert(this.data.map(neg)); }
  sub(other: ModuleInput): ModuleElement { return this.add(this.module.convert(other).neg()); }
  mul(scalar: ExprLike): ModuleElement {
    const c = this.module.ring.fromSympy(scalar);
    return this.module.convert(this.data.map((a) => mul(c, a)));
  }
  /** Divide every component by a scalar, requiring the quotient to remain in the module. */
  div(scalar: ExprLike): ModuleElement {
    return this.module.convert(this.data.map((a) => cancel(mul(a, pow(scalar, -1)))));
  }
  equals(other: ModuleElement): boolean {
    return sameAmbient(this.module.ambient, other.module.ambient) && this.module.ambient.zeroContains(this.data.map((a, i) => add(a, neg(at(other.data, i)))));
  }
  isZero(): boolean { return this.module.ambient.zeroContains(this.data); }
}

function sameAmbient(a: FreeModule | QuotientModule, b: FreeModule | QuotientModule): boolean {
  if (!a.ring.equals(b.ring) || a.rank !== b.rank) return false;
  if (a instanceof QuotientModule) return b instanceof QuotientModule && a.killedModule.equals(b.killedModule);
  return b instanceof FreeModule;
}

/** Common operations on free modules, submodules and quotient modules. */
export abstract class Module {
  readonly context: PolynomialModuleContext;
  constructor(readonly ring: Domain, readonly rank: number) { this.context = polynomialModuleContext(ring); }
  abstract readonly ambient: FreeModule | QuotientModule;
  abstract readonly gens: readonly ModuleElement[];
  abstract convert(element: ModuleInput): ModuleElement;
  abstract toString(): string;
  contains(element: ModuleInput): boolean {
    try { this.convert(element); return true; }
    catch (error) { if (error instanceof CoercionFailed) return false; throw error; }
  }
  subset(elements: Iterable<ModuleInput>): boolean { return [...elements].every((e) => this.contains(e)); }
  /** As in SymPy, tests whether this module CONTAINS other. */
  isSubmodule(other: unknown): boolean {
    return other instanceof Module && sameAmbient(this.ambient, other.ambient) && other.gens.every((g) => this.contains(g));
  }
  equals(other: Module): boolean { return this.isSubmodule(other) && other.isSubmodule(this); }
  isZero(): boolean { return this.gens.every((g) => g.isZero()); }
  submodule(...gens: ModuleInput[]): SubModule {
    return new SubModule(gens.map((g) => this.convert(g)), this.ambient);
  }
  quotientModule(other: SubModule | readonly ModuleInput[]): QuotientModule | SubModule {
    const denominator = other instanceof SubModule ? other : this.submodule(...other);
    if (!this.isSubmodule(denominator)) throw new RangeError('denominator must be a submodule');
    const ambient = this.ambient;
    const base = ambient instanceof QuotientModule ? ambient.base : ambient;
    const killed = base.submodule(...denominator.gens.map((g) => g.data), ...ambient.relations());
    const quotient = new QuotientModule(base, killed);
    return this instanceof SubModule ? quotient.submodule(...this.gens.map((g) => g.data)) : quotient;
  }
  multiplyIdeal(ideal: ModuleImplementedIdeal): SubModule {
    if (!this.ring.equals(ideal.ring)) throw new RangeError('ideal must have the same ring');
    return this.submodule(...ideal.gens.flatMap((c) => this.gens.map((g) => g.mul(c))));
  }
}

/** A finite free module over a polynomial ring or a quotient of one. */
export class FreeModule extends Module {
  readonly ambient = this;
  constructor(ring: Domain, rank: IntLike) {
    const n = intArg(rank, 'rank');
    if (n < 0) throw new RangeError('rank must be nonnegative');
    super(ring, n);
    if (!this.context.domain.isField) throw new NotImplementedError('module standard bases require a coefficient field');
  }
  get gens(): readonly ModuleElement[] { return this.basis(); }
  basis(): ModuleElement[] { return units(this.rank).map((v) => this.convert(v)); }
  toString(): string {
    const name = this.ring.toString();
    return `${this.context.relations.length ? `(${name})` : name}**${this.rank}`;
  }
  convert(element: ModuleInput): ModuleElement {
    const value = element instanceof ModuleElement ? element.data : element;
    const scalar = groundToSympy(value);
    const data = scalar instanceof Expr && isZero(scalar) ? zeros(this.rank) : Array.isArray(value) ? value : undefined;
    if (!data || data.length !== this.rank) throw new CoercionFailed(`expected a vector of length ${this.rank}`);
    return new ModuleElement(this, data.map((v: ExprLike) => this.ring.fromSympy(v)));
  }
  /** Relations of the coefficient ring lifted to each component. @internal */
  relations(): Expr[][] {
    return this.context.relations.flatMap((c) => units(this.rank).map((v) => v.map((e) => mul(c, e))));
  }
  zeroContains(data: readonly Expr[]): boolean { return data.every((e) => isZero(this.ring.canon(e))); }
  /** The same module as a quotient over the polynomial coefficient ring. */
  get quot(): QuotientModule {
    const base = this.context.polynomialRing.freeModule(this.rank);
    return new QuotientModule(base, base.submodule(...this.relations()));
  }
  /** Lift a vector over R/I to its coset in R**n / I*R**n. */
  lift(element: ModuleInput): ModuleElement { return this.quot.convert(this.convert(element).data); }
}

/** A quotient F/N, represented by vectors of F. */
export class QuotientModule extends Module {
  readonly ambient = this;
  constructor(readonly base: FreeModule, readonly killedModule: SubModule) {
    super(base.ring, base.rank);
    if (!base.isSubmodule(killedModule)) throw new RangeError('denominator must be a submodule of the base');
  }
  get gens(): readonly ModuleElement[] { return this.base.gens.map((g) => this.convert(g)); }
  toString(): string { return `${this.base.toString()}/${this.killedModule.toString()}`; }
  convert(element: ModuleInput): ModuleElement { return new ModuleElement(this, this.base.convert(element).data); }
  relations(): Expr[][] { return [...this.killedModule.gens.map((g) => [...g.data]), ...this.base.relations()]; }
  zeroContains(data: readonly Expr[]): boolean { return this.killedModule.contains(data); }
}

/** A finitely generated submodule. Computation uses Mora standard bases. */
export class SubModule extends Module {
  readonly gens: readonly ModuleElement[];
  readonly ambient: FreeModule | QuotientModule;
  private basisCache?: Sdm[];
  private extendedCache?: [Sdm[], Sdm[]];
  private readonly order: SdmOrder;
  constructor(gens: readonly ModuleInput[], readonly container: FreeModule | QuotientModule, elimination = false) {
    super(container.ring, container.rank);
    this.ambient = container;
    this.gens = Object.freeze(gens.map((g) => container.convert(g)));
    this.order = elimination
      ? (m) => [-first(m), this.context.order.key(m.slice(1))]
      : (m) => [this.context.order.key(m.slice(1)), first(m)];
  }
  toString(): string { return `<${this.gens.map((g) => g.toString()).join(', ')}>`; }
  private sparse(vector: readonly Expr[]): Sdm {
    if (this.context.order.isGlobal === true) return sdmFromVector(vector, this.order, this.context.domain, { gens: this.context.symbols });
    const fractions = vector.map((e) => fraction(together(e)));
    const cleared = fractions.map(([n], i) => mul(n, ...fractions.filter((_, j) => i !== j).map(([, d]) => d)));
    return sdmFromVector(cleared, this.order, this.context.domain, { gens: this.context.symbols });
  }
  private vector(sparse: Sdm, rank: number): Expr[] { return sdmToVector(sparse, this.context.symbols, this.context.domain, rank); }
  private lifted(): readonly (readonly Expr[])[] { return [...this.gens.map((g) => g.data), ...this.container.relations()]; }
  private basis(): Sdm[] {
    this.basisCache ??= sdmGroebner(this.lifted().map((g) => this.sparse(g)), sdmNfMora, this.order, this.context.domain);
    return this.basisCache;
  }
  private extendedBasis(): [Sdm[], Sdm[]] {
    if (!this.extendedCache) {
      const lifted = this.lifted();
      const [G, coefficients] = sdmGroebner(lifted.map((g) => this.sparse(g)), sdmNfMora, this.order, this.context.domain, true);
      // Extended coefficients refer to the generators after clearing their denominators.
      const scales = lifted.map((g) => mul(...g.map((e) => fraction(together(e))[1])));
      this.extendedCache = [G, this.context.order.isGlobal === true ? coefficients : coefficients.map((c) => sdmFromVector(this.vector(c, lifted.length).map((e, i) => mul(e, at(scales, i))), this.order, this.context.domain, { gens: this.context.symbols }))];
    }
    return this.extendedCache;
  }
  convert(element: ModuleInput): ModuleElement {
    const vector = this.container.convert(element).data;
    if (sdmNfMora(this.sparse(vector), this.basis(), this.order, this.context.domain).length) throw new CoercionFailed('vector is not in this submodule');
    return new ModuleElement(this, vector);
  }
  isFullModule(): boolean { return this.container.gens.every((g) => this.contains(g)); }
  union(other: SubModule): SubModule {
    this.checkAmbient(other);
    return this.container.submodule(...this.gens, ...other.gens);
  }
  private checkAmbient(other: SubModule): void {
    if (!sameAmbient(this.container, other.container)) throw new RangeError('submodules must have the same ambient module');
  }
  /** Weak normal form, zero exactly for elements in the submodule. */
  reduceElement(element: ModuleInput, fully = false): ModuleElement {
    const vector = this.container.convert(element).data;
    if (this.context.order.isGlobal !== true) {
      const G = this.basis();
      // Restore Mora's local-unit multiplier to preserve the original coset.
      const [remainder, multiplier] = sdmNfMora(this.sparse(vector), G, this.order, this.context.domain, [this.sparse([S.One]), G.map(() => [])]);
      const denominator = mul(first(this.vector(multiplier, 1)), ...vector.map((e) => fraction(together(e))[1]));
      return this.container.convert(this.vector(remainder, this.rank).map((e) => mul(e, pow(denominator, -1))));
    }
    const NF = fully ? sdmNfBuchbergerReduced : sdmNfMora;
    return this.container.convert(this.vector(NF(this.sparse(vector), this.basis(), this.order, this.context.domain), this.rank));
  }
  inTermsOfGenerators(element: ModuleInput): Expr[] {
    if (this.context.order.isGlobal !== true) {
      const vector = this.convert(element);
      const relations = this.container.submodule(vector, ...this.gens).syzygyModule();
      const ordered = new SubModule(relations.gens, relations.container, true);
      const relation = first(ordered.basis().map((g) => ordered.vector(g, this.gens.length + 1)).filter((g) => this.context.polynomialRing.isUnit(first(g))));
      return relation.slice(1).map((c) => this.ring.fromSympy(mul(neg(c), pow(first(relation), -1))));
    }
    const vector = this.container.convert(element).data;
    const [G, coefficients] = this.extendedBasis();
    const [remainder, relation] = sdmNfMora(this.sparse(vector), G, this.order, this.context.domain, [[], coefficients]);
    if (remainder.length) throw new RangeError('vector is not in this submodule');
    return this.vector(relation, this.lifted().length).slice(0, this.gens.length).map(neg);
  }
  syzygyModule(): SubModule {
    const generators = this.lifted(), r = this.rank, k = generators.length;
    const F = this.context.polynomialRing.freeModule(r + k);
    const identity = units(k);
    const augmented = new SubModule(generators.map((g, i) => [...g, ...at(identity, i)]), F, true);
    const vectors = augmented.basis().map((g) => augmented.vector(g, r + k));
    const result = vectors.filter((g) => g.slice(0, r).every((e) => isZero(e))).map((g) => g.slice(r, r + this.gens.length));
    return this.ring.freeModule(this.gens.length).submodule(...result.filter((g) => g.some((e) => !isZero(e))));
  }
  intersect(other: SubModule): SubModule;
  intersect(other: SubModule, relations: true): [SubModule, Expr[][], Expr[][]];
  intersect(other: SubModule, relations?: false): SubModule;
  intersect(other: SubModule, relations = false): SubModule | [SubModule, Expr[][], Expr[][]] {
    this.checkAmbient(other);
    const r = this.rank;
    const left = this.lifted(), right = other.lifted();
    const vectors = [...units(r).map((e) => [...e, ...e]), ...left.map((g) => [...g, ...zeros(r)]), ...right.map((g) => [...zeros(r), ...g])];
    const syzygies = this.context.polynomialRing.freeModule(2 * r).submodule(...vectors).syzygyModule().gens.filter((g) => g.data.slice(0, r).some((e) => !isZero(e)));
    const result = this.container.submodule(...syzygies.map((g) => g.data.slice(0, r).map(neg)));
    return relations ? [result, syzygies.map((g) => g.data.slice(r, r + this.gens.length)), syzygies.map((g) => g.data.slice(r + left.length, r + left.length + other.gens.length))] : result;
  }
  moduleQuotient(other: SubModule): ModuleImplementedIdeal;
  moduleQuotient(other: SubModule, relations: true): [ModuleImplementedIdeal, Expr[][]];
  moduleQuotient(other: SubModule, relations?: false): ModuleImplementedIdeal;
  moduleQuotient(other: SubModule, relations = false): ModuleImplementedIdeal | [ModuleImplementedIdeal, Expr[][]] {
    this.checkAmbient(other);
    if (relations && other.gens.length !== 1) throw new NotImplementedError('quotient relations require a single divisor generator');
    if (other.gens.length === 0) return this.ring.ideal(1);
    if (other.gens.length > 1) return other.gens.map((g) => this.moduleQuotient(this.container.submodule(g))).reduce((a, b) => a.intersect(b));
    const vectors = [[...first(other.gens).data, S.One], ...this.gens.map((g) => [...g.data, S.Zero]), ...this.container.relations().map((g) => [...g, S.Zero])];
    const M = new SubModule(vectors, this.context.polynomialRing.freeModule(this.rank + 1), true);
    const [G, coefficients] = M.extendedBasis();
    const selected = G.map((g, i) => ({ vector: M.vector(g, this.rank + 1), i })).filter(({ vector }) => vector.slice(0, -1).every((e) => isZero(e)));
    const result = this.ring.ideal(...selected.map(({ vector }) => last(vector)));
    return relations ? [result, selected.map(({ i }) => M.vector(at(coefficients, i), M.lifted().length).slice(1, 1 + this.gens.length).map(neg))] : result;
  }
}

domainHooks.freeModule = (ring, rank) => new FreeModule(ring, rank);

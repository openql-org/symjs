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
import { ProductOrder, lex, monomialKey, type MonomialOrdering } from '../orderings';

/**
 * A product order separating the module index from polynomial exponents.
 *
 * @see SymPy `sympy.polys.agca.modules.ModuleOrder`
 */
export class ModuleOrder extends ProductOrder {
  /**
   * Combines position and term orders to compare module monomials.
   *
   * @param o1 - First monomial ordering.
   * @param o2 - Second monomial ordering.
   * @param top - Use term-over-position order.
   */
  constructor(o1: MonomialOrdering, o2: MonomialOrdering, top: boolean) {
    const blocks: [MonomialOrdering, number[]][] = top ? [[o2, []], [o1, [0]]] : [[o1, [0]], [o2, []]];
    super(...blocks);
  }
  /**
   * Forms a term comparison key from the module position and polynomial exponents.
   *
   * @param monomial - Exponents and module position of the term.
   * @returns The monomial comparison key.
   * @see SymPy `sympy.polys.agca.modules.ModuleOrder.__call__`
   */
  override key(monomial: readonly number[]): ReturnType<ProductOrder['key']> {
    return this.args.map(([order, indices]) => indices.length ? order.compare([first(monomial)], [0]) : order.key(monomial.slice(1)));
  }
  /**
   * Compares the two operands for equality.
   *
   * @param other - Value to compare against.
   * @returns Whether the operands are equal.
   * @see SymPy `sympy.polys.agca.modules.ModuleOrder.__eq__`
   */
  equals(other: unknown): boolean { return other instanceof ModuleOrder && this.toString() === other.toString() && this.args.every(([, indices], i) => indices.length === at(other.args, i)[1].length); }
  /**
   * Formats the value as text.
   *
   * @returns The printable representation.
   * @see SymPy `sympy.polys.agca.modules.ModuleOrder.__str__`
   */
  override toString(): string { return `ModuleOrder(${this.args.map(([order]) => String(order)).join(', ')})`; }
}

/** Represents module input as an existing element, a coordinate vector or a scalar. */
export type ModuleInput = ModuleElement | readonly ExprLike[] | ExprLike;
const isZero = (e: Expr): boolean => e.key === S.Zero.key;
const zeros = (n: number): Expr[] => Array.from({ length: n }, () => S.Zero);
const units = (n: number): Expr[][] => Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, j) => i === j ? S.One : S.Zero));

/**
 * A vector, or a coset represented by a vector, in a finitely presented module.
 *
 * @see SymPy `sympy.polys.agca.modules.ModuleElement`
 */
export class ModuleElement {
  /**
   * The coordinates in the ambient module.
   *
   * @see SymPy `sympy.polys.agca.modules.ModuleElement.data`
   */
  readonly data: readonly Expr[];
  /**
   * Constructs a new `ModuleElement`.
   *
   * @param module - Module in which to interpret the coordinates.
   * @param data - Coordinate data representing the element.
   */
  constructor(
    /**
     * The module containing the element.
     *
     * @see SymPy `sympy.polys.agca.modules.ModuleElement.__module__`
     */
    readonly module: Module, data: readonly Expr[]) { this.data = Object.freeze([...data]); }
  /**
   * Iterates over the coordinates in basis order.
   *
   * @returns An iterator over the coordinate expressions.
   */
  [Symbol.iterator](): Iterator<Expr> { return this.data[Symbol.iterator](); }
  /**
   * Displays the coordinates of the element in its module.
   *
   * @returns The printable representation.
   */
  toString(): string {
    const relations = this.module.context.relations;
    const suffix = relations.length ? ` + <${relations.map(str).join(', ')}>` : '';
    const vector = `[${this.data.map((e) => str(e) + suffix).join(', ')}]`;
    const ambient = this.module.ambient;
    return ambient instanceof QuotientModule ? `${vector} + ${ambient.killedModule.toString()}` : vector;
  }
  /**
   * Adds the other operand to this value.
   *
   * @param other - Addend.
   * @returns The sum of the operands.
   * @see SymPy `sympy.polys.agca.modules.ModuleElement.add`
   */
  add(other: ModuleInput | SubModule): ModuleElement {
    if (other instanceof SubModule) return other.add(this);
    const b = this.module.convert(other);
    return this.module.convert(this.data.map((a, i) => add(a, at(b.data, i))));
  }
  /**
   * Reverses the sign of the value.
   *
   * @returns The additive inverse.
   * @see SymPy `sympy.polys.agca.modules.ModuleElement.__neg__`
   */
  neg(): ModuleElement { return this.module.convert(this.data.map(neg)); }
  /**
   * Subtracts the other operand from this value.
   *
   * @param other - Value to subtract.
   * @returns The difference in operand order.
   * @see SymPy `sympy.polys.agca.modules.ModuleElement.__sub__`
   */
  sub(other: ModuleInput): ModuleElement { return this.add(this.module.convert(other).neg()); }
  /**
   * Multiplies this value by the factor on its right.
   *
   * @param scalar - Scalar used to scale the value.
   * @returns The product in operand order.
   * @see SymPy `sympy.polys.agca.modules.ModuleElement.mul`
   */
  mul(scalar: ExprLike): ModuleElement {
    const c = this.module.ring.fromSympy(scalar);
    return this.module.convert(this.data.map((a) => mul(c, a)));
  }
  /**
   * Divide every component by a scalar, requiring the quotient to remain in the module.
   *
   * @param scalar - Divisor.
   * @returns The quotient.
   * @see SymPy `sympy.polys.agca.modules.ModuleElement.div`
   */
  div(scalar: ExprLike): ModuleElement {
    return this.module.convert(this.data.map((a) => cancel(mul(a, pow(scalar, -1)))));
  }
  /**
   * Compares the two operands for equality.
   *
   * @param other - Value to compare against.
   * @returns Whether the operands are equal.
   * @see SymPy `sympy.polys.agca.modules.ModuleElement.__eq__`
   */
  equals(other: ModuleInput): boolean {
    try {
      const value = this.module.convert(other);
      return this.module.ambient.zeroContains(this.data.map((a, i) => add(a, neg(at(value.data, i)))));
    } catch (error) { if (error instanceof CoercionFailed) return false; throw error; }
  }
  /**
   * Tests for the additive identity.
   *
   * @returns Whether the value equals zero.
   */
  isZero(): boolean { return this.module.ambient.zeroContains(this.data); }
}

function sameAmbient(a: FreeModule | QuotientModule, b: FreeModule | QuotientModule): boolean {
  if (!a.ring.equals(b.ring) || a.rank !== b.rank) return false;
  if (a instanceof QuotientModule) return b instanceof QuotientModule && a.killedModule.equals(b.killedModule);
  return b instanceof FreeModule;
}

/**
 * Common operations on free modules, submodules and quotient modules.
 *
 * @see SymPy `sympy.polys.agca.modules.Module`
 * @example
 * ```ts
 * import { QQ, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * QQ.oldPolyRing(x).freeModule(2).toString(); // => QQ[x]**2
 * ```
 */
export abstract class Module {
  /** The polynomial arithmetic and relations for this module. */
  readonly context: PolynomialModuleContext;
  /**
   * Specifies the coefficient ring and the number of ambient coordinates.
   *
   * @param ring - Coefficient ring.
   * @param rank - Number of ambient coordinates.
   */
  constructor(
    /**
     * The underlying ring.
     *
     * @see SymPy `sympy.polys.agca.modules.Module.ring`
     */
    readonly ring: Domain,
    /** The number of ambient coordinates. */
    readonly rank: number) { this.context = polynomialModuleContext(ring); }
  /** Identifies the containing module in which coordinates are expressed. */
  abstract readonly ambient: FreeModule | QuotientModule;
  /** The generating elements. */
  abstract readonly gens: readonly ModuleElement[];
  /**
   * Coerces the input into the target domain.
   *
   * @param element - Element to represent or transform.
   * @returns The element in this module.
   * @see SymPy `sympy.polys.agca.modules.Module.convert`
   */
  abstract convert(element: ModuleInput): ModuleElement;
  /**
   * Formats the value as text.
   *
   * @returns The printable representation.
   */
  abstract toString(): string;
  /**
   * Tests membership of the specified element.
   *
   * @param element - Element to represent or transform.
   * @returns Whether the element is a member.
   * @see SymPy `sympy.polys.agca.modules.Module.contains`
   */
  contains(element: ModuleInput): boolean {
    try { this.convert(element); return true; }
    catch (error) { if (error instanceof CoercionFailed) return false; throw error; }
  }
  /**
   * Checks that all the supplied elements belong to this object.
   *
   * @param elements - Entries in their given order.
   * @returns Whether every supplied element is a member.
   * @see SymPy `sympy.polys.agca.modules.Module.subset`
   */
  subset(elements: Iterable<ModuleInput>): boolean { return [...elements].every((e) => this.contains(e)); }
  /**
   * Tests whether the supplied module is contained in this module.
   *
   * @param other - Candidate submodule.
   * @returns Whether this module contains the other module.
   * @see SymPy `sympy.polys.agca.modules.Module.is_submodule`
   */
  isSubmodule(other: unknown): boolean {
    return other instanceof Module && sameAmbient(this.ambient, other.ambient) && other.gens.every((g) => this.contains(g));
  }
  /**
   * Compares the two operands for equality.
   *
   * @param other - Value to compare against.
   * @returns Whether the operands are equal.
   * @see SymPy `sympy.polys.agca.modules.Module.__eq__`
   */
  equals(other: Module): boolean { return this.isSubmodule(other) && other.isSubmodule(this); }
  /**
   * Tests for the additive identity.
   *
   * @returns Whether the value equals zero.
   * @see SymPy `sympy.polys.agca.modules.Module.is_zero`
   */
  isZero(): boolean { return this.gens.every((g) => g.isZero()); }
  /**
   * Takes the span of the supplied elements in the ambient module.
   *
   * @param gens - Generators in their given order.
   * @returns The submodule spanned by the generators.
   * @see SymPy `sympy.polys.agca.modules.Module.submodule`
   */
  submodule(...gens: ModuleInput[]): SubModule {
    return new SubModule(gens.map((g) => this.convert(g)), this.ambient);
  }
  /**
   * Identifies vectors whose difference belongs to the denominator submodule.
   *
   * @param other - Submodule or generators to quotient out.
   * @returns The quotient by the specified submodule.
   * @throws RangeError when the denominator is not a submodule.
   * @see SymPy `sympy.polys.agca.modules.Module.quotient_module`
   */
  quotientModule(other: SubModule | readonly ModuleInput[]): QuotientModule | SubModule {
    const denominator = other instanceof SubModule ? other : this.submodule(...other);
    if (!this.isSubmodule(denominator)) throw new RangeError('denominator must be a submodule');
    const ambient = this.ambient;
    const base = ambient instanceof QuotientModule ? ambient.base : ambient;
    const killed = base.submodule(...denominator.gens.map((g) => g.data), ...ambient.relations());
    const quotient = new QuotientModule(base, killed);
    return this instanceof SubModule ? quotient.submodule(...this.gens.map((g) => g.data)) : quotient;
  }
  /**
   * Forms the span of products of ideal generators with module generators.
   *
   * @param ideal - Ideal defining the operation.
   * @returns The submodule spanned by products with the ideal.
   * @throws RangeError when the ideal belongs to another ring.
   * @see SymPy `sympy.polys.agca.modules.Module.multiply_ideal`
   */
  multiplyIdeal(ideal: ModuleImplementedIdeal): SubModule {
    if (!this.ring.equals(ideal.ring)) throw new RangeError('ideal must have the same ring');
    return this.submodule(...ideal.gens.flatMap((c) => this.gens.map((g) => g.mul(c))));
  }
  /**
   * The submodule generated by products with a scalar or an ideal.
   *
   * @param scalar - Scalar used to scale the value.
   * @returns The product in operand order.
   * @see SymPy `sympy.polys.agca.modules.Module.__mul__`
   */
  mul(scalar: ExprLike | ModuleImplementedIdeal): SubModule {
    return this.multiplyIdeal(typeof scalar === 'object' && 'gens' in scalar ? scalar : this.ring.ideal(scalar));
  }
}

/**
 * A finite free module over a polynomial ring or a quotient of one.
 *
 * @see SymPy `sympy.polys.agca.modules.FreeModule`
 */
export class FreeModule extends Module {
  /** Identifies the containing module in which coordinates are expressed. */
  readonly ambient = this;
  /**
   * Creates a coordinate module of the specified rank over the coefficient ring.
   *
   * @param ring - Coefficient ring.
   * @param rank - Number of ambient coordinates.
   * @throws RangeError when the rank is negative.
   * @throws NotImplementedError when the coefficient domain is not a field.
   */
  constructor(ring: Domain, rank: IntLike) {
    const n = intArg(rank, 'rank');
    if (n < 0) throw new RangeError('rank must be nonnegative');
    super(ring, n);
    if (!this.context.domain.isField) throw new NotImplementedError('module standard bases require a coefficient field');
  }
  /**
   * Lists the standard basis vectors of the coordinate module.
   *
   * @returns The generating elements.
   */
  get gens(): readonly ModuleElement[] { return this.basis(); }
  /**
   * Counts the independent generators of the Lie algebra.
   *
   * @returns The standard coordinate vectors.
   * @see SymPy `sympy.polys.agca.modules.FreeModule.basis`
   */
  basis(): ModuleElement[] { return units(this.rank).map((v) => this.convert(v)); }
  /**
   * Formats the value as text.
   *
   * @returns The printable representation.
   * @see SymPy `sympy.polys.agca.modules.FreeModule.__repr__`
   */
  toString(): string {
    const name = this.ring.toString();
    return `${this.context.relations.length ? `(${name})` : name}**${this.rank}`;
  }
  /**
   * Coerces the input into the target domain.
   *
   * @param element - Element to represent or transform.
   * @returns The element in this module.
   * @throws CoercionFailed when the value cannot be represented in the target domain.
   * @see SymPy `sympy.polys.agca.modules.FreeModule.convert`
   */
  convert(element: ModuleInput): ModuleElement {
    if (element instanceof ModuleElement && element.module.ambient instanceof QuotientModule) throw new CoercionFailed('a quotient coset has no canonical lift to a free module');
    const value = element instanceof ModuleElement ? element.data : element;
    const scalar = groundToSympy(value);
    const data = scalar instanceof Expr && isZero(scalar) ? zeros(this.rank) : Array.isArray(value) ? value : undefined;
    if (!data || data.length !== this.rank) throw new CoercionFailed(`expected a vector of length ${this.rank}`);
    return new ModuleElement(this, data.map((v: ExprLike) => this.ring.fromSympy(v)));
  }
  /**
   * Relations of the coefficient ring lifted to each component.
   *
   * @returns The defining relation vectors.
   * @internal
   */
  relations(): Expr[][] {
    return this.context.relations.flatMap((c) => units(this.rank).map((v) => v.map((e) => mul(c, e))));
  }
  /**
   * Tests whether the coordinate vector represents zero modulo the defining relations.
   *
   * @param data - Coordinate data representing the element.
   * @returns Whether the vector represents zero.
   */
  zeroContains(data: readonly Expr[]): boolean { return data.every((e) => isZero(this.ring.canon(e))); }
  /**
   * The same module as a quotient over the polynomial coefficient ring.
   *
   * @returns The corresponding quotient module.
   */
  get quot(): QuotientModule {
    const base = this.context.polynomialRing.freeModule(this.rank);
    return new QuotientModule(base, base.submodule(...this.relations()));
  }
  /**
   * Lift a vector over R/I to its coset in R**n / I*R**n.
   *
   * @param element - Element to represent or transform.
   * @returns The lifted module element.
   */
  lift(element: ModuleInput): ModuleElement { return this.quot.convert(this.convert(element).data); }
}

/**
 * A quotient F/N, represented by vectors of F.
 *
 * @see SymPy `sympy.polys.agca.modules.QuotientModule`
 */
export class QuotientModule extends Module {
  /** Identifies the containing module in which coordinates are expressed. */
  readonly ambient = this;
  /**
   * Identifies two vectors of the base module when their difference belongs to the specified
   * submodule.
   *
   * @param base - Free module to quotient.
   * @param killedModule - Submodule to identify with zero.
   * @throws RangeError when the denominator lies outside the base module.
   */
  constructor(
    /**
     * The free module before taking the quotient.
     *
     * @see SymPy `sympy.polys.agca.modules.QuotientModule.base`
     */
    readonly base: FreeModule,
    /**
     * The submodule whose elements represent zero in the quotient.
     *
     * @see SymPy `sympy.polys.agca.modules.QuotientModule.killed_module`
     */
    readonly killedModule: SubModule) {
    super(base.ring, base.rank);
    if (!base.isSubmodule(killedModule)) throw new RangeError('denominator must be a submodule of the base');
  }
  /**
   * Projects the generators of the base module onto the quotient.
   *
   * @returns The generating elements.
   */
  get gens(): readonly ModuleElement[] { return this.base.gens.map((g) => this.convert(g)); }
  /**
   * Formats the value as text.
   *
   * @returns The printable representation.
   * @see SymPy `sympy.polys.agca.modules.QuotientModule.__repr__`
   */
  toString(): string { return `${this.base.toString()}/${this.killedModule.toString()}`; }
  /**
   * Coerces the input into the target domain.
   *
   * @param element - Element to represent or transform.
   * @returns The element in this module.
   * @throws CoercionFailed when the value cannot be represented in the target domain.
   * @see SymPy `sympy.polys.agca.modules.QuotientModule.convert`
   */
  convert(element: ModuleInput): ModuleElement {
    if (element instanceof ModuleElement && element.module.ambient instanceof QuotientModule) {
      if (!this.killedModule.isSubmodule(element.module.ambient.killedModule)) throw new CoercionFailed('quotient relations are not contained in the target');
      return new ModuleElement(this, this.base.convert(element.data).data);
    }
    return new ModuleElement(this, this.base.convert(element).data);
  }
  /**
   * Includes the vectors killed by the quotient along with the base module relations.
   *
   * @returns The defining relation vectors.
   */
  relations(): Expr[][] { return [...this.killedModule.gens.map((g) => [...g.data]), ...this.base.relations()]; }
  /**
   * Tests whether the coordinate vector represents zero modulo the defining relations.
   *
   * @param data - Coordinate data representing the element.
   * @returns Whether the vector represents zero.
   */
  zeroContains(data: readonly Expr[]): boolean { return this.killedModule.contains(data); }
}

/**
 * Represents the submodule spanned by a finite list of generators.
 *
 * @see SymPy `sympy.polys.agca.modules.SubModule`
 */
export class SubModule extends Module {
  /**
   * The generating elements.
   *
   * @see SymPy `sympy.polys.agca.modules.SubModule.gens`
   */
  readonly gens: readonly ModuleElement[];
  /** Identifies the containing module in which coordinates are expressed. */
  readonly ambient: FreeModule | QuotientModule;
  private basisCache?: Sdm[];
  private extendedCache?: [Sdm[], Sdm[]];
  private readonly order: SdmOrder;
  /**
   * Generates a submodule inside the supplied ambient module.
   *
   * @param gens - Generators in their given order.
   * @param container - Ambient module containing the generators.
   * @param elimination - Use an elimination order on the module components.
   * @param componentOrder - Ordering of module components.
   */
  constructor(gens: readonly ModuleInput[],
    /**
     * The module in which the generators are interpreted.
     *
     * @see SymPy `sympy.polys.agca.modules.SubModule.container`
     */
    readonly container: FreeModule | QuotientModule, elimination = false, private readonly componentOrder: string | MonomialOrdering = lex) {
    super(container.ring, container.rank);
    this.ambient = container;
    this.gens = Object.freeze(gens.map((g) => container.convert(g)));
    const componentKey = monomialKey(componentOrder);
    this.order = elimination
      ? (m) => [-first(m), this.context.order.key(m.slice(1))]
      : (m) => [this.context.order.key(m.slice(1)), componentKey([first(m)])];
  }
  /**
   * Compares the two operands for equality.
   *
   * @param other - Value to compare against.
   * @returns Whether the operands are equal.
   * @see SymPy `sympy.polys.agca.modules.SubModule.__eq__`
   */
  override equals(other: Module): boolean {
    return (!(other instanceof SubModule) || String(this.componentOrder) === String(other.componentOrder)) && super.equals(other);
  }
  /**
   * Formats the value as text.
   *
   * @returns The printable representation.
   * @see SymPy `sympy.polys.agca.modules.SubModule.__repr__`
   */
  toString(): string { return `<${this.gens.map((g) => g.toString()).join(', ')}>`; }
  /**
   * Adds the other operand to this value.
   *
   * @param element - Element to represent or transform.
   * @returns The sum of the operands.
   * @see SymPy `sympy.polys.agca.modules.SubModule.__add__`
   */
  add(element: ModuleInput): ModuleElement { return this.container.quotientModule(this).convert(element); }
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
  /**
   * Coerces the input into the target domain.
   *
   * @param element - Element to represent or transform.
   * @returns The element in this module.
   * @throws CoercionFailed when the value cannot be represented in the target domain.
   * @see SymPy `sympy.polys.agca.modules.SubModule.convert`
   */
  convert(element: ModuleInput): ModuleElement {
    const vector = this.container.convert(element).data;
    if (sdmNfMora(this.sparse(vector), this.basis(), this.order, this.context.domain).length) throw new CoercionFailed('vector is not in this submodule');
    return new ModuleElement(this, vector);
  }
  /**
   * Checks whether the generators span the containing module.
   *
   * @returns Whether the submodule equals its ambient module.
   * @see SymPy `sympy.polys.agca.modules.SubModule.is_full_module`
   */
  isFullModule(): boolean { return this.container.gens.every((g) => this.contains(g)); }
  /**
   * Generates the sum from the generators of both operands.
   *
   * @param other - Submodule of the same ambient module.
   * @returns The sum generated by the two operands.
   * @throws RangeError when the submodules have different ambient modules.
   * @see SymPy `sympy.polys.agca.modules.SubModule.union`
   */
  union(other: SubModule): SubModule {
    this.checkAmbient(other);
    return this.container.submodule(...this.gens, ...other.gens);
  }
  private checkAmbient(other: SubModule): void {
    if (!sameAmbient(this.container, other.container)) throw new RangeError('submodules must have the same ambient module');
  }
  /**
   * Weak normal form, zero exactly for elements in the submodule.
   *
   * @param element - Element to represent or transform.
   * @param fully - Request full reduction of the representative.
   * @returns A reduced representative of the element.
   * @see SymPy `sympy.polys.agca.modules.SubModule.reduce_element`
   */
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
  /**
   * Writes the element as a linear combination of generators.
   *
   * @param element - Element to represent or transform.
   * @returns Coefficients expressing the element in the given generators.
   * @throws RangeError when the vector does not belong to the submodule.
   * @see SymPy `sympy.polys.agca.modules.SubModule.in_terms_of_generators`
   */
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
  /**
   * Finds the linear relations among the given generators.
   *
   * @returns The module of relations among the generators.
   * @see SymPy `sympy.polys.agca.modules.SubModule.syzygy_module`
   */
  syzygyModule(): SubModule {
    const generators = this.lifted(), r = this.rank, k = generators.length;
    const F = this.context.polynomialRing.freeModule(r + k);
    const identity = units(k);
    const augmented = new SubModule(generators.map((g, i) => [...g, ...at(identity, i)]), F, true);
    const vectors = augmented.basis().map((g) => augmented.vector(g, r + k));
    const result = vectors.filter((g) => g.slice(0, r).every((e) => isZero(e))).map((g) => g.slice(r, r + this.gens.length));
    return this.ring.freeModule(this.gens.length).submodule(...result.filter((g) => g.some((e) => !isZero(e))));
  }
  /**
   * Computes the intersection and optionally expresses its generators in each input basis.
   *
   * @param other - Submodule of the same ambient module.
   * @returns The intersection submodule.
   * @throws RangeError when the submodules have different ambient modules.
   * @see SymPy `sympy.polys.agca.modules.SubModule.intersect`
   */
  intersect(other: SubModule): SubModule;
  /**
   * Computes the intersection and optionally expresses its generators in each input basis.
   *
   * @param other - Submodule of the same ambient module.
   * @param relations - Include coefficient relations for the resulting generators.
   * @returns The intersection and its expressions in both generating sets.
   * @throws RangeError when the submodules have different ambient modules.
   * @see SymPy `sympy.polys.agca.modules.SubModule.intersect`
   */
  intersect(other: SubModule, relations: true): [SubModule, Expr[][], Expr[][]];
  /**
   * Computes the intersection and optionally expresses its generators in each input basis.
   *
   * @param other - Submodule of the same ambient module.
   * @param relations - Include coefficient relations for the resulting generators.
   * @returns The intersection submodule.
   * @throws RangeError when the submodules have different ambient modules.
   * @see SymPy `sympy.polys.agca.modules.SubModule.intersect`
   */
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
  /**
   * Finds the scalars sending every divisor generator into this submodule.
   *
   * @param other - Divisor submodule.
   * @returns The ideal of scalars taking the divisor submodule into this one.
   * @throws NotImplementedError when relations are requested and the divisor does not have exactly
   *   one generator.
   * @throws RangeError when the submodules have different ambient modules.
   * @see SymPy `sympy.polys.agca.modules.SubModule.module_quotient`
   */
  moduleQuotient(other: SubModule): ModuleImplementedIdeal;
  /**
   * Finds the scalars sending every divisor generator into this submodule.
   *
   * @param other - Divisor submodule.
   * @param relations - Include coefficient relations for the resulting generators.
   * @returns The quotient ideal and relations for its generators.
   * @throws NotImplementedError when relations are requested and the divisor does not have exactly
   *   one generator.
   * @throws RangeError when the submodules have different ambient modules.
   * @see SymPy `sympy.polys.agca.modules.SubModule.module_quotient`
   */
  moduleQuotient(other: SubModule, relations: true): [ModuleImplementedIdeal, Expr[][]];
  /**
   * Finds the scalars sending every divisor generator into this submodule.
   *
   * @param other - Divisor submodule.
   * @param relations - Include coefficient relations for the resulting generators.
   * @returns The ideal of scalars taking the divisor submodule into this one.
   * @throws NotImplementedError when relations are requested and the divisor does not have exactly
   *   one generator.
   * @throws RangeError when the submodules have different ambient modules.
   * @see SymPy `sympy.polys.agca.modules.SubModule.module_quotient`
   */
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

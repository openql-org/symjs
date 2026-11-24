// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/agca/homomorphisms.py), Copyright (c)
// 2006-2023 SymPy Development Team, BSD 3-Clause (see LICENSE).

import { at } from '../../core/guard';
import { add, mul } from '../../core/ops';
import type { Expr, ExprLike } from '../../core/nodes';
import { str } from '../../printing/str';
import { type Module, type ModuleElement, SubModule, QuotientModule, type ModuleInput } from './modules';

/**
 * A linear map given by the images of the ambient coordinate vectors.
 *
 * @see SymPy `sympy.polys.agca.homomorphisms.ModuleHomomorphism`
 * @example
 * ```ts
 * import { QQ, homomorphism, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * const F = QQ.oldPolyRing(x).freeModule(2);
 * const identity = homomorphism(F, F, [[1, 0], [0, 1]]);
 * identity.apply([1, 1]).toString(); // => [1, 1]
 * ```
 */
export class ModuleHomomorphism {
  /** The images of the ambient coordinate vectors. */
  readonly matrix: readonly ModuleElement[];
  /**
   * Formats the value as text.
   *
   * @returns The printable representation.
   */
  toString(): string {
    const rows = Array.from({ length: this.codomain.rank }, (_, j) => this.matrix.map((column) => str(at(column.data, j))));
    const widths = this.matrix.map((_, i) => Math.max(0, ...rows.map((r) => at(r, i).length)));
    const printed = rows.map((r) => `[${r.map((s, i) => s.padStart(at(widths, i))).join(', ')}]`);
    const matrix = !this.domain.rank || !this.codomain.rank ? `Matrix(${this.codomain.rank}, ${this.domain.rank}, [])` : printed.length === 1 ? `Matrix([${at(printed, 0)}])` : `Matrix([\n${printed.join(',\n')}])`;
    const lines = matrix.split('\n');
    const label = ` : ${this.domain.toString()} -> ${this.codomain.toString()}`;
    return lines.map((line, i) => line + (i === Math.floor(lines.length / 2) ? label : ' '.repeat(label.length))).join('\n');
  }
  /**
   * Defines a map between modules by specifying the image of each domain coordinate.
   *
   * @param domain - Module on which the map acts.
   * @param codomain - Target of the homomorphism.
   * @param matrix - Matrix giving the images of the ambient coordinate vectors.
   * @throws RangeError when the modules have different coefficient rings or the coordinate images do
   *   not define a map into the codomain that respects the domain relations.
   */
  constructor(
    /**
     * The source module of the homomorphism.
     *
     * @see SymPy `sympy.polys.agca.homomorphisms.ModuleHomomorphism.domain`
     */
    readonly domain: Module,
    /**
     * The target of the homomorphism.
     *
     * @see SymPy `sympy.polys.agca.homomorphisms.ModuleHomomorphism.codomain`
     */
    readonly codomain: Module, matrix: readonly ModuleInput[]) {
    if (!domain.ring.equals(codomain.ring)) throw new RangeError('homomorphism modules must have the same ring');
    if (matrix.length !== domain.rank) throw new RangeError('one image is required per ambient domain coordinate');
    this.matrix = Object.freeze(matrix.map((v) => codomain.ambient.convert(v)));
    if (!domain.ambient.relations().every((r) => codomain.ambient.zeroContains(this.applyVector(r)))) throw new RangeError('map does not annihilate the domain relations');
    if (!domain.gens.every((g) => codomain.contains(this.applyVector(g.data)))) throw new RangeError('image is not contained in the codomain');
  }
  private applyVector(data: readonly Expr[]): Expr[] {
    return Array.from({ length: this.codomain.rank }, (_, j) => add(...data.map((c, i) => mul(c, at(at(this.matrix, i).data, j)))));
  }
  /**
   * Maps the input into the codomain using the images of the coordinate vectors.
   *
   * @param element - Element to represent or transform.
   * @returns The image of the argument.
   * @see SymPy `sympy.polys.agca.homomorphisms.ModuleHomomorphism.__call__`
   */
  apply(element: ModuleInput): ModuleElement { return this.codomain.convert(this.applyVector(this.domain.convert(element).data)); }
  /**
   * Generates the image from the images of the source generators.
   *
   * @returns The submodule spanned by the images.
   * @see SymPy `sympy.polys.agca.homomorphisms.ModuleHomomorphism.image`
   */
  image(): SubModule { return this.codomain.submodule(...this.domain.gens.map((g) => this.apply(g))); }
  /**
   * Finds the elements of the domain with zero image.
   *
   * @returns The submodule mapped to zero.
   * @see SymPy `sympy.polys.agca.homomorphisms.ModuleHomomorphism.kernel`
   */
  kernel(): SubModule {
    const relations = this.codomain.ambient.submodule(...this.matrix).syzygyModule();
    const ambientKernel = this.domain.ambient.submodule(...relations.gens.map((g) => g.data));
    return this.domain instanceof SubModule ? ambientKernel.intersect(this.domain) : ambientKernel;
  }
  /**
   * Tests the homomorphism for injectivity.
   *
   * @returns Whether the kernel is zero.
   * @see SymPy `sympy.polys.agca.homomorphisms.ModuleHomomorphism.is_injective`
   */
  isInjective(): boolean { return this.kernel().isZero(); }
  /**
   * Tests whether the homomorphism maps onto the target.
   *
   * @returns Whether the image equals the codomain.
   * @see SymPy `sympy.polys.agca.homomorphisms.ModuleHomomorphism.is_surjective`
   */
  isSurjective(): boolean { return this.image().equals(this.codomain); }
  /**
   * Tests whether the homomorphism is both injective and surjective.
   *
   * @returns Whether the map is bijective.
   * @see SymPy `sympy.polys.agca.homomorphisms.ModuleHomomorphism.is_isomorphism`
   */
  isIsomorphism(): boolean { return this.isInjective() && this.isSurjective(); }
  /**
   * Tests for the additive identity.
   *
   * @returns Whether the value equals zero.
   * @see SymPy `sympy.polys.agca.homomorphisms.ModuleHomomorphism.is_zero`
   */
  isZero(): boolean { return this.image().isZero(); }
  /**
   * Restricts the source of the homomorphism to a submodule.
   *
   * @param submodule - Submodule through which to restrict or quotient the map.
   * @returns The map restricted to the given source submodule.
   * @throws RangeError when the proposed domain is not a submodule of the original domain.
   * @see SymPy `sympy.polys.agca.homomorphisms.ModuleHomomorphism.restrict_domain`
   */
  restrictDomain(submodule: Module): ModuleHomomorphism {
    if (!this.domain.isSubmodule(submodule)) throw new RangeError('restriction must be a submodule of the domain');
    return homomorphism(submodule, this.codomain, this.matrix);
  }
  /**
   * Restricts the target to a submodule containing the image.
   *
   * @param submodule - Submodule through which to restrict or quotient the map.
   * @returns The map with the given target submodule.
   * @throws RangeError when the proposed codomain is not a submodule containing the image.
   * @see SymPy `sympy.polys.agca.homomorphisms.ModuleHomomorphism.restrict_codomain`
   */
  restrictCodomain(submodule: Module): ModuleHomomorphism {
    if (!this.codomain.isSubmodule(submodule) || !submodule.isSubmodule(this.image())) throw new RangeError('codomain restriction must contain the image');
    return homomorphism(this.domain, submodule, this.matrix);
  }
  /**
   * Factors the source by a submodule of the kernel.
   *
   * @param submodule - Submodule through which to restrict or quotient the map.
   * @returns The induced map on the quotient.
   * @throws RangeError when the proposed denominator is not contained in the kernel.
   * @see SymPy `sympy.polys.agca.homomorphisms.ModuleHomomorphism.quotient_domain`
   */
  quotientDomain(submodule: SubModule): ModuleHomomorphism {
    if (!this.kernel().isSubmodule(submodule)) throw new RangeError('quotient denominator must lie in the kernel');
    return homomorphism(this.domain.quotientModule(submodule), this.codomain, this.matrix);
  }
  /**
   * Composes the map with projection onto the quotient of its codomain.
   *
   * @param submodule - Submodule through which to restrict or quotient the map.
   * @returns The induced map on the quotient.
   * @see SymPy `sympy.polys.agca.homomorphisms.ModuleHomomorphism.quotient_codomain`
   */
  quotientCodomain(submodule: SubModule): ModuleHomomorphism {
    return homomorphism(this.domain, this.codomain.quotientModule(submodule), this.matrix);
  }
  /**
   * Add maps with the same domain and codomain.
   *
   * @param other - Addend.
   * @returns The sum of the operands.
   * @throws TypeError when the maps do not have the same domain and codomain.
   * @see SymPy `sympy.polys.agca.homomorphisms.ModuleHomomorphism.__add__`
   */
  add(other: unknown): ModuleHomomorphism {
    if (!(other instanceof ModuleHomomorphism) || !this.domain.equals(other.domain) || !this.codomain.equals(other.codomain)) throw new TypeError('homomorphisms must have the same domain and codomain');
    return homomorphism(this.domain, this.codomain, this.matrix.map((g, i) => g.add(at(other.matrix, i))));
  }
  /**
   * Reverses the sign of the value.
   *
   * @returns The additive inverse.
   */
  neg(): ModuleHomomorphism { return this.mul(-1); }
  /**
   * Subtracts the other operand from this value.
   *
   * @param other - Value to subtract.
   * @returns The difference in operand order.
   * @throws TypeError when the operand is not a compatible homomorphism.
   * @see SymPy `sympy.polys.agca.homomorphisms.ModuleHomomorphism.__sub__`
   */
  sub(other: unknown): ModuleHomomorphism {
    if (!(other instanceof ModuleHomomorphism)) throw new TypeError('expected a homomorphism');
    return this.add(other.neg());
  }
  /**
   * Multiplies this value by the factor on its right.
   *
   * @param other - Factor on the right.
   * @returns The composite or scalar multiple of the map.
   * @see SymPy `sympy.polys.agca.homomorphisms.ModuleHomomorphism.__mul__`
   */
  mul(other: ModuleHomomorphism | ExprLike): ModuleHomomorphism {
    return other instanceof ModuleHomomorphism ? this.compose(other)
      : homomorphism(this.domain, this.codomain, this.matrix.map((g) => g.mul(other)));
  }
  /**
   * Divides by the supplied divisor.
   *
   * @param scalar - Divisor.
   * @returns The quotient.
   * @see SymPy `sympy.polys.agca.homomorphisms.ModuleHomomorphism.__truediv__`
   */
  div(scalar: ExprLike): ModuleHomomorphism {
    return homomorphism(this.domain, this.codomain, this.matrix.map((g) => g.div(scalar)));
  }
  /**
   * Compares the two operands for equality.
   *
   * @param other - Value to compare against.
   * @returns Whether the operands are equal.
   * @see SymPy `sympy.polys.agca.homomorphisms.ModuleHomomorphism.__eq__`
   */
  equals(other: unknown): boolean {
    return other instanceof ModuleHomomorphism && this.domain.equals(other.domain) && this.codomain.equals(other.codomain) && this.sub(other).isZero();
  }
  /**
   * Composition this ∘ other.
   *
   * @param other - Homomorphism to apply first.
   * @returns The composition with the other map applied first.
   * @throws RangeError when the intermediate modules are incompatible.
   * @see SymPy `sympy.polys.agca.homomorphisms.ModuleHomomorphism._compose`
   */
  compose(other: ModuleHomomorphism): ModuleHomomorphism {
    if (!this.domain.isSubmodule(other.codomain)) throw new RangeError('composition requires a compatible intermediate module');
    return homomorphism(other.domain, this.codomain, other.matrix.map((g) => this.applyVector(g.data)));
  }
}

/**
 * Construct a map, validating both the image and the relations of the domain.
 *
 * @param domain - Source module.
 * @param codomain - Target module.
 * @param matrix - Images of the ambient coordinate vectors in order.
 * @returns The linear map determined by the coordinate images.
 * @throws RangeError when the modules have different coefficient rings or the coordinate images do
 *   not define a map into the codomain that respects the domain relations.
 * @see SymPy `sympy.polys.agca.homomorphisms.homomorphism`
 * @example
 * ```ts
 * import { QQ, ex, homomorphism, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * const F = QQ.oldPolyRing(x).freeModule(2);
 * const h = homomorphism(F, F, [[1, x], [ex`x**2`, 0]]);
 * h.apply([1, 1]).toString(); // => [x**2 + 1, x]
 * ```
 */
export function homomorphism(domain: Module, codomain: Module, matrix: readonly ModuleInput[]): ModuleHomomorphism {
  if (domain instanceof SubModule && domain.container instanceof QuotientModule) {
    const ambient = domain.container;
    // A presentation of a subquotient includes the generators of its kernel.
    const presented = ambient.submodule(...domain.gens, ...ambient.killedModule.gens.map((g) => g.data));
    return new ModuleHomomorphism(presented, domain === codomain ? presented : codomain, matrix);
  }
  return new ModuleHomomorphism(domain, codomain, matrix);
}

/**
 * The identity map on a module.
 *
 * @param module - Module on which the map acts.
 * @returns The identity endomorphism.
 * @see SymPy `sympy.polys.agca.modules.Module.identity_hom`
 */
export function identityHom(module: Module): ModuleHomomorphism {
  return homomorphism(module, module, Array.from({ length: module.rank }, (_, i) => Array.from({ length: module.rank }, (_, j) => i === j ? 1 : 0)));
}

/**
 * Inclusion of a submodule in its ambient module.
 *
 * @param module - Submodule to include.
 * @returns The canonical inclusion map.
 * @see SymPy `sympy.polys.agca.modules.SubModule.inclusion_hom`
 * @example
 * ```ts
 * import { QQ, inclusionHom, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * const M = QQ.oldPolyRing(x).freeModule(2).submodule([x, x]);
 * inclusionHom(M).apply([x, x]).toString(); // => [x, x]
 * ```
 */
export function inclusionHom(module: SubModule): ModuleHomomorphism {
  return identityHom(module.container).restrictDomain(module);
}

/**
 * Natural projection onto a quotient or a submodule of a quotient.
 *
 * @param module - Target quotient module or submodule of a quotient.
 * @returns The natural projection.
 * @throws TypeError when the submodule does not lie in a quotient.
 * @see SymPy `sympy.polys.agca.modules.QuotientModule.quotient_hom`
 * @example
 * ```ts
 * import { QQ, quotientHom, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * const F = QQ.oldPolyRing(x).freeModule(2);
 * const M = F.quotientModule([[1, 2], [1, x]]);
 * quotientHom(M).apply([1, 2]).isZero(); // => True
 * ```
 */
export function quotientHom(module: QuotientModule | SubModule): ModuleHomomorphism {
  if (module instanceof QuotientModule) return identityHom(module.base).quotientCodomain(module.killedModule);
  const ambient = module.container;
  if (!(ambient instanceof QuotientModule)) throw new TypeError('expected a submodule of a quotient');
  const preimage = ambient.base.submodule(...module.gens.map((g) => g.data), ...ambient.killedModule.gens);
  return identityHom(preimage).quotientCodomain(ambient.killedModule);
}

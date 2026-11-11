// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/agca/homomorphisms.py), Copyright (c)
// 2006-2023 SymPy Development Team, BSD 3-Clause (see LICENSE).

import { at } from '../../core/guard';
import { add, mul } from '../../core/ops';
import type { Expr } from '../../core/nodes';
import { str } from '../../printing/str';
import { type Module, type ModuleElement, SubModule, QuotientModule, type ModuleInput } from './modules';

/** A linear map given by the images of the ambient coordinate vectors. */
export class ModuleHomomorphism {
  readonly matrix: readonly ModuleElement[];
  /** SymPy's matrix representation with the domain and codomain beside it. */
  toString(): string {
    const rows = Array.from({ length: this.codomain.rank }, (_, j) => this.matrix.map((column) => str(at(column.data, j))));
    const widths = this.matrix.map((_, i) => Math.max(0, ...rows.map((r) => at(r, i).length)));
    const printed = rows.map((r) => `[${r.map((s, i) => s.padStart(at(widths, i))).join(', ')}]`);
    const matrix = !this.domain.rank || !this.codomain.rank ? `Matrix(${this.codomain.rank}, ${this.domain.rank}, [])` : printed.length === 1 ? `Matrix([${at(printed, 0)}])` : `Matrix([\n${printed.join(',\n')}])`;
    const lines = matrix.split('\n');
    const label = ` : ${this.domain.toString()} -> ${this.codomain.toString()}`;
    return lines.map((line, i) => line + (i === Math.floor(lines.length / 2) ? label : ' '.repeat(label.length))).join('\n');
  }
  constructor(readonly domain: Module, readonly codomain: Module, matrix: readonly ModuleInput[]) {
    if (!domain.ring.equals(codomain.ring)) throw new RangeError('homomorphism modules must have the same ring');
    if (matrix.length !== domain.rank) throw new RangeError('one image is required per ambient domain coordinate');
    this.matrix = Object.freeze(matrix.map((v) => codomain.ambient.convert(v)));
    if (!domain.ambient.relations().every((r) => codomain.ambient.zeroContains(this.applyVector(r)))) throw new RangeError('map does not annihilate the domain relations');
    if (!domain.gens.every((g) => codomain.contains(this.applyVector(g.data)))) throw new RangeError('image is not contained in the codomain');
  }
  private applyVector(data: readonly Expr[]): Expr[] {
    return Array.from({ length: this.codomain.rank }, (_, j) => add(...data.map((c, i) => mul(c, at(at(this.matrix, i).data, j)))));
  }
  apply(element: ModuleInput): ModuleElement { return this.codomain.convert(this.applyVector(this.domain.convert(element).data)); }
  image(): SubModule { return this.codomain.submodule(...this.domain.gens.map((g) => this.apply(g))); }
  kernel(): SubModule {
    const relations = this.codomain.ambient.submodule(...this.matrix).syzygyModule();
    const ambientKernel = this.domain.ambient.submodule(...relations.gens.map((g) => g.data));
    return this.domain instanceof SubModule ? ambientKernel.intersect(this.domain) : ambientKernel;
  }
  isInjective(): boolean { return this.kernel().isZero(); }
  isSurjective(): boolean { return this.image().equals(this.codomain); }
  isIsomorphism(): boolean { return this.isInjective() && this.isSurjective(); }
  isZero(): boolean { return this.image().isZero(); }
  restrictDomain(submodule: Module): ModuleHomomorphism {
    if (!this.domain.isSubmodule(submodule)) throw new RangeError('restriction must be a submodule of the domain');
    return homomorphism(submodule, this.codomain, this.matrix);
  }
  restrictCodomain(submodule: Module): ModuleHomomorphism {
    if (!this.codomain.isSubmodule(submodule) || !submodule.isSubmodule(this.image())) throw new RangeError('codomain restriction must contain the image');
    return homomorphism(this.domain, submodule, this.matrix);
  }
  quotientDomain(submodule: SubModule): ModuleHomomorphism {
    if (!this.kernel().isSubmodule(submodule)) throw new RangeError('quotient denominator must lie in the kernel');
    return homomorphism(this.domain.quotientModule(submodule), this.codomain, this.matrix);
  }
  quotientCodomain(submodule: SubModule): ModuleHomomorphism {
    return homomorphism(this.domain, this.codomain.quotientModule(submodule), this.matrix);
  }
  /** Composition this ∘ other. */
  compose(other: ModuleHomomorphism): ModuleHomomorphism {
    if (!this.domain.isSubmodule(other.codomain)) throw new RangeError('composition requires a compatible intermediate module');
    return homomorphism(other.domain, this.codomain, other.matrix.map((g) => this.applyVector(g.data)));
  }
}

/** Construct a map, validating both the image and the relations of the domain. */
export function homomorphism(domain: Module, codomain: Module, matrix: readonly ModuleInput[]): ModuleHomomorphism {
  if (domain instanceof SubModule && domain.container instanceof QuotientModule) {
    const ambient = domain.container;
    // A presentation of a subquotient includes the generators of its kernel.
    const presented = ambient.submodule(...domain.gens, ...ambient.killedModule.gens.map((g) => g.data));
    return new ModuleHomomorphism(presented, codomain, matrix);
  }
  return new ModuleHomomorphism(domain, codomain, matrix);
}

/** The identity map on a module (SymPy Module.identity_hom). */
export function identityHom(module: Module): ModuleHomomorphism {
  return homomorphism(module, module, Array.from({ length: module.rank }, (_, i) => Array.from({ length: module.rank }, (_, j) => i === j ? 1 : 0)));
}

/** Inclusion of a submodule in its ambient module. */
export function inclusionHom(module: SubModule): ModuleHomomorphism {
  return identityHom(module.container).restrictDomain(module);
}

/** Natural projection onto a quotient or a submodule of a quotient. */
export function quotientHom(module: QuotientModule | SubModule): ModuleHomomorphism {
  if (module instanceof QuotientModule) return identityHom(module.base).quotientCodomain(module.killedModule);
  const ambient = module.container;
  if (!(ambient instanceof QuotientModule)) throw new TypeError('expected a submodule of a quotient');
  const preimage = ambient.base.submodule(...module.gens.map((g) => g.data), ...ambient.killedModule.gens);
  return identityHom(preimage).quotientCodomain(ambient.killedModule);
}

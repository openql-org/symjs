// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/agca/ideals.py), Copyright (c)
// 2006-2023 SymPy Development Team, BSD 3-Clause (see LICENSE).

import { first } from '../../core/guard';
import type { Expr, ExprLike } from '../../core/nodes';
import { mul } from '../../core/ops';
import { str } from '../../printing/str';
import { type Domain, domainHooks } from '../domains';
import type { SubModule } from './modules';

/** An ideal represented by a submodule of a rank-one free module. */
export class ModuleImplementedIdeal {
  readonly module: SubModule;
  constructor(readonly ring: Domain, gens: readonly ExprLike[]) {
    this.module = ring.freeModule(1).submodule(...gens.map((g) => [g]));
  }
  get gens(): readonly Expr[] { return this.module.gens.map((g) => first(g.data)); }
  toString(): string { return `<${this.gens.map(str).join(',')}>`; }
  contains(element: ExprLike): boolean { return this.module.contains([element]); }
  subset(elements: Iterable<ExprLike> | ModuleImplementedIdeal): boolean {
    return [...(elements instanceof ModuleImplementedIdeal ? elements.gens : elements)].every((g) => this.contains(g));
  }
  equals(other: ModuleImplementedIdeal): boolean { return this.ring.equals(other.ring) && this.module.equals(other.module); }
  isWholeRing(): boolean { return this.module.isFullModule(); }
  isZero(): boolean { return this.module.isZero(); }
  reduceElement(element: ExprLike): Expr { return first(this.module.reduceElement([element], true).data); }
  private checkRing(other: ModuleImplementedIdeal): void {
    if (!this.ring.equals(other.ring)) throw new RangeError('ideals must have the same ring');
  }
  union(other: ModuleImplementedIdeal): ModuleImplementedIdeal {
    this.checkRing(other);
    return this.ring.ideal(...this.gens, ...other.gens);
  }
  intersect(other: ModuleImplementedIdeal): ModuleImplementedIdeal {
    this.checkRing(other);
    return this.ring.ideal(...this.module.intersect(other.module).gens.map((g) => first(g.data)));
  }
  product(other: ModuleImplementedIdeal): ModuleImplementedIdeal {
    this.checkRing(other);
    return this.ring.ideal(...this.gens.flatMap((a) => other.gens.map((b) => mul(a, b))));
  }
  quotient(other: ModuleImplementedIdeal): ModuleImplementedIdeal {
    this.checkRing(other);
    return this.module.moduleQuotient(other.module);
  }
}

domainHooks.ideal = (ring, gens) => new ModuleImplementedIdeal(ring, gens);

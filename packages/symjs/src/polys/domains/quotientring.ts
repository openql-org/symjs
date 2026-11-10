// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/domains/quotientring.py), Copyright (c)
// 2006-2023 SymPy Development Team, BSD 3-Clause (see LICENSE).

import { NotImplementedError } from '../../core/errors';
import type { Expr, ExprLike } from '../../core/nodes';
import { Domain, domainHooks } from '../domains';
import { ModuleImplementedIdeal } from '../agca/ideals';
import { polynomialModuleContext, registerModuleContext } from './oldpolynomialring';

/** A polynomial quotient ring with expression representatives in normal form. */
export class QuotientRing extends Domain {
  readonly isField = false;
  readonly ground;
  override readonly symbols;
  readonly baseIdeal: ModuleImplementedIdeal;
  constructor(readonly ring: Domain, ideal: ModuleImplementedIdeal | readonly ExprLike[]) {
    super();
    const context = polynomialModuleContext(ring);
    if (!context.order.isGlobal) throw new NotImplementedError('quotient rings with local orders require local-unit normal forms');
    this.baseIdeal = ideal instanceof ModuleImplementedIdeal ? ideal : ring.ideal(...ideal);
    if (!ring.equals(this.baseIdeal.ring)) throw new RangeError('ideal must belong to the base ring');
    this.ground = ring.ground;
    this.symbols = ring.symbols;
    registerModuleContext(this, { ...context, relations: [...context.relations, ...this.baseIdeal.gens] });
  }
  override get dom(): Domain { return this.ring.dom; }
  toString(): string { return `${this.ring.toString()}/${this.baseIdeal.toString()}`; }
  canon(e: Expr): Expr { return this.baseIdeal.reduceElement(this.ring.canon(e)); }
  fromSympy(e: ExprLike): Expr { return this.canon(this.ring.fromSympy(e)); }
  override equals(other: Domain): boolean { return other instanceof QuotientRing && this.ring.equals(other.ring) && this.baseIdeal.equals(other.baseIdeal); }
  getField(): Domain { throw new NotImplementedError('a quotient ring need not have a fraction field'); }
}

domainHooks.quotientRing = (ring, ideal) => new QuotientRing(ring, ideal);

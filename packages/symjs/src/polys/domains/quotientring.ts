// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/domains/quotientring.py), Copyright (c)
// 2006-2023 SymPy Development Team, BSD 3-Clause (see LICENSE).

import { NotImplementedError } from '../../core/errors';
import type { Expr, ExprLike } from '../../core/nodes';
import { Domain, domainHooks } from '../domains';
import { ModuleImplementedIdeal } from '../agca/ideals';
import { polynomialModuleContext, registerModuleContext } from './oldpolynomialring';

/**
 * A polynomial quotient ring with expression representatives in normal form.
 *
 * @see SymPy `sympy.polys.domains.quotientring.QuotientRing`
 * @example
 * ```ts
 * import { QQ, ex, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * const ring = QQ.oldPolyRing(x);
 * ring.quotientRing(ring.ideal(ex`x**3 + 1`)).toString(); // => QQ[x]/<x**3 + 1>
 * ```
 */
export class QuotientRing extends Domain {
  /**
   * Indicates whether the domain supports field arithmetic.
   *
   * @see SymPy `sympy.polys.domains.quotientring.QuotientRing.is_Field`
   */
  readonly isField = false;
  /** The identifier for the underlying coefficient domain. */
  readonly ground;
  /** The ordered polynomial generators. */
  override readonly symbols;
  /**
   * The ideal by which the polynomial ring is quotiented.
   *
   * @see SymPy `sympy.polys.domains.quotientring.QuotientRing.base_ideal`
   */
  readonly baseIdeal: ModuleImplementedIdeal;
  /**
   * Forms residue classes of the base polynomial ring modulo the given ideal.
   *
   * @param ring - Coefficient ring.
   * @param ideal - Ideal defining the operation.
   * @throws RangeError when the ideal belongs to a different ring.
   */
  constructor(
    /**
     * The underlying ring.
     *
     * @see SymPy `sympy.polys.domains.quotientring.QuotientRing.ring`
     */
    readonly ring: Domain, ideal: ModuleImplementedIdeal | readonly ExprLike[]) {
    super();
    const context = polynomialModuleContext(ring);
    this.baseIdeal = ideal instanceof ModuleImplementedIdeal ? ideal : ring.ideal(...ideal);
    if (!ring.equals(this.baseIdeal.ring)) throw new RangeError('ideal must belong to the base ring');
    this.ground = ring.ground;
    this.symbols = ring.symbols;
    registerModuleContext(this, { ...context, relations: [...context.relations, ...this.baseIdeal.gens] });
  }
  /**
   * The underlying coefficient domain.
   *
   * @returns The underlying coefficient domain.
   */
  override get dom(): Domain { return this.ring.dom; }
  /**
   * Formats the value as text.
   *
   * @returns The printable representation.
   * @see SymPy `sympy.polys.domains.quotientring.QuotientRing.__str__`
   */
  toString(): string { return `${this.ring.toString()}/${this.baseIdeal.toString()}`; }
  /**
   * Reduces the expression to the canonical form for this domain.
   *
   * @param e - Expression to represent in this domain.
   * @returns The canonical expression in this domain.
   */
  canon(e: Expr): Expr { return this.baseIdeal.reduceElement(this.ring.canon(e)); }
  /**
   * Interprets a symbolic expression in this domain.
   *
   * @param e - Expression to represent in this domain.
   * @returns The expression converted into the domain.
   * @see SymPy `sympy.polys.domains.quotientring.QuotientRing.from_sympy`
   */
  fromSympy(e: ExprLike): Expr { return this.canon(this.ring.fromSympy(e)); }
  /**
   * Compares the two operands for equality.
   *
   * @param other - Value to compare against.
   * @returns Whether the operands are equal.
   * @see SymPy `sympy.polys.domains.quotientring.QuotientRing.__eq__`
   */
  override equals(other: Domain): boolean { return other instanceof QuotientRing && this.ring.equals(other.ring) && this.baseIdeal.equals(other.baseIdeal); }
  /**
   * Finds the field associated with this domain.
   *
   * @returns The associated field.
   * @throws NotImplementedError when a fraction field is requested for the quotient ring.
   * @see SymPy `sympy.polys.domains.quotientring.QuotientRing.get_field`
   */
  getField(): Domain { throw new NotImplementedError('a quotient ring need not have a fraction field'); }
}

domainHooks.quotientRing = (ring, ideal) => new QuotientRing(ring, ideal);

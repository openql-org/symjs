// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/domains/expressionrawdomain.py), Copyright
// (c) 2006-2023 SymPy Development Team, BSD 3-Clause License (see LICENSE).

/**
 * @file The domain EXRAW of raw expressions (SymPy ExpressionRawDomain):
 * unlike EX, elements are kept exactly as given, without simplification.
 */

import type { ExprLike } from '../../core/nodes';
import { Expr } from '../../core/nodes';
import { add, sympify } from '../../core/ops';
import { Domain, type UnificationKind } from '../domains';

/**
 * Represents arbitrary symbolic expressions without applying simplification during conversion.
 *
 * @see SymPy `sympy.polys.domains.expressionrawdomain.ExpressionRawDomain`
 */
export class ExpressionRawDomain extends Domain {
  /** The identifier for the underlying coefficient domain. */
  readonly ground = 'EX' as const;
  /**
   * Indicates whether the domain supports field arithmetic.
   *
   * @see SymPy `sympy.polys.domains.expressionrawdomain.ExpressionRawDomain.is_Field`
   */
  readonly isField = true;
  /**
   * Formats the value as text.
   *
   * @returns The printable representation.
   * @see SymPy `sympy.polys.domains.expressionrawdomain.ExpressionRawDomain.__str__`
   */
  toString(): string {
    return 'EXRAW';
  }
  protected override get unificationKind(): UnificationKind {
    return 'EXRAW';
  }
  /**
   * Checks the characteristic of the coefficient ring.
   *
   * @returns Whether the characteristic is zero.
   * @see SymPy `sympy.polys.domains.expressionrawdomain.ExpressionRawDomain.has_CharacteristicZero`
   */
  override get hasCharacteristicZero(): boolean {
    return true;
  }
  /**
   * Reduces the expression to the canonical form for this domain.
   *
   * @param e - Expression to represent in this domain.
   * @returns The canonical expression in this domain.
   */
  canon(e: Expr): Expr {
    return e;
  }
  /**
   * Accepts a symbolic expression as an element of the raw expression domain.
   *
   * @param e - Expression to represent in this domain.
   * @returns The expression converted into the domain.
   * @see SymPy `sympy.polys.domains.expressionrawdomain.ExpressionRawDomain.from_sympy`
   */
  fromSympy(e: ExprLike): Expr {
    return sympify(e);
  }
  /**
   * Coerces the input into the target domain.
   *
   * @param a - Element on which to operate.
   * @param base - Source domain when converting an existing element.
   * @returns The value represented in the target domain.
   * @see SymPy `sympy.polys.domains.expressionrawdomain.ExpressionRawDomain.convert`
   */
  override convert(a: unknown, base?: Domain): Expr {
    return (base ?? this).toSympy(a);
  }
  /**
   * Interprets an expression as an element of the raw expression domain.
   *
   * @param args - Value or coefficients defining the domain element.
   * @returns The newly constructed element.
   * @see SymPy `sympy.polys.domains.expressionrawdomain.ExpressionRawDomain.new`
   */
  override new(...args: unknown[]): Expr {
    return this.convert(args[0]);
  }
  /**
   * Checks whether the input already belongs to the native element type.
   *
   * @param a - Element on which to operate.
   * @returns Whether the value is a native element of the domain.
   * @see SymPy `sympy.polys.domains.expressionrawdomain.ExpressionRawDomain.of_type`
   */
  override ofType(a: unknown): boolean {
    return a instanceof Expr;
  }
  /**
   * Finds the field associated with this domain.
   *
   * @returns The associated field.
   * @see SymPy `sympy.polys.domains.expressionrawdomain.ExpressionRawDomain.get_field`
   */
  getField(): Domain {
    return this;
  }
  /**
   * The sum of the items, unevaluated beyond Add.
   *
   * @param items - Terms to sum.
   * @returns The sum of the terms.
   * @see SymPy `sympy.polys.domains.expressionrawdomain.ExpressionRawDomain.sum`
   */
  sum(items: readonly Expr[]): Expr {
    return add(...items);
  }
}

/**
 * The domain of symbolic expressions kept in their original form.
 *
 * @see SymPy `sympy.polys.domains.EXRAW`
 */
export const EXRAW: ExpressionRawDomain = new ExpressionRawDomain();

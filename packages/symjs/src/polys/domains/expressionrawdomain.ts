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
import { Domain } from '../domains';

/** SymPy ExpressionRawDomain: arbitrary expressions, not simplified. */
export class ExpressionRawDomain extends Domain {
  readonly ground = 'EX' as const;
  readonly isField = true;
  toString(): string {
    return 'EXRAW';
  }
  canon(e: Expr): Expr {
    return e;
  }
  /** The expression itself (SymPy from_sympy); throws CoercionFailed for a non-expression. */
  fromSympy(e: ExprLike): Expr {
    return sympify(e);
  }
  /** The value as an expression (SymPy convert_from: K.to_sympy(a)); throws CoercionFailed. */
  override convert(a: unknown, base?: Domain): Expr {
    return (base ?? this).toSympy(a);
  }
  override new(...args: unknown[]): Expr {
    return this.convert(args[0]);
  }
  override ofType(a: unknown): boolean {
    return a instanceof Expr;
  }
  getField(): Domain {
    return this;
  }
  /** The sum of the items, unevaluated beyond Add (SymPy sum). */
  sum(items: readonly Expr[]): Expr {
    return add(...items);
  }
}

/** SymPy EXRAW. */
export const EXRAW: ExpressionRawDomain = new ExpressionRawDomain();

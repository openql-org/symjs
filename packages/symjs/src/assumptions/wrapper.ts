// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Assumption queries that use the new assumptions when they are given
 * (SymPy sympy.assumptions.wrapper): is_infinite, is_extended_real and
 * is_extended_nonnegative. Without assumptions they are the facts of the
 * expression itself (SymPy `obj.is_infinite`, ...).
 */

import type { ExprLike } from '../core/nodes';
import type { Assumption } from '../core/refine';
import { Q, ask } from '../core/refine';
import { sympify } from '../core/ops';
import { fact } from '../core/exprfacts';
import type { Truth } from '../core/truth';
import { toTruth } from '../core/truth';

/** The fact of obj (without assumptions) or what ask decides under them. */
function query(obj: ExprLike, name: 'infinite' | 'extended_real' | 'extended_nonnegative' | 'integer' | 'odd', assumptions: Assumption | undefined): Truth {
  if (assumptions === undefined) return toTruth(fact(sympify(obj), name));
  return ask(Q[name](obj), assumptions);
}

/** SymPy is_infinite: Q.infinite of obj under the assumptions ('unknown' when undecided). */
export function isInfinite(obj: ExprLike, assumptions?: Assumption): Truth {
  return query(obj, 'infinite', assumptions);
}

/** SymPy is_extended_real: Q.extended_real of obj under the assumptions. */
export function isExtendedReal(obj: ExprLike, assumptions?: Assumption): Truth {
  return query(obj, 'extended_real', assumptions);
}

/** SymPy is_extended_nonnegative: Q.extended_nonnegative of obj under the assumptions. */
export function isExtendedNonnegative(obj: ExprLike, assumptions?: Assumption): Truth {
  return query(obj, 'extended_nonnegative', assumptions);
}

/** An expression with local assumptions for integer and parity queries. */
export class AssumptionsWrapper {
  constructor(readonly expr: ExprLike, readonly assumptions?: Assumption) {}

  get isInteger(): Truth {
    return query(this.expr, 'integer', this.assumptions);
  }

  get isOdd(): Truth {
    return query(this.expr, 'odd', this.assumptions);
  }
}

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Assumption queries that use the new assumptions when they are given
 * (SymPy sympy.assumptions.wrapper): is_infinite, is_extended_real and
 * is_extended_nonnegative.
 */

import type { ExprLike } from '../core/nodes';
import type { Assumption } from '../core/refine';
import { Q, ask } from '../core/refine';
import type { Truth } from '../core/truth';

/** SymPy is_infinite: Q.infinite of obj under the assumptions ('unknown' when undecided). */
export function isInfinite(obj: ExprLike, assumptions: Assumption = true): Truth {
  return ask(Q.infinite(obj), assumptions);
}

/** SymPy is_extended_real: Q.extended_real of obj under the assumptions. */
export function isExtendedReal(obj: ExprLike, assumptions: Assumption = true): Truth {
  return ask(Q.extended_real(obj), assumptions);
}

/** SymPy is_extended_nonnegative: Q.extended_nonnegative of obj under the assumptions. */
export function isExtendedNonnegative(obj: ExprLike, assumptions: Assumption = true): Truth {
  return ask(Q.extended_nonnegative(obj), assumptions);
}

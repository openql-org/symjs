// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import type { ExprLike } from '../core/nodes';
import type { Truth } from '../core/truth';
import { sub } from '../core/ops';
import { isLt } from '../core/relational';
import { abs } from '../functions/elementary/elementary';
import { float } from './floatctor';

/**
 * Tests whether the absolute difference between the operands is strictly less than `epsilon`.
 *
 * @param a - The first operand.
 * @param b - The second operand.
 * @param epsilon - The tolerance for the numerical comparison.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 * @see SymPy `sympy.core.numbers.Float.epsilon_eq`
 */
export function epsilonEq(a: ExprLike, b: ExprLike, epsilon: ExprLike = 1e-15): Truth {
  return isLt(abs(sub(a, b)), float(epsilon));
}

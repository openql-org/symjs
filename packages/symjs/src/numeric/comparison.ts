// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import type { ExprLike } from '../core/nodes';
import type { Truth } from '../core/truth';
import { sub } from '../core/ops';
import { isLt } from '../core/relational';
import { abs } from '../functions/elementary/elementary';
import { float } from './floatctor';

/** SymPy Float.epsilon_eq: strict comparison using an absolute tolerance. */
export function epsilonEq(a: ExprLike, b: ExprLike, epsilon: ExprLike = 1e-15): Truth {
  return isLt(abs(sub(a, b)), float(epsilon));
}

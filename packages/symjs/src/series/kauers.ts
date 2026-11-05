// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Finite differences (SymPy sympy.series.kauers): the forward
 * difference of an expression and Kauers' difference of a sum.
 */

import type { Expr, ExprLike } from '../core/nodes';
import { sub, sympify } from '../core/ops';
import { subs } from '../core/traverse';
import { Concrete } from '../core/concrete';
import { expand } from '../simplify/expand';
import { at } from '../core/guard';

/**
 * SymPy finite_diff: the forward difference expr(variable + increment) -
 * expr(variable) of the expanded expression.
 */
export function finiteDiff(expression: ExprLike, variable: ExprLike, increment: ExprLike = 1): Expr {
  const e = expand(sympify(expression));
  const v = sympify(variable);
  const shifted = expand(subs(e, [[v, v.add(increment)]]));
  return sub(shifted, e);
}

/**
 * SymPy finite_diff_kauers: the difference of a sum with respect to its
 * upper limits, the summand with every variable replaced by its upper limit
 * plus one.
 */
export function finiteDiffKauers(sum: ExprLike): Expr {
  const s = sympify(sum);
  if (!(s instanceof Concrete)) throw new TypeError('finite_diff_kauers expects a Sum');
  let f = s.function;
  for (const l of s.limits) f = subs(f, [[at(l, 0), at(l, 2).add(1)]]);
  return f;
}

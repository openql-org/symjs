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
 * The forward difference expr(variable + increment) -
 * expr(variable) of the expanded expression.
 *
 * @param expression - Expression to difference.
 * @param variable - Independent variable.
 * @param increment - Step added to the variable.
 * @returns The expanded forward difference.
 * @see SymPy `sympy.series.kauers.finite_diff`
 * @example
 * ```ts
 * import { ex, finiteDiff, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * finiteDiff(ex`x**2`, x); // => 2*x + 1
 * finiteDiff(ex`x**2 + 3*x + 8`, x, 2); // => 4*x + 10
 * ```
 */
export function finiteDiff(expression: ExprLike, variable: ExprLike, increment: ExprLike = 1): Expr {
  const e = expand(sympify(expression));
  const v = sympify(variable);
  const shifted = expand(subs(e, [[v, v.add(increment)]]));
  return sub(shifted, e);
}

/**
 * The difference of a sum with respect to its
 * upper limits, the summand with every variable replaced by its upper limit
 * plus one.
 *
 * @param sum - Sum whose upper bounds are advanced.
 * @returns The summand with the summation variables replaced by their upper bounds plus one.
 * @throws TypeError when the argument is not a sum.
 * @see SymPy `sympy.series.kauers.finite_diff_kauers`
 * @example
 * ```ts
 * import { Sum, finiteDiffKauers, symbols } from '@symjs/symjs';
 *
 * const [k, n] = symbols('k n');
 * finiteDiffKauers(Sum(k, [k, 1, n])); // => n + 1
 * ```
 */
export function finiteDiffKauers(sum: ExprLike): Expr {
  const s = sympify(sum);
  if (!(s instanceof Concrete)) throw new TypeError('finite_diff_kauers expects a Sum');
  let f = s.function;
  for (const l of s.limits) f = subs(f, [[at(l, 0), at(l, 2).add(1)]]);
  return f;
}

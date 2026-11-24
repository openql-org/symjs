// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Assumptions for the linear real arithmetic solver (SymPy
 * sympy.assumptions.lra_satask): the predicates that the old assumptions of
 * the expressions give, and satisfiability queries in linear real arithmetic.
 *
 * Ported from SymPy 1.14 (BSD 3-Clause, see LICENSE).
 */

import { S, Expr, type ExprLike } from '../core/nodes';
import { and, not } from '../core/boolalg';
import type { Truth } from '../core/truth';
import { sympify } from '../core/ops';
import { freeSymbols } from '../core/traverse';
import { isIntegerQ, isNegative, isPositive, isReal, isZero } from '../core/assumptions';
import type { Assumption } from '../core/refine';
import { type AppliedPredicate, globalAssumptions, registerPropositionHandler, Q } from '../core/refine';
import { UnhandledInput, linearSatisfiable } from '../logic/algorithms/lratheory';

/**
 * The predicate (Q.zero, Q.positive,
 * Q.negative, Q.nonzero, Q.nonpositive or Q.nonnegative) that the old
 * assumptions of each non-constant expression give. Throws UnhandledInput
 * for an expression that is not known to be real, is an integer (other
 * than zero), cannot be an integer or is irrational.
 *
 * @param allExprs - Expressions whose intrinsic assumptions supply facts.
 * @returns The sign predicates implied by the nonconstant expressions.
 * @throws UnhandledInput when a nonconstant expression lacks the real-domain assumptions required by the solver.
 * @see SymPy `sympy.assumptions.lra_satask.extract_pred_from_old_assum`
 * @example
 * ```ts
 * import { ex, extractPredFromOldAssum, symbols } from '@symjs/symjs';
 *
 * const [x, y] = symbols('x y', { positive: true });
 * extractPredFromOldAssum([x, y, ex`2`]); // => [Q.positive(x), Q.positive(y)]
 * ```
 */
export function extractPredFromOldAssum(allExprs: Iterable<ExprLike>): AppliedPredicate[] {
  const ret: AppliedPredicate[] = [];
  for (const e of allExprs) {
    const expr = sympify(e);
    if (freeSymbols(expr).size === 0) continue;
    // SymPy also rejects a real product of a non-real factor (I times an imaginary variable) and an
    // irrational expression; the old assumptions of symjs report neither (such a product is not known to be
    // real, and an expression known to be irrational is not known to be real), so the checks are not repeated
    if (isReal(expr) !== true) throw new UnhandledInput(`LRASolver: ${String(expr)} must be real`);
    const integer = isIntegerQ(expr);
    if (integer === true && isZero(expr) !== true) throw new UnhandledInput(`LRASolver: ${String(expr)} is an integer`);
    if (integer === false) throw new UnhandledInput(`LRASolver: ${String(expr)} can't be an integer`);
    // expr is real: nonzero, nonpositive and nonnegative are the negations of zero, positive and negative
    const [zero, positive, negative] = [isZero(expr), isPositive(expr), isNegative(expr)];
    if (zero === true) ret.push(Q.zero(expr));
    else if (positive === true) ret.push(Q.positive(expr));
    else if (negative === true) ret.push(Q.negative(expr));
    else if (zero === false) ret.push(Q.nonzero(expr));
    else if (positive === false) ret.push(Q.nonpositive(expr));
    else if (negative === false) ret.push(Q.nonnegative(expr));
  }
  return ret;
}


/**
 * Decide a proposition by checking both polarities against the real theory.
 *
 * @param proposition - Proposition whose truth is to be decided.
 * @param assumptions - Facts assumed to hold.
 * @returns Whether the predicate holds, or `'unknown'` when undecided.
 * @throws RangeError when the assumptions are inconsistent.
 * @throws UnhandledInput when the expression falls outside linear real arithmetic.
 * @see SymPy `sympy.assumptions.lra_satask.lra_satask`
 */
export function lraSatask(proposition: ExprLike | boolean, assumptions: Assumption = true): Truth {
  const prop = typeof proposition === 'boolean' ? (proposition ? S.true : S.false) : sympify(proposition);
  const assumed = typeof assumptions === 'boolean' ? (assumptions ? S.true : S.false) : assumptions instanceof Expr ? assumptions : and(...assumptions);
  const context = and(assumed, ...globalAssumptions);
  const symbols = new Set([...freeSymbols(prop), ...freeSymbols(context)]);
  const old = extractPredFromOldAssum(symbols);
  const base = and(context, ...old);
  if (!linearSatisfiable(base)) throw new RangeError('inconsistent assumptions');
  const yes = linearSatisfiable(and(base, prop));
  const no = linearSatisfiable(and(base, not(prop)));
  return !yes ? false : !no ? true : 'unknown';
}

registerPropositionHandler((proposition, assumptions) => {
  try { return lraSatask(proposition, assumptions); }
  catch (error) {
    if (error instanceof UnhandledInput) return 'unknown';
    throw error;
  }
});

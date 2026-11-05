// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Assumptions for the linear real arithmetic solver (SymPy
 * sympy.assumptions.lra_satask): the predicates that the old assumptions of
 * the expressions give. lra_satask itself needs the LRASolver of
 * sympy.logic.algorithms.lra_theory, which is not ported.
 *
 * Ported from SymPy 1.14 (BSD 3-Clause, see LICENSE).
 */

import type { ExprLike } from '../core/nodes';
import { sympify } from '../core/ops';
import { freeSymbols } from '../core/traverse';
import { isIntegerQ, isNegative, isPositive, isReal, isZero } from '../core/assumptions';
import type { AppliedPredicate } from '../core/refine';
import { Q } from '../core/refine';
import { UnhandledInput } from '../logic/algorithms/lratheory';

/**
 * SymPy extract_pred_from_old_assum: the predicate (Q.zero, Q.positive,
 * Q.negative, Q.nonzero, Q.nonpositive or Q.nonnegative) that the old
 * assumptions of each non-constant expression give. Throws UnhandledInput
 * for an expression that is not known to be real, is an integer (other
 * than zero), cannot be an integer or is irrational.
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

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14, assumptions/relation/binrel.py, BSD-3-Clause; see LICENSE.

/**
 * @file User-defined binary relational predicates (SymPy BinaryRelation): `BinaryRelation(name,
 * handler, options)` adds `Q[name]`, a predicate of two arguments that `ask` decides with the handler,
 * after the quick answer of a reflexive (or antireflexive) relation on structurally equal arguments.
 */

import type { Expr } from '../../core/nodes';
import { S } from '../../core/nodes';
import type { Predicate } from '../../core/refine';
import { registerHandler, Q } from '../../core/refine';
import type { Truth } from '../../core/truth';
import { defined, pair } from '../../core/guard';

/**
 * A callback that decides a binary relation for two expressions under local assumptions.
 *
 * @param lhs - Left operand of the relation.
 * @param rhs - Right operand of the relation.
 * @param assumptions - Facts assumed to hold.
 * @returns True, false, or `'unknown'` when the relation cannot be decided.
 */
export type BinaryRelationHandler = (lhs: Expr, rhs: Expr, assumptions: Expr) => Truth;

/** Controls how a binary relation treats equal operands. */
export interface BinaryRelationOptions {
  /**
   * True when `x R x` holds for every x, false when it never holds (an antireflexive
   * relation); undefined (the default) when neither.
   */
  readonly isReflexive?: boolean;
}

/**
 * Defines a binary relation `Q[name]` (SymPy `class MyRel(BinaryRelation)` with `Q.R = MyRel()` and
 * handlers registered with `Q.R.register(...)`). `ask(Q[name](a, b))` answers the reflexivity of
 * structurally equal arguments without calling the handler (never for nan), then asks the handler, and
 * for a reflexive relation also the handler with the arguments swapped.
 *
 * @param name - Name under which to register the predicate in `Q`.
 * @param handler - Callback deciding the relation for two operands under the current assumptions.
 * @param options - Set `isReflexive` to decide the relation on equal operands.
 * @returns The registered binary predicate.
 * @throws RangeError when the resulting predicate is queried with a number of operands other than two.
 * @see SymPy `sympy.assumptions.relation.binrel.BinaryRelation`
 * @example
 * ```ts
 * import { BinaryRelation, ask, ex } from '@symjs/symjs';
 *
 * const R = BinaryRelation('R', (a, b) => a.equals(b), { isReflexive: true });
 * ask(R(ex`x`, ex`x`)); // => True
 * ```
 */
export function BinaryRelation(name: string, handler: BinaryRelationHandler, options: BinaryRelationOptions = {}): Predicate {
  registerHandler(name, (_e, assumptions, args) => {
    if (args.length !== 2) throw new RangeError(`Binary relation takes two arguments, but got ${args.length}.`);
    const [lhs, rhs] = pair(args);
    // SymPy _compare_reflexive: reflexivity does not hold for nan
    if (options.isReflexive !== undefined && lhs !== S.NaN && rhs !== S.NaN && lhs.equals(rhs)) return options.isReflexive;
    const ret = handler(lhs, rhs, assumptions);
    if (ret !== 'unknown' || options.isReflexive !== true) return ret;
    return handler(rhs, lhs, assumptions);
  });
  return defined(Q[name], `Q.${name}`);
}

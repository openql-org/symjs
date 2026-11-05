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

/** Decides `lhs R rhs` under the assumptions: true, false or 'unknown' (a SymPy dispatch handler). */
export type BinaryRelationHandler = (lhs: Expr, rhs: Expr, assumptions: Expr) => Truth;

export interface BinaryRelationOptions {
  /**
   * SymPy is_reflexive: true when `x R x` holds for every x, false when it never holds (an antireflexive
   * relation); undefined (the default) when neither.
   */
  readonly isReflexive?: boolean;
}

/**
 * Defines a binary relation `Q[name]` (SymPy `class MyRel(BinaryRelation)` with `Q.R = MyRel()` and
 * handlers registered with `Q.R.register(...)`). `ask(Q[name](a, b))` answers the reflexivity of
 * structurally equal arguments without calling the handler (never for nan), then asks the handler, and
 * for a reflexive relation also the handler with the arguments swapped.
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

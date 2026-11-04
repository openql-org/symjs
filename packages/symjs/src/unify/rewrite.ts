// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/unify/rewrite.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/** @file SymPy sympy.unify.rewrite: rewrite rules built by unification. */

import type { Expr, ExprLike } from '../core/nodes';
import { Expr as ExprClass, S } from '../core/nodes';
import { sympify } from '../core/ops';
import type { Assumption } from '../core/refine';
import { ask } from '../core/refine';
import { xreplace } from '../core/traverse';
import type { Truth } from '../core/truth';
import { subs } from '../strategies/tools';
import { rebuild, unify } from './usympy';

/** A rewrite rule: the expressions an expression rewrites to, under optional assumptions. */
export type RewriteRule = (expr: ExprLike, assumptions?: Assumption) => Generator<Expr, void, undefined>;

const holds = (r: Truth | Expr): boolean => r === true || (r instanceof ExprClass && r.equals(S.true));

/**
 * SymPy `rewriterule(source, target, variables=(), condition=None,
 * assume=None)`: a rule that rewrites the expressions matching `source`
 * into `target`, the `variables` being wild. `condition` receives the
 * values of the variables (in the order of `variables`) and must hold
 * (`true`); `assume` is a proposition (`Q.integer(x)`) that must follow
 * from the assumptions given when the rule is applied.
 */
export function rewriterule(
  sourceIn: ExprLike,
  targetIn: ExprLike,
  variables: readonly Expr[] = [],
  condition: ((...args: Expr[]) => Truth | Expr) | null = null,
  assume: Expr | null = null,
): RewriteRule {
  const source = sympify(sourceIn);
  const target = sympify(targetIn);
  return function* rewriteRl(expr: ExprLike, assumptions: Assumption = true): Generator<Expr, void, undefined> {
    for (const match of unify(source, expr, null, variables)) {
      if (condition && !holds(condition(...variables.map((v) => match.get(v) ?? v)))) continue;
      if (assume && ask(xreplace(assume, match), assumptions) !== true) continue;
      yield rebuild(subs(match)(target));
    }
  };
}

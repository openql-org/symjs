// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Facts about the arguments of an expression (SymPy
 * sympy.assumptions.sathandlers): a fact in a symbol applied to all, any or
 * exactly one of the arguments.
 */

import type { Expr, ExprLike } from '../core/nodes';
import { sympify } from '../core/ops';
import { subs } from '../core/traverse';
import { and, not, or } from '../core/boolalg';

const applied = (symbol: ExprLike, fact: ExprLike, expr: ExprLike): Expr[] => {
  const [s, f] = [sympify(symbol), sympify(fact)];
  return sympify(expr).args.map((a) => subs(f, [[s, a]]));
};

/** SymPy allargs: the fact (in symbol) holds for all the arguments of expr. */
export function allargs(symbol: ExprLike, fact: ExprLike, expr: ExprLike): Expr {
  return and(...applied(symbol, fact, expr));
}

/** SymPy anyarg: the fact (in symbol) holds for some argument of expr. */
export function anyarg(symbol: ExprLike, fact: ExprLike, expr: ExprLike): Expr {
  return or(...applied(symbol, fact, expr));
}

/** SymPy exactlyonearg: the fact (in symbol) holds for exactly one argument of expr. */
export function exactlyonearg(symbol: ExprLike, fact: ExprLike, expr: ExprLike): Expr {
  const ps = applied(symbol, fact, expr);
  return or(...ps.map((p, i) => and(p, ...ps.filter((_q, j) => j !== i).map((q) => not(q)))));
}

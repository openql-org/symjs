// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/strategies/traverse.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.strategies.traverse: strategies that apply a rule
 * through an expression tree. `fns` says how a node is taken apart and
 * rebuilt ({@link basicFns}: without evaluation, {@link exprFns}: with it).
 */

import type { Expr } from '../core/nodes';
import type { Rule } from './core';
import { chain, doOne } from './core';
import type { TreeFns } from './util';
import { basicFns } from './util';

/** SymPy `top_down(rule, fns=basic_fns)`: apply a rule down a tree, on the top nodes first. */
export function topDown(rule: Rule<Expr>, fns: TreeFns = basicFns): Rule<Expr> {
  return chain(rule, (expr) => sall(topDown(rule, fns), fns)(expr));
}

/** SymPy `bottom_up(rule, fns=basic_fns)`: apply a rule down a tree, on the bottom nodes first. */
export function bottomUp(rule: Rule<Expr>, fns: TreeFns = basicFns): Rule<Expr> {
  return chain((expr) => sall(bottomUp(rule, fns), fns)(expr), rule);
}

/** SymPy `top_down_once(rule, fns=basic_fns)`: apply a rule down a tree, stopping on success. */
export function topDownOnce(rule: Rule<Expr>, fns: TreeFns = basicFns): Rule<Expr> {
  return doOne(rule, (expr) => sall(topDown(rule, fns), fns)(expr));
}

/** SymPy `bottom_up_once(rule, fns=basic_fns)`: apply a rule up a tree, stopping on success. */
export function bottomUpOnce(rule: Rule<Expr>, fns: TreeFns = basicFns): Rule<Expr> {
  return doOne((expr) => sall(bottomUp(rule, fns), fns)(expr), rule);
}

/** SymPy `sall(rule, fns=basic_fns)`: strategic all, apply a rule to the arguments of a node. */
export function sall(rule: Rule<Expr>, fns: TreeFns = basicFns): Rule<Expr> {
  return function allRl(expr: Expr): Expr {
    if (fns.leaf(expr)) return expr;
    return fns.new(fns.op(expr), fns.children(expr).map((a) => rule(a)));
  };
}

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

/**
 * Applies a rule down a tree, on the top nodes first.
 *
 * @param rule - The transformation to apply.
 * @param fns - The operations for inspecting and rebuilding tree nodes.
 * @returns A rewrite rule applying this strategy.
 * @see SymPy `sympy.strategies.traverse.top_down`
 */
export function topDown(rule: Rule<Expr>, fns: TreeFns = basicFns): Rule<Expr> {
  return chain(rule, (expr) => sall(topDown(rule, fns), fns)(expr));
}

/**
 * Applies a rule down a tree, on the bottom nodes first.
 *
 * @param rule - The transformation to apply.
 * @param fns - The operations for inspecting and rebuilding tree nodes.
 * @returns A rewrite rule applying this strategy.
 * @see SymPy `sympy.strategies.traverse.bottom_up`
 */
export function bottomUp(rule: Rule<Expr>, fns: TreeFns = basicFns): Rule<Expr> {
  return chain((expr) => sall(bottomUp(rule, fns), fns)(expr), rule);
}

/**
 * Applies a rule down a tree, stopping on success.
 *
 * @param rule - The transformation to apply.
 * @param fns - The operations for inspecting and rebuilding tree nodes.
 * @returns A rewrite rule applying this strategy.
 * @see SymPy `sympy.strategies.traverse.top_down_once`
 */
export function topDownOnce(rule: Rule<Expr>, fns: TreeFns = basicFns): Rule<Expr> {
  return doOne(rule, (expr) => sall(topDown(rule, fns), fns)(expr));
}

/**
 * Applies a rule up a tree, stopping on success.
 *
 * @param rule - The transformation to apply.
 * @param fns - The operations for inspecting and rebuilding tree nodes.
 * @returns A rewrite rule applying this strategy.
 * @see SymPy `sympy.strategies.traverse.bottom_up_once`
 */
export function bottomUpOnce(rule: Rule<Expr>, fns: TreeFns = basicFns): Rule<Expr> {
  return doOne((expr) => sall(bottomUp(rule, fns), fns)(expr), rule);
}

/**
 * Strategic all, apply a rule to the arguments of a node.
 *
 * @param rule - The transformation to apply.
 * @param fns - The operations for inspecting and rebuilding tree nodes.
 * @returns A rewrite rule applying this strategy.
 * @see SymPy `sympy.strategies.traverse.sall`
 */
export function sall(rule: Rule<Expr>, fns: TreeFns = basicFns): Rule<Expr> {
  return function allRl(expr: Expr): Expr {
    if (fns.leaf(expr)) return expr;
    return fns.new(fns.op(expr), fns.children(expr).map((a) => rule(a)));
  };
}

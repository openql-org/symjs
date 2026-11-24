// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/strategies/__init__.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.strategies: rewrite rules and strategies.
 *
 * A rule transforms one expression into another (`Rule: Expr -> Expr`); a
 * strategy says how rules are applied to a tree and builds a new rule from
 * rules. The submodules are namespaces as in SymPy: `rl` (fundamental
 * rules), `traverse` (tree traversals), `tools` (conglomerate strategies),
 * `tree` (strategic trees), `util` (tree functions) and `branch` (branching
 * strategies, rules that yield several results).
 */

/**
 * Rules for removing identities, sorting arguments and distributing operators.
 *
 * @see SymPy `sympy.strategies.rl`
 */
export * as rl from './rl';
/**
 * Strategies that apply rewrite rules during traversal of an expression tree.
 *
 * @see SymPy `sympy.strategies.traverse`
 */
export * as traverse from './traverse';
/**
 * Combinators for constructing canonicalizing and type-directed rewrite rules.
 *
 * @see SymPy `sympy.strategies.tools`
 */
export * as tools from './tools';
/**
 * Strategies for composing alternatives and sequences of rewrite rules.
 *
 * @see SymPy `sympy.strategies.tree`
 */
export * as tree from './tree';
/**
 * Operations for inspecting and rebuilding the nodes of an expression tree.
 *
 * @see SymPy `sympy.strategies.util`
 */
export * as util from './util';
/**
 * Branching strategies that yield multiple possible rewrites.
 *
 * @see SymPy `sympy.strategies.branch`
 */
export * as branch from './branch/index';
export { distribute, flatten, glom, rebuild, rmId, sort, unpack } from './rl';
export type { NewFn, NodeClass } from './rl';
export { chain, condition, debug, doOne, exhaust, memoize, minimize, nullSafe, switch, tryit } from './core';
export type { ErrorClass, Rule, Writer } from './core';
export { canon, typed } from './tools';
export type { TreeFns } from './util';
export type { BranchRule } from './branch/core';
export type { StrategyTree } from './tree';

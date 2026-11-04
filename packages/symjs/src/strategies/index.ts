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

export * as rl from './rl';
export * as traverse from './traverse';
export * as tools from './tools';
export * as tree from './tree';
export * as util from './util';
export * as branch from './branch/index';
export { distribute, flatten, glom, rebuild, rmId, sort, unpack } from './rl';
export type { NewFn, NodeClass } from './rl';
export { chain, condition, debug, doOne, exhaust, memoize, minimize, nullSafe, switch, tryit } from './core';
export type { ErrorClass, Rule, Writer } from './core';
export { canon, typed } from './tools';
export type { TreeFns } from './util';
export type { BranchRule } from './branch/core';
export type { StrategyTree } from './tree';

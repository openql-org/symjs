// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/strategies/tree.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.strategies.tree: executing strategic trees.
 *
 * A strategic tree has functions as leaves, Python lists (a selection among
 * alternatives) and Python tuples (a sequence of chained operations) as
 * nodes. JavaScript has one kind of array, so a list is an array and a tuple
 * is a {@link TreeTuple}.
 */

import type { Rule } from './core';
import { chain, identity, minBy, minimize } from './core';
import type { BranchRule } from './branch/core';
import { chain as bchain, multiplex, yieldify } from './branch/core';

/** A Python tuple in a strategic tree: a sequence of chained operations (`(f, g)` in SymPy). */
export class TreeTuple<T = unknown> implements Iterable<T> {
  /** The values in the tuple, in order. */
  readonly items: readonly T[];
  /**
   * Creates a TreeTuple instance.
   *
   * @param items - The child strategies in tuple order.
   */
  constructor(...items: T[]) {
    this.items = items;
  }
  [Symbol.iterator](): Iterator<T> {
    return this.items[Symbol.iterator]();
  }
}

/** A strategic tree with leaves of type `R`: arrays choose, {@link TreeTuple}s chain. */
export type StrategyTree<R> = R | readonly StrategyTree<R>[] | TreeTuple<StrategyTree<R>>;

/** A function of any arguments (compared bivariantly, like a Python callable). */
export type TreeFunction = { bivarianceHack(...args: unknown[]): unknown }['bivarianceHack'];

/** A container type of a tree (`list`, `tuple`, ... in SymPy): `Array`, {@link TreeTuple} or another class. */
export type TreeContainer = abstract new (...args: never[]) => unknown;

const isIterable = (x: unknown): x is Iterable<unknown> => typeof x === 'object' && x !== null && Symbol.iterator in x && typeof x[Symbol.iterator] === 'function';

/**
 * Applies functions onto a
 * recursive container. `join` maps container types to functions of the
 * results of their elements (`new Map([[Array, max], [TreeTuple, min]])`);
 * anything else is a leaf, mapped by `leaf`.
 *
 * @param tree - The tree of rules to combine.
 * @param join - The combining functions associated with tree container types.
 * @param leaf - The transformation applied at a leaf.
 * @returns The value obtained by combining the transformed leaves.
 * @see SymPy `sympy.strategies.tree.treeapply`
 */
export function treeapply(tree: unknown, join: ReadonlyMap<TreeContainer, TreeFunction>, leaf: TreeFunction = identity): unknown {
  for (const [typ, fn] of join) {
    if (tree instanceof typ) {
      if (!isIterable(tree)) throw new TypeError(`treeapply: a ${typ.name} is not iterable`);
      return fn(...[...tree].map((t) => treeapply(t, join, leaf)));
    }
  }
  return leaf(tree);
}

const isList = <R>(t: StrategyTree<R>): t is readonly StrategyTree<R>[] => Array.isArray(t);

/**
 * Execute a strategic tree,
 * choosing among the alternatives of a list the result that minimizes the
 * objective (greedily, without foresight of what follows).
 *
 * @param tree - The tree of rules to combine.
 * @param objective - The function that scores candidate results.
 * @returns A rewrite rule applying this strategy.
 * @see SymPy `sympy.strategies.tree.greedy`
 */
export function greedy<T>(tree: StrategyTree<Rule<T>>, objective: (x: T) => unknown = identity): Rule<T> {
  if (tree instanceof TreeTuple) return chain(...tree.items.map((t) => greedy(t, objective)));
  if (isList(tree)) return minimize(...tree.map((t) => greedy(t, objective)), { objective });
  return tree;
}

/**
 * Execute a strategic tree,
 * yielding every possible result (lists multiplex, tuples chain).
 *
 * @param tree - The tree of rules to combine.
 * @param leaf - The transformation applied at a leaf.
 * @returns A branching rule yielding each result permitted by the tree.
 * @see SymPy `sympy.strategies.tree.allresults`
 */
export function allresults<T>(tree: StrategyTree<Rule<T>>, leaf: (rl: Rule<T>) => BranchRule<T> = yieldify): BranchRule<T> {
  if (tree instanceof TreeTuple) return bchain(...tree.items.map((t) => allresults(t, leaf)));
  if (isList(tree)) return multiplex(...tree.map((t) => allresults(t, leaf)));
  return leaf(tree);
}

/**
 * The result of all of {@link allresults} that minimizes the objective.
 *
 * @param tree - The tree of rules to combine.
 * @param objective - The function that scores candidate results.
 * @param leaf - The transformation applied at a leaf.
 * @returns A rewrite rule applying this strategy.
 * @see SymPy `sympy.strategies.tree.brute`
 */
export function brute<T>(tree: StrategyTree<Rule<T>>, objective: (x: T) => unknown = identity, leaf: (rl: Rule<T>) => BranchRule<T> = yieldify): Rule<T> {
  return (expr: T): T => minBy([...allresults(tree, leaf)(expr)], objective);
}

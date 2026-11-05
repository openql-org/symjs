// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/printing/tree.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy's tree printer: `tree`, `print_tree`, `print_node` and
 * `pprint_nodes` show an expression as its class names and `str()` forms,
 * one node per line, with the assumptions of its symbols.
 */

import type { Expr } from '../core/nodes';
import { deduceAllFacts } from '../core/facts';
import type { BasicView } from './repr';
import { basicView, symbolAssumptionFacts } from './repr';

/** The options of {@link tree}, {@link printTree} and {@link printNode}. */
export interface TreeOptions {
  /** Show the assumptions of the symbols (default true). */
  readonly assumptions?: boolean;
}

/**
 * SymPy `pprint_nodes(subtrees)`: the subtrees one below the other, joined
 * by `+-` branches (`|` continues a branch that has more below it).
 */
export function pprintNodes(subtrees: readonly string[]): string {
  const indent = (s: string, last: boolean): string => {
    const [head = '', ...rest] = s.split('\n');
    return `+-${head}\n${rest
      .filter((a) => a !== '')
      .map((a) => `${last ? '  ' : '| '}${a}\n`)
      .join('')}`;
  };
  return subtrees.map((s, i) => indent(s, i === subtrees.length - 1)).join('');
}

/**
 * The facts SymPy has deduced for a node: the closure of the assumptions of
 * a symbol (SymPy `Symbol._assumptions`). Other nodes show none; SymPy shows
 * whatever its assumption cache holds for them, which depends on what was
 * asked before.
 */
function nodeFacts(view: BasicView): [string, boolean][] {
  const given = view.expr ? symbolAssumptionFacts(view.expr) : undefined;
  if (given === undefined) return [];
  return [...deduceAllFacts(given)].sort(([a], [b]) => (a < b ? -1 : 1));
}

function viewNode(view: BasicView, assumptions: boolean): string {
  let s = `${view.cls}: ${view.str}\n`;
  if (assumptions) for (const [k, v] of nodeFacts(view)) s += `${k}: ${v ? 'True' : 'False'}\n`;
  return s;
}

function viewTree(view: BasicView, assumptions: boolean): string {
  return viewNode(view, assumptions) + pprintNodes(view.args.map((a) => viewTree(a, assumptions)));
}

/**
 * SymPy `print_node(node, assumptions=True)`: the class name and the str()
 * form of the node, then its assumption facts, one per line.
 */
export function printNode(node: Expr, options: TreeOptions = {}): string {
  return viewNode(basicView(node), options.assumptions ?? true);
}

/**
 * SymPy `tree(node, assumptions=True)`: {@link printNode} of the node and,
 * below it, the trees of its arguments (SymPy's `args`, in SymPy's order).
 */
export function tree(node: Expr, options: TreeOptions = {}): string {
  return viewTree(basicView(node), options.assumptions ?? true);
}

/**
 * SymPy `print_tree(node, assumptions=True)`: SymPy prints the tree; symjs
 * has no console output, so this returns the text that would be printed
 * (followed by a newline).
 *
 * ```
 * printTree(pow(y, x), { assumptions: false })
 * // Pow: y**x
 * // +-Symbol: y
 * // +-Symbol: x
 * ```
 */
export function printTree(node: Expr, options: TreeOptions = {}): string {
  return `${tree(node, options)}\n`;
}

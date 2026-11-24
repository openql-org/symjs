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
import { Sym, WildFunction } from '../core/nodes';
import type { BasicView } from './repr';
import { basicView } from './repr';

/** The options of {@link tree}, {@link printTree} and {@link printNode}. */
export interface TreeOptions {
  /** Show the assumptions of the symbols (default true). */
  readonly assumptions?: boolean;
}

/**
 * Joins formatted child subtrees using branch lines and vertical guides.
 *
 * @param subtrees - The child trees as multiline strings.
 * @returns The formatted text.
 * @see SymPy `sympy.printing.tree.pprint_nodes`
 * @example
 * ```ts
 * import { pprintNodes } from '@symjs/symjs';
 * pprintNodes(['a', 'b1\nb2', 'c']).trimEnd(); // => +-a
 * //   +-b1
 * //   | b2
 * //   +-c
 * ```
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
  if (!(view.expr instanceof Sym) || view.expr instanceof WildFunction) return [];
  return [...view.expr.assumptions0].sort(([a], [b]) => (a < b ? -1 : 1));
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
 * The class name and the str()
 * form of the node, then its assumption facts, one per line.
 *
 * @param node - The expression whose node information to display.
 * @param options - The tree settings.
 * @returns The formatted node.
 * @see SymPy `sympy.printing.tree.print_node`
 */
export function printNode(node: Expr, options: TreeOptions = {}): string {
  return viewNode(basicView(node), options.assumptions ?? true);
}

/**
 * Formats the expression as a tree, with the {@link printNode} text for each node followed by
 * its argument subtrees in SymPy argument order.
 *
 * @see SymPy `sympy.printing.tree.tree`
 */
export function tree(node: Expr, options: TreeOptions = {}): string {
  return viewTree(basicView(node), options.assumptions ?? true);
}

/**
 * Formats the expression tree as indented text with one node per branch.
 *
 * @param node - The expression at the root of the tree.
 * @param options - The tree settings.
 * @returns The formatted text.
 * @see SymPy `sympy.printing.tree.print_tree`
 * @example
 * ```ts
 * import { ex, printTree, symbols } from '@symjs/symjs';
 *
 * const [y] = symbols('y', { even: true });
 * const [x] = symbols('x', { odd: true });
 * printTree(ex`${y}**${x}`, { assumptions: false }).trimEnd(); // => Pow: y**x
 * //   +-Symbol: y
 * //   +-Symbol: x
 * ```
 */
export function printTree(node: Expr, options: TreeOptions = {}): string {
  return `${tree(node, options)}\n`;
}

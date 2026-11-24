// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy Basic(*args): a generic node that only holds its arguments,
 * used as a container in pattern matching and tree manipulation.
 */

import type { Expr, ExprLike } from './nodes';
import { ExtensionExpr } from './nodes';
import { sympify } from './ops';

/**
 * A generic node holding its arguments: an instance of one of SymPy's base
 * classes (Basic, Expr, Atom, AtomicExpr) created directly.
 *
 * @see SymPy `sympy.core.basic.Basic`
 * @example
 * ```ts
 * import { BasicNode, ex } from '@symjs/symjs';
 *
 * new BasicNode([ex`x`, ex`y`]).args; // => [x, y]
 * ```
 */
export class BasicNode extends ExtensionExpr {
  /**
   * Creates a `BasicNode`.
   *
   * @param args - The arguments in positional order.
   * @param head - The head.
   */
  constructor(
    args: readonly Expr[],
    /** The SymPy class name printed (Basic by default). */
    head = 'Basic',
  ) {
    super(head, args);
  }
  /**
   * Rebuilds the node with the supplied arguments.
   *
   * @param args - The replacement arguments, in node order.
   * @returns The expression rebuilt with the new arguments.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new BasicNode(args, this.name);
  }
}

/**
 * Constructs a generic symbolic node with the given arguments.
 *
 * @param args - The arguments in positional order.
 * @returns The constructed symbolic node.
 * @see SymPy `sympy.core.basic.Basic`
 * @example
 * ```ts
 * import { Basic, ex } from '@symjs/symjs';
 *
 * Basic(ex`x`, ex`y`).args; // => [x, y]
 * ```
 */
export function Basic(...args: ExprLike[]): BasicNode {
  return new BasicNode(args.map(sympify));
}

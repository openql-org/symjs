// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy Basic(*args): a generic node that only holds its arguments,
 * used as a container in pattern matching and tree manipulation.
 */

import { Expr, ExprLike, ExtensionExpr } from './nodes';
import { sympify } from './ops';

/**
 * A generic node holding its arguments: an instance of one of SymPy's base
 * classes (Basic, Expr, Atom, AtomicExpr) created directly.
 */
export class BasicNode extends ExtensionExpr {
  constructor(
    args: readonly Expr[],
    /** The SymPy class name printed (Basic by default). */
    head = 'Basic',
  ) {
    super(head, args);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new BasicNode(args, this.name);
  }
}

/** SymPy Basic(*args). */
export function Basic(...args: ExprLike[]): BasicNode {
  return new BasicNode(args.map(sympify));
}

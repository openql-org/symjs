// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy Basic(*args): a generic node that only holds its arguments,
 * used as a container in pattern matching and tree manipulation.
 */

import { Expr, ExprLike, ExtensionExpr } from './nodes';
import { sympify } from './ops';

/** A generic node holding its arguments (SymPy Basic instance). */
export class BasicNode extends ExtensionExpr {
  constructor(args: readonly Expr[]) {
    super('Basic', args);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new BasicNode(args);
  }
}

/** SymPy Basic(*args). */
export function Basic(...args: ExprLike[]): BasicNode {
  return new BasicNode(args.map(sympify));
}

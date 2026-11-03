// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy `Lambda(variables, expr)`: an anonymous function whose
 * variables are bound in its expression.
 */

import type { ExprLike } from './nodes';
import { Expr, ExtensionExpr } from './nodes';
import { sympify } from './ops';
import { at } from './guard';

/** Lambda(variables, expr): args are [...variables, expr]. */
export class LambdaNode extends ExtensionExpr {
  constructor(args: readonly Expr[]) {
    super('Lambda', args);
  }
  get variables(): Expr[] {
    return this.args.slice(0, -1);
  }
  get expr(): Expr {
    return at(this.args, this.args.length - 1);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new LambdaNode(args);
  }
  override bindings(): { variables: readonly number[]; scope: readonly number[] } {
    const n = this.args.length - 1;
    return { variables: Array.from({ length: n }, (_, i) => i), scope: [n] };
  }
  override printStr(print: (e: Expr) => string): string {
    const vs = this.variables;
    return `Lambda(${vs.length === 1 ? print(at(vs, 0)) : `(${vs.map(print).join(', ')})`}, ${print(this.expr)})`;
  }
  override printLatex(print: (e: Expr) => string): string {
    const vs = this.variables;
    return `\\left( ${vs.length === 1 ? print(at(vs, 0)) : `\\left( ${vs.map(print).join(', \\  ')}\\right)`} \\mapsto ${print(this.expr)} \\right)`;
  }
  /** Apply the function to arguments (SymPy Lambda.__call__). */
  call(...args: ExprLike[]): Expr {
    const vs = this.variables;
    if (args.length !== vs.length) throw new TypeError(`Lambda takes ${vs.length} arguments (${args.length} given)`);
    return this.expr.subs(vs.map((v, i): [Expr, Expr] => [v, sympify(at(args, i))]));
  }
}

/** SymPy Lambda(variables, expr) with one variable or an array of them. */
export function Lambda(variables: Expr | readonly Expr[], expr: ExprLike): LambdaNode {
  const vs = variables instanceof Expr ? [variables] : variables;
  return new LambdaNode([...vs, sympify(expr)]);
}

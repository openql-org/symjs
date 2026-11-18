// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy `Lambda(variables, expr)`: an anonymous function whose
 * variables are bound in its expression.
 */

import type { ExprLike } from './nodes';
import { Dummy, Expr, ExtensionExpr, Sym, impl } from './nodes';
import { sympify } from './ops';
import { at } from './guard';

/** Lambda(variables, expr): args are [...variables, expr]. */
export class LambdaNode extends ExtensionExpr {
  constructor(args: readonly Expr[]) {
    super('Lambda', args);
    const seen = new Set<string>();
    const validate = (v: Expr): void => {
      if (v instanceof ExtensionExpr && v.name === 'Tuple') {
        v.args.forEach(validate);
      } else {
        if (!(v instanceof Sym || (v instanceof ExtensionExpr && ['Indexed', 'IndexedBase', 'MatrixSymbol'].includes(v.name)))) throw new TypeError('Lambda signature must contain symbols');
        if (seen.has(v.key)) throw new TypeError('Lambda signature contains a duplicate variable');
        seen.add(v.key);
      }
    };
    args.slice(0, -1).forEach(validate);
  }
  get variables(): Expr[] {
    const flatten = (v: Expr): Expr[] => v instanceof ExtensionExpr && v.name === 'Tuple' ? v.args.flatMap(flatten) : [v];
    return this.args.slice(0, -1).flatMap(flatten);
  }
  get expr(): Expr {
    return at(this.args, this.args.length - 1);
  }
  /** Bound variables renamed without colliding with free symbol names. */
  get canonicalVariables(): Map<Expr, Sym> {
    const names = new Set([...this.freeSymbols()].filter((s) => s instanceof Sym).map((s) => s.name));
    let i = 0;
    return new Map(this.variables.map((v) => {
      while (names.has(`_${i}`)) i++;
      return [v, new Sym(`_${i++}`)];
    }));
  }
  withArgs(args: readonly Expr[]): Expr {
    return new LambdaNode(args);
  }
  override bindings(): { variables: readonly number[]; scope: readonly number[] } {
    const n = this.args.length - 1;
    return { variables: Array.from({ length: n }, (_, i) => i), scope: [n] };
  }
  override freeSymbolsSelf(): ReadonlySet<Expr> {
    const bound = new Set(this.variables.map((v) => v.key));
    return new Set([...this.expr.freeSymbols()].filter((v) => !bound.has(v.key)));
  }
  override printStr(print: (e: Expr) => string): string {
    const vs = this.args.slice(0, -1);
    return `Lambda(${vs.length === 1 ? print(at(vs, 0)) : `(${vs.map(print).join(', ')})`}, ${print(this.expr)})`;
  }
  override printLatex(print: (e: Expr) => string): string {
    const vs = this.args.slice(0, -1);
    return `\\left( ${vs.length === 1 ? print(at(vs, 0)) : `\\left( ${vs.map(print).join(', \\  ')}\\right)`} \\mapsto ${print(this.expr)} \\right)`;
  }
  /** Apply the function to arguments (SymPy Lambda.__call__). */
  call(...args: ExprLike[]): Expr {
    const vs = this.args.slice(0, -1);
    if (args.length !== vs.length) throw new TypeError(`Lambda takes ${vs.length} arguments (${args.length} given)`);
    const pairs: [Expr, Expr][] = [];
    const bind = (v: Expr, value: Expr): void => {
      if (v instanceof ExtensionExpr && v.name === 'Tuple') {
        if (!(value instanceof ExtensionExpr && value.name === 'Tuple') || value.args.length !== v.args.length) throw new TypeError('Lambda argument does not match its tuple signature');
        v.args.forEach((item, i) => bind(item, at(value.args, i)));
      } else pairs.push([v, value]);
    };
    vs.forEach((v, i) => bind(v, sympify(at(args, i))));
    return impl.xreplace(this.expr, new Map(pairs));
  }
}

/** SymPy Lambda(variables, expr) with one variable or an array of them. */
export function Lambda(variables: Expr | readonly Expr[], expr: ExprLike): LambdaNode {
  const vs = variables instanceof Expr ? [variables] : variables;
  return new LambdaNode([...vs, sympify(expr)]);
}

/** SymPy Id (S.IdentityFunction): the identity function Lambda(_x, _x); Id.call(x) is x. */
export const Id: LambdaNode = /* @__PURE__ */ identity();

function identity(): LambdaNode {
  const x = new Dummy('x');
  return new LambdaNode([x, x]);
}

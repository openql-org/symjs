// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy `Subs`: an unevaluated substitution, e.g. the value of a
 * derivative at a point, `Subs(Derivative(f(x), x), x, 0)`.
 */

import type { ExprLike } from './nodes';
import { Expr, ExtensionExpr } from './nodes';
import { add, mul, sympify } from './ops';
import { at } from './guard';

/** Subs(expr, variables, points): args are [expr, ...variables, ...points]. */
export class SubsNode extends ExtensionExpr {
  constructor(args: readonly Expr[]) {
    super('Subs', args);
  }
  get expr(): Expr {
    return at(this.args, 0);
  }
  get variables(): Expr[] {
    const n = (this.args.length - 1) / 2;
    return this.args.slice(1, 1 + n);
  }
  get point(): Expr[] {
    const n = (this.args.length - 1) / 2;
    return this.args.slice(1 + n);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new SubsNode(args);
  }
  override bindings(): { variables: readonly number[]; scope: readonly number[] } {
    const n = (this.args.length - 1) / 2;
    return { variables: Array.from({ length: n }, (_, i) => 1 + i), scope: [0] };
  }
  override printStr(print: (e: Expr) => string): string {
    const tuple = (xs: Expr[]) => (xs.length === 1 ? print(at(xs, 0)) : `(${xs.map(print).join(', ')})`);
    return `Subs(${print(this.expr)}, ${tuple(this.variables)}, ${tuple(this.point)})`;
  }
  override printLatex(print: (e: Expr) => string): string {
    const eqs = this.variables.map((v, i) => `${print(v)}=${print(at(this.point, i))}`).join('\\\\ ');
    return `\\left. ${print(this.expr)} \\right|_{\\substack{ ${eqs} }}`;
  }
  override diffSelf(x: Expr, d: (e: Expr, x: Expr) => Expr): Expr | undefined {
    // d/dx Subs(e, v, p) = Subs(de/dx, v, p) (x not substituted) + sum_i Subs(de/dv_i, v, p) * dp_i/dx
    // (each Subs evaluated by subs, which keeps it unevaluated only where needed)
    const vars = this.variables;
    const pairs = vars.map((v, i): [Expr, Expr] => [v, at(this.point, i)]);
    const atPoint = (e: Expr) => e.subs(pairs);
    const terms: Expr[] = [];
    if (!vars.some((v) => v.key === x.key)) terms.push(atPoint(d(this.expr, x)));
    for (const [v, p] of pairs) {
      const dp = d(p, x);
      if (!(dp.isNumber && dp.key === '0')) terms.push(mul(atPoint(d(this.expr, v)), dp));
    }
    return add(...terms);
  }
  override doitSelf(): Expr {
    return this.expr.subs(this.variables.map((v, i): [Expr, Expr] => [v, at(this.point, i)]));
  }
}

const asList = (x: ExprLike | readonly ExprLike[]): readonly ExprLike[] => (x instanceof Expr || typeof x !== 'object' ? [x] : x);

/**
 * SymPy `Subs(expr, variables, point)`: one variable and point, or arrays
 * of them (unevaluated; `doit` performs the substitution).
 */
export function Subs(exprIn: ExprLike, variables: ExprLike | readonly ExprLike[], point: ExprLike | readonly ExprLike[]): Expr {
  const expr = sympify(exprIn);
  const vs = asList(variables).map((v) => sympify(v));
  const ps = asList(point).map((p) => sympify(p));
  if (vs.length !== ps.length) throw new RangeError('Subs: number of variables and points differ');
  if (!vs.length) return expr;
  return new SubsNode([expr, ...vs, ...ps]);
}

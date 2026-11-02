// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy `Subs`: an unevaluated substitution, e.g. the value of a
 * derivative at a point, `Subs(Derivative(f(x), x), x, 0)`.
 */

import { Expr, ExprLike, ExtensionExpr } from './nodes';
import { add, mul, sympify } from './ops';

/** Subs(expr, variables, points): args are [expr, ...variables, ...points]. */
export class SubsNode extends ExtensionExpr {
  constructor(args: readonly Expr[]) {
    super('Subs', args);
  }
  get expr(): Expr {
    return this.args[0]!;
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
    const tuple = (xs: Expr[]) => (xs.length === 1 ? print(xs[0]!) : `(${xs.map(print).join(', ')})`);
    return `Subs(${print(this.expr)}, ${tuple(this.variables)}, ${tuple(this.point)})`;
  }
  override printLatex(print: (e: Expr) => string): string {
    const eqs = this.variables.map((v, i) => `${print(v)}=${print(this.point[i]!)}`).join('\\\\ ');
    return `\\left. ${print(this.expr)} \\right|_{\\substack{ ${eqs} }}`;
  }
  override diffSelf(x: Expr, d: (e: Expr, x: Expr) => Expr): Expr | undefined {
    // d/dx Subs(e, v, p) = Subs(de/dx, v, p) (x not substituted) + sum_i Subs(de/dv_i, v, p) * dp_i/dx
    // (each Subs evaluated by subs, which keeps it unevaluated only where needed)
    const vars = this.variables;
    const pairs = vars.map((v, i) => [v, this.point[i]!] as [Expr, Expr]);
    const at = (e: Expr) => e.subs(pairs);
    const terms: Expr[] = [];
    if (!vars.some((v) => v.key === x.key)) terms.push(at(d(this.expr, x)));
    for (const [v, p] of pairs) {
      const dp = d(p, x);
      if (!(dp.isNumber && dp.key === '0')) terms.push(mul(at(d(this.expr, v)), dp));
    }
    return add(...terms);
  }
  override doitSelf(): Expr {
    return this.expr.subs(this.variables.map((v, i) => [v, this.point[i]!] as [Expr, Expr]));
  }
}

/**
 * SymPy `Subs(expr, variables, point)`: one variable and point, or arrays
 * of them (unevaluated; `doit` performs the substitution).
 */
export function Subs(exprIn: ExprLike, variables: ExprLike | readonly ExprLike[], point: ExprLike | readonly ExprLike[]): Expr {
  const expr = sympify(exprIn);
  const vs = (Array.isArray(variables) ? variables : [variables]).map((v) => sympify(v as ExprLike));
  const ps = (Array.isArray(point) ? point : [point]).map((p) => sympify(p as ExprLike));
  if (vs.length !== ps.length) throw new Error('Subs: number of variables and points differ');
  if (!vs.length) return expr;
  return new SubsNode([expr, ...vs, ...ps]);
}

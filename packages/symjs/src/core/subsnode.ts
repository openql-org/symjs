// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy `Subs`: an unevaluated substitution, e.g. the value of a
 * derivative at a point, `Subs(Derivative(f(x), x), x, 0)`.
 */

import type { ExprLike } from './nodes';
import { Derivative, Expr, ExtensionExpr, Fn, Sym, UndefFn, impl } from './nodes';
import { add, mul, sympify } from './ops';
import { FunctionHead } from './undef';
import { at } from './guard';

/** A bound slot keyed by its evaluation point; it cannot collide with a free symbol. */
class SubsPoint extends Sym {
  protected override computeKey(): string {
    return `SubsPoint(${this.name})`;
  }
}

/** Subs(expr, variables, points): args are [expr, ...variables, ...points]. */
export class SubsNode extends ExtensionExpr {
  /**
   * Creates a held substitution from its expression, variables and values.
   *
   * @param args - The operands in node order.
   */
  constructor(args: readonly Expr[]) {
    super('Subs', args);
  }
  /**
   * The expression in which the substitution will take place.
   *
   * @see SymPy `sympy.core.function.Subs.expr`
   */
  get expr(): Expr {
    return at(this.args, 0);
  }
  /**
   * The expressions to replace.
   *
   * @see SymPy `sympy.core.function.Subs.variables`
   */
  get variables(): Expr[] {
    const n = (this.args.length - 1) / 2;
    return this.args.slice(1, 1 + n);
  }
  /**
   * The replacement values in variable order.
   *
   * @see SymPy `sympy.core.function.Subs.point`
   */
  get point(): Expr[] {
    const n = (this.args.length - 1) / 2;
    return this.args.slice(1 + n);
  }
  /**
   * Rebuilds the node with the supplied arguments.
   *
   * @param args - The operands in node order.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new SubsNode(args);
  }
  protected override computeKey(): string {
    // The bound variable's name does not affect a derivative evaluated at a
    // point. Normalize before hashing so equality also works inside Add/Mul.
    const replacements = this.variables.map((v, i): [Expr, Expr] => [v, new SubsPoint(at(this.point, i).key)]);
    const body = impl.xreplace(this.expr, replacements);
    const unused = this.variables.flatMap((v, i) => this.expr.has(v) ? [] : [`${v.key}:${at(this.point, i).key}`]).sort();
    return `Subs(${body.key};${unused.join(',')})`;
  }
  /**
   * Identifies the argument positions binding variables and the positions in their scope.
   *
   * @returns The bound-variable and scope positions.
   */
  override bindings(): { variables: readonly number[]; scope: readonly number[] } {
    const n = (this.args.length - 1) / 2;
    return { variables: Array.from({ length: n }, (_, i) => 1 + i), scope: [0] };
  }
  /**
   * Formats the node using the supplied printer for its children.
   *
   * @param print - The expression printer for child nodes.
   * @returns The formatted expression.
   */
  override printStr(print: (e: Expr) => string): string {
    const tuple = (xs: Expr[]) => (xs.length === 1 ? print(at(xs, 0)) : `(${xs.map(print).join(', ')})`);
    return `Subs(${print(this.expr)}, ${tuple(this.variables)}, ${tuple(this.point)})`;
  }
  /**
   * Formats the node in LaTeX using the supplied printer for its children.
   *
   * @param print - The expression printer for child nodes.
   * @returns The LaTeX representation.
   */
  override printLatex(print: (e: Expr) => string): string {
    const eqs = this.variables.map((v, i) => `${print(v)}=${print(at(this.point, i))}`).join('\\\\ ');
    return `\\left. ${print(this.expr)} \\right|_{\\substack{ ${eqs} }}`;
  }
  /**
   * Differentiates the substitution, including the dependence of its evaluation point.
   *
   * @param x - The differentiation variable.
   * @param d - The callback for differentiating a subexpression.
   * @returns The derivative under this node’s differentiation rule.
   */
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
  /**
   * Evaluates the substitution numerically.
   *
   * @param evaluate - The numerical evaluator for a child expression.
   * @returns The numerically evaluated substitution.
   */
  override evalfSelf(evaluate: (x: Expr) => Expr): Expr {
    const value = this.doitSelf();
    return value.key === this.key ? this : evaluate(value);
  }
  /** Whether to evaluate child nodes before performing this substitution. */
  override get doitDeep(): boolean { return false; }

  /**
   * Substitutes within the expression while respecting its bound variables.
   *
   * @param old - The expression to replace.
   * @param replacement - The value to substitute.
   * @param recurse - The substitution callback for child expressions.
   * @returns The expression with the requested substitution applied.
   */
  override subsSelf(old: Expr, replacement: Expr, recurse: (e: Expr) => Expr): Expr {
    const variables = this.variables;
    const points = this.point;
    const i = variables.findIndex((v) => v.key === old.key);
    if (i >= 0) {
      if ((replacement instanceof Sym || replacement instanceof Fn || replacement instanceof UndefFn) && !this.has(replacement)) return impl.xreplace(this, [[old, replacement]]);
      return new SubsNode([this.expr, ...variables, ...points.map((p, j) => j < i ? p : recurse(p))]);
    }
    const changed = variables.map(recurse);
    if (changed.some((v, j) => v.key !== at(variables, j).key)) {
      return new SubsNode([this.expr, ...variables, old, ...points, replacement]);
    }
    return new SubsNode([recurse(this.expr), ...variables, ...points.map(recurse)]);
  }

  /**
   * Performs the substitution, carrying out pending derivatives when possible.
   *
   * @returns The expression after applying the substitution.
   * @see SymPy `sympy.core.function.Subs.doit`
   */
  override doitSelf(): Expr {
    const substitutions = this.variables.map((v, i): [Expr, Expr] => [v, at(this.point, i)]).filter(([v, p]) => v.key !== p.key);
    if (!substitutions.length) return this.expr;
    let source = this.expr;
    const values: [Expr, Expr][] = [];
    for (const [from, to] of substitutions) {
      if (from instanceof FunctionHead && to instanceof FunctionHead && to.apply && impl.subsFunction) {
        source = impl.subsFunction(source, from.name, to.apply, to.arities);
      } else values.push([from, to]);
    }
    if (!(source instanceof Derivative)) return (impl.doit?.(source) ?? source).subs(values);
    let expression = source.expr;
    const pending: [Expr, Expr][] = [];
    for (const [variable, order] of source.variableOrders) {
      if (expression.has(variable)) expression = impl.diff(expression, variable, order);
      else pending.push([variable, order]);
    }
    expression = expression.subs(values);
    for (const [variable, order] of pending) expression = impl.diff(expression, variable, order);
    return expression.key === this.key ? this : impl.doit?.(expression) ?? expression;
  }
}

const asList = (x: ExprLike | readonly ExprLike[]): readonly ExprLike[] => (x instanceof Expr || typeof x !== 'object' ? [x] : x);

/**
 * Represents an unevaluated substitution of one variable or an array of variables at the corresponding
 * points. Calling `doit` performs the substitution.
 *
 * @see SymPy `sympy.core.function.Subs`
 */
export function Subs(exprIn: ExprLike, variables: ExprLike | readonly ExprLike[], point: ExprLike | readonly ExprLike[]): Expr {
  const expr = sympify(exprIn);
  const vs = asList(variables).map((v) => sympify(v));
  const ps = asList(point).map((p) => sympify(p));
  if (vs.length !== ps.length) throw new RangeError('Subs: number of variables and points differ');
  if (new Set(vs.map((v) => v.key)).size !== vs.length) throw new RangeError('Subs: duplicate substitution variable');
  if (!vs.length) return expr;
  return new SubsNode([expr, ...vs, ...ps]);
}

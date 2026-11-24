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
  /**
   * Creates a function from its bound variables and body.
   *
   * @param args - The operands in node order.
   */
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
  /**
   * The bound variables, with nested parameter tuples flattened.
   *
   * @see SymPy `sympy.core.function.Lambda.variables`
   */
  get variables(): Expr[] {
    const flatten = (v: Expr): Expr[] => v instanceof ExtensionExpr && v.name === 'Tuple' ? v.args.flatMap(flatten) : [v];
    return this.args.slice(0, -1).flatMap(flatten);
  }
  /**
   * The body of the anonymous function.
   *
   * @see SymPy `sympy.core.function.Lambda.expr`
   */
  get expr(): Expr {
    return at(this.args, this.args.length - 1);
  }
  /**
   * Bound variables renamed without colliding with free symbol names.
   *
   * @see SymPy `sympy.core.function.Lambda.canonical_variables`
   */
  get canonicalVariables(): Map<Expr, Sym> {
    const names = new Set([...this.freeSymbols()].filter((s) => s instanceof Sym).map((s) => s.name));
    let i = 0;
    return new Map(this.variables.map((v) => {
      while (names.has(`_${i}`)) i++;
      return [v, new Sym(`_${i++}`)];
    }));
  }
  /**
   * Rebuilds the node with the supplied arguments.
   *
   * @param args - The operands in node order.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new LambdaNode(args);
  }
  /**
   * Identifies the argument positions binding variables and the positions in their scope.
   *
   * @returns The bound-variable and scope positions.
   */
  override bindings(): { variables: readonly number[]; scope: readonly number[] } {
    const n = this.args.length - 1;
    return { variables: Array.from({ length: n }, (_, i) => i), scope: [n] };
  }
  /**
   * Collects the free symbols of the body after removing the bound variables.
   *
   * @returns The free symbols of the body.
   */
  override freeSymbolsSelf(): ReadonlySet<Expr> {
    const bound = new Set(this.variables.map((v) => v.key));
    return new Set([...this.expr.freeSymbols()].filter((v) => !bound.has(v.key)));
  }
  /**
   * Formats the node using the supplied printer for its children.
   *
   * @param print - The expression printer for child nodes.
   * @returns The formatted expression.
   */
  override printStr(print: (e: Expr) => string): string {
    const vs = this.args.slice(0, -1);
    return `Lambda(${vs.length === 1 ? print(at(vs, 0)) : `(${vs.map(print).join(', ')})`}, ${print(this.expr)})`;
  }
  /**
   * Formats the node in LaTeX using the supplied printer for its children.
   *
   * @param print - The expression printer for child nodes.
   * @returns The LaTeX representation.
   */
  override printLatex(print: (e: Expr) => string): string {
    const vs = this.args.slice(0, -1);
    return `\\left( ${vs.length === 1 ? print(at(vs, 0)) : `\\left( ${vs.map(print).join(', \\  ')}\\right)`} \\mapsto ${print(this.expr)} \\right)`;
  }
  /**
   * Apply the function to arguments (SymPy Lambda.__call__).
   *
   * @param args - The argument values in signature order.
   * @returns The function body with the arguments substituted.
   * @throws TypeError when the argument count or tuple structure does not match the signature.
   * @see SymPy `sympy.core.function.Lambda.__call__`
   * @example
   * ```ts
   * import { ex, Lambda, symbols } from '@symjs/symjs';
   *
   * const [x] = symbols('x');
   * Lambda(x, ex`x**2 + 1`).call(3); // => 10
   * ```
   */
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

/**
 * Constructs a symbolic function with the given variable or array of variables and body `expr`.
 *
 * @see SymPy `sympy.core.function.Lambda`
 */
export function Lambda(variables: Expr | readonly Expr[], expr: ExprLike): LambdaNode {
  const vs = variables instanceof Expr ? [variables] : variables;
  return new LambdaNode([...vs, sympify(expr)]);
}

/**
 * The identity function, which returns its single argument.
 *
 * @see SymPy `sympy.functions.elementary.miscellaneous.IdentityFunction`
 * @example
 * ```ts
 * import { Id, ex } from '@symjs/symjs';
 *
 * Id.call(ex`x`); // => x
 * ```
 */
export const Id: LambdaNode = /* @__PURE__ */ identity();

function identity(): LambdaNode {
  const x = new Dummy('x');
  return new LambdaNode([x, x]);
}

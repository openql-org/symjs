// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/** SymPy utilities.lambdify: Python lambda source for symbolic expressions. */
import { Expr, Sym } from '../core/nodes';
import type { ExprLike } from '../core/nodes';
import { sympify } from '../core/ops';
import { str } from '../printing/str';

/** Nested argument lists are unpacked by an outer lambda, as in SymPy lambdastr. */
export type LambdaArgs = string | Sym | readonly LambdaArgs[];
/** An expression or nested collection of expressions forming the body of a lambda. */
export type LambdaBody = ExprLike | readonly LambdaBody[];

/**
 * Python lambda source, including nested tuple arguments.
 *
 * @param args - The operands in their defining order.
 * @param expr - The expression to evaluate.
 * @returns The formatted text.
 * @see SymPy `sympy.utilities.lambdify.lambdastr`
 * @example
 * ```ts
 * import { ex, lambdastr, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * lambdastr(x, ex`x**2`); // => lambda x: (x**2)
 * ```
 */
export function lambdastr(args: LambdaArgs, expr: LambdaBody): string {
  const top = typeof args === 'string' || args instanceof Sym ? [args] : args;
  const names: string[] = [], paths: string[] = [];
  const visit = (arg: LambdaArgs, path: string): void => {
    if (typeof arg === 'string' || arg instanceof Sym) {
      names.push(typeof arg === 'string' ? arg : arg.name);
      paths.push(path);
    } else arg.forEach((a, i) => visit(a, `${path}[${i}]`));
  };
  top.forEach((a, i) => visit(a, `_${i}`));
  const body = (e: LambdaBody): string => e instanceof Expr || typeof e !== 'object'
    ? str(sympify(e)) : `[${e.map(body).join(', ')}]`;
  const inner = `lambda ${names.join(',')}: (${body(expr)})`;
  if (top.every((a) => typeof a === 'string' || a instanceof Sym)) return inner;
  return `lambda ${top.map((_, i) => `_${i}`).join(',')}: (${inner})(${paths.join(',')})`;
}

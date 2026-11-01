// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Undefined functions (SymPy `Function('f')`) and unevaluated derivatives.
 */

import { Derivative, Expr, ExprLike, Rational, UndefFn } from './nodes';
import { sympify } from './ops';

/** A callable undefined function: f(x, y) builds the application. */
export interface UndefinedFunction {
  (...args: ExprLike[]): Expr;
  readonly functionName: string;
}

/** Create an undefined function, like SymPy `Function('f')`. */
export function Function(name: string): UndefinedFunction {
  if (!/^[A-Za-z_][A-Za-z0-9_]*$/.test(name)) throw new SyntaxError(`Invalid function name: ${name}`);
  const f = (...args: ExprLike[]) => new UndefFn(name, args.map(sympify));
  Object.defineProperty(f, 'functionName', { value: name });
  Object.defineProperty(f, 'name', { value: name });
  return f as unknown as UndefinedFunction;
}

/** Create several undefined functions: functions('f g'). */
export function functions(names: string): UndefinedFunction[] {
  return names
    .split(/[\s,]+/)
    .filter(Boolean)
    .map(Function);
}

/** Build Derivative(expr, (v, n)...), merging repeated consecutive variables. */
export function derivative(expr: Expr, variables: readonly [Expr, number][]): Expr {
  let e = expr;
  let vc: [Expr, number][] = [];
  if (e instanceof Derivative) {
    vc = e.variableCount;
    e = e.expr;
  }
  for (const [v, n] of variables) {
    const last = vc[vc.length - 1];
    if (last && last[0].key === v.key) last[1] += n;
    else vc.push([v, n]);
  }
  return new Derivative([e, ...vc.flatMap(([v, n]) => [v, Rational.of(n)])]);
}

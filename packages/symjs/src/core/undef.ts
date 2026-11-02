// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Undefined functions (SymPy `Function('f')`) and unevaluated derivatives.
 */

import type { Expr, ExprLike } from './nodes';
import { Derivative, Rational, Sym, UndefFn } from './nodes';
import { sympify } from './ops';
import { cast } from './guard';

/** A callable undefined function: f(x, y) builds the application. */
export interface UndefinedFunction {
  (...args: ExprLike[]): Expr;
  readonly functionName: string;
}

/** Create an undefined function, like SymPy `Function('f')`. */
export function SymFunction(name: string): UndefinedFunction {
  if (!/^[A-Za-z_][A-Za-z0-9_]*$/.test(name)) throw new SyntaxError(`Invalid function name: ${name}`);
  const f = (...args: ExprLike[]) => new UndefFn(name, args.map(sympify));
  Object.defineProperty(f, 'functionName', { value: name });
  Object.defineProperty(f, 'name', { value: name });
  // oxlint-disable-next-line typescript/no-unsafe-type-assertion -- functionName was added above with Object.defineProperty (non-enumerable, read-only)
  return f as unknown as UndefinedFunction;
}

/** Create several undefined functions: functions('f g'). */
export function functions(names: string): UndefinedFunction[] {
  return names
    .split(/[\s,]+/)
    .filter(Boolean)
    .map((n) => SymFunction(n));
}

/** Build Derivative(expr, (v, n)...), merging repeated consecutive variables. */
export function derivative(expr: Expr, variables: readonly [Expr, number][], evaluated = false): Expr {
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
  // evaluated derivatives: SymPy sorts symbol variables (they commute) and merges repeats
  if (evaluated && vc.every(([v]) => v instanceof Sym)) {
    const merged = new Map<string, [Expr, number]>();
    for (const [v, n] of vc) {
      const m = merged.get(v.key);
      if (m) m[1] += n;
      else merged.set(v.key, [v, n]);
    }
    vc = [...merged.values()].sort(([a], [b]) => {
      const an = cast(a, Sym).name;
      const bn = cast(b, Sym).name;
      return an < bn ? -1 : an > bn ? 1 : 0;
    });
  }
  return new Derivative([e, ...vc.flatMap(([v, n]) => [v, Rational.of(n)])]);
}

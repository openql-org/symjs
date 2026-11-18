// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Undefined functions (SymPy `Function('f')`) and unevaluated derivatives.
 */

import type { Expr, ExprLike } from './nodes';
import { Derivative, Rational, Sym, UndefFn } from './nodes';
import { sympify } from './ops';
import { cast } from './guard';
import { NoMatch, isNoMatch, type NoMatchResult } from './truth';

/** A callable undefined function: f(x, y) builds the application. */
export interface UndefinedFunction {
  (...args: ExprLike[]): Expr;
  readonly functionName: string;
  readonly arity: readonly number[] | NoMatchResult;
}

/** A function class (SymPy `FunctionClass`): a callable that builds applications of a named function. */
export interface FunctionClassLike {
  (...args: never[]): unknown;
  readonly functionName: string;
}

/** The undefined functions made by SymFunction. */
const undefinedFunctions = new WeakSet<object>();

/** Whether a value is a function class (an undefined function, a defined function, ...). */
export const isFunctionClass = (v: unknown): v is FunctionClassLike => typeof v === 'function' && 'functionName' in v && typeof v.functionName === 'string';

/** Whether a value is an undefined function made by SymFunction (SymPy `UndefinedFunction`). */
export const isUndefinedFunction = (v: unknown): v is UndefinedFunction => typeof v === 'function' && undefinedFunctions.has(v);

/** Create an undefined function, like SymPy `Function('f')`. */
export function SymFunction(name: string, options: { nargs?: number | readonly number[] } = {}): UndefinedFunction {
  if (!/^[A-Za-z_][A-Za-z0-9_]*$/.test(name)) throw new SyntaxError(`Invalid function name: ${name}`);
  const arity = options.nargs === undefined ? NoMatch : Object.freeze([...new Set(typeof options.nargs === 'number' ? [options.nargs] : options.nargs)].sort((a,b) => a-b));
  if (!isNoMatch(arity) && arity.length === 0) throw new RangeError('function arities must not be empty');
  if (!isNoMatch(arity) && arity.some((n) => !Number.isSafeInteger(n) || n < 0)) throw new RangeError('function arities must be nonnegative integers');
  const f = (...args: ExprLike[]): Expr => {
    if (!isNoMatch(arity) && !arity.includes(args.length)) throw new TypeError(`${name} does not accept ${args.length} arguments`);
    return new UndefFn(name, args.map(sympify));
  };
  Object.defineProperty(f, 'functionName', { value: name });
  Object.defineProperty(f, 'arity', { value: arity });
  Object.defineProperty(f, 'name', { value: name });
  undefinedFunctions.add(f);
  // oxlint-disable-next-line typescript/no-unsafe-type-assertion -- functionName and arity were added above with Object.defineProperty (non-enumerable, read-only)
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
    if (!Number.isSafeInteger(n) || n < 0) throw new RangeError('derivative order must be a nonnegative integer');
    if (n === 0) continue;
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
  return vc.length ? new Derivative([e, ...vc.flatMap(([v, n]) => [v, Rational.of(n)])]) : e;
}

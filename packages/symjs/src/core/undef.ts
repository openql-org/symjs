// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Undefined functions (SymPy `Function('f')`) and unevaluated derivatives.
 */

import type { Expr, ExprLike } from './nodes';
import { Derivative, ExtensionExpr, Float, S, Sym, UndefFn } from './nodes';
import { add, sympify } from './ops';
import { isIntegerQ, isNegative, isZero } from './assumptions';
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

/** A named function held as a symbolic argument of Subs. */
export class FunctionHead extends ExtensionExpr {
  constructor(name: string, readonly apply?: (...args: Expr[]) => Expr, readonly arities?: readonly number[]) {
    super(name, []);
  }

  withArgs(): Expr { return this; }

  protected override computeKey(): string { return `FunctionHead(${JSON.stringify(this.name)})`; }

  override printStr(): string { return this.name; }
}

/** Build Derivative(expr, (v, n)...), merging repeated consecutive variables. */
export function derivative(expr: Expr, variables: readonly [Expr, ExprLike][], evaluated = false): Expr {
  let e = expr;
  let vc: [Expr, Expr][] = [];
  if (e instanceof Derivative) {
    vc = e.variableOrders;
    e = e.expr;
  }
  for (const [v, count] of variables) {
    const n = derivativeCount(count);
    if (n === S.Zero) continue;
    const last = vc[vc.length - 1];
    if (last && last[0].key === v.key) last[1] = add(last[1], n);
    else vc.push([v, n]);
  }
  // evaluated derivatives: SymPy sorts symbol variables (they commute) and merges repeats
  if (evaluated && vc.every(([v]) => v instanceof Sym)) {
    const merged = new Map<string, [Expr, Expr]>();
    for (const [v, n] of vc) {
      const m = merged.get(v.key);
      if (m) m[1] = add(m[1], n);
      else merged.set(v.key, [v, n]);
    }
    vc = [...merged.values()].sort(([a], [b]) => {
      const an = cast(a, Sym).name;
      const bn = cast(b, Sym).name;
      return an < bn ? -1 : an > bn ? 1 : 0;
    });
  }
  vc = vc.filter(([, n]) => n !== S.Zero);
  return vc.length ? new Derivative([e, ...vc.flat()]) : e;
}

/** A concrete or symbolic nonnegative integer order. */
export function derivativeCount(order: ExprLike): Expr {
  const n = sympify(order);
  if (n instanceof Float || isIntegerQ(n) === false || isNegative(n) === true) {
    throw new RangeError('derivative order must be a nonnegative integer');
  }
  return isZero(n) === true ? S.Zero : n;
}

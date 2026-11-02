// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file User-defined functions: the counterpart of subclassing SymPy's
 * Function (eval, fdiff, _eval_rewrite_as_*, _eval_expand_*, _eval_evalf)
 * and of implemented_function.
 */

import { Expr, ExprLike, ExtensionExpr, Float } from './nodes';
import { add, mul, sympify } from './ops';

/** The behaviour of a function defined with defineFunction. *
 * @experimental May change in a minor release.
 */
export interface FunctionDefinition {
  /** Accepted argument counts (SymPy nargs); any count when omitted. */
  nargs?: number | readonly number[];
  /**
   * Automatic evaluation (SymPy eval classmethod): a value for these
   * arguments, or undefined to keep the call unevaluated.
   */
  eval?: (...args: Expr[]) => ExprLike | undefined;
  /** Partial derivative with respect to the argument at `index` (0-based; SymPy fdiff(index + 1)). */
  fdiff?: (args: readonly Expr[], index: number) => ExprLike;
  /** Rewrites by target name (SymPy _eval_rewrite_as_<target>): rewrite(f(x), 'cos'). */
  rewrite?: Readonly<Record<string, (...args: Expr[]) => ExprLike | undefined>>;
  /**
   * Expansions by hint name (SymPy _eval_expand_<hint>): expand(f(x), { hint: true }).
   * `self` has its arguments already expanded when the expansion is deep.
   */
  expand?: Readonly<Record<string, (self: Expr, hints: Readonly<Record<string, unknown>>) => ExprLike | undefined>>;
  /** Numeric value for real arguments (SymPy implemented_function / _eval_evalf). */
  evalf?: (...args: number[]) => number;
  /** LaTeX form; defaults to \operatorname{name}\left(...\right). */
  latex?: (args: readonly string[]) => string;
}

/** A function created by defineFunction: call it to apply it. *
 * @experimental May change in a minor release.
 */
export interface DefinedFunction {
  (...args: ExprLike[]): Expr;
  /** The function name (SymPy __name__). */
  readonly functionName: string;
  /** True when e is an application of this function. */
  isApplied(e: Expr): e is DefinedFunctionCall;
}

/** An application of a function created by defineFunction. *
 * @experimental May change in a minor release.
 */
export class DefinedFunctionCall extends ExtensionExpr {
  constructor(
    name: string,
    args: readonly Expr[],
    readonly definition: FunctionDefinition,
  ) {
    super(name, args);
  }
  withArgs(args: readonly Expr[]): Expr {
    return applyDefined(this.name, this.definition, args);
  }
  override printLatex(print: (e: Expr) => string): string {
    return this.definition.latex ? this.definition.latex(this.args.map(print)) : super.printLatex(print);
  }
  override diffSelf(x: Expr, d: (e: Expr, x: Expr) => Expr): Expr | undefined {
    const fdiff = this.definition.fdiff;
    if (!fdiff) return undefined;
    return add(...this.args.map((a, i) => (a.has(x) ? mul(sympify(fdiff(this.args, i)), d(a, x)) : 0)));
  }
  override rewriteSelf(target: string, args: readonly Expr[]): Expr | undefined {
    const r = this.definition.rewrite?.[target]?.(...args);
    return r === undefined ? undefined : sympify(r);
  }
  override expandSelf(hint: string, hints: Readonly<Record<string, unknown>>): Expr | undefined {
    const r = this.definition.expand?.[hint]?.(this, hints);
    return r === undefined ? undefined : sympify(r);
  }
  override numericValue(_dps: number): Expr | undefined {
    const f = this.definition.evalf;
    if (!f || this.args.some((a) => !a.isNumber)) return undefined;
    const v = f(...this.args.map((a) => a.toNumber()));
    return Number.isFinite(v) ? new Float(v) : undefined;
  }
}

function applyDefined(name: string, def: FunctionDefinition, args: readonly Expr[]): Expr {
  if (def.eval) {
    const v = def.eval(...args);
    if (v !== undefined) return sympify(v);
  }
  return new DefinedFunctionCall(name, args, def);
}

/**
 * Define a function with its own evaluation, derivative, rewrites and
 * expansions (SymPy: subclassing Function).
 *
 * @example
 * const mysin = defineFunction('mysin', {
 *   eval: (x) => (x.equals(0) ? 0 : undefined),
 *   fdiff: ([x]) => cos(x!),
 *   rewrite: { cos: (x) => fn('cos', [sub(pi.div(2), x)], { evaluate: false }) },
 * });
 *
 * @experimental May change in a minor release.
 */
export function defineFunction(name: string, def: FunctionDefinition = {}): DefinedFunction {
  if (!/^[A-Za-z_][A-Za-z0-9_]*$/.test(name)) throw new SyntaxError(`Invalid function name: ${name}`);
  const counts = def.nargs === undefined ? undefined : typeof def.nargs === 'number' ? [def.nargs] : def.nargs;
  const f = (...args: ExprLike[]): Expr => {
    if (counts && !counts.includes(args.length)) throw new TypeError(`${name} takes ${counts.join(' or ')} argument(s) (${args.length} given)`);
    return applyDefined(name, def, args.map(sympify));
  };
  Object.defineProperty(f, 'functionName', { value: name });
  Object.defineProperty(f, 'name', { value: name });
  Object.defineProperty(f, 'isApplied', { value: (e: Expr) => e instanceof DefinedFunctionCall && e.name === name && e.definition === def });
  return f as unknown as DefinedFunction;
}

/**
 * A function with a numeric implementation (SymPy implemented_function):
 * symbolic otherwise, evaluated by evalf/N when its arguments are numbers.
 *
 * @experimental May change in a minor release.
 */
export function implementedFunction(name: string, impl: (...args: number[]) => number): DefinedFunction {
  return defineFunction(name, { evalf: impl });
}

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file User-defined functions: the counterpart of subclassing SymPy's
 * Function (eval, fdiff, _eval_rewrite_as_*, _eval_expand_*, _eval_evalf)
 * and of implemented_function.
 */

import type { Expr, ExprLike } from './nodes';
import { Dummy, ExtensionExpr, Float, Sym, UndefFn } from './nodes';
import { add, mul, sympify } from './ops';
import { derivative } from './undef';
import { SubsNode } from './subsnode';
import { at } from './guard';
import type { NoMatchResult } from './truth';
import { NoMatch } from './truth';

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
    // by default like an undefined function of the same name (SymPy \operatorname{name}{\left(x \right)})
    return this.definition.latex ? this.definition.latex(this.args.map(print)) : print(new UndefFn(this.name, this.args));
  }
  override diffSelf(x: Expr, d: (e: Expr, x: Expr) => Expr): Expr {
    const fdiff = this.definition.fdiff ?? ((args: readonly Expr[], i: number) => this.defaultPartial(args, i));
    return add(...this.args.map((a, i) => (a.has(x) ? mul(sympify(fdiff(this.args, i)), d(a, x)) : 0)));
  }
  /**
   * SymPy Function.fdiff without a definition: Derivative(f(x), x) for a symbol that
   * no other argument contains, Derivative(f(g(x)), g(x)) for a function g(x), else
   * Subs(Derivative(f(xi), xi), xi, a).
   */
  private defaultPartial(args: readonly Expr[], i: number): Expr {
    const a = at(args, i);
    if (a instanceof UndefFn || (a instanceof Sym && !args.some((v, j) => j !== i && v.has(a)))) return derivative(this, [[a, 1]]);
    const xi = new Dummy(`xi_${i + 1}`);
    return new SubsNode([derivative(this.withArgs(args.map((b, j) => (j === i ? xi : b))), [[xi, 1]]), xi, a]);
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
  if (counts) definedCounts.set(f, counts);
  else if (def.eval) definedCounts.set(f, [def.eval.length]);
  Object.defineProperty(f, 'functionName', { value: name });
  Object.defineProperty(f, 'name', { value: name });
  Object.defineProperty(f, 'isApplied', { value: (e: Expr) => e instanceof DefinedFunctionCall && e.name === name && e.definition === def });
  // oxlint-disable-next-line typescript/no-unsafe-type-assertion -- the members of DefinedFunction were added above with Object.defineProperty (non-enumerable, read-only)
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

/** The argument counts of the functions made by defineFunction (from nargs, else from eval). */
const definedCounts = new WeakMap<object, readonly number[]>();

/**
 * The parameters of a JavaScript function from its source: their number
 * and how many have a default value, or undefined with a rest parameter.
 */
function parameters(f: (...args: never[]) => unknown): [number, number] | undefined {
  const src = Function.prototype.toString.call(f);
  const open = src.indexOf('(');
  const arrow = src.indexOf('=>');
  // a single parameter without parentheses: x => ...
  if (arrow >= 0 && (open < 0 || arrow < open)) return [1, 0];
  const params: string[] = [];
  let depth = 0;
  let quote = '';
  let cur = '';
  for (const ch of src.slice(open + 1)) {
    if (quote) {
      if (ch === quote) quote = '';
    } else if (ch === '"' || ch === "'" || ch === '`') quote = ch;
    else if ('([{'.includes(ch)) depth++;
    else if (')]}'.includes(ch)) {
      if (depth === 0) break;
      depth--;
    } else if (ch === ',' && depth === 0) {
      params.push(cur);
      cur = '';
      continue;
    }
    cur += ch;
  }
  params.push(cur);
  const ps = params.map((p) => p.trim()).filter((p) => p !== '');
  if (ps.some((p) => p.startsWith('...'))) return undefined;
  const withDefault = ps.filter((p) => /^[^=({[]*=(?!>)/.test(p)).length;
  return [ps.length, withDefault];
}

/**
 * SymPy arity(f): the number of arguments f takes, the possible numbers
 * [n, n + 1, ...] when some have default values, or NoMatch when it takes
 * any number (a rest parameter; SymPy None). A function of defineFunction
 * has the counts of its `nargs` (else of its `eval`). TypeScript optional
 * parameters leave no trace at run time and count as required (symjs `log`
 * has arity 2, SymPy's (1, 2)).
 */
export function arity(f: (...args: never[]) => unknown): number | number[] | NoMatchResult {
  const counts = definedCounts.get(f);
  if (counts) return counts.length === 1 ? at(counts, 0) : [...counts].sort((a, b) => a - b);
  if (Object.prototype.hasOwnProperty.call(f, 'functionName')) return NoMatch;
  const p = parameters(f);
  if (p === undefined) return NoMatch;
  const [n, optional] = p;
  const required = n - optional;
  return optional === 0 ? required : Array.from({ length: optional + 1 }, (_, i) => required + i);
}

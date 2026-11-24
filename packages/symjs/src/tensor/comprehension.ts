// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy ArrayComprehension and ArrayComprehensionMap
 * (sympy.tensor.array.array_comprehension): arrays defined by an
 * expression or a function of their indices over integer ranges.
 */

import { at, defined, expectType } from '../core/guard';
import type { ExprLike } from '../core/nodes';
import { Expr, ExtensionExpr, Rational, Sym } from '../core/nodes';
import { add, mul, sympify } from '../core/ops';
import { subs } from '../core/traverse';
import type { Matrix } from '../matrices/matrix';
import type { NestedList } from './ndimarray';
import { ImmutableDenseNDimArray } from './ndimarray';

/** A limit [variable, lower, upper] (bounds inclusive; combinations of integers and symbols). */
export type ComprehensionLimit = readonly [ExprLike, ExprLike, ExprLike];

/** The bounds must be built from integers and symbols only (SymPy: atoms(Symbol, Integer) == atoms()). */
function onlyIntegersAndSymbols(e: Expr): boolean {
  if (e.args.length === 0) return e instanceof Sym || (e instanceof Rational && e.q === 1n);
  return e.args.every(onlyIntegersAndSymbols);
}

/** SymPy _check_limits_validity: the limits as [variable, lower, upper] expressions. */
function checkLimits(limits: readonly ComprehensionLimit[]): Expr[] {
  const out: Expr[] = [];
  for (const l of limits) {
    if (!Array.isArray(l) || (l as readonly unknown[]).length !== 3) throw new RangeError('ArrayComprehension requires values lower and upper bound for the expression');
    const bounds = l.map((x) => {
      if (!(x instanceof Expr) && typeof x !== 'number' && typeof x !== 'bigint') {
        throw new TypeError('Bounds should be an Expression(combination of Integer and Symbol)');
      }
      return sympify(x);
    });
    const [v, lo, hi] = [at(bounds, 0), at(bounds, 1), at(bounds, 2)];
    if (![lo, hi].every(onlyIntegersAndSymbols)) throw new TypeError('Bounds should be an Expression(combination of Integer and Symbol)');
    const d = add(hi, mul(-1, lo));
    if (d instanceof Rational && d.isNegative) throw new RangeError('Lower bound should be inferior to upper bound');
    if ([...lo.freeSymbols(), ...hi.freeSymbols()].some((s) => s.key === v.key)) {
      throw new RangeError('Variable should not be part of its bounds');
    }
    out.push(v, lo, hi);
  }
  return out;
}

/**
 * The array whose element at the indices (i, j, ...) running over the limits is `function`. It
 * stays unevaluated until `doit()`, which needs numeric bounds.
 *
 * @see SymPy `sympy.tensor.array.array_comprehension.ArrayComprehension`
 * @example
 * ```ts
 * import { add, ArrayComprehension, mul, symbols } from '@symjs/symjs';
 *
 * const [i, j] = symbols('i j');
 * ArrayComprehension(add(mul(10, i), j), [i, 1, 4], [j, 1, 3]).doit()
 * // [[11, 12, 13], [21, 22, 23], [31, 32, 33], [41, 42, 43]]
 * ```
 */
export class ArrayComprehensionNode extends ExtensionExpr {
  /**
   * The arguments are the function followed by the limits (variable, lower, upper);
   * ArrayComprehensionMap keeps 0 in place of the function.
   *
   * @param fn - Function defining each array entry.
   * @param limits - Bound variables and their inclusive limits.
   */
  constructor(fn: ExprLike, ...limits: ComprehensionLimit[]) {
    super('ArrayComprehension', [sympify(fn), ...checkLimits(limits)]);
  }

  /**
   * The expression of the elements.
   *
   * @returns The expression of the elements.
   * @see SymPy `sympy.tensor.array.array_comprehension.ArrayComprehension.function`
   */
  get function(): Expr {
    return at(this.args, 0);
  }
  /**
   * The limits [variable, lower, upper].
   *
   * @returns The limits [variable, lower, upper].
   * @see SymPy `sympy.tensor.array.array_comprehension.ArrayComprehension.limits`
   */
  get limits(): [Expr, Expr, Expr][] {
    const out: [Expr, Expr, Expr][] = [];
    for (let k = 1; k < this.args.length; k += 3) out.push([at(this.args, k), at(this.args, k + 1), at(this.args, k + 2)]);
    return out;
  }
  /**
   * The index variables.
   *
   * @returns The differentiation variables in their original order.
   * @see SymPy `sympy.tensor.array.array_comprehension.ArrayComprehension.variables`
   */
  get variables(): Expr[] {
    return this.limits.map(([v]) => v);
  }
  /**
   * The shape upper - lower + 1 of each limit, possibly symbolic.
   *
   * @returns The shape upper - lower + 1 of each limit, possibly symbolic.
   * @see SymPy `sympy.tensor.array.array_comprehension.ArrayComprehension.shape`
   */
  get shape(): Expr[] {
    return this.limits.map(([, lo, hi]) => add(hi, mul(-1, lo), 1));
  }
  /**
   * Whether no bound contains a symbol.
   *
   * @returns Whether no bound contains a symbol.
   * @see SymPy `sympy.tensor.array.array_comprehension.ArrayComprehension.is_shape_numeric`
   */
  get isShapeNumeric(): boolean {
    return this.limits.every(([, lo, hi]) => lo.freeSymbols().size === 0 && hi.freeSymbols().size === 0);
  }
  /**
   * The number of dimensions (SymPy rank()).
   *
   * @returns The number of dimensions (SymPy rank()).
   * @see SymPy `sympy.tensor.array.array_comprehension.ArrayComprehension.rank`
   */
  rank(): number {
    return this.limits.length;
  }
  /**
   * The number of elements (SymPy len; 1 for no limits, as for a rank-0 array); a symbolic shape
   * has no length.
   *
   * @returns The number of elements (SymPy len; 1 for no limits, as for a rank-0 array); a symbolic shape has no length.
   * @throws RangeError when the length is symbolic.
   */
  get length(): number {
    const n = mul(...this.shape);
    if (!(n instanceof Rational)) throw new RangeError('Symbolic length is not supported');
    return Number(n.p);
  }
  /**
   * Not a scalar: differentiating by it stays unevaluated.
   *
   * @returns Not a scalar: differentiating by it stays unevaluated.
   */
  override get isScalar(): boolean {
    return false;
  }
  /**
   * The bound indices and their inclusive iteration ranges.
   *
   * @returns The bound indices and their inclusive iteration ranges.
   */
  override bindings(): { variables: readonly number[]; scope: readonly number[] } {
    const variables: number[] = [];
    for (let k = 1; k < this.args.length; k += 3) variables.push(k);
    return { variables, scope: [0] };
  }

  /** The element at the given index values. */
  protected element(values: readonly number[]): Expr {
    return subs(
      this.function,
      this.variables.map((v, k) => [v, at(values, k)] as const),
    );
  }

  /**
   * The explicit ImmutableDenseNDimArray when the shape is numeric, else this node.
   *
   * @returns The evaluated expression when the operation can be performed.
   * @see SymPy `sympy.tensor.array.array_comprehension.ArrayComprehension.doit`
   */
  doit(): Expr {
    return this.isShapeNumeric ? this.expandArray() : this;
  }
  /**
   * Evaluates this node when expression evaluation reaches it.
   *
   * @returns The evaluated expression.
   */
  override doitSelf(): Expr | undefined {
    return this.isShapeNumeric ? this.expandArray() : undefined;
  }
  private expandArray(): ImmutableDenseNDimArray {
    const ranges = this.limits.map(([, lo, hi]) => {
      const a = rationalInt(lo);
      const b = rationalInt(hi);
      return Array.from({ length: b - a + 1 }, (_, i) => a + i);
    });
    let tuples: number[][] = [[]];
    for (const r of ranges) tuples = tuples.flatMap((t) => r.map((v) => [...t, v]));
    return new ImmutableDenseNDimArray(
      tuples.map((t) => this.element(t)),
      this.shape.map((s) => rationalInt(s)),
    );
  }
  /**
   * Transform the expanded array to a list.
   *
   * @returns The entries as a nested list in axis order.
   * @throws RangeError when the array dimensions are symbolic.
   * @see SymPy `sympy.tensor.array.array_comprehension.ArrayComprehension.tolist`
   */
  tolist(): NestedList {
    if (!this.isShapeNumeric) throw new RangeError('A symbolic array cannot be expanded to a list');
    return this.expandArray().tolist();
  }
  /**
   * Transform the expanded array to a matrix.
   *
   * @returns A matrix with the same rows and columns.
   * @throws RangeError when the array dimensions are symbolic or the input does not have dimension two.
   * @see SymPy `sympy.tensor.array.array_comprehension.ArrayComprehension.tomatrix`
   */
  tomatrix(): Matrix {
    if (!this.isShapeNumeric) throw new RangeError('A symbolic array cannot be expanded to a matrix');
    if (this.rank() !== 2) throw new RangeError('Dimensions must be of size of 2');
    return this.expandArray().tomatrix();
  }

  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    const lim: ComprehensionLimit[] = [];
    for (let k = 1; k < args.length; k += 3) lim.push([at(args, k), at(args, k + 1), at(args, k + 2)]);
    return new ArrayComprehensionNode(at(args, 0), ...lim);
  }
  protected limitsStr(print: (e: Expr) => string): string[] {
    return this.limits.map((l) => `(${l.map(print).join(', ')})`);
  }
  protected limitsLatex(print: (e: Expr) => string): string[] {
    return this.limits.map((l) => `\\left( ${l.map(print).join(', \\  ')}\\right)`);
  }
  /**
   * Formats the expression in plain text.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted expression.
   */
  override printStr(print: (e: Expr) => string): string {
    return `${this.name}(${[print(this.function), ...this.limitsStr(print)].join(', ')})`;
  }
  /**
   * Formats the expression as LaTeX.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted LaTeX.
   */
  override printLatex(print: (e: Expr) => string): string {
    return `\\operatorname{${this.name}}\\left(${[print(this.function), ...this.limitsLatex(print)].join(', ')}\\right)`;
  }
}

/**
 * Computes one entry of a mapped array comprehension.
 *
 * @param n - Product of the current index values for a one-argument callback.
 * @returns The entry at the current combination of indices.
 */
export type ComprehensionLambda = (() => ExprLike) | ((n: number) => ExprLike);

/** The value of an integer bound or dimension (numeric once the shape is). */
function rationalInt(e: Expr): number {
  return Number(expectType(e, (v): v is Rational => v instanceof Rational, 'a numeric bound').p);
}

/** A lambda declaring no parameter is called without arguments (SymPy checks its arity). */
const isNullary = (f: ComprehensionLambda): f is () => ExprLike => f.length === 0;

const lambdaIds = new WeakMap<Function, number>();
let lambdaCounter = 0;

/**
 * Like ArrayComprehension with a JavaScript function instead of an expression. A function of one
 * argument receives the product of the index values (as SymPy does), a function of none is a
 * constant.
 *
 * @see SymPy `sympy.tensor.array.array_comprehension.ArrayComprehensionMap`
 * @example
 * ```ts
 * import { ArrayComprehensionMap, symbols } from '@symjs/symjs';
 *
 * const [j] = symbols('j');
 * ArrayComprehensionMap((a: number) => a + 1, [j, 1, 4]).doit(); // => [2, 3, 4, 5]
 * ```
 */
export class ArrayComprehensionMapNode extends ArrayComprehensionNode {
  readonly #fn: ComprehensionLambda;
  /**
   * Constructs an instance of `ArrayComprehensionMapNode`.
   *
   * @param fn - Function defining each array entry.
   * @param limits - Bound variables and their inclusive limits.
   * @throws TypeError when the callback takes more than one argument or the input type is unsupported.
   */
  constructor(fn: ComprehensionLambda, ...limits: ComprehensionLimit[]) {
    if (typeof fn !== 'function') throw new TypeError('Data type not supported');
    if (fn.length > 1) throw new TypeError('ArrayComprehensionMap: the function takes no argument or one argument');
    super(0, ...limits);
    this.#fn = fn;
    if (!lambdaIds.has(fn)) lambdaIds.set(fn, ++lambdaCounter);
  }
  /**
   * The JavaScript function of the elements.
   *
   * @returns The JavaScript function of the elements.
   */
  get lambda(): ComprehensionLambda {
    return this.#fn;
  }
  /**
   * The array entries are defined by the callback in `lambda`.
   *
   * @returns Accessing the symbolic function of a callback comprehension always throws a `TypeError`.
   * @throws TypeError when the comprehension uses a callback instead of a symbolic expression.
   * @see SymPy `sympy.tensor.array.array_comprehension.ArrayComprehensionMap.function`
   */
  override get function(): Expr {
    throw new TypeError('ArrayComprehensionMap has no symbolic function; use lambda');
  }
  protected override element(values: readonly number[]): Expr {
    const f = this.#fn;
    return sympify(isNullary(f) ? f() : f(values.reduce((a, b) => a * b, 1)));
  }
  /**
   * Rebuilds the expression with replacement arguments in their original order.
   *
   * @param args - Replacement arguments in the same order as `args` on the original expression.
   * @returns The rebuilt expression.
   */
  override withArgs(args: readonly Expr[]): Expr {
    const lim: ComprehensionLimit[] = [];
    for (let k = 1; k < args.length; k += 3) lim.push([at(args, k), at(args, k + 1), at(args, k + 2)]);
    return new ArrayComprehensionMapNode(this.#fn, ...lim);
  }
  /**
   * Formats the expression in plain text.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted expression.
   */
  override printStr(print: (e: Expr) => string): string {
    return `ArrayComprehensionMap(${this.limitsStr(print).join(', ')})`;
  }
  /**
   * Formats the expression as LaTeX.
   *
   * @param print - Formatter for a child expression.
   * @returns The formatted LaTeX.
   */
  override printLatex(print: (e: Expr) => string): string {
    return `\\operatorname{ArrayComprehensionMap}\\left(${this.limitsLatex(print).join(', ')}\\right)`;
  }
  protected override computeKey(): string {
    return `ArrayComprehensionMap#${defined(lambdaIds.get(this.#fn), 'lambda id')}${super.computeKey()}`;
  }
}

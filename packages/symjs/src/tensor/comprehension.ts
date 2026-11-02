// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy ArrayComprehension and ArrayComprehensionMap
 * (sympy.tensor.array.array_comprehension): arrays defined by an
 * expression or a function of their indices over integer ranges.
 */

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
    const [v, lo, hi] = l.map((x) => {
      if (!(x instanceof Expr) && typeof x !== 'number' && typeof x !== 'bigint') {
        throw new TypeError('Bounds should be an Expression(combination of Integer and Symbol)');
      }
      return sympify(x);
    }) as [Expr, Expr, Expr];
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
 * SymPy ArrayComprehension(function, *limits): the array whose element at
 * the indices (i, j, ...) running over the limits is `function`. It stays
 * unevaluated until `doit()`, which needs numeric bounds.
 *
 * @example
 * ArrayComprehension(add(mul(10, i), j), [i, 1, 4], [j, 1, 3]).doit()
 * // [[11, 12, 13], [21, 22, 23], [31, 32, 33], [41, 42, 43]]
 */
export class ArrayComprehensionNode extends ExtensionExpr {
  /**
   * The arguments are the function followed by the limits (variable,
   * lower, upper); ArrayComprehensionMap keeps 0 in place of the function.
   */
  constructor(fn: ExprLike, ...limits: ComprehensionLimit[]) {
    super('ArrayComprehension', [sympify(fn), ...checkLimits(limits)]);
  }

  /** The expression of the elements (SymPy function). */
  get function(): Expr {
    return this.args[0]!;
  }
  /** The limits [variable, lower, upper] (SymPy limits). */
  get limits(): [Expr, Expr, Expr][] {
    const out: [Expr, Expr, Expr][] = [];
    for (let k = 1; k < this.args.length; k += 3) out.push([this.args[k]!, this.args[k + 1]!, this.args[k + 2]!]);
    return out;
  }
  /** The index variables (SymPy variables). */
  get variables(): Expr[] {
    return this.limits.map(([v]) => v);
  }
  /** The shape upper - lower + 1 of each limit, possibly symbolic (SymPy shape). */
  get shape(): Expr[] {
    return this.limits.map(([, lo, hi]) => add(hi, mul(-1, lo), 1));
  }
  /** Whether no bound contains a symbol (SymPy is_shape_numeric). */
  get isShapeNumeric(): boolean {
    return this.limits.every(([, lo, hi]) => lo.freeSymbols().size === 0 && hi.freeSymbols().size === 0);
  }
  /** The number of dimensions (SymPy rank()). */
  rank(): number {
    return this.limits.length;
  }
  /** The number of elements (SymPy len); a symbolic shape has no length. */
  get length(): number {
    if (this.limits.length === 0) return 0;
    const n = mul(...this.shape);
    if (!(n instanceof Rational)) throw new RangeError('Symbolic length is not supported');
    return Number(n.p);
  }
  /** Not a scalar: differentiating by it stays unevaluated. */
  override get isScalar(): boolean {
    return false;
  }
  override bindings(): { variables: readonly number[]; scope: readonly number[] } {
    const variables: number[] = [];
    for (let k = 1; k < this.args.length; k += 3) variables.push(k);
    return { variables, scope: [0] };
  }

  /** The element at the given index values. */
  protected element(values: readonly number[]): Expr {
    return subs(
      this.function,
      this.variables.map((v, k) => [v, values[k]!] as const),
    );
  }

  /** SymPy doit: the explicit ImmutableDenseNDimArray when the shape is numeric, else this node. */
  doit(): Expr {
    return this.isShapeNumeric ? this.expandArray() : this;
  }
  override doitSelf(): Expr | undefined {
    return this.isShapeNumeric ? this.expandArray() : undefined;
  }
  private expandArray(): ImmutableDenseNDimArray {
    const ranges = this.limits.map(([, lo, hi]) => {
      const a = Number((lo as Rational).p);
      const b = Number((hi as Rational).p);
      return Array.from({ length: b - a + 1 }, (_, i) => a + i);
    });
    let tuples: number[][] = [[]];
    for (const r of ranges) tuples = tuples.flatMap((t) => r.map((v) => [...t, v]));
    return new ImmutableDenseNDimArray(
      tuples.map((t) => this.element(t)),
      this.shape.map((s) => Number((s as Rational).p)),
    );
  }
  /** SymPy tolist (numeric shape only). */
  tolist(): NestedList {
    if (!this.isShapeNumeric) throw new RangeError('A symbolic array cannot be expanded to a list');
    return this.expandArray().tolist();
  }
  /** SymPy tomatrix (numeric shape and rank 2 only). */
  tomatrix(): Matrix {
    if (!this.isShapeNumeric) throw new RangeError('A symbolic array cannot be expanded to a matrix');
    if (this.rank() !== 2) throw new RangeError('Dimensions must be of size of 2');
    return this.expandArray().tomatrix();
  }

  withArgs(args: readonly Expr[]): Expr {
    const lim: ComprehensionLimit[] = [];
    for (let k = 1; k < args.length; k += 3) lim.push([args[k]!, args[k + 1]!, args[k + 2]!]);
    return new ArrayComprehensionNode(args[0]!, ...lim);
  }
  protected limitsStr(print: (e: Expr) => string): string[] {
    return this.limits.map((l) => `(${l.map(print).join(', ')})`);
  }
  protected limitsLatex(print: (e: Expr) => string): string[] {
    return this.limits.map((l) => `\\left( ${l.map(print).join(', \\  ')}\\right)`);
  }
  override printStr(print: (e: Expr) => string): string {
    return `${this.name}(${[print(this.function), ...this.limitsStr(print)].join(', ')})`;
  }
  override printLatex(print: (e: Expr) => string): string {
    return `\\operatorname{${this.name}}\\left(${[print(this.function), ...this.limitsLatex(print)].join(', ')}\\right)`;
  }
}

/** The function of an ArrayComprehensionMap: no argument, or the product of the index values. */
export type ComprehensionLambda = (() => ExprLike) | ((n: number) => ExprLike);

const lambdaIds = new WeakMap<Function, number>();
let lambdaCounter = 0;

/**
 * SymPy ArrayComprehensionMap(lambda, *limits): like ArrayComprehension
 * with a JavaScript function instead of an expression. A function of one
 * argument receives the product of the index values (as SymPy does), a
 * function of none is a constant.
 *
 * @example
 * ArrayComprehensionMap((a: number) => a + 1, [j, 1, 4]).doit() // [2, 3, 4, 5]
 */
export class ArrayComprehensionMapNode extends ArrayComprehensionNode {
  readonly #fn: ComprehensionLambda;
  constructor(fn: ComprehensionLambda, ...limits: ComprehensionLimit[]) {
    if (typeof fn !== 'function') throw new TypeError('Data type not supported');
    if (fn.length > 1) throw new TypeError('ArrayComprehensionMap: the function takes no argument or one argument');
    super(0, ...limits);
    this.#fn = fn;
    if (!lambdaIds.has(fn)) lambdaIds.set(fn, ++lambdaCounter);
  }
  /** The JavaScript function of the elements. */
  get lambda(): ComprehensionLambda {
    return this.#fn;
  }
  /**
   * An ArrayComprehensionMap has no symbolic function (SymPy returns its
   * first limit here); use `lambda`.
   */
  override get function(): Expr {
    throw new TypeError('ArrayComprehensionMap has no symbolic function; use lambda');
  }
  protected override element(values: readonly number[]): Expr {
    const f = this.#fn;
    return sympify(f.length === 0 ? (f as () => ExprLike)() : f(values.reduce((a, b) => a * b, 1)));
  }
  override withArgs(args: readonly Expr[]): Expr {
    const lim: ComprehensionLimit[] = [];
    for (let k = 1; k < args.length; k += 3) lim.push([args[k]!, args[k + 1]!, args[k + 2]!]);
    return new ArrayComprehensionMapNode(this.#fn, ...lim);
  }
  override printStr(print: (e: Expr) => string): string {
    return `ArrayComprehensionMap(${this.limitsStr(print).join(', ')})`;
  }
  override printLatex(print: (e: Expr) => string): string {
    return `\\operatorname{ArrayComprehensionMap}\\left(${this.limitsLatex(print).join(', ')}\\right)`;
  }
  protected override computeKey(): string {
    return `ArrayComprehensionMap#${lambdaIds.get(this.#fn) ?? 0}${super.computeKey()}`;
  }
}

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy IndexedBase and Indexed: indexed objects such as A[i] or f[n],
 * usable as unknowns and inside sums.
 */

import type { Assumptions, Expr, ExprLike, Head } from './nodes';
import { ExtensionExpr, Rational, S, Sym } from './nodes';
import { sympify } from './ops';
import { at } from './guard';
import { cast } from './guard';
import { TupleNode } from './containers';
import { NoMatch, isNoMatch } from './truth';
import type { NoMatchResult } from './truth';

/** An explicit N-dimensional array (tensor/ndimarray), recognised without importing it. */
function isExplicitArray(base: Expr): base is Expr & { get(...index: number[]): Expr } {
  return base instanceof ExtensionExpr && base.name.endsWith('NDimArray') && 'get' in base && typeof base.get === 'function';
}

/**
 * Represents an indexed element such as `base[i, j]`. Its arguments are the base symbol followed by the
 * indices.
 *
 * @see SymPy `sympy.tensor.indexed.Indexed`
 * @example
 * ```ts
 * import { Indexed, ex } from '@symjs/symjs';
 *
 * new Indexed([ex`A`, ex`i`]); // => A[i]
 * ```
 */
export class Indexed extends ExtensionExpr {
  /**
   * Creates an `Indexed`.
   *
   * @param args - The indexed base followed by the subscripts.
   * @throws TypeError when the base is already indexed.
   * @throws RangeError when no index is supplied.
   */
  constructor(args: readonly Expr[]) {
    if (args.length < 2) throw new RangeError('Indexed needs at least one index.');
    const base = at(args, 0);
    if (base instanceof Indexed) throw new TypeError('Indexed requires an unindexed base.');
    super('Indexed', [base instanceof Sym ? new IndexedBase(base) : base, ...args.slice(1)]);
  }
  /**
   * Counts the indices applied to the base.
   *
   * @returns The tensor rank.
   * @see SymPy `sympy.tensor.indexed.Indexed.rank`
   */
  get rank(): number { return this.args.length - 1; }
  /**
   * Identifies the object to which the indices apply.
   *
   * @returns The indexed base.
   * @see SymPy `sympy.tensor.indexed.Indexed.base`
   */
  get base(): Expr {
    return at(this.args, 0);
  }
  /**
   * Lists the subscripts in axis order.
   *
   * @returns The index expressions.
   * @see SymPy `sympy.tensor.indexed.Indexed.indices`
   */
  get indices(): Expr[] {
    return this.args.slice(1);
  }
  /**
   * Collects the assumptions inherited from the base label.
   *
   * @returns The known facts keyed by their SymPy names.
   * @see SymPy `sympy.tensor.indexed.Indexed.assumptions0`
   */
  get assumptions0(): Map<string, boolean> {
    return this.base instanceof IndexedBase ? this.base.assumptions0 : new Map();
  }
  /**
   * Queries the indexed object's reality assumption through its label.
   *
   * @returns The known truth value, or `undefined` when the hook has no answer.
   */
  override isRealSelf(): boolean | undefined {
    return this.assumptions0.get('real');
  }
  /**
   * Rebuilds the node with the supplied arguments.
   *
   * @param args - The replacement arguments, in node order.
   * @returns The expression rebuilt with the new arguments.
   * @throws RangeError when an explicit sequence index is out of bounds.
   */
  withArgs(args: readonly Expr[]): Expr {
    const base = at(args, 0), index = at(args, 1);
    if (base instanceof TupleNode && args.length === 2 && index instanceof Rational && index.isInteger) {
      const n = Number(index.p);
      const value = base.args[n < 0 ? base.args.length + n : n];
      if (value === undefined) throw new RangeError('Indexed sequence index out of range.');
      return value;
    }
    // an explicit array with integer indices gives its element (SymPy Indexed.__new__ on an NDimArray base)
    const indices = args.slice(1);
    if (isExplicitArray(base) && indices.every((i): i is Rational => i instanceof Rational && i.isInteger)) {
      return base.get(...indices.map((i) => Number(i.p)));
    }
    return new Indexed(args);
  }
  /**
   * Substitutes in the node using its specialized substitution rule.
   *
   * @param old - The expression to replace.
   * @param nw - The new expression.
   * @returns The specialized result, or `undefined` to use the default behavior.
   */
  override subsSelf(old: Expr, nw: Expr): Expr | undefined {
    if (this.base instanceof IndexedBase && this.base.label.key === old.key) return this.withArgs([nw, ...this.indices]);
    return undefined;
  }
  /**
   * Collects the free symbols contributed by the node.
   *
   * @returns The free indexed expression, label and subscript symbols.
   */
  override freeSymbolsSelf(): ReadonlySet<Expr> {
    // An indexed entry is an independent scalar as well as containing the
    // symbols in its label and indices (SymPy Indexed.free_symbols).
    return new Set([this, ...this.args.flatMap((a) => [...a.freeSymbols()])]);
  }
  /**
   * Formats the node using the expression printer for its arguments.
   *
   * @param print - The printer to use for child expressions.
   * @returns The formatted string.
   */
  override printStr(print: (e: Expr) => string): string {
    return `${print(this.base)}[${this.indices.map(print).join(', ')}]`;
  }
  /**
   * Formats the node in LaTeX using the supplied child printer.
   *
   * @param print - The printer to use for child expressions.
   * @returns The formatted string.
   */
  override printLatex(print: (e: Expr) => string): string {
    return `{${print(this.base)}}_{${this.indices.map(print).join(',')}}`;
  }
  /**
   * Differentiates the indexed object with respect to its index or label, giving NaN for index
   * differentiation and zero for the label.
   *
   * @param x - The differentiation variable.
   * @returns The derivative with respect to the specified expression.
   */
  override diffSelf(x: Expr): Expr {
    return this.indices.some((i) => i.has(x)) ? S.NaN : S.Zero;
  }
}

/**
 * Represents the base of an indexed expression. Use `base.at(i, j)` to form a component.
 *
 * @see SymPy `sympy.tensor.indexed.IndexedBase`
 * @example
 * ```ts
 * import { IndexedBase, ex } from '@symjs/symjs';
 *
 * new IndexedBase('A').at(ex`i`); // => A[i]
 * ```
 */
export class IndexedBase extends ExtensionExpr {
  /**
   * Identifies the constructor associated with the expression.
   *
   * @returns The callable expression head.
   * @see SymPy `sympy.tensor.indexed.IndexedBase.func`
   */
  override get func(): Head {
    return indexedBaseFromArgs;
  }
  /**
   * The symbolic label of the indexed base.
   *
   * @see SymPy `sympy.tensor.indexed.IndexedBase.label`
   */
  readonly label: Sym | Expr;
  readonly #assumptionSymbol: Sym;
  /**
   * Creates an `IndexedBase`.
   *
   * @param name - The symbolic name or names.
   * @param options - Symbol assumptions for the base label and an optional `shape` of axis lengths.
   */
  constructor(name: string | Sym | Expr, options: Assumptions & { readonly shape?: readonly ExprLike[] } = {}) {
    const { shape, ...assumptions } = options;
    const label = typeof name === 'string' ? new Sym(name, assumptions) : name;
    super('IndexedBase', [label, ...(shape === undefined ? [] : [new TupleNode(shape.map(sympify))])]);
    this.label = label;
    // a label that is an expression (IndexedBase(a/b)) has no name: its assumptions live on a fixed placeholder
    this.#assumptionSymbol = label instanceof Sym ? new Sym(label.name, { ...label.assumptions, ...assumptions }) : new Sym('IndexedBase_label', assumptions);
  }
  /**
   * Collects the assumptions inherited from the base label.
   *
   * @returns The known facts keyed by their SymPy names.
   * @see SymPy `sympy.tensor.indexed.IndexedBase.assumptions0`
   */
  get assumptions0(): Map<string, boolean> {
    return this.#assumptionSymbol.assumptions0;
  }
  protected override computeKey(): string {
    return `${super.computeKey()}:${this.#assumptionSymbol.key}`;
  }
  protected override computeCommutative(): boolean {
    return this.#assumptionSymbol.isCommutative;
  }
  /**
   * Queries the indexed object's reality assumption through its label.
   *
   * @returns The known truth value, or `undefined` when the hook has no answer.
   */
  override isRealSelf(): boolean | undefined {
    return this.assumptions0.get('real');
  }
  /**
   * Reports the declared size of each axis.
   *
   * @returns The axis lengths or `NoMatch`.
   * @see SymPy `sympy.tensor.indexed.IndexedBase.shape`
   */
  get shape(): readonly Expr[] | NoMatchResult {
    return this.args.length === 1 ? NoMatch : cast(at(this.args, 1), TupleNode).args;
  }
  /**
   * Rebuilds the node with the supplied arguments.
   *
   * @param args - The replacement arguments, in node order.
   * @returns The expression rebuilt with the new arguments.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new IndexedBase(at(args, 0), { ...this.#assumptionSymbol.assumptions, ...(args.length === 1 ? {} : { shape: cast(at(args, 1), TupleNode).args }) });
  }
  /**
   * Tests for structural equality with the other object.
   *
   * @param other - The other operand.
   * @returns Whether the two objects have equal components.
   * @see SymPy `sympy.tensor.indexed.IndexedBase.equals`
   */
  equals(other: unknown): boolean {
    return other instanceof IndexedBase && this.key === other.key;
  }
  /**
   * Reads the reality assumption from the base label.
   *
   * @returns The truth value of the assumption.
   * @see SymPy `sympy.tensor.indexed.IndexedBase.is_real`
   */
  get isReal(): boolean | 'unknown' {
    return this.assumptions0.get('real') ?? 'unknown';
  }
  /**
   * Applies subscripts to this base to form an indexed component.
   *
   * @param indices - The subscripts in axis order.
   * @returns The indexed component of the base.
   * @throws RangeError when the number of subscripts differs from the rank.
   */
  at(...indices: ExprLike[]): Indexed {
    const shape = this.shape;
    if (!isNoMatch(shape) && shape.length !== indices.length) throw new RangeError('Rank mismatch.');
    return new Indexed([this, ...indices.map(sympify)]);
  }
  /**
   * Formats the node using the expression printer for its arguments.
   *
   * @param print - The printer to use for child expressions.
   * @returns The formatted string.
   */
  override printStr(print: (e: Expr) => string): string {
    return print(this.label);
  }
  /**
   * Formats the node in LaTeX using the supplied child printer.
   *
   * @param print - The printer to use for child expressions.
   * @returns The formatted string.
   */
  override printLatex(print: (e: Expr) => string): string {
    return print(this.label);
  }
}

const indexedBaseFromArgs = (...args: ExprLike[]): IndexedBase => new IndexedBase(cast(sympify(at(args, 0)), Sym), args[1] === undefined ? {} : { shape: cast(sympify(args[1]), TupleNode).args });

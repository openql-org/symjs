// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy (sympy/core/containers.py), Copyright (c) SymPy Development Team, BSD-3-Clause.

/**
 * @file SymPy's containers as expressions: `Tuple(a, b, ...)` and
 * `Dict({k: v, ...})`. Their elements are sympified, they take part in
 * substitution and traversal like any other node, and they print as Python
 * tuples and dicts.
 */

import type { Expr, ExprLike } from './nodes';
import { Derivative, ExtensionExpr, Integral, Piecewise } from './nodes';
import { Concrete } from './concrete';
import { sympify } from './ops';
import { callableClass } from './callable';
import { at, cast } from './guard';
import { ordered } from './match';
import { compareKeys, sortKey } from '../printing/sortkey';

/**
 * An immutable sequence of expressions.
 *
 * @see SymPy `sympy.core.containers.Tuple`
 * @example
 * ```ts
 * import { TupleNode, ex } from '@symjs/symjs';
 *
 * new TupleNode([ex`1`, ex`2`]).at(-1); // => 2
 * ```
 */
export class TupleNode extends ExtensionExpr {
  /**
   * Creates a `TupleNode`.
   *
   * @param args - The arguments in positional order.
   */
  constructor(args: readonly Expr[]) {
    super('Tuple', args);
  }
  /**
   * Rebuilds the node with the supplied arguments.
   *
   * @param args - The replacement arguments, in node order.
   * @returns The expression rebuilt with the new arguments.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new TupleNode(args);
  }
  /**
   * Counts the elements in the tuple.
   *
   * @returns The tuple length.
   */
  get length(): number {
    return this.args.length;
  }
  /**
   * Selects a tuple element, counting negative indices from the end.
   *
   * @param i - The zero-based index.
   * @returns The indexed expression.
   */
  at(i: number): Expr {
    return at(this.args, i < 0 ? this.args.length + i : i);
  }
  /**
   * Collects the tuple elements in their original order.
   *
   * @returns An array of expressions.
   */
  toArray(): Expr[] {
    return [...this.args];
  }
  [Symbol.iterator](): Iterator<Expr> {
    return this.args[Symbol.iterator]();
  }
  /**
   * Counts occurrences of the supplied value in the tuple.
   *
   * @param value - The value to examine.
   * @returns The number of matching occurrences.
   * @see SymPy `sympy.core.containers.Tuple.count`
   */
  count(value: ExprLike): number {
    const k = sympify(value).key;
    return this.args.filter((a) => a.key === k).length;
  }
  /**
   * Locates the first occurrence of a value, raising `RangeError` if it is absent.
   *
   * @param value - The value to examine.
   * @param start - The starting value or index.
   * @param stop - The exclusive upper index.
   * @returns The zero-based position.
   * @throws RangeError when the requested element is absent from the search range.
   * @see SymPy `sympy.core.containers.Tuple.index`
   */
  index(value: ExprLike, start = 0, stop = this.length): number {
    const k = sympify(value).key;
    const from = start < 0 ? Math.max(0, this.length + start) : start;
    const to = stop < 0 ? Math.max(0, this.length + stop) : stop;
    const i = this.args.findIndex((a, j) => j >= from && j < to && a.key === k);
    if (i < 0) throw new RangeError(`${String(value)} is not in the Tuple`);
    return i;
  }
  /**
   * Concatenates the tuples in order.
   *
   * @param other - The other operand.
   * @returns The tuple containing both sequences in order.
   */
  concat(other: TupleNode | readonly ExprLike[]): TupleNode {
    return new TupleNode([...this.args, ...(other instanceof TupleNode ? other.args : other.map(sympify))]);
  }
  /**
   * Repeats the tuple the specified number of times.
   *
   * @param count - The repetition count.
   * @returns The tuple repeated the requested number of times.
   * @throws TypeError when the repetition count is not an integer.
   */
  repeat(count: number): TupleNode {
    if (!Number.isSafeInteger(count)) throw new TypeError('Tuple repetition requires an integer');
    return new TupleNode(Array.from({ length: Math.max(0, count) }, () => this.args).flat());
  }
  /**
   * Prints the tuple with parentheses and preserves the trailing comma for a single element.
   *
   * @param print - The printer to use for child expressions.
   * @returns The formatted string.
   */
  override printStr(print: (e: Expr) => string): string {
    return this.args.length === 1 ? `(${print(at(this.args, 0))},)` : `(${this.args.map(print).join(', ')})`;
  }
}

/**
 * Constructs an immutable ordered sequence of expressions.
 *
 * @param xs - The elements of the tuple.
 * @returns The immutable tuple.
 * @see SymPy `sympy.core.containers.Tuple`
 * @example
 * ```ts
 * import { Tuple } from '@symjs/symjs';
 *
 * Tuple(1, 2).at(-1); // => 2
 * ```
 */
export const Tuple = /* @__PURE__ */ callableClass(TupleNode, (...xs: ExprLike[]): TupleNode => new TupleNode(xs.map(sympify)));
export type Tuple = TupleNode;


type DictInput = ReadonlyMap<ExprLike, ExprLike> | readonly (readonly [ExprLike, ExprLike])[];
const isMapInput = (x: DictInput): x is ReadonlyMap<ExprLike, ExprLike> => !Array.isArray(x);

/**
 * An immutable mapping of expressions; its arguments are the (key, value) Tuples in canonical order.
 *
 * @see SymPy `sympy.core.containers.Dict`
 * @example
 * ```ts
 * import { DictNode, Tuple, ex } from '@symjs/symjs';
 *
 * new DictNode([Tuple(ex`x`, 2)]).get(ex`x`); // => 2
 * ```
 */
export class DictNode extends ExtensionExpr {
  private readonly map: ReadonlyMap<string, readonly [Expr, Expr]>;
  /**
   * Creates a `DictNode`.
   *
   * @param items - The expressions to search for.
   */
  constructor(items: readonly TupleNode[]) {
    super('Dict', ordered(items));
    this.map = new Map(this.args.map((t) => [at(t.args, 0).key, [at(t.args, 0), at(t.args, 1)] as const]));
  }
  /**
   * Rebuilds the node with the supplied arguments.
   *
   * @param args - The replacement arguments, in node order.
   * @returns The expression rebuilt with the new arguments.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new DictNode(args.map((t) => cast(t, TupleNode, 'Dict item')));
  }
  /**
   * Counts the entries in the dictionary.
   *
   * @returns The entry count.
   */
  get size(): number {
    return this.map.size;
  }
  /**
   * Looks up a key and uses the supplied fallback for a missing entry. A missing key without a fallback
   * raises `RangeError`.
   *
   * @param key - The lookup key.
   * @param fallback - The value to return for a missing key.
   * @returns The stored value or fallback.
   * @throws RangeError when the key is absent and no fallback was supplied.
   * @see SymPy `sympy.core.containers.Dict.get`
   */
  get(key: ExprLike, fallback?: Expr): Expr {
    const v = this.map.get(sympify(key).key);
    if (v) return v[1];
    if (fallback) return fallback;
    throw new RangeError(`${String(key)} is not a key of the Dict`);
  }
  /**
   * Tests whether the key occurs in the dictionary.
   *
   * @param key - The lookup key.
   * @returns True if the key is present.
   */
  containsKey(key: ExprLike): boolean {
    return this.map.has(sympify(key).key);
  }
  /**
   * Lists the keys in canonical order.
   *
   * @returns The resulting expressions in order.
   * @see SymPy `sympy.core.containers.Dict.keys`
   */
  keys(): Expr[] {
    return [...this.map.values()].map(([k]) => k);
  }
  /**
   * Lists the values in canonical key order.
   *
   * @returns The resulting expressions in order.
   * @see SymPy `sympy.core.containers.Dict.values`
   */
  values(): Expr[] {
    return [...this.map.values()].map(([, v]) => v);
  }
  /**
   * Lists the key-value pairs in canonical key order.
   *
   * @returns The ordered entry pairs.
   * @see SymPy `sympy.core.containers.Dict.items`
   */
  items(): (readonly [Expr, Expr])[] {
    return [...this.map.values()];
  }
  /**
   * Copies the dictionary entries into an expression-keyed map.
   *
   * @returns A map of keys to values.
   */
  toMap(): Map<Expr, Expr> {
    return new Map(this.items());
  }
  /** The (key, value) Tuples with the keys in default_sort_key order (the printers' order). */
  private sortedItems(): Expr[] {
    return [...this.args].sort((a, b) => compareKeys(sortKey(at(a.args, 0)), sortKey(at(b.args, 0))));
  }
  /**
   * Formats the dictionary with keys in canonical order.
   *
   * @param print - The printer to use for child expressions.
   * @returns The formatted string.
   */
  override printStr(print: (e: Expr) => string): string {
    return `{${this.sortedItems().map((t) => `${print(at(t.args, 0))}: ${print(at(t.args, 1))}`).join(', ')}}`;
  }
  /**
   * Formats the key-value pairs as a LaTeX mapping.
   *
   * @param print - The printer to use for child expressions.
   * @returns The formatted string.
   */
  override printLatex(print: (e: Expr) => string): string {
    return `\\left\\{ ${this.sortedItems().map((t) => `${print(at(t.args, 0))} : ${print(at(t.args, 1))}`).join(', \\  ')}\\right\\}`;
  }
}

/**
 * Constructs an immutable mapping from expression keys to expression values.
 *
 * @param items - The map or sequence of key-value pairs.
 * @returns The immutable dictionary.
 * @see SymPy `sympy.core.containers.Dict`
 * @example
 * ```ts
 * import { Dict, ex } from '@symjs/symjs';
 *
 * Dict([[ex`x`, 2]]).get(ex`x`); // => 2
 * ```
 */
export const Dict = /* @__PURE__ */ callableClass(DictNode, (items: DictInput): DictNode => {
  const pairs = isMapInput(items) ? [...items] : items;
  const m = new Map<string, TupleNode>();
  for (const [k, v] of pairs) {
    const key = sympify(k);
    m.set(key.key, new TupleNode([key, sympify(v)]));
  }
  return new DictNode([...m.values()]);
});
export type Dict = DictNode;

/** The symbolic arguments in the public traversal API. */
export function traversalArgs(e: Expr): readonly Expr[] {
  const tuple = (args: readonly Expr[]) => new TupleNode(args);
  if (e instanceof Piecewise) return e.pairs.map(([value, condition]) => tuple([value, condition]));
  if (e instanceof Integral) {
    const limits: Expr[] = [];
    let body: Expr = e;
    while (body instanceof Integral) {
      limits.unshift(tuple(body.args.slice(1)));
      body = body.integrand;
    }
    return [body, ...limits];
  }
  if (e instanceof Concrete) return [e.function, ...e.limits.map((limit) => tuple(limit))];
  if (e instanceof Derivative) return [e.expr, ...e.variableOrders.map(([v, n]) => tuple([v, n]))];
  return e.args;
}

/**
 * Traverses the expression tree breadth first.
 *
 * @param e - The input expression.
 * @returns An iterable visiting the selected expressions in breadth-first order.
 * @see SymPy `sympy.core.traversal.iterargs`
 * @example
 * ```ts
 * import { ex, iterArgs } from '@symjs/symjs';
 *
 * [...iterArgs(ex`x + 1`)]; // => [x + 1, 1, x]
 * ```
 */
export function* iterArgs(e: Expr): Generator<Expr, void, undefined> {
  const queue = [e];
  for (const node of queue) {
    yield node;
    queue.push(...traversalArgs(node));
  }
}

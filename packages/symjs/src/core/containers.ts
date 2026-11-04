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
import { ExtensionExpr } from './nodes';
import { sympify } from './ops';
import { callableClass } from './callable';
import { at, cast } from './guard';
import { ordered } from './match';
import { compareKeys, sortKey } from '../printing/sortkey';

/** SymPy Tuple(*args): an immutable sequence of expressions. */
export class TupleNode extends ExtensionExpr {
  constructor(args: readonly Expr[]) {
    super('Tuple', args);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new TupleNode(args);
  }
  /** The number of elements (SymPy len(Tuple)). */
  get length(): number {
    return this.args.length;
  }
  /** The element at index i (negative indices count from the end). */
  at(i: number): Expr {
    return at(this.args, i < 0 ? this.args.length + i : i);
  }
  /** The elements as an array. */
  toArray(): Expr[] {
    return [...this.args];
  }
  [Symbol.iterator](): Iterator<Expr> {
    return this.args[Symbol.iterator]();
  }
  /** SymPy Tuple.count(value): the number of elements equal to value. */
  count(value: ExprLike): number {
    const k = sympify(value).key;
    return this.args.filter((a) => a.key === k).length;
  }
  /** SymPy Tuple.index(value): the first position of value (RangeError when absent). */
  index(value: ExprLike): number {
    const k = sympify(value).key;
    const i = this.args.findIndex((a) => a.key === k);
    if (i < 0) throw new RangeError(`${String(value)} is not in the Tuple`);
    return i;
  }
  /** SymPy Tuple + Tuple: the concatenation. */
  concat(other: TupleNode | readonly ExprLike[]): TupleNode {
    return new TupleNode([...this.args, ...(other instanceof TupleNode ? other.args : other.map(sympify))]);
  }
  /** SymPy StrPrinter._print_tuple: (a, b), (a,) and (). */
  override printStr(print: (e: Expr) => string): string {
    return this.args.length === 1 ? `(${print(at(this.args, 0))},)` : `(${this.args.map(print).join(', ')})`;
  }
  /** SymPy LatexPrinter._print_tuple. */
  override printLatex(print: (e: Expr) => string): string {
    return this.args.length === 1 ? `\\left( ${print(at(this.args, 0))},\\right)` : `\\left( ${this.args.map(print).join(', \\  ')}\\right)`;
  }
}

/** SymPy Tuple(a, b, ...). */
export const Tuple = /* @__PURE__ */ callableClass(TupleNode, (...xs: ExprLike[]): TupleNode => new TupleNode(xs.map(sympify)));
export type Tuple = TupleNode;

type DictInput = ReadonlyMap<ExprLike, ExprLike> | readonly (readonly [ExprLike, ExprLike])[];
const isMapInput = (x: DictInput): x is ReadonlyMap<ExprLike, ExprLike> => !Array.isArray(x);

/** SymPy Dict: an immutable mapping of expressions; its arguments are the (key, value) Tuples in canonical order. */
export class DictNode extends ExtensionExpr {
  private readonly map: ReadonlyMap<string, readonly [Expr, Expr]>;
  constructor(items: readonly TupleNode[]) {
    super('Dict', ordered(items));
    this.map = new Map(this.args.map((t) => [at(t.args, 0).key, [at(t.args, 0), at(t.args, 1)] as const]));
  }
  withArgs(args: readonly Expr[]): Expr {
    return new DictNode(args.map((t) => cast(t, TupleNode, 'Dict item')));
  }
  /** The number of entries. */
  get size(): number {
    return this.map.size;
  }
  /** The value of key, or `fallback` (SymPy Dict.get; undefined is never returned without a fallback: RangeError). */
  get(key: ExprLike, fallback?: Expr): Expr {
    const v = this.map.get(sympify(key).key);
    if (v) return v[1];
    if (fallback) return fallback;
    throw new RangeError(`${String(key)} is not a key of the Dict`);
  }
  /** SymPy `key in Dict`. */
  containsKey(key: ExprLike): boolean {
    return this.map.has(sympify(key).key);
  }
  /** SymPy Dict.keys(). */
  keys(): Expr[] {
    return [...this.map.values()].map(([k]) => k);
  }
  /** SymPy Dict.values(). */
  values(): Expr[] {
    return [...this.map.values()].map(([, v]) => v);
  }
  /** SymPy Dict.items(). */
  items(): (readonly [Expr, Expr])[] {
    return [...this.map.values()];
  }
  /** The entries as a Map keyed by expression. */
  toMap(): Map<Expr, Expr> {
    return new Map(this.items());
  }
  /** The (key, value) Tuples with the keys in default_sort_key order (the printers' order). */
  private sortedItems(): Expr[] {
    return [...this.args].sort((a, b) => compareKeys(sortKey(at(a.args, 0)), sortKey(at(b.args, 0))));
  }
  /** SymPy StrPrinter._print_Dict: {k: v, ...} with the keys in default_sort_key order. */
  override printStr(print: (e: Expr) => string): string {
    return `{${this.sortedItems().map((t) => `${print(at(t.args, 0))}: ${print(at(t.args, 1))}`).join(', ')}}`;
  }
  /** SymPy LatexPrinter._print_dict. */
  override printLatex(print: (e: Expr) => string): string {
    return `\\left\\{ ${this.sortedItems().map((t) => `${print(at(t.args, 0))} : ${print(at(t.args, 1))}`).join(', \\  ')}\\right\\}`;
  }
}

/** SymPy Dict({k: v}) or Dict((k1, v1), (k2, v2), ...). */
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

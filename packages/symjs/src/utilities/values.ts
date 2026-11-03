// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Python value semantics for the iterable utilities: equality and
 * hashing (`==` and `hash`), ordering (`<`), `default_sort_key` and
 * `ordered` for arbitrary values (numbers, strings, arrays, sets, maps and
 * expressions).
 *
 * Expressions compare structurally (by their key), arrays element by
 * element, sets and maps by content; other objects by identity.
 */

import { at, expectType, getOrThrow } from '../core/guard';
import { ordered } from '../core/match';
import { Derivative, Expr, Float, S, isNum } from '../core/nodes';
import { sympify } from '../core/ops';
import type { Key } from '../printing/sortkey';
import { compareKeys, sortKey } from '../printing/sortkey';

const objectIds = new WeakMap<object, number>();
let nextObjectId = 0;

/**
 * A string that is equal for two values exactly when they are equal in the
 * Python sense used by SymPy (the analogue of `hash` plus `==`).
 */
export function valueKey(x: unknown): string {
  switch (typeof x) {
    case 'string':
      return `s${x}`;
    case 'number':
      return Object.is(x, -0) ? 'n0' : `n${x}`;
    case 'bigint':
      return `n${x}`;
    case 'boolean':
      return x ? 'b1' : 'b0';
    case 'undefined':
      return 'u';
    case 'symbol':
      return `y${String(x.description)}`;
    case 'function':
    case 'object': {
      if (x === null) return 'N';
      if (x instanceof Expr) return `e${x.key}`;
      if (Array.isArray(x)) return `[${JSON.stringify(x.map(valueKey))}`;
      if (x instanceof Set) return `{${JSON.stringify([...x].map(valueKey).sort())}`;
      if (x instanceof Map) {
        return `m${JSON.stringify([...x].map(([k, v]) => `${valueKey(k)}:${valueKey(v)}`).sort())}`;
      }
      let id = objectIds.get(x);
      if (id === undefined) {
        id = nextObjectId++;
        objectIds.set(x, id);
      }
      return `o${id}`;
    }
  }
}

/** Python `a == b` for the values handled by {@link valueKey}. */
export function valueEquals(a: unknown, b: unknown): boolean {
  if (a === b) return true;
  return valueKey(a) === valueKey(b);
}

const isNumeric = (x: unknown): x is number | bigint | boolean =>
  typeof x === 'number' || typeof x === 'bigint' || typeof x === 'boolean';

/**
 * Python `a < b` as a three-way comparison: numbers (and booleans) by value,
 * strings lexicographically, arrays element by element, numeric expressions
 * by value and other expressions by their sort key. Throws a TypeError for
 * values that Python cannot order.
 */
export function compareValues(a: unknown, b: unknown): number {
  if (isNumeric(a) && isNumeric(b)) {
    const x = typeof a === 'boolean' ? Number(a) : a;
    const y = typeof b === 'boolean' ? Number(b) : b;
    return x < y ? -1 : x > y ? 1 : 0;
  }
  if (typeof a === 'string' && typeof b === 'string') return a < b ? -1 : a > b ? 1 : 0;
  if (Array.isArray(a) && Array.isArray(b)) {
    const n = Math.min(a.length, b.length);
    for (let i = 0; i < n; i++) {
      if (!valueEquals(a[i], b[i])) return compareValues(a[i], b[i]);
    }
    return a.length - b.length;
  }
  if (a instanceof Expr && b instanceof Expr) {
    if (isNum(a) && isNum(b)) return a.value < b.value ? -1 : a.value > b.value ? 1 : 0;
    return compareKeys(sortKey(a), sortKey(b));
  }
  if (a instanceof Expr && isNumeric(b)) return compareValues(a, sympify(typeof b === 'boolean' ? Number(b) : b));
  if (b instanceof Expr && isNumeric(a)) return compareValues(sympify(typeof a === 'boolean' ? Number(a) : a), b);
  throw new TypeError(`'<' not supported between ${typeName(a)} and ${typeName(b)}`);
}

function typeName(x: unknown): string {
  if (x === null) return 'null';
  if (Array.isArray(x)) return 'list';
  if (typeof x === 'object') return (x as { constructor?: { name?: string } }).constructor?.name ?? 'object';
  return typeof x;
}

/**
 * A `Map` whose keys compare by value ({@link valueKey}): `m.get([1, 2])`
 * finds an entry stored under another array `[1, 2]`, and expressions are
 * found by structure. Used for the results that are dicts in SymPy.
 */
export class ValueMap<K, V> extends Map<K, V> {
  #byKey = new Map<string, K>();

  constructor(entries?: Iterable<readonly [K, V]> | null) {
    super();
    if (entries) for (const [k, v] of entries) this.set(k, v);
  }

  override get(k: K): V | undefined {
    const c = this.#byKey.get(valueKey(k));
    return c === undefined ? undefined : super.get(c);
  }

  override has(k: K): boolean {
    return this.#byKey.has(valueKey(k));
  }

  override set(k: K, v: V): this {
    const vk = valueKey(k);
    if (this.#byKey.has(vk)) return super.set(getOrThrow(this.#byKey, vk), v);
    this.#byKey.set(vk, k);
    return super.set(k, v);
  }

  override delete(k: K): boolean {
    const vk = valueKey(k);
    if (!this.#byKey.has(vk)) return false;
    const c = getOrThrow(this.#byKey, vk);
    this.#byKey.delete(vk);
    return super.delete(c);
  }

  override clear(): void {
    this.#byKey.clear();
    super.clear();
  }
}

const ONE_KEY: Key = sortKey(S.One);

/** Whether x is a sort key (shallow: the elements of an array key are not inspected). */
const isKey = (x: unknown): x is Key => typeof x === 'number' || typeof x === 'string' || Array.isArray(x);

const isIterableObject = (x: unknown): x is Iterable<unknown> =>
  typeof x === 'object' && x !== null && typeof (x as { [Symbol.iterator]?: unknown })[Symbol.iterator] === 'function';

/**
 * SymPy `default_sort_key` for any value: expressions use their sort key,
 * numbers are sympified, strings and other atoms are keyed by their text,
 * arrays (Python lists), sets and maps by the keys of their elements.
 */
export function defaultSortKeyOf(item: unknown): Key {
  if (item instanceof Expr) return sortKey(item);
  if (typeof item === 'number' || typeof item === 'bigint') return sortKey(sympify(item));
  if (typeof item !== 'string' && isIterableObject(item)) {
    let args: Key[];
    let name: string;
    if (item instanceof Map) {
      name = 'dict';
      args = [...item].map(([k, v]) => [[10, 0, 'tuple'], [2, [defaultSortKeyOf(k), defaultSortKeyOf(v)]], ONE_KEY, 1] as Key);
      args.sort(compareKeys);
    } else if (item instanceof Set) {
      name = 'set';
      args = [...item].map(defaultSortKeyOf).sort(compareKeys);
    } else {
      name = Array.isArray(item) ? 'list' : typeName(item);
      args = [...item].map(defaultSortKeyOf);
    }
    return [[10, 0, name], [args.length, args], ONE_KEY, 1];
  }
  const name = typeof item === 'string' ? 'str' : typeof item === 'boolean' ? 'bool' : typeName(item);
  return [[0, 0, name], [1, [String(item)]], ONE_KEY, 1];
}

/** SymPy `_node_count`. */
function nodeCount(e: Expr): number {
  if (e instanceof Float) return 0.5;
  let n = 1;
  for (const a of e.args) n += nodeCount(a);
  return n;
}

/** SymPy `_nodes`: the size of a value, the first key of `ordered`. */
export function nodesOf(e: unknown): number {
  if (e instanceof Derivative) {
    let n = nodesOf(e.args[0]);
    for (let i = 1; i < e.args.length; i += 2) {
      const c = at(e.args, i + 1);
      n += isNum(c) ? c.value : nodesOf(c);
    }
    return n;
  }
  if (e instanceof Expr) return nodeCount(e);
  if (e instanceof Map) {
    let n = 1;
    for (const [k, v] of e) n += nodesOf(k) + nodesOf(v);
    return n;
  }
  if (typeof e !== 'string' && isIterableObject(e)) {
    let n = 1;
    for (const x of e) n += nodesOf(x);
    return n;
  }
  return 1;
}

/** A sort key function for {@link orderedValues}. */
export type KeyFunction<T> = (x: T) => unknown;

/**
 * SymPy `ordered(seq, keys, default)` for any values: sort by the keys in
 * turn, breaking remaining ties with `_nodes` and `default_sort_key` when
 * `defaultKeys` is true; values that tie on every key keep their order.
 */
export function orderedValues<T>(seq: Iterable<T>, keys?: KeyFunction<T> | readonly KeyFunction<T>[] | null, defaultKeys = true): T[] {
  const items = [...seq];
  const ks = keys === undefined || keys === null ? [] : typeof keys === 'function' ? [keys] : [...keys];
  const [f, ...rest] = ks;
  if (f === undefined) {
    if (!defaultKeys) throw new RangeError('if default=False then keys must be provided');
    const exprs = items.filter((x): x is T & Expr => x instanceof Expr);
    if (exprs.length === items.length && exprs.every((x) => !(x instanceof Derivative))) {
      // ordered() sorts the same objects; map them back to the element type
      const back = new Map<Expr, T>(exprs.map((x) => [x, x]));
      return ordered(exprs).map((e) => getOrThrow(back, e));
    }
    return orderedBy(items, [nodesOf, defaultSortKeyOf], false, true);
  }
  return orderedBy(items, [f, ...rest], defaultKeys, false);
}

function orderedBy<T>(items: T[], keys: readonly [KeyFunction<T>, ...KeyFunction<T>[]], defaultKeys: boolean, sortKeys: boolean): T[] {
  if (items.length < 2) return items;
  const [f, ...rest] = keys;
  const groups = new ValueMap<unknown, T[]>();
  for (const a of items) {
    const k = f(a);
    const g = groups.get(k);
    if (g) g.push(a);
    else groups.set(k, [a]);
  }
  const cmp = sortKeys ? (a: unknown, b: unknown) => compareKeys(expectType(a, isKey, 'sort key'), expectType(b, isKey, 'sort key')) : compareValues;
  const sorted = [...groups].sort((a, b) => cmp(a[0], b[0]));
  const out: T[] = [];
  for (const [, g] of sorted) {
    const [f2, ...rest2] = rest;
    if (g.length > 1) out.push(...(f2 !== undefined ? orderedBy(g, [f2, ...rest2], defaultKeys, sortKeys) : defaultKeys ? orderedBy(g, [nodesOf, defaultSortKeyOf], false, true) : g));
    else out.push(...g);
  }
  return out;
}

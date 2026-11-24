// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file A `Map` keyed by expressions with structural equality, used for the
 * results that are dicts in SymPy (`roots`, `as_coefficients_dict`, `match`).
 */

import { Expr, impl, type ExprLike } from './nodes';

/**
 * `Map<Expr, V>` whose keys compare structurally: `m.get(parse('x + 1'))`
 * finds an entry stored under another instance of `x + 1`. Keys given as
 * numbers or strings are sympified.
 */
export class ExprMap<V> extends Map<Expr, V> {
  #byKey = new Map<string, Expr>();

  /**
   * Creates an `ExprMap`.
   *
   * @param entries - The initial key-value pairs.
   */
  constructor(entries?: Iterable<readonly [ExprLike, V]> | null) {
    super();
    if (entries) for (const [k, v] of entries) this.set(k, v);
  }

  #canonical(k: ExprLike): Expr | undefined {
    const e = k instanceof Expr ? k : impl.sympify(k);
    return this.#byKey.get(e.key);
  }

  /**
   * Looks up the value of a structurally equal expression key.
   *
   * @param k - The expression key, compared structurally.
   * @returns The mapped value, or `undefined` for a missing key.
   */
  override get(k: ExprLike): V | undefined {
    const c = this.#canonical(k);
    return c === undefined ? undefined : super.get(c);
  }

  /**
   * Tests whether the map contains a structurally equal key.
   *
   * @param k - The expression key, compared structurally.
   * @returns True if the map contains a structurally equal key, otherwise false.
   */
  override has(k: ExprLike): boolean {
    return this.#canonical(k) !== undefined;
  }

  /**
   * Associates a value with an expression key.
   *
   * @param k - The expression key, compared structurally.
   * @param v - The value associated with the key.
   * @returns This map.
   */
  override set(k: ExprLike, v: V): this {
    const e = k instanceof Expr ? k : impl.sympify(k);
    const c = this.#byKey.get(e.key);
    if (c !== undefined) return super.set(c, v);
    this.#byKey.set(e.key, e);
    return super.set(e, v);
  }

  /**
   * Removes the entry with the given expression key.
   *
   * @param k - The expression key, compared structurally.
   * @returns Whether a matching entry was removed.
   */
  override delete(k: ExprLike): boolean {
    const c = this.#canonical(k);
    if (c === undefined) return false;
    this.#byKey.delete(c.key);
    return super.delete(c);
  }

  /** Removes all entries. */
  override clear(): void {
    this.#byKey.clear();
    super.clear();
  }
}

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

  constructor(entries?: Iterable<readonly [ExprLike, V]> | null) {
    super();
    if (entries) for (const [k, v] of entries) this.set(k as Expr, v);
  }

  #canonical(k: ExprLike): Expr | undefined {
    const e = k instanceof Expr ? k : impl.sympify(k);
    return this.#byKey.get(e.key);
  }

  override get(k: ExprLike): V | undefined {
    const c = this.#canonical(k);
    return c === undefined ? undefined : super.get(c);
  }

  override has(k: ExprLike): boolean {
    return this.#canonical(k) !== undefined;
  }

  override set(k: ExprLike, v: V): this {
    const e = k instanceof Expr ? k : impl.sympify(k);
    const c = this.#byKey.get(e.key);
    if (c !== undefined) return super.set(c, v);
    this.#byKey.set(e.key, e);
    return super.set(e, v);
  }

  override delete(k: ExprLike): boolean {
    const c = this.#canonical(k);
    if (c === undefined) return false;
    this.#byKey.delete(c.key);
    return super.delete(c);
  }

  override clear(): void {
    this.#byKey.clear();
    super.clear();
  }
}

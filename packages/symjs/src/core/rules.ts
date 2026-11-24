// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14, core/rules.py, BSD-3-Clause; see LICENSE.

/**
 * @file Replacement rules (SymPy `sympy.core.rules`): `Transform`, an immutable mapping computed by a
 * function, usable as a generic transformation rule (for example by `xreplace`-like traversals).
 */

import { NoMatch, type NoMatchResult } from './truth';

/**
 * An immutable mapping whose value at a key is computed by `transform` (SymPy Transform). When a
 * `filter` is given, only the keys it accepts are in the mapping. SymPy's `key in t` is `t.has(key)`
 * and `t[key]` is `t.at(key)`.
 *
 * @see SymPy `sympy.core.rules.Transform`
 * @example
 * ```ts
 * import { Transform } from '@symjs/symjs';
 *
 * new Transform((x: number) => x * x).at(3); // => 9
 * ```
 */
export class Transform<K, V> {
  /**
   * Creates a `Transform`.
   *
   * @param transform - Converts a LaTeX grammar tree into an expression or ambiguity tree.
   * @param filter - The predicate selecting keys in the mapping.
   */
  constructor(
    private readonly transform: (key: K) => V,
    private readonly filter: (key: K) => boolean = () => true,
  ) {}

  /**
   * Tests whether the filter accepts the key.
   *
   * @param key - The lookup key.
   * @returns True if the key passes the filter.
   */
  has(key: K): boolean {
    return this.filter(key);
  }

  /**
   * Applies the transformation to an accepted key.
   *
   * @param key - The lookup key.
   * @returns The value computed for the key.
   * @throws RangeError when the filter rejects the key.
   */
  at(key: K): V {
    if (!this.filter(key)) throw new RangeError(`key not in the mapping: ${String(key)}`);
    return this.transform(key);
  }

  /**
   * Transforms the key when it satisfies the filter and uses the optional default otherwise.
   *
   * @param key - The lookup key.
   * @param defaultValue - The value to return for a missing key.
   * @returns The transformed value, the supplied default, or `NoMatch`.
   * @see SymPy `sympy.core.rules.Transform.get`
   */
  get(key: K): V | NoMatchResult;
  get<D>(key: K, defaultValue: D): V | D;
  get<D>(key: K, ...rest: [] | [D]): V | D | NoMatchResult {
    if (this.has(key)) return this.transform(key);
    return rest.length === 0 ? NoMatch : rest[0];
  }
}

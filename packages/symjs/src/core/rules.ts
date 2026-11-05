// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14, core/rules.py, BSD-3-Clause; see LICENSE.

/**
 * @file Replacement rules (SymPy `sympy.core.rules`): `Transform`, an immutable mapping computed by a
 * function, usable as a generic transformation rule (for example by `xreplace`-like traversals).
 */

/**
 * An immutable mapping whose value at a key is computed by `transform` (SymPy Transform). When a
 * `filter` is given, only the keys it accepts are in the mapping. SymPy's `key in t` is `t.has(key)`
 * and `t[key]` is `t.at(key)`.
 */
export class Transform<K, V> {
  constructor(
    private readonly transform: (key: K) => V,
    private readonly filter: (key: K) => boolean = () => true,
  ) {}

  /** SymPy `key in t`: whether the filter accepts the key. */
  has(key: K): boolean {
    return this.filter(key);
  }

  /** SymPy `t[key]`: the transformed key; a key outside the mapping is a RangeError (SymPy KeyError). */
  at(key: K): V {
    if (!this.filter(key)) throw new RangeError(`key not in the mapping: ${String(key)}`);
    return this.transform(key);
  }

  /** SymPy `t.get(key, default)`: the transformed key, or the default for a key outside the mapping. */
  get<D>(key: K, defaultValue: D): V | D {
    return this.has(key) ? this.transform(key) : defaultValue;
  }
}

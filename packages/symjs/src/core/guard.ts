// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Checked access for values the algorithms guarantee to exist, used
 * instead of non-null (`x!`) and unchecked type assertions (`x as T`): a
 * violated guarantee throws InvariantError instead of continuing with
 * undefined or a value of the wrong class.
 */

import { InvariantError } from './errors';

/** The element at index i (negative counts from the end); throws when out of range. */
export function at<T>(xs: ArrayLike<T>, i: number): T {
  const k = i < 0 ? xs.length + i : i;
  if (k < 0 || k >= xs.length) throw new InvariantError(`index ${i} out of range (length ${xs.length})`);
  // oxlint-disable-next-line typescript/no-unsafe-type-assertion -- k is in range, so the element is a T (T itself may include undefined)
  return xs[k] as T;
}

/** The first element; throws for an empty sequence. */
export const first = <T>(xs: ArrayLike<T>): T => at(xs, 0);

/** The last element; throws for an empty sequence. */
export const last = <T>(xs: ArrayLike<T>): T => at(xs, -1);

/** v itself; throws when it is undefined or null (what names the value in the message). */
export function defined<T>(v: T | undefined | null, what = 'value'): T {
  if (v === undefined || v === null) throw new InvariantError(`${what} is missing`);
  return v;
}

/** The entry for key; throws when the map has none. */
export function getOrThrow<K, V>(m: ReadonlyMap<K, V>, key: K): V {
  const v = m.get(key);
  if (v === undefined && !m.has(key)) throw new InvariantError('missing map entry');
  // oxlint-disable-next-line typescript/no-unsafe-type-assertion -- the key is present, so the entry is a V (V itself may include undefined)
  return v as V;
}

/** v as an instance of cls; throws when it is not one. */
export function cast<T>(v: unknown, cls: abstract new (...args: never[]) => T, what?: string): T {
  if (!(v instanceof cls)) throw new InvariantError(`${what ?? 'value'} is not a ${cls.name}`);
  return v;
}

/** Narrows with a type guard; throws when the guard fails. */
export function expectType<T>(v: unknown, guard: (x: unknown) => x is T, what = 'value'): T {
  if (!guard(v)) throw new InvariantError(`${what} has an unexpected type`);
  return v;
}

/** The first two elements as a pair; throws when there are fewer. */
export function pair<T>(xs: ArrayLike<T>): [T, T] {
  return [at(xs, 0), at(xs, 1)];
}

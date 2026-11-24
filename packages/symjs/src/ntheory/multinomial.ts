// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Binomial and multinomial coefficients (SymPy
 * sympy.ntheory.multinomial). Dicts keyed by tuples are Maps keyed by
 * arrays of bigints (in SymPy's insertion order).
 */

import { at, getOrThrow } from '../core/guard';
import type { IntLike } from './intutil';
import { asInt } from './intutil';

/**
 * The coefficients of (x + y)**n as a Map [k1, k2] -> coefficient.
 *
 * @remarks SymPy uses tuple keys such as `(1, 8)` for the coefficient 9.
 * @param nIn - Nonnegative power of the binomial.
 * @returns The coefficients indexed by exponent pairs.
 * @see SymPy `sympy.ntheory.multinomial.binomial_coefficients`
 * @example
 * ```ts
 * import { binomialCoefficients } from '@symjs/symjs';
 *
 * binomialCoefficients(9); // => {[0, 9]: 1, [9, 0]: 1, [1, 8]: 9, [8, 1]: 9, [2, 7]: 36, [7, 2]: 36, [3, 6]: 84, [6, 3]: 84, [4, 5]: 126, [5, 4]: 126}
 * ```
 */
export function binomialCoefficients(nIn: IntLike): Map<readonly bigint[], bigint> {
  const n = asInt(nIn);
  const d = new Map<string, [readonly bigint[], bigint]>();
  const put = (k: readonly bigint[], v: bigint): void => {
    d.set(k.join(','), [k, v]);
  };
  put([0n, n], 1n);
  put([n, 0n], 1n);
  let a = 1n;
  for (let k = 1n; k <= n / 2n; k++) {
    a = (a * (n - k + 1n)) / k;
    put([k, n - k], a);
    put([n - k, k], a);
  }
  return new Map([...d.values()]);
}

/**
 * The coefficients of (x + y)**n as a list.
 *
 * @param nIn - Nonnegative power of the binomial.
 * @returns The coefficients in increasing order of the exponent index.
 * @see SymPy `sympy.ntheory.multinomial.binomial_coefficients_list`
 * @example
 * ```ts
 * import { binomialCoefficientsList } from '@symjs/symjs';
 *
 * binomialCoefficientsList(9); // => [1, 9, 36, 84, 126, 126, 84, 36, 9, 1]
 * ```
 */
export function binomialCoefficientsList(nIn: IntLike): bigint[] {
  const n = asInt(nIn);
  const d = new Array<bigint>(Number(n) + 1).fill(1n);
  let a = 1n;
  for (let k = 1n; k <= n / 2n; k++) {
    a = (a * (n - k + 1n)) / k;
    d[Number(k)] = a;
    d[Number(n - k)] = a;
  }
  return d;
}

function mcInternal(m: number, n: number): Map<string, [number[], bigint]> {
  const r = new Map<string, [number[], bigint]>();
  const t = [n, ...new Array<number>(m - 1).fill(0)];
  const key = (x: number[]) => x.join(',');
  const get = (x: number[]) => getOrThrow(r, key(x))[1];
  r.set(key(t), [[...t], 1n]);
  let j = n ? 0 : m;
  while (j < m - 1) {
    const tj = at(t, j);
    if (j) {
      t[j] = 0;
      t[0] = tj;
    }
    let start: number;
    let v: bigint;
    if (tj > 1) {
      t[j + 1] = at(t, j + 1) + 1;
      j = 0;
      start = 1;
      v = 0n;
    } else {
      j++;
      start = j + 1;
      v = get(t);
      t[j] = at(t, j) + 1;
    }
    for (let k = start; k < m; k++) {
      if (t[k]) {
        t[k] = at(t, k) - 1;
        v += get(t);
        t[k] = at(t, k) + 1;
      }
    }
    t[0] = at(t, 0) - 1;
    r.set(key(t), [[...t], (v * BigInt(tj)) / BigInt(n - at(t, 0))]);
  }
  return r;
}

/**
 * The coefficients of (x1 +... + xm)**n as a Map of exponent tuples to coefficients.
 *
 * @remarks SymPy uses tuple keys such as `(1, 4)` for the coefficient 5.
 * @param mIn - Number of terms in the sum.
 * @param nIn - Nonnegative exponent of the sum.
 * @returns The exponent vectors and their multinomial coefficients.
 * @see SymPy `sympy.ntheory.multinomial.multinomial_coefficients`
 * @example
 * ```ts
 * import { multinomialCoefficients } from '@symjs/symjs';
 *
 * multinomialCoefficients(2, 5); // => {[0, 5]: 1, [5, 0]: 1, [1, 4]: 5, [4, 1]: 5, [2, 3]: 10, [3, 2]: 10}
 * ```
 */
export function multinomialCoefficients(mIn: IntLike, nIn: IntLike): Map<readonly bigint[], bigint> {
  const m = Number(asInt(mIn));
  const n = Number(asInt(nIn));
  if (!m) return n ? new Map() : new Map([[[], 1n]]);
  if (m === 2) return binomialCoefficients(n);
  if (m >= 2 * n && n > 1) return new Map(multinomialCoefficientsIterator(m, n));
  return new Map([...mcInternal(m, n).values()].map(([k, v]) => [k.map(BigInt), v]));
}

/**
 * The multinomial coefficients as a generator of [tuple, coefficient].
 *
 * @remarks SymPy yields a pair whose first entry is an exponent tuple and whose second entry is the
 *   coefficient.
 * @param mIn - Number of terms in the sum.
 * @param nIn - Nonnegative exponent of the sum.
 * @returns The exponent vectors and their multinomial coefficients.
 * @see SymPy `sympy.ntheory.multinomial.multinomial_coefficients_iterator`
 * @example
 * ```ts
 * import { multinomialCoefficientsIterator } from '@symjs/symjs';
 *
 * multinomialCoefficientsIterator(20, 3).next().value; // => [[3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 1]
 * ```
 */
export function* multinomialCoefficientsIterator(mIn: IntLike, nIn: IntLike): Generator<[readonly bigint[], bigint], void, undefined> {
  const m = Number(asInt(mIn));
  const n = Number(asInt(nIn));
  if (m < 2 * n || n === 1) {
    yield* multinomialCoefficients(m, n);
    return;
  }
  const mc = new Map<string, bigint>();
  // multinomial_coefficients(n, n) as in SymPy (mcInternal needs n >= 1: n = 0 gives {(): 1})
  for (const [k, v] of multinomialCoefficients(n, n)) mc.set(k.filter((x) => x).join(','), v);
  const t = [n, ...new Array<number>(m - 1).fill(0)];
  const b = (x: number[]) => getOrThrow(mc, x.filter((y) => y).join(','));
  yield [t.map(BigInt), b(t)];
  let j = n ? 0 : m;
  while (j < m - 1) {
    const tj = at(t, j);
    if (j) {
      t[j] = 0;
      t[0] = tj;
    }
    if (tj > 1) {
      t[j + 1] = at(t, j + 1) + 1;
      j = 0;
    } else {
      j++;
      t[j] = at(t, j) + 1;
    }
    t[0] = at(t, 0) - 1;
    yield [t.map(BigInt), b(t)];
  }
}

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Integer helpers of the exact values of cos(pi/n) for products of
 * Fermat primes (SymPy sympy.functions.elementary._trigonometric_special):
 * the extended gcd of several integers, integer partial fractions and the
 * Fermat prime factors of n.
 */

import { igcdex } from '../../core/numberutils';
import type { NoMatchResult } from '../../core/truth';
import { NoMatch } from '../../core/truth';
import type { IntLike } from '../../ntheory/intutil';
import { asInt } from '../../ntheory/intutil';

/**
 * SymPy migcdex: [u, g] with u_1*x_1 + ... + u_n*x_n = g = gcd(x_1, ..., x_n),
 * the extended Euclidean algorithm for several integers.
 */
export function migcdex(...xIn: IntLike[]): [bigint[], bigint] {
  const x = xIn.map((v) => asInt(v));
  const [x0, x1] = x;
  if (x0 === undefined) return [[], 0n];
  if (x1 === undefined) return [[1n], x0];
  if (x.length === 2) {
    const [u, v, h] = igcdex(x0, x1);
    return [[u, v], h];
  }
  const [y, g] = migcdex(...x.slice(1));
  const [u, v, h] = igcdex(x0, g);
  return [[u, ...y.map((i) => v * i)], h];
}

/**
 * SymPy ipartfrac: integers a_i with sum(a_i/d_i) = 1/(d_1*...*d_n) for
 * pairwise coprime denominators d_i.
 */
export function ipartfrac(...denomsIn: IntLike[]): bigint[] {
  if (!denomsIn.length) return [];
  const denoms = denomsIn.map((v) => asInt(v));
  const d = denoms.reduce((a, b) => a * b, 1n);
  return migcdex(...denoms.map((x) => d / x))[0];
}

/** SymPy fermat_coords: the distinct Fermat primes whose product is n, or NoMatch (SymPy None). */
export function fermatCoords(nIn: IntLike): number[] | NoMatchResult {
  let n = asInt(nIn);
  const primes: number[] = [];
  for (const p of [3n, 5n, 17n, 257n, 65537n]) {
    if (n % p === 0n) {
      n /= p;
      primes.push(Number(p));
      if (n === 1n) return primes;
    }
  }
  return NoMatch;
}

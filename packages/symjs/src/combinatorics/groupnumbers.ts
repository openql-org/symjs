// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Numbers n for which every group of order n has a property (SymPy
 * sympy.combinatorics.group_numbers): nilpotent, abelian and cyclic
 * numbers, and the number of groups of order n.
 */

import { gcd } from '../core/numbers';
import type { IntLike } from '../ntheory/intutil';
import { asInt } from '../ntheory/intutil';
import { factorint } from '../ntheory/factor';
import { at } from '../core/guard';

function positiveFactors(nIn: IntLike): Map<bigint, bigint> {
  const n = asInt(nIn);
  if (n <= 0n) throw new RangeError(`n must be a positive integer, not ${n}`);
  return factorint(n);
}

/** For no primes p, q of n is q**k = 1 (mod p) with 1 <= k <= the exponent of q. */
function nilpotentFactors(factors: ReadonlyMap<bigint, bigint>): boolean {
  for (const p of factors.keys()) {
    for (const [q, e] of factors) {
      let m = 1n;
      for (let i = 0n; i < e; i++) {
        m = (m * q) % p;
        if (m === 1n) return false;
      }
    }
  }
  return true;
}

/** SymPy is_nilpotent_number: every group of order n is nilpotent. */
export function isNilpotentNumber(n: IntLike): boolean {
  return nilpotentFactors(positiveFactors(n));
}

/** SymPy is_abelian_number: every group of order n is abelian. */
export function isAbelianNumber(n: IntLike): boolean {
  const f = positiveFactors(n);
  return [...f.values()].every((e) => e < 3n) && nilpotentFactors(f);
}

/** SymPy is_cyclic_number: every group of order n is cyclic. */
export function isCyclicNumber(n: IntLike): boolean {
  const f = positiveFactors(n);
  return [...f.values()].every((e) => e === 1n) && nilpotentFactors(f);
}

/** Hölder's formula: the number of groups of a squarefree order with the given prime factors. */
function holderFormula(primes: readonly bigint[]): bigint {
  const F = primes.filter((p) => primes.every((q) => q % p !== 1n));
  const M = primes.filter((p) => !F.includes(p));
  let s = 0n;
  for (let mask = 0; mask < 1 << M.length; mask++) {
    const ps = M.filter((_p, i) => (mask >> i) & 1);
    const rest = M.filter((_p, i) => !((mask >> i) & 1));
    let prod = 1n;
    for (const p of rest) {
      const c = [...F, ...ps].filter((q) => q % p === 1n).length;
      prod *= (p ** BigInt(c) - 1n) / (p - 1n);
      if (prod === 0n) break;
    }
    s += prod;
  }
  return s;
}

// the numbers of groups of order 2**e and 3**e (OEIS A000679, A090091)
const A000679 = [1n, 1n, 2n, 5n, 14n, 51n, 267n, 2328n, 56092n, 10494213n, 49487367289n];
const A090091 = [1n, 1n, 2n, 5n, 15n, 67n, 504n, 9310n, 1396077n, 5937876645n];
// known values for small orders that are neither prime powers nor squarefree (OEIS A000001)
const SMALL: Readonly<Record<string, bigint>> = {
  12: 5n, 18: 5n, 20: 5n, 24: 15n, 28: 4n, 36: 14n, 40: 14n, 44: 4n, 45: 2n, 48: 52n, 50: 5n, 52: 5n, 54: 15n, 56: 13n,
  60: 13n, 63: 4n, 68: 5n, 72: 50n, 75: 3n, 76: 4n, 80: 52n, 84: 15n, 88: 12n, 90: 10n, 92: 4n,
};

/** The number of groups of order p**e, or undefined when it is not known here. */
function primePowerCount(p: bigint, e: bigint): bigint | undefined {
  const table = p === 2n ? A000679 : p === 3n ? A090091 : undefined;
  if (table && e < BigInt(table.length)) return at(table, Number(e));
  if (e <= 2n) return e;
  const g = (k: bigint): bigint => gcd(p - 1n, k);
  switch (e) {
    case 3n:
      return 5n;
    case 4n:
      return 15n;
    case 5n:
      return 61n + 2n * p + 2n * g(3n) + g(4n);
    case 6n:
      return 3n * p ** 2n + 39n * p + 344n + 24n * g(3n) + 11n * g(4n) + 2n * g(5n);
    case 7n:
      if (p === 5n) return 34297n;
      return (
        3n * p ** 5n + 12n * p ** 4n + 44n * p ** 3n + 170n * p ** 2n + 707n * p + 2455n + (4n * p ** 2n + 44n * p + 291n) * g(3n) + (p ** 2n + 19n * p + 135n) * g(4n) + (3n * p + 31n) * g(5n) + 4n * g(7n) + 5n * g(8n) + g(9n)
      );
    default:
      return undefined;
  }
}

/**
 * SymPy groups_count: the number of groups of order n (gnu(n)), for prime
 * powers up to the seventh power, squarefree n and some small orders; a
 * RangeError when the number is unknown or not implemented.
 */
export function groupsCount(nIn: IntLike): bigint {
  const n = asInt(nIn);
  const factors = positiveFactors(n);
  const entries = [...factors];
  if (entries.length === 1) {
    const [p, e] = at(entries, 0);
    const c = primePowerCount(p, e);
    if (c !== undefined) return c;
  }
  if (entries.some(([, k]) => k > 1n)) {
    const v = SMALL[n.toString()];
    if (v !== undefined) return v;
    throw new RangeError('Number of groups of order n is unknown or not implemented');
  }
  // factorint lists the primes in increasing order
  const primes = [...factors.keys()];
  if (primes.length === 2) return at(primes, 1) % at(primes, 0) === 1n ? 2n : 1n;
  return holderFormula(primes);
}

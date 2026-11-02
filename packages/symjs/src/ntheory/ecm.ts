// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Lenstra's elliptic curve factorization (SymPy sympy.ntheory.ecm.ecm),
 * with Montgomery curves and SymPy's seeded curve choice.
 */

import { defined } from '../core/guard';
import { ecmOneFactor, perfectPowerInt } from './factor';
import type { IntLike } from './intutil';
import { asInt } from './intutil';
import { isprime } from './primetest';
import { sieve } from './sieve';

/** Options of ecm. */
export interface EcmOptions {
  /** Stage 1 bound (even, default 10000). */
  B1?: bigint | number;
  /** Stage 2 bound (even, default 100000). */
  B2?: bigint | number;
  /** The maximum number of curves (default 200). */
  maxCurve?: number;
  /** The seed of the curve choice (default 1234). */
  seed?: bigint | number;
}

/**
 * The set of prime factors of n by the elliptic curve method (SymPy ecm).
 * The set is filled in increasing order (Python's set has its own order).
 */
export function ecm(nIn: IntLike, opts: EcmOptions = {}): Set<bigint> {
  let n = asInt(nIn);
  const B1 = BigInt(opts.B1 ?? 10000);
  const B2 = BigInt(opts.B2 ?? 100000);
  const maxCurve = opts.maxCurve ?? 200;
  const seed = opts.seed ?? 1234;
  if (B1 % 2n !== 0n || B2 % 2n !== 0n) throw new RangeError('both bounds must be even');
  const TF_LIMIT = 100000n;
  const factors = new Set<bigint>();
  for (const prime of sieve.primerange(2n, TF_LIMIT)) {
    if (n % prime === 0n) {
      factors.add(prime);
      while (n % prime === 0n) n /= prime;
    }
  }
  const queue: bigint[] = [];
  const check = (m: bigint): void => {
    if (isprime(m)) {
      factors.add(m);
      return;
    }
    const result = perfectPowerInt(m, TF_LIMIT);
    if (result !== false) {
      check(result[0]);
      return;
    }
    queue.push(m);
  };
  check(n);
  while (queue.length > 0) {
    const m = defined(queue.pop(), 'queued factor');
    const factor = ecmOneFactor(m, B1, B2, maxCurve, seed);
    if (factor === undefined) throw new RangeError('Increase the bounds');
    check(factor);
    check(m / factor);
  }
  return new Set([...factors].sort((a, b) => (a < b ? -1 : a > b ? 1 : 0)));
}

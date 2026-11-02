// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Python's random.Random (the Mersenne Twister MT19937 with
 * init_by_array seeding, getrandbits, randrange, randint) and SymPy's
 * shared generator (sympy.core.random: rng, seed, _randint), so that the
 * randomized algorithms of the number theory module give the same results
 * as SymPy for the same seed.
 */

import { bitLength } from './intutil';

const N = 624;
const M = 397;
const MATRIX_A = 0x9908b0df;
const UPPER_MASK = 0x80000000;
const LOWER_MASK = 0x7fffffff;

/** Python's random.Random: the MT19937 generator seeded like CPython. */
export class Random {
  private readonly mt = new Uint32Array(N);
  private mti = N + 1;

  /** Random(seed): an integer seed as in Python; without a seed, one from Math.random. */
  constructor(seed?: bigint | number) {
    this.seed(seed);
  }

  /** Python Random.seed(a) for an integer a (None: a seed from Math.random). */
  seed(a?: bigint | number): void {
    let n: bigint;
    if (a === undefined) n = BigInt(Math.floor(Math.random() * 2 ** 32)) * (1n << 32n) + BigInt(Math.floor(Math.random() * 2 ** 32));
    else n = BigInt(a);
    if (n < 0n) n = -n;
    const key: number[] = [];
    if (n === 0n) key.push(0);
    while (n > 0n) {
      key.push(Number(n & 0xffffffffn));
      n >>= 32n;
    }
    this.initByArray(key);
  }

  private initGenrand(s: number): void {
    const mt = this.mt;
    mt[0] = s >>> 0;
    for (let i = 1; i < N; i++) {
      const prev = mt[i - 1]! ^ (mt[i - 1]! >>> 30);
      // 1812433253 * prev + i, modulo 2**32
      mt[i] = (Math.imul(1812433253, prev) + i) >>> 0;
    }
    this.mti = N;
  }

  private initByArray(key: readonly number[]): void {
    const mt = this.mt;
    this.initGenrand(19650218);
    let i = 1;
    let j = 0;
    const keyLength = key.length;
    for (let k = N > keyLength ? N : keyLength; k > 0; k--) {
      const prev = mt[i - 1]! ^ (mt[i - 1]! >>> 30);
      mt[i] = ((mt[i]! ^ Math.imul(prev, 1664525)) + key[j]! + j) >>> 0;
      i++;
      j++;
      if (i >= N) {
        mt[0] = mt[N - 1]!;
        i = 1;
      }
      if (j >= keyLength) j = 0;
    }
    for (let k = N - 1; k > 0; k--) {
      const prev = mt[i - 1]! ^ (mt[i - 1]! >>> 30);
      mt[i] = ((mt[i]! ^ Math.imul(prev, 1566083941)) - i) >>> 0;
      i++;
      if (i >= N) {
        mt[0] = mt[N - 1]!;
        i = 1;
      }
    }
    mt[0] = 0x80000000;
  }

  /** A uniformly distributed 32-bit unsigned integer (genrand_uint32). */
  genrandUint32(): number {
    const mt = this.mt;
    let y: number;
    if (this.mti >= N) {
      let kk = 0;
      for (; kk < N - M; kk++) {
        y = (mt[kk]! & UPPER_MASK) | (mt[kk + 1]! & LOWER_MASK);
        mt[kk] = mt[kk + M]! ^ (y >>> 1) ^ (y & 1 ? MATRIX_A : 0);
      }
      for (; kk < N - 1; kk++) {
        y = (mt[kk]! & UPPER_MASK) | (mt[kk + 1]! & LOWER_MASK);
        mt[kk] = mt[kk + (M - N)]! ^ (y >>> 1) ^ (y & 1 ? MATRIX_A : 0);
      }
      y = (mt[N - 1]! & UPPER_MASK) | (mt[0]! & LOWER_MASK);
      mt[N - 1] = mt[M - 1]! ^ (y >>> 1) ^ (y & 1 ? MATRIX_A : 0);
      this.mti = 0;
    }
    y = mt[this.mti++]!;
    y ^= y >>> 11;
    y ^= (y << 7) & 0x9d2c5680;
    y ^= (y << 15) & 0xefc60000;
    y ^= y >>> 18;
    return y >>> 0;
  }

  /** Python Random.getrandbits(k): a non-negative integer with k random bits. */
  getrandbits(k: number): bigint {
    if (k < 0) throw new RangeError('number of bits must be non-negative');
    if (k === 0) return 0n;
    if (k <= 32) return BigInt(this.genrandUint32() >>> (32 - k));
    let r = 0n;
    let shift = 0n;
    for (let left = k; left > 0; left -= 32) {
      let w = this.genrandUint32();
      if (left < 32) w >>>= 32 - left;
      r |= BigInt(w) << shift;
      shift += 32n;
    }
    return r;
  }

  /** Python Random._randbelow(n): an integer in [0, n). */
  randbelow(n: bigint): bigint {
    const k = bitLength(n);
    let r = this.getrandbits(k);
    while (r >= n) r = this.getrandbits(k);
    return r;
  }

  /** Python Random.randrange(start, stop) (step 1). */
  randrange(start: bigint, stop: bigint): bigint {
    const width = stop - start;
    if (width <= 0n) throw new RangeError(`empty range in randrange(${start}, ${stop})`);
    return start + this.randbelow(width);
  }

  /** Python Random.randint(a, b): an integer in [a, b]. */
  randint(a: bigint, b: bigint): bigint {
    return this.randrange(a, b + 1n);
  }
}

/** SymPy's shared generator (sympy.core.random.rng). */
export const rng: Random = new Random();

/** SymPy sympy.core.random.seed(a): seed the shared generator. */
export function seed(a?: bigint | number): void {
  rng.seed(a);
}

/** A randint function: SymPy _randint(seed) (an integer seed reseeds the shared generator). */
export type RandInt = (a: bigint, b: bigint) => bigint;

/** @internal SymPy _randint(seed) for an integer seed or none. */
export function randintFrom(s?: bigint | number): RandInt {
  if (s !== undefined) rng.seed(s);
  return (a, b) => rng.randint(a, b);
}

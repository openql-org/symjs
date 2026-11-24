// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Python's random.Random (the Mersenne Twister MT19937 with
 * init_by_array seeding, getrandbits, randrange, randint) and SymPy's
 * shared generator (sympy.core.random: rng, seed, _randint), so that the
 * randomized algorithms of the number theory module give the same results
 * as SymPy for the same seed.
 */

import { at } from '../core/guard';
import { bitLength } from './intutil';

const N = 624;
const M = 397;
const MATRIX_A = 0x9908b0df;
const UPPER_MASK = 0x80000000;
const LOWER_MASK = 0x7fffffff;

/** The MT19937 words, current offset and optional cached Gaussian. */
export interface RandomState {
  readonly words: readonly number[];
  readonly index: number;
  readonly gaussian?: number;
}

/** Generates pseudorandom numbers with the MT19937 algorithm and Python-compatible integer seeding. */
export class Random {
  private readonly mt = new Uint32Array(N);
  private mti = N + 1;

  /**
   * Initializes a pseudorandom generator, using the integer seed when supplied.
   *
   * @param seed - Seed for the pseudorandom sequence.
   */
  constructor(seed?: bigint | number) {
    this.seed(seed);
  }

  /**
   * A seed from Math.random).
   *
   * @param a - Seed for the pseudorandom sequence.
   */
  seed(a?: bigint | number): void {
    this.#gaussNext = undefined;
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

  /**
   * Save an independent copy of the current generator state.
   *
   * @returns A snapshot of the generator state.
   */
  getState(): RandomState {
    return { words: [...this.mt], index: this.mti, ...(this.#gaussNext === undefined ? {} : { gaussian: this.#gaussNext }) };
  }

  /**
   * Restore the generator state.
   *
   * @param state - Previously saved generator state.
   * @throws RangeError when the state is not a valid MT19937 state.
   */
  setState(state: RandomState): void {
    if (state.words.length !== N || !Number.isInteger(state.index) || state.index < 0 || state.index > N ||
        state.words.some((word) => !Number.isInteger(word) || word < 0 || word > 0xffffffff)) {
      throw new RangeError('invalid MT19937 state');
    }
    this.mt.set(state.words);
    this.mti = state.index;
    this.#gaussNext = state.gaussian;
  }

  private initGenrand(s: number): void {
    const mt = this.mt;
    mt[0] = s >>> 0;
    for (let i = 1; i < N; i++) {
      const prev = at(mt, i - 1) ^ (at(mt, i - 1) >>> 30);
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
      const prev = at(mt, i - 1) ^ (at(mt, i - 1) >>> 30);
      mt[i] = ((at(mt, i) ^ Math.imul(prev, 1664525)) + at(key, j) + j) >>> 0;
      i++;
      j++;
      if (i >= N) {
        mt[0] = at(mt, N - 1);
        i = 1;
      }
      if (j >= keyLength) j = 0;
    }
    for (let k = N - 1; k > 0; k--) {
      const prev = at(mt, i - 1) ^ (at(mt, i - 1) >>> 30);
      mt[i] = ((at(mt, i) ^ Math.imul(prev, 1566083941)) - i) >>> 0;
      i++;
      if (i >= N) {
        mt[0] = at(mt, N - 1);
        i = 1;
      }
    }
    mt[0] = 0x80000000;
  }

  /**
   * A uniformly distributed 32-bit unsigned integer (genrand_uint32).
   *
   * @returns An unsigned 32-bit sample.
   */
  genrandUint32(): number {
    const mt = this.mt;
    let y: number;
    if (this.mti >= N) {
      let kk = 0;
      for (; kk < N - M; kk++) {
        y = (at(mt, kk) & UPPER_MASK) | (at(mt, kk + 1) & LOWER_MASK);
        mt[kk] = at(mt, kk + M) ^ (y >>> 1) ^ (y & 1 ? MATRIX_A : 0);
      }
      for (; kk < N - 1; kk++) {
        y = (at(mt, kk) & UPPER_MASK) | (at(mt, kk + 1) & LOWER_MASK);
        mt[kk] = at(mt, kk + (M - N)) ^ (y >>> 1) ^ (y & 1 ? MATRIX_A : 0);
      }
      y = (at(mt, N - 1) & UPPER_MASK) | (at(mt, 0) & LOWER_MASK);
      mt[N - 1] = at(mt, M - 1) ^ (y >>> 1) ^ (y & 1 ? MATRIX_A : 0);
      this.mti = 0;
    }
    y = at(mt, this.mti++);
    y ^= y >>> 11;
    y ^= (y << 7) & 0x9d2c5680;
    y ^= (y << 15) & 0xefc60000;
    y ^= y >>> 18;
    return y >>> 0;
  }

  /**
   * A non-negative integer with k random bits.
   *
   * @param k - Number of random bits.
   * @returns The sampled nonnegative integer.
   * @throws RangeError when the number of bits is negative.
   */
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

  /**
   * A float in [0, 1) with 53 random bits (genrand_res53).
   *
   * @returns A uniform sample in the half-open unit interval.
   */
  random(): number {
    const a = this.genrandUint32() >>> 5;
    const b = this.genrandUint32() >>> 6;
    return (a * 67108864 + b) * (1 / 9007199254740992);
  }

  #gaussNext: number | undefined;

  /**
   * A normally distributed float (Box-Muller, the second value kept for the next call).
   *
   * @param mu - Mean of the normal distribution.
   * @param sigma - Standard deviation.
   * @returns A normally distributed sample.
   */
  gauss(mu = 0, sigma = 1): number {
    let z = this.#gaussNext;
    this.#gaussNext = undefined;
    if (z === undefined) {
      const x2pi = this.random() * 2 * Math.PI;
      const g2rad = Math.sqrt(-2 * Math.log(1 - this.random()));
      z = Math.cos(x2pi) * g2rad;
      this.#gaussNext = Math.sin(x2pi) * g2rad;
    }
    return mu + z * sigma;
  }

  /**
   * Draws a uniformly distributed integer from zero up to the exclusive bound.
   *
   * @param n - Exclusive upper bound.
   * @returns A nonnegative sample below the bound.
   */
  randbelow(n: bigint): bigint {
    const k = bitLength(n);
    let r = this.getrandbits(k);
    while (r >= n) r = this.getrandbits(k);
    return r;
  }

  /**
   * Samples an integer uniformly from a half-open range with unit stride.
   *
   * @param start - First position in the range.
   * @param stop - Exclusive end of the range.
   * @returns An integer from the half-open range.
   * @throws RangeError when the range is empty.
   */
  randrange(start: bigint, stop: bigint): bigint {
    const width = stop - start;
    if (width <= 0n) throw new RangeError(`empty range in randrange(${start}, ${stop})`);
    return start + this.randbelow(width);
  }

  /**
   * Draws a uniformly distributed integer between the two inclusive bounds.
   *
   * @param a - Inclusive lower bound.
   * @param b - Inclusive upper bound.
   * @returns An integer between the inclusive bounds.
   * @throws RangeError when the upper bound is below the lower bound.
   */
  randint(a: bigint, b: bigint): bigint {
    return this.randrange(a, b + 1n);
  }
}

/**
 * The shared pseudorandom generator for number-theory operations.
 *
 * @see SymPy `sympy.core.random.rng`
 */
export const rng: Random = new Random();

/**
 * Seeds the shared pseudorandom number generator.
 *
 * @param a - Seed for the shared pseudorandom number generator.
 * @see SymPy `sympy.core.random.seed`
 */
export function seed(a?: bigint | number): void {
  rng.seed(a);
}

/** A function drawing an integer from a closed interval. */
export type RandInt = (a: bigint, b: bigint) => bigint;

/** @internal SymPy _randint(seed) for an integer seed or none. */
export function randintFrom(s?: bigint | number): RandInt {
  if (s !== undefined) rng.seed(s);
  return (a, b) => rng.randint(a, b);
}

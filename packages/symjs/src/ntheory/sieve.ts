// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The dynamically growing sieve of Eratosthenes (SymPy
 * sympy.ntheory.generate.Sieve) with its shared instance `sieve`.
 */

import { at, last } from '../core/guard';
import type { IntLike } from './intutil';
import { asInt, asIntCeiling, isqrt } from './intutil';

/** The index of the first element > x in a sorted array (Python bisect.bisect_right). */
export function bisectRight(a: ArrayLike<number>, x: number): number {
  let lo = 0;
  let hi = a.length;
  while (lo < hi) {
    const mid = (lo + hi) >> 1;
    if (x < at(a, mid)) hi = mid;
    else lo = mid + 1;
  }
  return lo;
}

/** The index of the first element >= x in a sorted array (Python bisect.bisect_left). */
export function bisectLeft(a: ArrayLike<number>, x: number): number {
  let lo = 0;
  let hi = a.length;
  while (lo < hi) {
    const mid = (lo + hi) >> 1;
    if (at(a, mid) < x) lo = mid + 1;
    else hi = mid;
  }
  return lo;
}

const toNum = (n: bigint): number => {
  if (n > 0xffffffffn) throw new RangeError('the sieve is limited to primes below 2**32');
  return Number(n);
};

/**
 * A list of prime numbers, implemented as a dynamically growing sieve of
 * Eratosthenes, with lists of totients and Mobius values (SymPy Sieve).
 * Primes are limited to 2**32 - 1. Values are returned as bigints.
 */
export class Sieve {
  private static readonly INIT_PRIMES = [2, 3, 5, 7, 11, 13];
  private static readonly INIT_TOTIENT = [0, 1, 1, 2, 2, 4];
  private static readonly INIT_MOBIUS = [0, 1, -1, -1, 0, -1];
  /** @internal The primes found so far (SymPy _list). */
  primes: number[] = [...Sieve.INIT_PRIMES];
  /** @internal Totients of 0, 1, 2, ... (SymPy _tlist). */
  tlist: number[] = [...Sieve.INIT_TOTIENT];
  /** @internal Mobius values of 0, 1, 2, ... (SymPy _mlist). */
  mlist: number[] = [...Sieve.INIT_MOBIUS];
  /** Size of the blocks of the segmented sieve. */
  readonly sieveInterval: number;

  /** Sieve(sieve_interval=1_000_000). */
  constructor(sieveInterval = 1_000_000) {
    if (sieveInterval <= 0) throw new RangeError('sieve_interval should be a positive integer');
    this.sieveInterval = sieveInterval;
  }

  /** The primes found so far (SymPy sieve._list). */
  get list(): bigint[] {
    return this.primes.map(BigInt);
  }

  /** String form like SymPy's repr. */
  toString(): string {
    const f = (name: string, l: number[]) => `${name} sieve (${l.length}): ${l[0]}, ${l[1]}, ${l[2]}, ... ${l[l.length - 2]}, ${l[l.length - 1]}`;
    return `<${f('prime', this.primes)}\n${f('totient', this.tlist)}\n${f('mobius', this.mlist)}>`;
  }

  /** Reset the caches (SymPy _reset); with options, only the selected ones. */
  reset(opts: { prime?: boolean; totient?: boolean; mobius?: boolean } = {}): void {
    let { prime, totient, mobius } = opts;
    if (prime === undefined && totient === undefined && mobius === undefined) prime = totient = mobius = true;
    if (prime === true) this.primes = this.primes.slice(0, 6);
    if (totient === true) this.tlist = this.tlist.slice(0, 6);
    if (mobius === true) this.mlist = this.mlist.slice(0, 6);
  }

  /** Grow the sieve to cover all primes <= n (SymPy Sieve.extend). */
  extend(nIn: IntLike): void {
    const n = toNum(asInt(nIn));
    let num = last(this.primes) + 1;
    if (n < num) return;
    let num2 = num * num;
    while (num2 <= n) {
      for (const p of this.rangeOf(num, num2)) this.primes.push(p);
      num = num2;
      num2 = num2 * num2;
    }
    for (const p of this.rangeOf(num, n + 1)) this.primes.push(p);
  }

  private rangeOf(a: number, b: number): number[] {
    return [...this.primerangeInternal(a, b)];
  }

  /**
   * @internal The primes in (a, b) for an even a with
   * 2 < last prime < a < b < nextprime(last prime)**2 (SymPy _primerange).
   */
  *primerangeInternal(aIn: number, bIn: number): Generator<number, void, undefined> {
    let a = aIn;
    const b = bIn % 2 ? bIn - 1 : bIn;
    while (a < b) {
      const blockSize = Math.min(this.sieveInterval, Math.floor((b - a) / 2));
      const block = new Uint8Array(blockSize).fill(1);
      const lim = Number(isqrt(BigInt(a + 2 * blockSize + 1)));
      const end = bisectRight(this.primes, lim);
      for (let k = 1; k < end; k++) {
        const p = at(this.primes, k);
        // t = (-(a + 1 + p) // 2) % p with Python floor semantics
        let t = ((Math.floor(-(a + 1 + p) / 2) % p) + p) % p;
        for (; t < blockSize; t += p) block[t] = 0;
      }
      for (let idx = 0; idx < blockSize; idx++) if (block[idx]) yield a + 2 * idx + 1;
      a += 2 * blockSize;
    }
  }

  /** Extend to include the ith prime number (SymPy Sieve.extend_to_no). */
  extendToNo(iIn: IntLike): void {
    const i = Number(asInt(iIn));
    while (this.primes.length < i) this.extend(Math.floor(last(this.primes) * 1.5));
  }

  /** All primes in [2, a) or [a, b) (SymPy Sieve.primerange). */
  *primerange(aIn: IntLike, bIn?: IntLike): Generator<bigint, void, undefined> {
    let a: bigint;
    let b: bigint;
    if (bIn === undefined) {
      b = asIntCeiling(aIn);
      a = 2n;
    } else {
      a = asIntCeiling(aIn);
      if (a < 2n) a = 2n;
      b = asIntCeiling(bIn);
    }
    if (a >= b) return;
    this.extend(b);
    // extend(b) checked that b fits the sieve
    const lo = bisectLeft(this.primes, Number(a));
    const hi = bisectLeft(this.primes, Number(b));
    const ps = this.primes.slice(lo, hi);
    for (const p of ps) yield BigInt(p);
  }

  /** Totients of the integers in [a, b) (SymPy Sieve.totientrange). */
  *totientrange(aIn: IntLike, bIn: IntLike): Generator<bigint, void, undefined> {
    let a = Number(asIntCeiling(aIn));
    if (a < 1) a = 1;
    const b = Number(asIntCeiling(bIn));
    const n = this.tlist.length;
    if (a >= b) return;
    if (b <= n) {
      for (const v of this.tlist.slice(a, b)) yield BigInt(v);
      return;
    }
    const t = this.tlist;
    for (let i = n; i < b; i++) t.push(i);
    for (let i = 1; i < n; i++) {
      const ti = at(t, i);
      if (ti === i - 1) {
        const start = Math.floor((n + i - 1) / i) * i;
        for (let j = start; j < b; j += i) {
          const tj = at(t, j);
          t[j] = tj - Math.floor(tj / i);
        }
      }
      if (i >= a) yield BigInt(ti);
    }
    for (let i = n; i < b; i++) {
      if (at(t, i) === i) {
        for (let j = i; j < b; j += i) {
          const tj = at(t, j);
          t[j] = tj - Math.floor(tj / i);
        }
      }
      if (i >= a) yield BigInt(at(t, i));
    }
  }

  /** Mobius values of the integers in [a, b) (SymPy Sieve.mobiusrange). */
  *mobiusrange(aIn: IntLike, bIn: IntLike): Generator<bigint, void, undefined> {
    let a = Number(asIntCeiling(aIn));
    if (a < 1) a = 1;
    const b = Number(asIntCeiling(bIn));
    const n = this.mlist.length;
    if (a >= b) return;
    if (b <= n) {
      for (const v of this.mlist.slice(a, b)) yield BigInt(v);
      return;
    }
    const m = this.mlist;
    for (let i = n; i < b; i++) m.push(0);
    for (let i = 1; i < n; i++) {
      const mi = at(m, i);
      const start = Math.floor((n + i - 1) / i) * i;
      for (let j = start; j < b; j += i) m[j] = at(m, j) - mi;
      if (i >= a) yield BigInt(mi);
    }
    for (let i = n; i < b; i++) {
      const mi = at(m, i);
      for (let j = 2 * i; j < b; j += i) m[j] = at(m, j) - mi;
      if (i >= a) yield BigInt(mi);
    }
  }

  /** The indices [i, j] of the primes that bound n; i == j when n is prime (SymPy Sieve.search). */
  search(nIn: IntLike): [bigint, bigint] {
    const test = asIntCeiling(nIn);
    const n = asInt(nIn);
    if (n < 2n) throw new RangeError(`n should be >= 2 but got: ${n}`);
    if (n > BigInt(last(this.primes))) this.extend(n);
    const b = bisectRight(this.primes, Number(n));
    if (BigInt(at(this.primes, b - 1)) === test) return [BigInt(b), BigInt(b)];
    return [BigInt(b), BigInt(b + 1)];
  }

  /** n is a prime (SymPy `n in sieve`). */
  contains(nIn: IntLike): boolean {
    let n: bigint;
    try {
      n = asInt(nIn);
    } catch {
      return false;
    }
    if (n < 2n) return false;
    if (n % 2n === 0n) return n === 2n;
    const [a, b] = this.search(n);
    return a === b;
  }

  /** The nth prime, indexed from 1 (SymPy sieve[n]). */
  get(nIn: IntLike): bigint {
    const n = asInt(nIn);
    if (n < 1n) throw new RangeError('Sieve indices start at 1.');
    this.extendToNo(n);
    return BigInt(at(this.primes, Number(n) - 1));
  }

  /** The primes with indices in [start, stop) by step (SymPy sieve[start:stop:step]). */
  slice(start: IntLike, stop: IntLike, step: IntLike = 1): bigint[] {
    const s = Number(asInt(start));
    const e = Number(asInt(stop));
    const st = Number(asInt(step));
    if (s < 1) throw new RangeError('Sieve indices start at 1.');
    if (st <= 0) throw new RangeError('slice step must be positive');
    this.extendToNo(e);
    const out: bigint[] = [];
    for (let i = s - 1; i < Math.min(e - 1, this.primes.length); i += st) out.push(BigInt(at(this.primes, i)));
    return out;
  }

  /** All primes in increasing order (SymPy iter(sieve)); infinite. */
  *[Symbol.iterator](): Generator<bigint, void, undefined> {
    for (let n = 1; ; n++) yield this.get(n);
  }
}

/** The shared sieve (SymPy sympy.ntheory.generate.sieve). */
export const sieve: Sieve = new Sieve();

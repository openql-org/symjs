// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Generating and counting primes (SymPy sympy.ntheory.generate):
 * prime, nextprime, prevprime, primerange, randprime, primorial,
 * cycle_length, composite and compositepi.
 */

import { at, getOrThrow, last } from '../core/guard';
import { Expr } from '../core/nodes';
import type { NoMatchResult, UnsolvedResult } from '../core/truth';
import { NoMatch, Unsolved } from '../core/truth';
import type { IntLike } from './intutil';
import { asInt, asIntCeiling, isqrt, truncInt } from './intutil';
import { isprime } from './primetest';
import { rng } from './random';
import { bisectLeft, sieve } from './sieve';

const lastPrime = (): bigint => BigInt(last(sieve.primes));

/** prevprime(n) for 3 <= n < 8. */
const SMALL_PREVPRIME = new Map<bigint, bigint>([
  [3n, 2n],
  [4n, 3n],
  [5n, 3n],
  [6n, 5n],
  [7n, 5n],
]);

/** The logarithmic integral li(x) for x > 1 in double precision (Ramanujan's series). */
export function liFloat(x: number): number {
  const EULER = 0.5772156649015329;
  const L = Math.log(x);
  let sum = 0;
  let term = 1; // (ln x)^n / (n! 2^(n-1)) built up
  let inner = 0;
  for (let n = 1; n < 1000; n++) {
    term *= L / n;
    if (n > 1) term /= 2;
    if ((n - 1) % 2 === 0) inner += 1 / n; // adds 1/(2k+1) for k = (n-1)/2
    const t = (n % 2 === 1 ? 1 : -1) * term * inner;
    sum += t;
    if (Math.abs(t) < 1e-17 * Math.abs(sum) && n > L) break;
  }
  return EULER + Math.log(L) + Math.sqrt(x) * sum;
}

/** The prime counting function pi(n) by the Legendre-Lucy method (SymPy _primepi). */
export function primepiInt(nIn: IntLike): bigint {
  const nb = asInt(nIn);
  if (nb < 2n) return 0n;
  if (nb <= lastPrime()) return sieve.search(nb)[0];
  if (nb >= 1n << 53n) throw new RangeError('primepi: n is too large');
  const n = Number(nb);
  const lim = Number(isqrt(nb));
  const arr1: number[] = [];
  for (let i = 0; i <= lim; i++) arr1.push((i + 1) >> 1);
  const arr2: number[] = [0];
  for (let i = 1; i <= lim; i++) arr2.push(Math.floor((Math.floor(n / i) + 1) / 2));
  const skip = new Uint8Array(lim + 1);
  for (let i = 3; i <= lim; i += 2) {
    if (skip[i]) continue;
    const p = at(arr1, i - 1);
    for (let j = i; j <= lim; j += i) skip[j] = 1;
    const top = Math.min(Math.floor(n / (i * i)), lim);
    for (let j = 1; j <= top; j += 2) {
      if (skip[j]) continue;
      const st = i * j;
      const sub = st <= lim ? at(arr2, st) : at(arr1, Math.floor(n / st));
      arr2[j] = at(arr2, j) - (sub - p);
    }
    for (let j = lim; j > Math.min(lim, i * i - 1); j--) arr1[j] = at(arr1, j) - (at(arr1, Math.floor(j / i)) - p);
  }
  return BigInt(at(arr2, 1));
}

/**
 * Selects a prime by its one-based index, starting with 2.
 *
 * @param nth - One-based position in the sequence.
 * @returns The number at the requested index.
 * @throws RangeError when the index is not positive.
 * @see SymPy `sympy.ntheory.generate.prime`
 * @example
 * ```ts
 * import { prime } from '@symjs/symjs';
 *
 * prime(10); // => 29
 * prime(1); // => 2
 * ```
 */
export function prime(nth: IntLike): bigint {
  const n = asInt(nth);
  if (n < 1n) throw new RangeError('nth must be a positive integer; prime(1) == 2');
  if (n <= BigInt(sieve.primes.length)) return sieve.get(n);
  if (n < 1000n) {
    sieve.extend(8n * n);
    return sieve.get(n);
  }
  const nn = Number(n);
  let a = 2;
  let b = Math.floor(nn * (Math.log(nn) + Math.log(Math.log(nn))));
  while (a < b) {
    const mid = Math.floor((a + b) / 2);
    if (liFloat(mid) > nn) b = mid;
    else a = mid + 1;
  }
  return nextprime(a - 1, n - primepiInt(a - 1));
}

/**
 * The ith prime greater than n.
 *
 * @param nIn - Exclusive lower bound.
 * @param ithIn - One-based index among primes above the bound.
 * @returns The prime at the requested offset.
 * @throws RangeError when the prime offset is not positive.
 * @see SymPy `sympy.ntheory.generate.nextprime`
 * @example
 * ```ts
 * import { nextprime } from '@symjs/symjs';
 *
 * nextprime(2, 2); // => 5
 * ```
 */
export function nextprime(nIn: IntLike, ithIn: IntLike = 1): bigint {
  let n = truncInt(nIn);
  let i = asInt(ithIn);
  if (i <= 0n) throw new RangeError('ith should be positive');
  if (n < 2n) {
    n = 2n;
    i -= 1n;
  }
  const ps = sieve.primes;
  if (n <= BigInt(at(ps, ps.length - 2))) {
    const l = sieve.search(n)[0];
    if (l + i - 1n < BigInt(ps.length)) return BigInt(at(ps, Number(l + i - 1n)));
    n = BigInt(at(ps, ps.length - 1));
    i += l - BigInt(ps.length);
  }
  const nn = 6n * (n / 6n);
  if (nn === n) {
    n += 1n;
    if (isprime(n)) {
      i -= 1n;
      if (i === 0n) return n;
    }
    n += 4n;
  } else if (n - nn === 5n) {
    n += 2n;
    if (isprime(n)) {
      i -= 1n;
      if (i === 0n) return n;
    }
    n += 4n;
  } else n = nn + 5n;
  for (;;) {
    if (isprime(n)) {
      i -= 1n;
      if (i === 0n) return n;
    }
    n += 2n;
    if (isprime(n)) {
      i -= 1n;
      if (i === 0n) return n;
    }
    n += 4n;
  }
}

/**
 * The largest prime smaller than n.
 *
 * @param nIn - Exclusive upper bound.
 * @returns The immediately preceding prime.
 * @throws RangeError when there is no preceding prime.
 * @see SymPy `sympy.ntheory.generate.prevprime`
 * @example
 * ```ts
 * import { prevprime } from '@symjs/symjs';
 *
 * [10, 11, 12, 13, 14].map(n => prevprime(n)); // => [7, 7, 11, 11, 13]
 * ```
 */
export function prevprime(nIn: IntLike): bigint {
  let n = asIntCeiling(nIn);
  if (n < 3n) throw new RangeError('no preceding primes');
  if (n < 8n) return getOrThrow(SMALL_PREVPRIME, n);
  if (n <= lastPrime()) {
    const [l, u] = sieve.search(n);
    return l === u ? sieve.get(l - 1n) : sieve.get(l);
  }
  const nn = 6n * (n / 6n);
  if (n - nn <= 1n) {
    n = nn - 1n;
    if (isprime(n)) return n;
    n -= 4n;
  } else n = nn + 1n;
  for (;;) {
    if (isprime(n)) return n;
    n -= 2n;
    if (isprime(n)) return n;
    n -= 4n;
  }
}

/**
 * All primes in [2, a) or [a, b). Values beyond the shared sieve are computed without extending it.
 *
 * @param aIn - Lower bound, or exclusive upper bound when given alone.
 * @param bIn - Exclusive upper bound for the two-argument form.
 * @returns A generator of primes in the half-open interval.
 * @see SymPy `sympy.ntheory.generate.primerange`
 * @example
 * ```ts
 * import { primerange } from '@symjs/symjs';
 *
 * [...primerange(19)]; // => [2, 3, 5, 7, 11, 13, 17]
 * [...primerange(7, 19)]; // => [7, 11, 13, 17]
 * ```
 */
export function* primerange(aIn: IntLike, bIn?: IntLike): Generator<bigint, void, undefined> {
  let a: bigint;
  let b: bigint;
  if (bIn === undefined) {
    a = 2n;
    b = asIntCeiling(aIn);
  } else {
    a = asIntCeiling(aIn);
    b = asIntCeiling(bIn);
  }
  if (a >= b) return;
  const largest = lastPrime();
  if (b <= largest) {
    yield* sieve.primerange(a, b);
    return;
  }
  if (a <= largest) {
    const ps = sieve.primes.slice(bisectLeft(sieve.primes, Number(a < 0n ? 0n : a)));
    for (const p of ps) yield BigInt(p);
    a = largest + 1n;
  } else if (a % 2n !== 0n) a -= 1n;
  const tail = b < largest * largest ? b : largest * largest;
  if (a < tail) {
    for (const p of [...sieve.primerangeInternal(Number(a), Number(tail))]) yield BigInt(p);
    a = tail;
  }
  if (b <= a) return;
  for (;;) {
    a = nextprime(a);
    if (a < b) yield a;
    else return;
  }
}

/**
 * A random prime in [a, b), from the shared generator (see `seed`); NoMatch when a >= b.
 *
 * @param aIn - Inclusive lower bound.
 * @param bIn - Exclusive upper bound.
 * @returns A prime in the interval, or `NoMatch` if the bounds are reversed or equal.
 * @throws RangeError when a nonempty interval contains no primes.
 * @see SymPy `sympy.ntheory.generate.randprime`
 * @example
 * ```ts
 * import { randprime } from '@symjs/symjs';
 *
 * randprime(2, 3); // => 2
 * ```
 */
export function randprime(aIn: IntLike, bIn: IntLike): bigint | NoMatchResult {
  const a = truncInt(aIn);
  const b = truncInt(bIn);
  if (a >= b) return NoMatch;
  const n = rng.randint(a - 1n, b);
  let p = nextprime(n);
  if (p >= b) p = prevprime(b);
  if (p < a) throw new RangeError('no primes exist in the specified range');
  return p;
}

/**
 * The product of the first n primes, or of the primes <= n with `{ nth: false }`.
 *
 * @param nIn - Number of primes, or largest prime allowed when `nth` is false.
 * @param opts - Set `nth` to false to use an upper bound.
 * @returns The product of the selected primes.
 * @throws RangeError when the bound is less than one.
 * @see SymPy `sympy.ntheory.generate.primorial`
 * @example
 * ```ts
 * import { primorial } from '@symjs/symjs';
 *
 * primorial(4); // => 210
 * primorial(4, { nth: false }); // => 6
 * ```
 */
export function primorial(nIn: IntLike, opts: { nth?: boolean } = {}): bigint {
  const nth = opts.nth ?? true;
  const n = nth ? asInt(nIn) : truncInt(nIn);
  if (n < 1n) throw new RangeError('primorial argument must be >= 1');
  let p = 1n;
  if (nth) for (let i = 1n; i <= n; i++) p *= prime(i);
  else for (const q of primerange(2n, n + 1n)) p *= q;
  return p;
}

const same = (a: unknown, b: unknown): boolean => a === b || (a instanceof Expr && b instanceof Expr && a.key === b.key);

/**
 * Examines the orbit of a starting value under repeated application of a function. It yields the
 * cycle length and preceding tail length, or the visited values when requested.
 *
 * @remarks SymPy yields the tuple `(6, 3)` for this orbit.
 * @param f - Iteration function.
 * @param x0 - Initial value of the orbit.
 * @param opts - Limit the iterations with `nmax` or request the orbit with `values`.
 * @returns A generator of cycle information or successive iterates.
 * @see SymPy `sympy.ntheory.generate.cycle_length`
 * @example
 * ```ts
 * import { cycleLength } from '@symjs/symjs';
 *
 * const f = (i: number) => (i ** 2 + 1) % 51;
 * cycleLength(f, 4).next().value; // => [6, 3]
 * ```
 */
export function cycleLength<T>(f: (x: T) => T, x0: T, opts: { nmax?: number | bigint; values: true }): Generator<T, void, undefined>;
/**
 * Examines the orbit of a starting value under repeated application of a function. It yields the
 * cycle length and preceding tail length, or the visited values when requested.
 *
 * @remarks SymPy yields the tuple `(6, 3)` for this orbit.
 * @param f - Iteration function.
 * @param x0 - Initial value of the orbit.
 * @param opts - Limit the iterations with `nmax` or request the orbit with `values`.
 * @returns A generator of cycle information or successive iterates.
 * @see SymPy `sympy.ntheory.generate.cycle_length`
 */
export function cycleLength<T>(f: (x: T) => T, x0: T, opts?: { nmax?: number | bigint; values?: false }): Generator<[bigint, bigint | UnsolvedResult], void, undefined>;
export function* cycleLength<T>(f: (x: T) => T, x0: T, opts: { nmax?: number | bigint; values?: boolean } = {}): Generator<T | [bigint, bigint | UnsolvedResult], void, undefined> {
  const nmax = Number(opts.nmax ?? 0);
  const values = opts.values ?? false;
  let power = 1;
  let lam = 1;
  let tortoise = x0;
  let hare = f(x0);
  let i = 1;
  if (values) yield tortoise;
  while (!same(tortoise, hare) && (!nmax || i < nmax)) {
    i++;
    if (power === lam) {
      tortoise = hare;
      power *= 2;
      lam = 0;
    }
    if (values) yield hare;
    hare = f(hare);
    lam++;
  }
  if (nmax && i === nmax) {
    if (values) return;
    yield [BigInt(nmax), Unsolved];
    return;
  }
  if (!values) {
    let mu = 0;
    tortoise = hare = x0;
    for (let k = 0; k < lam; k++) hare = f(hare);
    while (!same(tortoise, hare)) {
      tortoise = f(tortoise);
      hare = f(hare);
      mu++;
    }
    yield [BigInt(lam), BigInt(mu)];
  }
}

/**
 * Selects a composite number by its one-based index, starting with 4.
 *
 * @param nth - One-based position in the sequence.
 * @returns The number at the requested index.
 * @throws RangeError when the index is not positive.
 * @see SymPy `sympy.ntheory.generate.composite`
 * @example
 * ```ts
 * import { composite } from '@symjs/symjs';
 *
 * composite(36); // => 52
 * composite(1); // => 4
 * ```
 */
export function composite(nth: IntLike): bigint {
  const n = asInt(nth);
  if (n < 1n) throw new RangeError('nth must be a positive integer; composite(1) == 4');
  const arr = [4n, 6n, 8n, 9n, 10n, 12n, 14n, 15n, 16n, 18n];
  if (n <= 10n) return at(arr, Number(n) - 1);
  let a = 4n;
  let b = lastPrime();
  if (n <= b - primepiInt(b) - 1n) {
    while (a < b - 1n) {
      const mid = (a + b) >> 1n;
      if (mid - primepiInt(mid) - 1n > n) b = mid;
      else a = mid;
    }
    if (isprime(a)) a -= 1n;
    return a;
  }
  const nn = Number(n);
  let lo = 4;
  let hi = Math.floor(nn * (Math.log(nn) + Math.log(Math.log(nn))));
  while (lo < hi) {
    const mid = Math.floor((lo + hi) / 2);
    if (mid - liFloat(mid) - 1 > nn) hi = mid;
    else lo = mid + 1;
  }
  a = BigInt(lo);
  let nComposites = a - primepiInt(a) - 1n;
  while (nComposites > n) {
    if (!isprime(a)) nComposites -= 1n;
    a -= 1n;
  }
  if (isprime(a)) a -= 1n;
  return a;
}

/**
 * Counts composite numbers up to and including the given bound.
 *
 * @param nIn - Inclusive upper bound.
 * @returns The count of composite numbers up to the bound.
 * @see SymPy `sympy.ntheory.generate.compositepi`
 * @example
 * ```ts
 * import { compositepi } from '@symjs/symjs';
 *
 * compositepi(25); // => 15
 * compositepi(1000); // => 831
 * ```
 */
export function compositepi(nIn: IntLike): bigint {
  const n = truncInt(nIn);
  if (n < 4n) return 0n;
  return n - primepiInt(n) - 1n;
}

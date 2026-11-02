// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Primality tests (SymPy sympy.ntheory.primetest: isprime with its
 * Miller-Rabin bases and the strong BPSW test, is_mersenne_prime,
 * is_gaussian_prime) and the cache of prime factors (SymPy
 * sympy.ntheory.factor_.FactorCache and factor_cache), which isprime
 * consults.
 */

import type { ExprLike } from '../core/nodes';
import { Add, I, Mul, Rational } from '../core/nodes';
import { sympify } from '../core/ops';
import type { NoMatchResult } from '../core/truth';
import { NoMatch, isNoMatch } from '../core/truth';
import type { IntLike } from './intutil';
import { asInt, babs, bitLength, bitScan1, isSquare, jacobi, powmod, remove } from './intutil';
import { bisectLeft, sieve } from './sieve';

/** The exponents p of the known Mersenne primes 2**p - 1 (SymPy MERSENNE_PRIME_EXPONENTS). */
export const MERSENNE_PRIME_EXPONENTS: readonly number[] = [
  2, 3, 5, 7, 13, 17, 19, 31, 61, 89, 107, 127, 521, 607, 1279, 2203, 2281, 3217, 4253, 4423, 9689, 9941, 11213, 19937, 21701, 23209, 44497, 86243,
  110503, 132049, 216091, 756839, 859433, 1257787, 1398269, 2976221, 3021377, 6972593, 13466917, 20996011, 24036583, 25964951, 30402457, 32582657,
  37156667, 42643801, 43112609, 57885161, 74207281, 77232917, 82589933, 136279841,
];

const MR_BASES_32 = [
  15591, 2018, 166, 7429, 8064, 16045, 10503, 4399, 1949, 1295, 2776, 3620, 560, 3128, 5212, 2657, 2300, 2021, 4652, 1471, 9336, 4018, 2398, 20462, 10277,
  8028, 2213, 6219, 620, 3763, 4852, 5012, 3185, 1333, 6227, 5298, 1074, 2391, 5113, 7061, 803, 1269, 3875, 422, 751, 580, 4729, 10239, 746, 2951, 556,
  2206, 3778, 481, 1522, 3476, 481, 2487, 3266, 5633, 488, 3373, 6441, 3344, 17, 15105, 1490, 4154, 2036, 1882, 1813, 467, 3307, 14042, 6371, 658, 1005,
  903, 737, 1887, 7447, 1888, 2848, 1784, 7559, 3400, 951, 13969, 4304, 177, 41, 19875, 3110, 13221, 8726, 571, 7043, 6943, 1199, 352, 6435, 165, 1169,
  3315, 978, 233, 3003, 2562, 2994, 10587, 10030, 2377, 1902, 5354, 4447, 1555, 263, 27027, 2283, 305, 669, 1912, 601, 6186, 429, 1930, 14873, 1784, 1661,
  524, 3577, 236, 2360, 6146, 2850, 55637, 1753, 4178, 8466, 222, 2579, 2743, 2031, 2226, 2276, 374, 2132, 813, 23788, 1610, 4422, 5159, 1725, 3597, 3366,
  14336, 579, 165, 1375, 10018, 12616, 9816, 1371, 536, 1867, 10864, 857, 2206, 5788, 434, 8085, 17618, 727, 3639, 1595, 4944, 2129, 2029, 8195, 8344,
  6232, 9183, 8126, 1870, 3296, 7455, 8947, 25017, 541, 19115, 368, 566, 5674, 411, 522, 1027, 8215, 2050, 6544, 10049, 614, 774, 2333, 3007, 35201, 4706,
  1152, 1785, 1028, 1540, 3743, 493, 4474, 2521, 26845, 8354, 864, 18915, 5465, 2447, 42, 4511, 1660, 166, 1249, 6259, 2553, 304, 272, 7286, 73, 6554, 899,
  2816, 5197, 13330, 7054, 2818, 3199, 811, 922, 350, 7514, 4452, 3449, 2663, 4708, 418, 1621, 1171, 3471, 88, 11345, 412, 1559, 194,
];

function mrTest(n: bigint, base: bigint, s: number, t: bigint): boolean {
  let b = powmod(base, t, n);
  if (b === 1n || b === n - 1n) return true;
  for (let i = 0; i < s - 1; i++) {
    b = (b * b) % n;
    if (b === n - 1n) return true;
    if (b === 1n) return false;
  }
  return false;
}

/** Miller-Rabin test of n for the given bases (SymPy mr). */
export function mr(n: bigint, bases: readonly bigint[]): boolean {
  if (n < 2n || (n > 2n && n % 2n === 0n)) return false;
  const s = bitScan1(n - 1n);
  const t = n >> BigInt(s);
  for (const b0 of bases) {
    const base = b0 >= n ? b0 % n : b0;
    if (base >= 2n && !mrTest(n, base, s, t)) return false;
  }
  return true;
}

/** U_k, V_k, Q^k modulo n of the Lucas sequence (SymPy _lucas_sequence). */
export function lucasSequence(n: bigint, P: bigint, Q: bigint, k: bigint): [bigint, bigint, bigint] {
  if (k === 0n) return [0n, 2n, 1n];
  const D = P * P - 4n * Q;
  let U = 1n;
  let V = P;
  let Qk = ((Q % n) + n) % n;
  const bits = k.toString(2).slice(1);
  const md = (a: bigint) => ((a % n) + n) % n;
  for (const b of bits) {
    U = md(U * V);
    V = md(V * V - 2n * Qk);
    Qk *= Qk;
    if (b === '1') {
      [U, V] = [U * P + V, V * P + U * D];
      if (U & 1n) U += n;
      if (V & 1n) V += n;
      [U, V] = [U >> 1n, V >> 1n];
      Qk *= Q;
    }
    Qk = md(Qk);
  }
  return [md(U), md(V), Qk];
}

function isStrongPrp(n: bigint, a: bigint): boolean {
  const s = bitScan1(n - 1n);
  let x = powmod(a, n >> BigInt(s), n);
  if (x === 1n || x === n - 1n) return true;
  for (let i = 0; i < s - 1; i++) {
    x = (x * x) % n;
    if (x === n - 1n) return true;
    if (x === 1n) return false;
  }
  return false;
}

function isStrongSelfridgePrp(n: bigint): boolean {
  for (let d = 5n; d < 1000000n; d += 2n) {
    const D = d & 2n ? -d : d;
    const j = jacobi(D, n);
    if (j === -1) {
      const s = bitScan1(n + 1n);
      const lucas = lucasSequence(n, 1n, (1n - D) / 4n, (n + 1n) >> BigInt(s));
      const U = lucas[0];
      let V = lucas[1];
      let Qk = lucas[2];
      if (U === 0n || V === 0n) return true;
      for (let i = 0; i < s - 1; i++) {
        V = (((V * V - 2n * Qk) % n) + n) % n;
        if (V === 0n) return true;
        Qk = powmod(Qk, 2n, n);
      }
      return false;
    }
    if (j === 0 && D % n !== 0n) return false;
    if (D === 13n && isSquare(n)) return false;
  }
  throw new RangeError('appropriate value for D cannot be found in is_strong_selfridge_prp()');
}

/** The strong Baillie-PSW probable prime test (gmpy is_strong_bpsw_prp). */
export function isStrongBpswPrp(n: bigint): boolean {
  if (n < 1n) throw new RangeError("is_strong_bpsw_prp() requires 'n' be greater than 0");
  if (n === 1n) return false;
  if (n % 2n === 0n) return n === 2n;
  return isStrongPrp(n, 2n) && isStrongSelfridgePrp(n);
}

const SMALL_PRIMES_TO_47 = [7n, 11n, 13n, 17n, 19n, 23n, 29n, 31n, 37n, 41n, 43n, 47n];

/**
 * Test whether n is prime (SymPy isprime): deterministic below 2**64
 * (and up to 3.3e24 with Miller-Rabin bases), the strong BPSW test above.
 */
export function isprime(nIn: IntLike): boolean {
  const n = asInt(nIn);
  if (n === 2n || n === 3n || n === 5n) return true;
  if (n < 2n || n % 2n === 0n || n % 3n === 0n || n % 5n === 0n) return false;
  if (n < 49n) return true;
  for (const p of SMALL_PRIMES_TO_47) if (n % p === 0n) return false;
  if (n < 2809n) return true;
  if (n < 65077n) {
    const r = powmod(2n, n >> 1n, n);
    return (r === 1n || r === n - 1n) && ![8321n, 31621n, 42799n, 49141n, 49981n].includes(n);
  }
  const last = sieve.primes[sieve.primes.length - 1]!;
  if (n <= BigInt(last)) {
    const i = bisectLeft(sieve.primes, Number(n));
    return sieve.primes[i] === Number(n);
  }
  const ret = factorCache.get(n);
  if (!isNoMatch(ret)) return ret === n;
  if (n < 341531n) return mr(n, [9345883071009581737n]);
  if (n < 4296595241n) {
    let h = ((n >> 16n) ^ n) * 73244475n;
    h = ((h >> 16n) ^ h) * 73244475n;
    h = ((h >> 16n) ^ h) & 255n;
    return mr(n, [BigInt(MR_BASES_32[Number(h)]!)]);
  }
  if (n < 350269456337n) return mr(n, [4230279247111683200n, 14694767155120705706n, 16641139526367750375n]);
  if (n < 55245642489451n) return mr(n, [2n, 141889084524735n, 1199124725622454117n, 11096072698276303650n]);
  if (n < 7999252175582851n) return mr(n, [2n, 4130806001517n, 149795463772692060n, 186635894390467037n, 3967304179347715805n]);
  if (n < 585226005592931977n) return mr(n, [2n, 123635709730000n, 9233062284813009n, 43835965440333360n, 761179012939631437n, 1263739024124850375n]);
  if (n < 18446744073709551616n) return mr(n, [2n, 325n, 9375n, 28178n, 450775n, 9780504n, 1795265022n]);
  if (n < 318665857834031151167461n) return mr(n, [2n, 3n, 5n, 7n, 11n, 13n, 17n, 19n, 23n, 29n, 31n, 37n]);
  if (n < 3317044064679887385961981n) return mr(n, [2n, 3n, 5n, 7n, 11n, 13n, 17n, 19n, 23n, 29n, 31n, 37n, 41n]);
  return isStrongBpswPrp(n);
}

function lucasLehmer(p: number): boolean {
  let v = 4n;
  const m = (1n << BigInt(p)) - 1n;
  for (let i = 0; i < p - 2; i++) v = powmod(v, 2n, m) - 2n;
  return v === 0n;
}

/** n is a Mersenne prime 2**p - 1 (SymPy is_mersenne_prime). */
export function isMersennePrime(nIn: IntLike): boolean {
  const n = asInt(nIn);
  if (n < 1n) return false;
  if ((n & (n + 1n)) !== 0n) return false;
  const p = bitLength(n);
  if (MERSENNE_PRIME_EXPONENTS.includes(p)) return true;
  if (p < 65000000 || !isprime(p)) return false;
  const result = lucasLehmer(p);
  if (result) throw new RangeError(`This Mersenne Prime, 2^${p} - 1, should be added to SymPy's known values.`);
  return result;
}

/** num = a + b*I is a Gaussian prime (SymPy is_gaussian_prime). */
export function isGaussianPrime(num: ExprLike | bigint): boolean {
  const e = sympify(num);
  let a = 0n;
  let b = 0n;
  const terms = e instanceof Add ? e.args : [e];
  for (const t of terms) {
    if (t instanceof Rational && t.q === 1n) a += t.p;
    else if (t.key === I.key) b += 1n;
    else if (t instanceof Mul && t.args.length === 2 && t.args[0] instanceof Rational && t.args[0].q === 1n && t.args[1]!.key === I.key) b += t.args[0].p;
    else throw new TypeError(`${e.toString()} is not a Gaussian integer`);
  }
  if (a === 0n) {
    b = babs(b);
    return isprime(b) && b % 4n === 3n;
  }
  if (b === 0n) {
    a = babs(a);
    return isprime(a) && a % 4n === 3n;
  }
  return isprime(a * a + b * b);
}

// ---------------------------------------------------------------------------
// FactorCache
// ---------------------------------------------------------------------------

/**
 * A cache of the largest known prime factor of integers (SymPy
 * FactorCache): a least recently used map of maximum size `maxsize`
 * (unbounded for undefined). `getExternal` can be overridden to consult an
 * external source of factors.
 */
export class FactorCache {
  private cache = new Map<bigint, bigint>();
  private maxsizeValue: number | undefined;

  /** FactorCache(maxsize). */
  constructor(maxsize?: number) {
    this.maxsize = maxsize;
  }

  /** The number of cached entries. */
  get size(): number {
    return this.cache.size;
  }

  /** The maximum number of entries (undefined: unbounded). */
  get maxsize(): number | undefined {
    return this.maxsizeValue;
  }

  set maxsize(value: number | undefined) {
    if (value !== undefined && value <= 0) throw new RangeError('maxsize must be None or a non-negative integer.');
    this.maxsizeValue = value;
    if (value !== undefined) this.trim(value);
  }

  private trim(max: number): void {
    while (this.cache.size > max) {
      const first = this.cache.keys().next();
      if (first.done === true) break;
      this.cache.delete(first.value);
    }
  }

  /** n has a cached factor (SymPy `n in factor_cache`). */
  has(nIn: IntLike): boolean {
    return this.cache.has(asInt(nIn));
  }

  /** Record that factor is a prime factor of n (SymPy factor_cache[n] = factor). */
  set(nIn: IntLike, factorIn: IntLike): this {
    const n = asInt(nIn);
    const factor = asInt(factorIn);
    if (!(factor > 1n && factor <= n && n % factor === 0n && isprime(factor))) throw new RangeError(`${factor} is not a prime factor of ${n}`);
    const old = this.cache.get(n) ?? 0n;
    this.cache.delete(n);
    this.cache.set(n, old > factor ? old : factor);
    if (this.maxsizeValue !== undefined) this.trim(this.maxsizeValue);
    return this;
  }

  /** Remove the entry of n (SymPy del factor_cache[n]). */
  delete(nIn: IntLike): boolean {
    const n = asInt(nIn);
    if (!this.cache.has(n)) throw new RangeError(`${n} does not exist.`);
    return this.cache.delete(n);
  }

  /** The cached integers. */
  keys(): IterableIterator<bigint> {
    return this.cache.keys();
  }

  /** Remove all entries (SymPy cache_clear). */
  cacheClear(): void {
    this.cache = new Map();
  }

  /** The largest known prime factor of n, or NoMatch (SymPy FactorCache.get). */
  get(nIn: IntLike): bigint | NoMatchResult {
    const n = asInt(nIn);
    const ps = sieve.primes;
    if (n <= BigInt(ps[ps.length - 1]!) && n >= 0n) {
      const i = bisectLeft(ps, Number(n));
      if (ps[i] === Number(n)) return n;
    }
    const v = this.cache.get(n);
    if (v !== undefined) {
      this.cache.delete(n);
      this.cache.set(n, v);
      return v;
    }
    const factors = this.getExternal(n);
    if (!isNoMatch(factors) && factors.length > 0) {
      this.add(n, factors);
      const w = this.cache.get(n);
      if (w !== undefined) return w;
    }
    return NoMatch;
  }

  /** The cached factor of n (SymPy factor_cache[n]); throws when there is none. */
  getItem(nIn: IntLike): bigint {
    const f = this.get(nIn);
    if (isNoMatch(f)) throw new RangeError(`${asInt(nIn)} does not exist.`);
    return f;
  }

  /** Cache the prime factors of n (SymPy FactorCache.add). */
  add(nIn: IntLike, factors: readonly bigint[]): void {
    let n = asInt(nIn);
    for (const p of [...factors].sort((x, y) => (x < y ? 1 : x > y ? -1 : 0))) {
      this.set(n, p);
      n = remove(n, p)[0];
    }
  }

  /** Prime factors of n from an external source; override in a subclass (default NoMatch). */
  getExternal(_n: bigint): bigint[] | NoMatchResult {
    return NoMatch;
  }
}

/** The shared factor cache (SymPy factor_cache), of maximum size 1000. */
export const factorCache: FactorCache = new FactorCache(1000);

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Primality tests (SymPy sympy.ntheory.primetest: isprime with its
 * Miller-Rabin bases and the strong BPSW test, the Fermat, Euler and
 * extra strong Lucas probable prime tests, is_mersenne_prime,
 * is_gaussian_prime) and the cache of prime factors (SymPy
 * sympy.ntheory.factor_.FactorCache and factor_cache), which isprime
 * consults.
 */

import { at, last } from '../core/guard';
import type { ExprLike } from '../core/nodes';
import { Add, I, Mul, Rational } from '../core/nodes';
import { sympify } from '../core/ops';
import type { NoMatchResult } from '../core/truth';
import { NoMatch, isNoMatch } from '../core/truth';
import type { IntLike } from './intutil';
import { asInt, babs, bitLength, bitScan1, gcdN, isSquare, jacobi, powmod, remove } from './intutil';
import { bisectLeft, sieve } from './sieve';

/**
 * The exponents p of the known Mersenne primes 2**p - 1.
 *
 * @see SymPy `sympy.ntheory.primetest.MERSENNE_PRIME_EXPONENTS`
 */
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

/**
 * Applies the strong probable-prime test at each witness base.
 *
 * @param nIn - Integer to test.
 * @param bases - Witness bases to test.
 * @returns Whether the candidate passes every Miller–Rabin round.
 * @see SymPy `sympy.ntheory.primetest.mr`
 * @example
 * ```ts
 * import { mr } from '@symjs/symjs';
 *
 * mr(1373651, [2, 3]); // => False
 * mr(479001599, [31, 73]); // => True
 * ```
 */
export function mr(nIn: IntLike, bases: readonly IntLike[]): boolean {
  const n = asInt(nIn);
  if (n < 2n || (n > 2n && n % 2n === 0n)) return false;
  const s = bitScan1(n - 1n);
  const t = n >> BigInt(s);
  for (const bIn of bases) {
    const b0 = asInt(bIn);
    const base = b0 >= n ? b0 % n : b0;
    if (base >= 2n && !mrTest(n, base, s, t)) return false;
  }
  return true;
}

/**
 * Tests the primality of a Proth number using Proth’s theorem.
 *
 * @param nIn - Proth number to test.
 * @returns Whether the Proth number is prime.
 * @throws RangeError when the argument is not a Proth number.
 * @see SymPy `sympy.ntheory.primetest.proth_test`
 * @example
 * ```ts
 * import { prothTest } from '@symjs/symjs';
 *
 * prothTest(41); // => True
 * prothTest(57); // => False
 * ```
 */
export function prothTest(nIn: IntLike): boolean {
  const n = asInt(nIn);
  if (n < 3n) throw new RangeError('n is not a Proth number');
  const m = bitScan1(n - 1n), k = n >> BigInt(m);
  if (m < bitLength(k)) throw new RangeError('n is not a Proth number');
  if (n % 3n === 0n) return n === 3n;
  if (k % 3n !== 0n) return powmod(3n, n >> 1n, n) === n - 1n;
  if (isSquare(n)) return false;
  for (let a = 5n; ; a++) {
    const j = jacobi(a, n);
    if (j === -1) return powmod(a, n >> 1n, n) === n - 1n;
    if (j === 0) return false;
  }
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
  // SymPy gives up at d = 10**6, never reached: a square n stops at D = 13
  // and a non-square has (D/n) = -1 for some small D
  for (let d = 5n; ; d += 2n) {
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
}

/** The strong Baillie-PSW probable prime test (gmpy is_strong_bpsw_prp). */
export function isStrongBpswPrp(n: bigint): boolean {
  if (n < 1n) throw new RangeError("is_strong_bpsw_prp() requires 'n' be greater than 0");
  if (n === 1n) return false;
  if (n % 2n === 0n) return n === 2n;
  return isStrongPrp(n, 2n) && isStrongSelfridgePrp(n);
}

/** The checks shared by the Fermat and Euler probable prime tests of n to the base a (gmpy is_fermat_prp, is_euler_prp). */
function prpBase(name: string, n: bigint, a0: bigint): bigint | boolean {
  if (a0 < 2n) throw new RangeError(`${name}() requires 'a' greater than or equal to 2`);
  if (n < 1n) throw new RangeError(`${name}() requires 'n' be greater than 0`);
  if (n === 1n) return false;
  if (n % 2n === 0n) return n === 2n;
  const a = a0 % n;
  if (gcdN(n, a) !== 1n) throw new RangeError(`${name}() requires gcd(n,a) == 1`);
  return a;
}

/**
 * Tests the Fermat congruence for the supplied base.
 *
 * @param nIn - Candidate integer.
 * @param aIn - Base for the test.
 * @returns Whether the candidate passes the congruence test.
 * @throws RangeError when the candidate or base is outside its permitted range or the two are not
 *   coprime.
 * @see SymPy `sympy.ntheory.primetest.is_fermat_pseudoprime`
 * @example
 * ```ts
 * import { isFermatPseudoprime } from '@symjs/symjs';
 *
 * isFermatPseudoprime(341, 2); // => True
 * ```
 */
export function isFermatPseudoprime(nIn: IntLike, aIn: IntLike): boolean {
  const [n, a0] = [asInt(nIn), asInt(aIn)];
  if (a0 === 1n) return n === 2n || n % 2n !== 0n;
  const a = prpBase('is_fermat_prp', n, a0);
  return typeof a === 'boolean' ? a : powmod(a, n - 1n, n) === 1n;
}

/**
 * Tests whether `a**((n - 1)/2)` is congruent to plus or minus one for an odd candidate `n` coprime
 * to `a`.
 *
 * @param nIn - Candidate integer.
 * @param aIn - Base for the test.
 * @returns Whether the candidate passes the congruence test.
 * @throws RangeError when the candidate is not positive or the base is not coprime to it.
 * @see SymPy `sympy.ntheory.primetest.is_euler_pseudoprime`
 * @example
 * ```ts
 * import { isEulerPseudoprime } from '@symjs/symjs';
 *
 * isEulerPseudoprime(341, 2); // => True
 * ```
 */
export function isEulerPseudoprime(nIn: IntLike, aIn: IntLike): boolean {
  const [n, a] = [asInt(nIn), asInt(aIn)];
  if (n < 1n) throw new RangeError('n should be an integer greater than 0');
  if (n === 1n) return false;
  if (a === 1n) return n === 2n || n % 2n !== 0n;
  if (n % 2n === 0n) return n === 2n;
  if (gcdN(n, a) !== 1n) throw new RangeError('The two numbers should be relatively prime');
  const r = powmod(a, (n - 1n) / 2n, n);
  return r === 1n || r === n - 1n;
}

/**
 * Tests whether `a**((n - 1)/2)` agrees with the Jacobi symbol modulo the candidate.
 *
 * @param nIn - Candidate integer.
 * @param aIn - Base for the test.
 * @returns Whether the candidate passes the congruence test.
 * @throws RangeError when the candidate or base is outside its permitted range or the two are not
 *   coprime.
 * @see SymPy `sympy.ntheory.primetest.is_euler_jacobi_pseudoprime`
 * @example
 * ```ts
 * import { isEulerJacobiPseudoprime } from '@symjs/symjs';
 *
 * isEulerJacobiPseudoprime(561, 2); // => True
 * ```
 */
export function isEulerJacobiPseudoprime(nIn: IntLike, aIn: IntLike): boolean {
  const [n, a0] = [asInt(nIn), asInt(aIn)];
  if (a0 === 1n) return n === 2n || n % 2n !== 0n;
  const a = prpBase('is_euler_prp', n, a0);
  return typeof a === 'boolean' ? a : powmod(a, n >> 1n, n) === (BigInt(jacobi(a, n)) + n) % n;
}

/** SymPy `_lucas_extrastrong_params(n)`: [D, P, Q] with (D/n) = -1, or [0, 0, 0] when a divisor of n shows. */
function lucasExtrastrongParams(n: bigint): [bigint, bigint, bigint] {
  // a square n has been excluded, so some D has Jacobi symbol -1
  for (let P = 3n; ; P++) {
    const D = P * P - 4n;
    const j = jacobi(D, n);
    if (j === -1) return [D, P, 1n];
    if (j === 0 && D % n !== 0n) return [0n, 0n, 0n];
  }
}

/**
 * Applies the extra-strong Lucas probable-prime test.
 *
 * @param nIn - Candidate integer.
 * @returns Whether the candidate passes the extra-strong Lucas test.
 * @see SymPy `sympy.ntheory.primetest.is_extra_strong_lucas_prp`
 * @example
 * ```ts
 * import { isExtraStrongLucasPrp } from '@symjs/symjs';
 *
 * isExtraStrongLucasPrp(989); // => True
 * ```
 */
export function isExtraStrongLucasPrp(nIn: IntLike): boolean {
  const n = asInt(nIn);
  if (n === 2n) return true;
  if (n < 2n || n % 2n === 0n || isSquare(n)) return false;
  const [D, P, Q] = lucasExtrastrongParams(n);
  if (D === 0n) return false;
  const s = bitScan1(n + 1n);
  const k = (n + 1n) >> BigInt(s);
  const [U, V0] = lucasSequence(n, P, Q, k);
  let V = V0;
  if (U === 0n && (V === 2n || V === n - 2n)) return true;
  for (let i = 1; i < s; i++) {
    if (V === 0n) return true;
    V = (V * V - 2n) % n;
  }
  return false;
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
  if (n <= BigInt(last(sieve.primes))) {
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
    return mr(n, [BigInt(at(MR_BASES_32, Number(h)))]);
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

/** @internal The Lucas-Lehmer test: 2**p - 1 is prime, for an odd prime p. */
export function lucasLehmer(p: number): boolean {
  let v = 4n;
  const m = (1n << BigInt(p)) - 1n;
  for (let i = 0; i < p - 2; i++) v = powmod(v, 2n, m) - 2n;
  return v === 0n;
}

/**
 * Tests whether an integer is a Mersenne prime.
 *
 * @param nIn - Integer to test.
 * @returns Whether the number is a prime of the form `2**p - 1`.
 * @see SymPy `sympy.ntheory.primetest.is_mersenne_prime`
 * @example
 * ```ts
 * import { isMersennePrime } from '@symjs/symjs';
 *
 * isMersennePrime(6); // => False
 * isMersennePrime(127); // => True
 * ```
 */
export function isMersennePrime(nIn: IntLike): boolean {
  // GIMPS verified every exponent below 65 million on September 19, 2023
  return mersennePrimeCheck(asInt(nIn), 65_000_000);
}

/**
 * @internal isMersennePrime with the bound below which every Mersenne
 * prime exponent is known as a parameter (a test reaches the Lucas-Lehmer
 * test with a small exponent).
 */
export function mersennePrimeCheck(n: bigint, verifiedBelow: number): boolean {
  if (n < 1n) return false;
  if ((n & (n + 1n)) !== 0n) return false;
  const p = bitLength(n);
  if (MERSENNE_PRIME_EXPONENTS.includes(p)) return true;
  // 2**p - 1 is composite for a composite p
  if (p < verifiedBelow || !isprime(p)) return false;
  // SymPy raises ValueError on a prime found here to have its exponent added
  // to the known values; it is a Mersenne prime, so the answer is true
  return lucasLehmer(p);
}

/**
 * Tests primality in the ring of Gaussian integers.
 *
 * @param num - Gaussian integer to test.
 * @returns Whether the input is prime in the Gaussian integers.
 * @throws TypeError when the value is not a Gaussian integer.
 * @see SymPy `sympy.ntheory.primetest.is_gaussian_prime`
 */
export function isGaussianPrime(num: ExprLike | bigint): boolean {
  const e = sympify(num);
  let a = 0n;
  let b = 0n;
  const terms = e instanceof Add ? e.args : [e];
  for (const t of terms) {
    if (t instanceof Rational && t.q === 1n) a += t.p;
    else if (t.key === I.key) b += 1n;
    else if (t instanceof Mul && t.args.length === 2 && t.args[0] instanceof Rational && t.args[0].q === 1n && t.args[1]?.key === I.key) b += t.args[0].p;
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
 * Stores a known prime divisor for each integer and evicts least recently used entries when its
 * capacity is reached. Override `getExternal` to supply factors from another source.
 *
 * @see SymPy `sympy.ntheory.factor_.FactorCache`
 * @example
 * ```ts
 * import { FactorCache } from '@symjs/symjs';
 *
 * const cache = new FactorCache();
 * cache.set(15, 5);
 * cache.get(15); // => 5
 * ```
 */
export class FactorCache {
  private cache = new Map<bigint, bigint>();
  private maxsizeValue: number | undefined;

  /**
   * Creates a prime-divisor cache with an optional capacity.
   *
   * @param maxsize - Maximum number of cached entries.
   */
  constructor(maxsize?: number) {
    this.maxsize = maxsize;
  }

  /**
   * The number of cached entries.
   *
   * @returns The current number of entries.
   * @see SymPy `sympy.ntheory.factor_.FactorCache.__len__`
   */
  get size(): number {
    return this.cache.size;
  }

  /**
   * Limits the number of entries retained in the cache.
   *
   * @returns The capacity of the cache; `Infinity` when it is unbounded.
   * @see SymPy `sympy.ntheory.factor_.FactorCache.maxsize`
   */
  get maxsize(): number {
    return this.maxsizeValue ?? Infinity;
  }

  /**
   * Limits the number of entries retained in the cache. An omitted limit leaves its capacity
   * unbounded.
   *
   * @param value - Positive capacity; `Infinity` or `undefined` for an unbounded cache.
   * @throws RangeError when the specified cache size is not positive.
   * @see SymPy `sympy.ntheory.factor_.FactorCache.maxsize`
   */
  set maxsize(value: number | undefined) {
    if (value !== undefined && !(value > 0)) throw new RangeError('maxsize must be None or a non-negative integer.');
    this.maxsizeValue = value === Infinity ? undefined : value;
    if (value !== undefined) this.trim(value);
  }

  private trim(max: number): void {
    // deleting the entry being visited does not disturb the iteration
    for (const k of this.cache.keys()) {
      if (this.cache.size <= max) break;
      this.cache.delete(k);
    }
  }

  /**
   * Checks for a stored factor of the given integer.
   *
   * @param nIn - Integer whose prime divisors are cached.
   * @returns Whether the integer is cached.
   * @see SymPy `sympy.ntheory.factor_.FactorCache.__contains__`
   */
  has(nIn: IntLike): boolean {
    return this.cache.has(asInt(nIn));
  }

  /**
   * Record that factor is a prime factor of n.
   *
   * @param nIn - Integer whose prime divisors are cached.
   * @param factorIn - Known prime divisor of the cache key.
   * @returns The updated cache.
   * @throws RangeError when the proposed factor is not a prime divisor.
   * @see SymPy `sympy.ntheory.factor_.FactorCache.__setitem__`
   */
  set(nIn: IntLike, factorIn: IntLike): this {
    const n = asInt(nIn);
    const factor = asInt(factorIn);
    if (!(factor > 1n && factor <= n && n % factor === 0n && isprime(factor))) throw new RangeError(`${factor} is not a prime factor of ${n}`);
    const old = this.cache.get(n) ?? 0n;
    // an existing entry keeps its place, as in SymPy's OrderedDict
    this.cache.set(n, old > factor ? old : factor);
    if (this.maxsizeValue !== undefined) this.trim(this.maxsizeValue);
    return this;
  }

  /**
   * Removes the cached prime factor of the given integer.
   *
   * @param nIn - Integer whose prime divisors are cached.
   * @returns Whether the entry was removed.
   * @throws RangeError when there is no entry for the integer.
   * @see SymPy `sympy.ntheory.factor_.FactorCache.__delitem__`
   */
  delete(nIn: IntLike): boolean {
    const n = asInt(nIn);
    if (!this.cache.has(n)) throw new RangeError(`${n} does not exist.`);
    return this.cache.delete(n);
  }

  /**
   * Lists the integers for which a factor is cached.
   *
   * @returns An iterator over the cached integers.
   * @see SymPy `sympy.ntheory.factor_.FactorCache.keys`
   */
  keys(): IterableIterator<bigint> {
    return this.cache.keys();
  }

  /**
   * Clears all cached factorizations.
   *
   * @see SymPy `sympy.ntheory.factor_.FactorCache.cache_clear`
   */
  cacheClear(): void {
    this.cache = new Map();
  }

  /**
   * The largest known prime factor of n, or NoMatch.
   *
   * @param nIn - Integer whose prime divisors are cached.
   * @returns The cached factor, or `NoMatch`.
   * @see SymPy `sympy.ntheory.factor_.FactorCache.get`
   */
  get(nIn: IntLike): bigint | NoMatchResult {
    const n = asInt(nIn);
    const ps = sieve.primes;
    if (n <= BigInt(last(ps)) && n >= 0n) {
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
      // the largest factor, which add() cached for n unless a small maxsize
      // already evicted it (where SymPy raises KeyError)
      return factors.reduce((a, b) => (a > b ? a : b));
    }
    return NoMatch;
  }

  /**
   * Retrieves a known prime factor of the given integer.
   *
   * @param nIn - Integer whose prime divisors are cached.
   * @returns The recorded prime divisor.
   * @throws RangeError when there is no entry for the integer.
   * @see SymPy `sympy.ntheory.factor_.FactorCache.__getitem__`
   */
  getItem(nIn: IntLike): bigint {
    const f = this.get(nIn);
    if (isNoMatch(f)) throw new RangeError(`${asInt(nIn)} does not exist.`);
    return f;
  }

  /**
   * Adds the other operand to this value.
   *
   * @param nIn - Integer whose prime divisors are cached.
   * @param factors - Known prime divisors of the cache key.
   * @see SymPy `sympy.ntheory.factor_.FactorCache.add`
   */
  add(nIn: IntLike, factors: readonly bigint[]): void {
    let n = asInt(nIn);
    // decreasing (the sign of y - x; a huge difference becomes an infinity of that sign)
    for (const p of [...factors].sort((x, y) => Number(y - x))) {
      this.set(n, p);
      n = remove(n, p)[0];
    }
  }

  /**
   * Prime factors of n from an external source; override in a subclass (default NoMatch).
   *
   * @param _n - Integer whose prime divisors are cached.
   * @returns External factors, or `NoMatch`.
   * @see SymPy `sympy.ntheory.factor_.FactorCache.get_external`
   */
  getExternal(_n: bigint): bigint[] | NoMatchResult {
    return NoMatch;
  }
}

/**
 * The shared cache of prime divisors, with capacity for 1,000 entries.
 *
 * @see SymPy `sympy.ntheory.factor_.factor_cache`
 * @example
 * ```ts
 * import { factorCache } from '@symjs/symjs';
 *
 * factorCache.set(15, 5);
 * factorCache.get(15); // => 5
 * ```
 */
export const factorCache: FactorCache = new FactorCache(1000);

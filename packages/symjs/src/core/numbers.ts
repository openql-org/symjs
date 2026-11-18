// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Pure bigint helpers (no dependency on expression nodes).
 */

export function babs(a: bigint): bigint {
  return a < 0n ? -a : a;
}

export function gcd(aIn: bigint, bIn: bigint): bigint {
  let a = aIn;
  let b = bIn;
  a = babs(a);
  b = babs(b);
  while (b !== 0n) {
    [a, b] = [b, a % b];
  }
  return a;
}

export function lcm(a: bigint, b: bigint): bigint {
  if (a === 0n || b === 0n) return 0n;
  return babs((a / gcd(a, b)) * b);
}

/** Integer power with non-negative exponent. */
export function ipow(base: bigint, exp: bigint): bigint {
  if (exp < 0n) throw new RangeError('ipow: negative exponent');
  let result = 1n;
  let b = base;
  let e = exp;
  while (e > 0n) {
    if (e & 1n) result *= b;
    b *= b;
    e >>= 1n;
  }
  return result;
}

/** floor(n^(1/k)) for n >= 0, k >= 1. */
/** The number of bits of a positive integer. */
export function bitLength(n: bigint): number {
  const hex = n.toString(16);
  return (hex.length - 1) * 4 + (32 - Math.clz32(parseInt(hex.charAt(0), 16)));
}

export function iroot(n: bigint, k: bigint): bigint {
  if (n < 0n) throw new RangeError('iroot: negative radicand');
  if (n < 2n || k === 1n) return n;
  const bits = bitLength(n);
  if (k >= BigInt(bits)) return 1n;
  // Newton's iteration from x0 = 2**ceil(bits/k) > n^(1/k) decreases to floor(n^(1/k)) and
  // stops there (y >= x); a floating-point guess would overflow beyond 2**1024
  let x = 1n << BigInt(Math.ceil(bits / Number(k)));
  for (;;) {
    // y = ((k-1) x + n / x^(k-1)) / k
    const y = ((k - 1n) * x + n / ipow(x, k - 1n)) / k;
    if (y >= x) return x;
    x = y;
  }
}

const TRIAL_LIMIT = 1n << 16n;

interface TrialChunk { smallest: bigint; product: bigint; divisors: bigint[] }

let chunksOfTrialDivisors: TrialChunk[] | undefined;

/** The trial divisors 6k - 1 and 6k + 1 up to the limit, in chunks with their products. */
function trialChunks(): TrialChunk[] {
  if (chunksOfTrialDivisors) return chunksOfTrialDivisors;
  const chunks: TrialChunk[] = [];
  for (let start = 5n; start <= TRIAL_LIMIT; start += 96n) {
    const divisors: bigint[] = [];
    for (let p = start; p < start + 96n && p <= TRIAL_LIMIT; p += 6n) divisors.push(p, p + 2n);
    chunks.push({ smallest: start, product: divisors.reduce((a, b) => a * b, 1n), divisors });
  }
  chunksOfTrialDivisors = chunks;
  return chunks;
}

/**
 * Factor a positive integer into prime powers.
 * Trial division up to a limit; the remaining cofactor is checked for being a
 * perfect power and otherwise treated as a single (possibly composite) factor.
 */
export function factorInt(nIn: bigint): Map<bigint, bigint> {
  if (nIn <= 0n) throw new RangeError('factorInt: n must be positive');
  if (!(nIn >> 128n)) return trialFactors(nIn);
  // the same large radicands recur while an expression is rebuilt
  const known = largeFactorizations.get(nIn);
  if (known) return new Map(known);
  const factors = trialFactors(nIn);
  if (largeFactorizations.size >= 512) largeFactorizations.clear();
  largeFactorizations.set(nIn, factors);
  return new Map(factors);
}

const largeFactorizations = new Map<bigint, Map<bigint, bigint>>();

function trialFactors(nIn: bigint): Map<bigint, bigint> {
  let n = nIn;
  const out = new Map<bigint, bigint>();
  const push = (p: bigint, e: bigint) => out.set(p, (out.get(p) ?? 0n) + e);
  for (const p of [2n, 3n]) {
    while (n % p === 0n) {
      push(p, 1n);
      n /= p;
    }
  }
  if (n >> 128n) {
    // a large n: one remainder by the product of a chunk of trial divisors tells which of them divide it
    for (const { smallest, product, divisors } of trialChunks()) {
      if (smallest * smallest > n) break;
      let remainder = n % product;
      for (const q of divisors) {
        if (remainder % q !== 0n) continue;
        while (n % q === 0n) {
          push(q, 1n);
          n /= q;
        }
        remainder = n % product;
      }
    }
  } else {
    for (let p = 5n; p <= TRIAL_LIMIT && p * p <= n; p += 6n) {
      for (const q of [p, p + 2n]) {
        while (n % q === 0n) {
          push(q, 1n);
          n /= q;
        }
      }
    }
  }
  if (n > 1n) {
    // detect perfect powers of the remaining cofactor (its prime factors exceed the trial limit, which
    // bounds the exponent by the bits of n over the bits of that limit)
    let base = n;
    let exp = 1n;
    const highest = n > TRIAL_LIMIT * TRIAL_LIMIT ? BigInt(Math.min(64, Math.floor(bitLength(n) / 16))) : 1n;
    for (let k = 2n; k <= highest; k++) {
      const r = iroot(n, k);
      if (r > 1n && ipow(r, k) === n) {
        base = r;
        exp = k;
      }
    }
    push(base, exp);
  }
  return out;
}

const smallPrimes: number[] = [2, 3];
let sieved = 3;

/** The primes up to n (at least), in increasing order. */
function primesUpTo(n: number): number[] {
  for (; sieved < n; sieved += 2) {
    const c = sieved + 2;
    if (smallPrimes.every((p) => p * p > c || c % p !== 0)) smallPrimes.push(c);
  }
  return smallPrimes;
}

const residueModulus = new Map<number, number>();

/** n is a p-th power modulo a small prime q = 1 (mod p): a necessary condition for a p-th power. */
function mayBePower(n: bigint, p: number): boolean {
  let q = residueModulus.get(p);
  if (q === undefined) {
    q = p + 1;
    const isPrime = (c: number): boolean => {
      for (let d = 2; d * d <= c; d++) if (c % d === 0) return false;
      return true;
    };
    while (!isPrime(q)) q += p;
    residueModulus.set(p, q);
  }
  const modulus = BigInt(q);
  let base = n % modulus;
  if (base === 0n) return true;
  let result = 1n;
  for (let e = BigInt((q - 1) / p); e > 0n; e >>= 1n) {
    if (e & 1n) result = (result * base) % modulus;
    base = (base * base) % modulus;
  }
  return result === 1n;
}

/**
 * The base b > 1 and the largest exponent k >= 2 with n = b**k, or undefined
 * when the positive integer n is not a perfect power.
 */
export function perfectPower(n: bigint): [bigint, bigint] | undefined {
  if (n < 4n) return undefined;
  const bits = bitLength(n);
  for (const p of primesUpTo(bits)) {
    if (p > bits) break;
    if (!mayBePower(n, p)) continue;
    const k = BigInt(p);
    const root = iroot(n, k);
    if (root > 1n && ipow(root, k) === n) {
      const inner = perfectPower(root);
      return inner ? [inner[0], inner[1] * k] : [root, k];
    }
  }
  return undefined;
}

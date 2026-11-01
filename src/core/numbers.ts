// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Pure bigint helpers (no dependency on expression nodes).
 */

export function babs(a: bigint): bigint {
  return a < 0n ? -a : a;
}

export function gcd(a: bigint, b: bigint): bigint {
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

/** Floor division for bigints (rounds toward -infinity). */
export function floorDiv(a: bigint, b: bigint): bigint {
  const q = a / b;
  return (a % b !== 0n && (a < 0n) !== (b < 0n)) ? q - 1n : q;
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
export function iroot(n: bigint, k: bigint): bigint {
  if (n < 0n) throw new RangeError('iroot: negative radicand');
  if (n < 2n || k === 1n) return n;
  // Initial guess from floating point, then Newton refinement.
  let x = BigInt(Math.floor(Math.pow(Number(n), 1 / Number(k)))) + 1n;
  if (x < 1n) x = 1n;
  for (;;) {
    // y = ((k-1) x + n / x^(k-1)) / k
    const y = ((k - 1n) * x + n / ipow(x, k - 1n)) / k;
    if (y >= x) break;
    x = y;
  }
  while (ipow(x, k) > n) x -= 1n;
  while (ipow(x + 1n, k) <= n) x += 1n;
  return x;
}

const TRIAL_LIMIT = 1n << 16n;

/**
 * Factor a positive integer into prime powers.
 * Trial division up to a limit; the remaining cofactor is checked for being a
 * perfect power and otherwise treated as a single (possibly composite) factor.
 */
export function factorInt(n: bigint): Map<bigint, bigint> {
  if (n <= 0n) throw new RangeError('factorInt: n must be positive');
  const out = new Map<bigint, bigint>();
  const push = (p: bigint, e: bigint) => out.set(p, (out.get(p) ?? 0n) + e);
  for (const p of [2n, 3n]) {
    while (n % p === 0n) {
      push(p, 1n);
      n /= p;
    }
  }
  for (let p = 5n; p <= TRIAL_LIMIT && p * p <= n; p += 6n) {
    for (const q of [p, p + 2n]) {
      while (n % q === 0n) {
        push(q, 1n);
        n /= q;
      }
    }
  }
  if (n > 1n) {
    // detect perfect powers of the remaining cofactor
    let base = n;
    let exp = 1n;
    for (let k = 2n; k <= 64n; k++) {
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

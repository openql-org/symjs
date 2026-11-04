// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Integer helpers of the number theory module: Python's integer
 * semantics (floor division, non-negative modulo), the gmpy-like functions
 * SymPy uses (sympy.external.ntheory: bit_scan1, remove, isqrt, iroot,
 * gcdext, invert, jacobi, is_square), floating-point logarithms of big
 * integers computed like Python's math module, and the conversion of
 * inputs to bigint (SymPy as_int).
 */

import { at, last } from '../core/guard';
import type { Expr, ExprLike } from '../core/nodes';
import { Fn, Rational } from '../core/nodes';
import { sympify } from '../core/ops';
import { gcd } from '../core/numbers';
import { ceiling as ceilingFn, floor as floorFn } from '../functions/special/special';

/** An integer input: an expression, a JavaScript integer or a bigint. */
export type IntLike = ExprLike | bigint | number;

/** Python's a % m (the result has the sign of m). */
export function pmod(a: bigint, m: bigint): bigint {
  const r = a % m;
  return r !== 0n && (r < 0n) !== (m < 0n) ? r + m : r;
}

/** Python's a // b (rounds toward -infinity). */
export function fdiv(a: bigint, b: bigint): bigint {
  const q = a / b;
  return a % b !== 0n && (a < 0n) !== (b < 0n) ? q - 1n : q;
}

/** Python's divmod(a, b). */
export function divmod(a: bigint, b: bigint): [bigint, bigint] {
  const q = fdiv(a, b);
  return [q, a - q * b];
}

export const babs = (a: bigint): bigint => (a < 0n ? -a : a);

/** int.bit_length(). */
export function bitLength(nIn: bigint): number {
  const n = babs(nIn);
  if (n === 0n) return 0;
  return n.toString(2).length;
}

/** The index of the lowest set bit of |x| (gmpy bit_scan1); -1 for 0. */
export function bitScan1(x: bigint): number {
  if (x === 0n) return -1;
  let n = babs(x);
  let t = 0;
  while ((n & 0xffffffffn) === 0n) {
    n >>= 32n;
    t += 32;
  }
  while ((n & 1n) === 0n) {
    n >>= 1n;
    t++;
  }
  return t;
}

/** (x / f**m, m) with m maximal (gmpy remove); f > 1. */
export function remove(xIn: bigint, f: bigint): [bigint, bigint] {
  if (f < 2n) throw new RangeError('factor must be > 1');
  let x = xIn;
  if (x === 0n) return [0n, 0n];
  if (f === 2n) {
    const b = bitScan1(x);
    return [x >> BigInt(b), BigInt(b)];
  }
  let m = 0n;
  while (x % f === 0n) {
    x /= f;
    m++;
    if (m > 5n) {
      const powList = [f * f];
      while (powList.length > 0) {
        const ff = last(powList);
        if (x % ff === 0n) {
          m += 1n << BigInt(powList.length);
          x /= ff;
          powList.push(ff * ff);
        } else powList.pop();
      }
    }
  }
  return [x, m];
}

/** floor(sqrt(n)) for n >= 0. */
export function isqrt(n: bigint): bigint {
  if (n < 0n) throw new RangeError('isqrt of a negative number');
  if (n < 2n) return n;
  if (n < 1n << 52n) {
    // Number(n) is exact and Math.sqrt correctly rounded; below 2**52 even
    // sqrt(k**2 - 1) stays below k, so the floor is isqrt(n)
    return BigInt(Math.floor(Math.sqrt(Number(n))));
  }
  // Newton iteration from above
  let x = 1n << BigInt(Math.ceil(bitLength(n) / 2));
  for (;;) {
    const y = (x + n / x) >> 1n;
    if (y >= x) return x;
    x = y;
  }
}

/** (isqrt(n), n - isqrt(n)**2). */
export function sqrtrem(n: bigint): [bigint, bigint] {
  const s = isqrt(n);
  return [s, n - s * s];
}

/** n is a perfect square (gmpy is_square). */
export function isSquare(n: bigint): boolean {
  if (n < 0n) return false;
  return sqrtrem(n)[1] === 0n;
}

/** (floor(y**(1/n)), exact) for y >= 0, n >= 1 (gmpy iroot). */
export function iroot(y: bigint, n: bigint): [bigint, boolean] {
  if (y < 0n) throw new RangeError('y must be nonnegative');
  if (n < 1n) throw new RangeError('n must be positive');
  if (y === 0n || y === 1n || n === 1n) return [y, true];
  if (n === 2n) {
    const [x, r] = sqrtrem(y);
    return [x, r === 0n];
  }
  if (n >= BigInt(bitLength(y))) return [1n, false];
  let x: bigint;
  const ex = pyLog2(y) / Number(n);
  if (ex > 50) {
    const shift = BigInt(Math.max(0, Math.floor(ex - 50)));
    x = (BigInt(Math.floor(2 ** (ex - Number(shift)))) + 1n) << shift;
    for (;;) {
      const t = x ** (n - 1n);
      const xprev = x;
      x = ((n - 1n) * x + y / t) / n;
      if (babs(x - xprev) < 2n) break;
    }
  } else x = BigInt(Math.floor(2 ** ex + 0.5));
  let t = x ** n;
  while (t < y) {
    x++;
    t = x ** n;
  }
  while (t > y) {
    x--;
    t = x ** n;
  }
  return [x, t === y];
}

/** (g, x, y) with a*x + b*y = g (sympy.external.ntheory gcdext). */
export function gcdext(aIn: bigint, bIn: bigint): [bigint, bigint, bigint] {
  if (aIn === 0n || bIn === 0n) {
    const g = babs(aIn) || babs(bIn);
    if (g === 0n) return [0n, 0n, 0n];
    return [g, aIn / g, bIn / g];
  }
  const xs = aIn < 0n ? -1n : 1n;
  const ys = bIn < 0n ? -1n : 1n;
  let a = babs(aIn);
  let b = babs(bIn);
  let [x, r] = [1n, 0n];
  let [y, s] = [0n, 1n];
  while (b !== 0n) {
    const [q, c] = divmod(a, b);
    [a, b] = [b, c];
    [x, r] = [r, x - q * r];
    [y, s] = [s, y - q * s];
  }
  return [a, x * xs, y * ys];
}

/** The inverse of x modulo m (Python pow(x, -1, m)); throws when none exists. */
export function invert(x: bigint, m: bigint): bigint {
  const mm = babs(m);
  if (mm === 1n) return 0n;
  const [g, s] = gcdext(pmod(x, mm), mm);
  if (g !== 1n) throw new RangeError('invert() no inverse exists');
  return pmod(s, m);
}

/** Python's pow(b, e, m) (a negative e uses the inverse). */
export function powmod(bIn: bigint, eIn: bigint, m: bigint): bigint {
  if (m === 1n || m === -1n) return 0n;
  let b = pmod(bIn, m);
  let e = eIn;
  if (e < 0n) {
    b = invert(b, m);
    e = -e;
  }
  let r = 1n;
  while (e > 0n) {
    if (e & 1n) r = (r * b) % m;
    e >>= 1n;
    if (e > 0n) b = (b * b) % m;
  }
  return pmod(r, m);
}

/** The gcd of several integers. */
export function gcdN(...xs: bigint[]): bigint {
  let g = 0n;
  for (const x of xs) g = gcd(g, x);
  return g;
}

/** Jacobi symbol (x / y) for odd y > 0 (sympy.external.ntheory jacobi). */
export function jacobi(xIn: bigint, yIn: bigint): number {
  if (yIn <= 0n || yIn % 2n === 0n) throw new RangeError('y should be an odd positive integer');
  let y = yIn;
  let x = pmod(xIn, y);
  if (x === 0n) return y === 1n ? 1 : 0;
  if (y === 1n || x === 1n) return 1;
  if (gcd(x, y) !== 1n) return 0;
  let j = 1;
  while (x !== 0n) {
    while (x % 2n === 0n && x > 0n) {
      x >>= 1n;
      const r = y % 8n;
      if (r === 3n || r === 5n) j = -j;
    }
    [x, y] = [y, x];
    if (x % 4n === 3n && y % 4n === 3n) j = -j;
    x = pmod(x, y);
  }
  return j;
}

// ---------------------------------------------------------------------------
// Python's math.log / math.log2 of integers
// ---------------------------------------------------------------------------

/** (x, e) with n = x * 2**e and x in [0.5, 1), correctly rounded (CPython _PyLong_Frexp). */
function frexpBig(n: bigint): [number, number] {
  const bits = bitLength(n);
  const shift = bits - 60;
  let top = n >> BigInt(shift);
  if ((n & ((1n << BigInt(shift)) - 1n)) !== 0n) top |= 1n;
  return [Number(top) / 2 ** 60, bits];
}

/** Python math.log2(n) for a positive integer (or a number). */
export function pyLog2(n: bigint | number): number {
  if (typeof n === 'number') return Math.log2(n);
  if (bitLength(n) <= 1000) return Math.log2(Number(n));
  const [x, e] = frexpBig(n);
  return Math.log2(x) + e;
}

/** Python math.log(n) for a positive integer (or a number). */
export function pyLog(n: bigint | number): number {
  if (typeof n === 'number') return Math.log(n);
  if (bitLength(n) <= 1000) return Math.log(Number(n));
  const [x, e] = frexpBig(n);
  return Math.log(x) + Math.log(2) * e;
}

/** Python math.log(n, base). */
export function pyLogBase(n: bigint | number, base: bigint | number): number {
  return pyLog(n) / pyLog(base);
}

/** Python round(x) for a float (round half to even), as a number. */
export function pyRound(x: number): number {
  const f = Math.floor(x);
  const d = x - f;
  if (d > 0.5) return f + 1;
  if (d < 0.5) return f;
  return f % 2 === 0 ? f : f + 1;
}

// ---------------------------------------------------------------------------
// conversion of inputs
// ---------------------------------------------------------------------------

/** The integer value of an input (SymPy as_int); throws a TypeError for a non-integer. */
export function asInt(n: IntLike, name = 'value'): bigint {
  if (typeof n === 'bigint') return n;
  if (typeof n === 'number') {
    if (!Number.isInteger(n)) throw new TypeError(`${name} must be an integer, got ${n}`);
    return BigInt(n);
  }
  const e = sympify(n);
  if (e instanceof Rational && e.q === 1n) return e.p;
  throw new TypeError(`${e.toString()} is not an integer`);
}

function exprInt(e: Expr, round: (x: Expr) => Expr): bigint {
  const r = round(e);
  if (r instanceof Rational && r.q === 1n) return r.p;
  throw new TypeError(`${e.toString()} cannot be converted to an integer`);
}

/** as_int(ceiling(n)) (SymPy _as_int_ceiling). */
export function asIntCeiling(n: IntLike): bigint {
  if (typeof n === 'bigint') return n;
  if (typeof n === 'number') return BigInt(Math.ceil(n));
  const e = sympify(n);
  if (e instanceof Rational) return -fdiv(-e.p, e.q);
  return exprInt(e, ceilingFn);
}

/** Python int(n): truncation toward zero. */
export function truncInt(n: IntLike): bigint {
  if (typeof n === 'bigint') return n;
  if (typeof n === 'number') return BigInt(Math.trunc(n));
  const e = sympify(n);
  if (e instanceof Rational) return e.p / e.q;
  const f = exprInt(e, floorFn);
  return f < 0n ? exprInt(e, ceilingFn) : f;
}

/** The expression is an unevaluated factorial(k). */
export const isFactorial = (e: Expr): e is Fn => e instanceof Fn && e.name === 'factorial';

/** A Python-like generator of the product of finite lists (itertools.product). */
export function* product<T>(lists: readonly (readonly T[])[]): Generator<T[], void, undefined> {
  if (lists.length === 0) {
    yield [];
    return;
  }
  if (lists.some((l) => l.length === 0)) return;
  const idx: number[] = lists.map(() => 0);
  for (;;) {
    yield idx.map((i, k) => at(at(lists, k), i));
    let k = lists.length - 1;
    while (k >= 0) {
      const v = at(idx, k) + 1;
      idx[k] = v;
      if (v < at(lists, k).length) break;
      idx[k] = 0;
      k--;
    }
    if (k < 0) return;
  }
}

/** The product of bigints. */
export function prod(xs: Iterable<bigint>): bigint {
  let p = 1n;
  for (const x of xs) p *= x;
  return p;
}

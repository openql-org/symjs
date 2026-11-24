// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Number utilities compatible with SymPy: exact rationals from
 * floats and decimal strings, integer_log, Integer truncation and the
 * range syntax of symbols().
 */

import { type Constant, type Expr, Float, Rational, impl } from './nodes';
import { bitLength, normalize, toRational } from '../numeric/mpf';
import { numCmp } from './num';
import { isPositive } from './assumptions';
import { at, pair } from './guard';
import { NoMatch } from './truth';
import type { NoMatchResult } from './truth';

type MpfTuple = readonly [sign: number, mantissa: bigint, exponent: bigint, bits: number];

/**
 * Normalize an mpf tuple to binary precision, preserving the special values.
 *
 * @param tuple - The raw binary floating-point tuple.
 * @param precision - The precision in bits.
 * @returns The normalized and rounded floating-point tuple.
 * @see SymPy `sympy.core.numbers.mpf_norm`
 */
export function mpfNorm(tuple: MpfTuple, precision: number): MpfTuple {
  const [sign, mantissa, exponent, bits] = tuple;
  if (mantissa === 0n) return bits === 0 ? [0, 0n, 0n, 0] : tuple;
  const rounded = normalize(sign === 0 ? mantissa : -mantissa, exponent, precision);
  const magnitude = rounded.man < 0n ? -rounded.man : rounded.man;
  return [sign, magnitude, rounded.exp, bitLength(magnitude)];
}

/** Exact rational value of a double (SymPy Rational(0.2) = 3602879701896397/18014398509481984). */
export function rationalFromFloat(v: number | Float): Rational {
  if (v instanceof Float) return Rational.of(...toRational(v.mpf));
  if (!Number.isFinite(v)) throw new RangeError('rationalFromFloat: non-finite value');
  if (Number.isInteger(v)) return Rational.of(BigInt(v));
  const buf = new DataView(new ArrayBuffer(8));
  buf.setFloat64(0, v);
  const hi = buf.getUint32(0);
  const lo = buf.getUint32(4);
  const sign = hi >>> 31 ? -1n : 1n;
  const expBits = (hi >>> 20) & 0x7ff;
  let mant = (BigInt(hi & 0xfffff) << 32n) | BigInt(lo);
  let e: number;
  if (expBits === 0) e = -1074;
  else {
    mant |= 1n << 52n;
    e = expBits - 1075;
  }
  // a non-integer double has a negative binary exponent
  return Rational.of(sign * mant, 1n << BigInt(-e));
}

/** Exact rational from a decimal string, e.g. '1.23' -> 123/100, '1e-2' -> 1/100, '1e-2/3.2' -> 1/320. */
export function rationalFromString(s0: string): Rational {
  const s = s0.trim().replace(/ /g, '');
  const slash = s.indexOf('/');
  if (slash >= 0) {
    const a = rationalFromString(s.slice(0, slash));
    const b = rationalFromString(s.slice(slash + 1));
    return Rational.of(a.p * b.q, a.q * b.p);
  }
  const m = /^([+-]?)(\d*)(?:\.(\d*))?(?:[eE]([+-]?\d+))?$/.exec(s.replace(/_/g, ''));
  if (!m || (m[2] === '' && (m[3] ?? '') === '')) throw new SyntaxError(`Invalid number: ${s0}`);
  const intPart = m[2] || '0';
  const frac = m[3] ?? '';
  const exp = Number(m[4] ?? '0') - frac.length;
  let num = BigInt(intPart + frac);
  if (m[1] === '-') num = -num;
  return exp >= 0 ? Rational.of(num * 10n ** BigInt(exp)) : Rational.of(num, 10n ** BigInt(-exp));
}

/**
 * (e, exact) with b**e <= |n| and exact when b**e == n.
 *
 * @param n - The integer argument or logarithm base, respectively.
 * @param b - The integer argument or logarithm base, respectively.
 * @returns The integer logarithm and whether the argument is an exact power.
 * @throws RangeError when the argument is zero or the base has magnitude less than two.
 * @remarks SymPy returns the tuple `(3, True)` for the example below.
 * @see SymPy `sympy.core.intfunc.integer_log`
 * @example
 * ```ts
 * import { integerLog } from '@symjs/symjs';
 *
 * integerLog(8n, 2n); // => [3, True]
 * ```
 */
export function integerLog(n: bigint, b: bigint): [bigint, boolean] {
  if (b < 0n) {
    const [e, t] = integerLog(n < 0n ? -n : n, -b);
    return [e, t && e % 2n === (n < 0n ? 1n : 0n)];
  }
  if (b <= 1n) throw new RangeError('integer_log: base must be > 1');
  if (n < 0n) {
    if (b !== 2n) return [0n, false];
    const [e] = integerLog(-n, b);
    return [e, false];
  }
  if (n === 0n) throw new RangeError('integer_log: n must be nonzero');
  let e = 0n;
  let p = 1n;
  while (p * b <= n) {
    p *= b;
    e++;
  }
  return [e, p === n];
}

/**
 * Expand SymPy's symbol range syntax: 'x:3' -> x0 x1 x2, 'x5:10', 'a:d',
 * ':c', 'x(:c)' -> xa xb xc, 'x:2(1:3)' -> x01 x02 x11 x12.
 */
export function expandSymbolNames(spec: string): string[] {
  // a port of the name parsing in SymPy symbols(): escaped separators (\, \: \ ),
  // comma/whitespace splitting and ranges such as x:3, a:d, x(:2)(:3)
  const literals: [string, string][] = [];
  let names = spec;
  let marker = 0xe000;
  for (const splitter of ['\\,', '\\:', '\\ ']) {
    if (names.includes(splitter)) {
      while (names.includes(String.fromCharCode(marker))) marker++;
      const c = String.fromCharCode(marker++);
      names = names.split(splitter).join(c);
      literals.push([c, splitter.slice(1)]);
    }
  }
  const literal = (t: string) => literals.reduce((acc, [c, l]) => acc.split(c).join(l), t);
  names = names.trim();
  if (names.endsWith(',')) names = names.slice(0, -1).trimEnd();
  if (!names) throw new RangeError('no symbols given');
  if (names.split(',').some((name) => !name.trim())) throw new RangeError('missing symbol');
  const parts = names
    .split(',')
    .map((n) => n.trim())
    .flatMap((n) => n.split(/\s+/).filter((t) => t.length));
  const out: string[] = [];
  for (const name of parts) {
    if (!name.includes(':')) {
      out.push(literal(name));
      continue;
    }
    const split = name.split(/([0-9]*:[0-9]+|[a-zA-Z]?:[a-zA-Z])/);
    // remove one layer of parentheses around ranges
    for (let i = 1; i < split.length - 1; i++) {
      if (at(split, i).includes(':') && split[i] !== ':' && at(split, i - 1).endsWith('(') && at(split, i + 1).startsWith(')')) {
        split[i - 1] = at(split, i - 1).slice(0, -1);
        split[i + 1] = at(split, i + 1).slice(1);
      }
    }
    const lists: string[][] = [];
    let empty = false;
    for (const t of split) {
      if (t.includes(':')) {
        if (t.endsWith(':')) throw new SyntaxError('missing end range');
        const [a, b] = pair(t.split(':'));
        if (/[0-9]$/.test(b)) {
          const lo = a ? Number(a) : 0;
          lists.push(Array.from({ length: Math.max(0, Number(b) - lo) }, (_, k) => String(lo + k)));
        } else {
          const letters = 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ';
          const lo = letters.indexOf(a || 'a');
          const hi = letters.indexOf(b);
          lists.push(Array.from({ length: Math.max(0, hi - lo + 1) }, (_, k) => at(letters, lo + k)));
        }
        if (!at(lists, lists.length - 1).length) {
          empty = true;
          break;
        }
      } else lists.push([t]);
    }
    if (empty) continue;
    let acc = [''];
    for (const vals of lists) acc = acc.flatMap((x) => vals.map((v) => x + v));
    out.push(...acc.map(literal));
  }
  return out;
}
impl.rationalFromFloat = rationalFromFloat;

const babs = (n: bigint): bigint => (n < 0n ? -n : n);

/**
 * Greatest common divisor of integers (SymPy igcd).
 *
 * @param xs - The operands, in order.
 * @returns The greatest common divisor.
 * @throws RangeError when an argument is not an integer.
 * @see SymPy `sympy.core.intfunc.igcd`
 * @example
 * ```ts
 * import { igcd } from '@symjs/symjs';
 *
 * igcd(12n, 18n); // => 6
 * ```
 */
export function igcd(...xs: bigint[]): bigint {
  if (xs.some((x) => typeof x !== 'bigint')) throw new RangeError('igcd: expected integers');
  let g = 0n;
  for (let x of xs) {
    x = babs(x);
    let a = g;
    while (x) [a, x] = [x, a % x];
    g = a;
  }
  return g;
}

/**
 * Least common multiple of integers (SymPy ilcm).
 *
 * @param xs - The operands, in order.
 * @returns The least common multiple.
 * @see SymPy `sympy.core.intfunc.ilcm`
 * @example
 * ```ts
 * import { ilcm } from '@symjs/symjs';
 *
 * ilcm(12n, 18n); // => 36
 * ```
 */
export function ilcm(...xs: bigint[]): bigint {
  let l = 1n;
  for (const x of xs) {
    if (x === 0n) return 0n;
    l = babs((l / igcd(l, x)) * x);
  }
  return l;
}

/**
 * [x, y, g] with x*a + y*b = g = gcd(a, b), from the extended
 * Euclidean algorithm (x and y are those SymPy gives).
 *
 * @param aIn - One of the two integers.
 * @param bIn - One of the two integers.
 * @returns The two Bézout coefficients followed by the greatest common divisor.
 * @remarks SymPy returns the tuple `(-1, 1, 1)` for the example below.
 * @see SymPy `sympy.core.intfunc.igcdex`
 * @example
 * ```ts
 * import { igcdex } from '@symjs/symjs';
 *
 * igcdex(2n, 3n); // => [-1, 1, 1]
 * ```
 */
export function igcdex(aIn: bigint, bIn: bigint): [bigint, bigint, bigint] {
  if (aIn === 0n && bIn === 0n) return [0n, 0n, 0n];
  if (aIn === 0n) return [0n, bIn < 0n ? -1n : 1n, babs(bIn)];
  if (bIn === 0n) return [aIn < 0n ? -1n : 1n, 0n, babs(aIn)];
  const xSign = aIn < 0n ? -1n : 1n;
  const ySign = bIn < 0n ? -1n : 1n;
  let [a, b] = [babs(aIn), babs(bIn)];
  let [x, y, r, s] = [1n, 0n, 0n, 1n];
  while (b) {
    const q = a / b;
    [a, b, r, s, x, y] = [b, a % b, x - q * r, y - q * s, r, s];
  }
  return [x * xSign, y * ySign, a];
}

/**
 * floor(sqrt(n)) of a nonnegative integer.
 *
 * @param value - The value to examine.
 * @returns The integer part of the square root.
 * @throws RangeError when the radicand is negative.
 * @see SymPy `sympy.core.intfunc.isqrt`
 * @example
 * ```ts
 * import { isqrt } from '@symjs/symjs';
 *
 * isqrt(15n); // => 3
 * ```
 */
export function isqrt(value: bigint | Rational | Float): bigint {
  let n: bigint;
  if (value instanceof Rational) {
    if (value.p < 0n) throw new RangeError('n must be nonnegative');
    n = value.p / value.q;
  } else if (value instanceof Float) {
    if (value.mpf.man < 0n) throw new RangeError('n must be nonnegative');
    n = value.mpf.exp >= 0n ? value.mpf.man << value.mpf.exp : value.mpf.man >> -value.mpf.exp;
  } else n = value;
  if (n < 0n) throw new RangeError('n must be nonnegative');
  return integerNthroot(n, 2)[0];
}

/**
 * (floor(y**(1/n)), exact) for nonnegative integers (SymPy integer_nthroot).
 *
 * @param y - The nonnegative radicand.
 * @param n - The root degree.
 * @returns The floor of the root and whether the root is exact.
 * @throws RangeError when the radicand is negative or the degree is not a positive integer.
 * @remarks SymPy returns the tuple `(4, True)` for the example below.
 * @see SymPy `sympy.core.intfunc.integer_nthroot`
 * @example
 * ```ts
 * import { integerNthroot } from '@symjs/symjs';
 *
 * integerNthroot(16n, 2); // => [4, True]
 * ```
 */
export function integerNthroot(y: bigint, n: number | bigint): [bigint, boolean] {
  if (!(n > 0) || typeof n === 'number' && !Number.isInteger(n)) throw new RangeError('integer_nthroot: n must be positive');
  if (y < 0n) throw new RangeError('integer_nthroot: y must be nonnegative');
  if (y < 2n) return [y, true];
  if (n >= y.toString(2).length) return [1n, false];
  const N = BigInt(n);
  let x = 1n << BigInt(Math.ceil(y.toString(2).length / Number(n)) + 1);
  for (;;) {
    const z = ((N - 1n) * x + y / x ** (N - 1n)) / N;
    if (z >= x) break;
    x = z;
  }
  // Newton's iteration from above stops at floor(y**(1/n))
  return [x, x ** N === y];
}

/**
 * Number of trailing zero bits (SymPy trailing).
 *
 * @param nIn - The integer whose trailing zero bits to count.
 * @returns The number of trailing zero bits.
 * @see SymPy `sympy.core.intfunc.trailing`
 * @example
 * ```ts
 * import { trailing } from '@symjs/symjs';
 *
 * trailing(24n); // => 3
 * ```
 */
export function trailing(nIn: bigint): number {
  let n = nIn;
  n = babs(n);
  if (n === 0n) return 0;
  let k = 0;
  while ((n & 1n) === 0n) {
    n >>= 1n;
    k++;
  }
  return k;
}

/**
 * Number of digits of |n| in the given base (SymPy num_digits).
 *
 * @param n - The index.
 * @param base - The integer base.
 * @returns The number of digits in the chosen base.
 * @throws RangeError when the base is not an integer greater than one.
 * @see SymPy `sympy.core.intfunc.num_digits`
 * @example
 * ```ts
 * import { numDigits } from '@symjs/symjs';
 *
 * numDigits(12345n); // => 5
 * ```
 */
export function numDigits(n: bigint, base = 10): number {
  if (base < 0) throw new RangeError('num_digits: base must be int greater than 1');
  if (n === 0n) return 1;
  if (base <= 1) throw new RangeError('num_digits: base must be 2 or more');
  // Number#toString covers radices 2..36; larger bases count by integer logarithm
  if (base <= 36) return babs(n).toString(base).length;
  return 1 + Number(integerLog(babs(n), BigInt(base))[0]);
}

/**
 * Inverse of a modulo m (SymPy mod_inverse); for non-integers 1/a when m > 1.
 *
 * @param a - The first operand.
 * @param m - The modulus.
 * @returns The multiplicative inverse modulo the modulus.
 * @throws TypeError when an argument is nonnumeric.
 * @throws RangeError when no inverse exists.
 * @see SymPy `sympy.core.intfunc.mod_inverse`
 * @example
 * ```ts
 * import { ex, modInverse } from '@symjs/symjs';
 *
 * modInverse(ex`2/7`, ex`5/2`); // => 7/2
 * ```
 */
export function modInverse(a: Rational, m: Rational): Rational;
export function modInverse(a: Expr, m: Expr): Expr;
export function modInverse(a: Expr, m: Expr): Expr {
  if (!(a instanceof Rational && m instanceof Rational)) {
    if (!a.isNumber || !m.isNumber) throw new TypeError('mod_inverse requires numeric arguments');
    if (m instanceof Rational || m instanceof Float ? numCmp(m, Rational.of(1)) > 0 : isPositive(m.sub(1)) === true) return a.pow(-1);
    throw new RangeError('mod_inverse: inverse does not exist');
  }
  if (a.isInteger && m.isInteger) {
    // no inverse modulo 1 or -1 (SymPy); the result has the sign of m (Python's x % m)
    if (babs(m.p) === 1n) throw new RangeError('mod_inverse: inverse does not exist');
    let [r0, r1] = [a.p, m.p];
    let [s0, s1] = [1n, 0n];
    while (r1) {
      const q = r0 / r1;
      [r0, r1] = [r1, r0 - q * r1];
      [s0, s1] = [s1, s0 - q * s1];
    }
    if (babs(r0) !== 1n) throw new RangeError('mod_inverse: inverse does not exist');
    let c = (s0 * r0) % m.p;
    if ((c < 0n) !== (m.p < 0n)) c += m.p;
    return Rational.of(c);
  }
  if (m.p > m.q) return Rational.of(a.q, a.p);
  throw new RangeError('mod_inverse: inverse does not exist');
}

/**
 * Closest rational with denominator at most maxDen (Python Fraction.limit_denominator).
 *
 * @param r - The rational number to approximate.
 * @param maxDen - The largest allowed denominator.
 * @returns The closest rational with a denominator within the bound.
 * @see SymPy `sympy.core.numbers.Rational.limit_denominator`
 * @example
 * ```ts
 * import { Rational, limitDenominator } from '@symjs/symjs';
 *
 * limitDenominator(Rational.of(22, 7), 5n); // => 16/5
 * ```
 */
export function limitDenominator(r: Rational, maxDen: bigint): Rational {
  if (r.q <= maxDen) return r;
  let [p0, q0, p1, q1] = [0n, 1n, 1n, 0n];
  let [n, d] = [r.p, r.q];
  for (;;) {
    const a = n >= 0n ? n / d : -((-n + d - 1n) / d);
    const q2 = q0 + a * q1;
    if (q2 > maxDen) break;
    [p0, q0, p1, q1] = [p1, q1, p0 + a * p1, q2];
    [n, d] = [d, n - a * d];
  }
  const k = (maxDen - q0) / q1;
  const b1 = Rational.of(p0 + k * p1, q0 + k * q1);
  const b2 = Rational.of(p1, q1);
  const dist = (x: Rational) => {
    const num = x.p * r.q - r.p * x.q;
    return Rational.of(num < 0n ? -num : num, x.q * r.q);
  };
  const d1 = dist(b1);
  const d2 = dist(b2);
  return d2.p * d1.q <= d1.p * d2.q ? b2 : b1;
}

/**
 * Whether a literal number has no fractional part, without symbolic inference.
 *
 * @param value - The value to examine.
 * @returns True when the numeric value represents an integer.
 * @see SymPy `sympy.core.numbers.int_valued`
 */
export function intValued(value: unknown): boolean {
  if (typeof value === 'bigint') return true;
  if (typeof value === 'number') return Number.isInteger(value);
  if (value instanceof Rational) return value.q === 1n;
  if (value instanceof Float) return value.mpf.man === 0n || value.mpf.exp >= 0n;
  return false;
}

/**
 * Greatest common divisor using Lehmer's leading-digit quotient batches.
 *
 * @param aIn - One of the two integers.
 * @param bIn - One of the two integers.
 * @returns The greatest common divisor.
 * @see SymPy `sympy.core.intfunc.igcd_lehmer`
 */
export function igcdLehmer(aIn: bigint, bIn: bigint): bigint {
  let a = babs(aIn), b = babs(bIn);
  if (a < b) [a, b] = [b, a];
  while (a.toString(2).length > 60 && b !== 0n) {
    const shift = BigInt(a.toString(2).length - 60);
    let x = a >> shift, y = b >> shift;
    let A = 1n, B = 0n, C = 0n, D = 1n;
    for (;;) {
      if (y + C <= 0n) break;
      let q = (x + A) / (y + C);
      let remainder = x - q * y;
      const nextB = B - q * D;
      if (remainder + nextB < 0n) break;
      [x, y] = [y, remainder];
      [A, B, C, D] = [C, D, A - q * C, nextB];
      if (y + D <= 0n) break;
      q = (x + B) / (y + D);
      remainder = x - q * y;
      const nextA = A - q * C;
      if (remainder + nextA < 0n) break;
      [x, y] = [y, remainder];
      [A, B, C, D] = [C, D, nextA, B - q * D];
    }
    if (B === 0n) [a, b] = [b, a % b];
    else [a, b] = [A * a + B * b, C * a + D * b];
  }
  return igcd(a, b);
}

/**
 * Proven enclosing intervals for SymPy's real number symbols.
 *
 * @param value - The symbolic number constant to enclose.
 * @param numberClass - The number class for the bounding values.
 * @returns The matching result, or `NoMatch` when the required form is absent.
 * @see SymPy `sympy.core.numbers.Pi.approximation_interval`
 */
export function approximationInterval(value: Constant, numberClass: 'Integer' | 'Rational' = 'Integer'): readonly [Rational, Rational] | NoMatchResult {
  if (numberClass === 'Rational') {
    switch (value.name) {
      case 'pi': return [Rational.of(223, 71), Rational.of(22, 7)];
      case 'EulerGamma': return [Rational.of(1, 2), Rational.of(3, 5)];
      case 'Catalan': return [Rational.of(9, 10), Rational.of(1)];
      default: return NoMatch;
    }
  }
  switch (value.name) {
    case 'pi': return [Rational.of(3), Rational.of(4)];
    case 'E': return [Rational.of(2), Rational.of(3)];
    case 'GoldenRatio':
    case 'TribonacciConstant': return [Rational.of(1), Rational.of(2)];
    case 'EulerGamma':
    case 'Catalan': return [Rational.of(0), Rational.of(1)];
    default: return NoMatch;
  }
}

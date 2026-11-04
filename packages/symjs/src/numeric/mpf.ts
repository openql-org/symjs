// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Arbitrary-precision binary floating point (a port of the parts of
 * mpmath's libmpf that SymPy relies on).
 *
 * A value is `man * 2**exp` with a signed bigint mantissa and, as in mpmath,
 * an unbounded integer (bigint) exponent, so exp(2**200) and its reciprocal
 * are ordinary values. Normalized values have an odd mantissa (or are
 * exactly zero). All rounding is round-half-to-even, like mpmath's
 * `round_nearest`.
 */

import { at, pair } from '../core/guard';

export interface Mpf {
  readonly man: bigint;
  readonly exp: bigint;
}

export const ZERO: Mpf = { man: 0n, exp: 0n };
export const ONE: Mpf = { man: 1n, exp: 0n };

/** A bigint exponent from a number or bigint. */
const big = (e: number | bigint): bigint => (typeof e === 'bigint' ? e : BigInt(e));

const babs = (n: bigint): bigint => (n < 0n ? -n : n);

/** Number of bits of a non-negative safe integer. */
function bitLengthSmall(x: number): number {
  const hi = Math.floor(x / 0x100000000);
  return hi ? 64 - Math.clz32(hi) : 32 - Math.clz32(x);
}

/** Number of bits of |n| (0 for 0). */
export function bitLength(nIn: bigint): number {
  const n = nIn < 0n ? -nIn : nIn;
  if (n <= 0x1fffffffffffffn) return bitLengthSmall(Number(n));
  const x = Number(n);
  if (x === Infinity) {
    const s = n.toString(16);
    return (s.length - 1) * 4 + (32 - Math.clz32(parseInt(s.charAt(0), 16)));
  }
  // log2 of the nearest double is within one of the exact floor(log2 n); the shift settles it
  const k = Math.floor(Math.log2(x)) - 1;
  return k + bitLengthSmall(Number(n >> BigInt(k)));
}

/** Number of trailing zero bits of n != 0. */
function trailingZeros(n: bigint): number {
  return bitLength(n & -n) - 1;
}

/** Strip trailing zero bits without rounding. */
function strip(man: bigint, exp: bigint): Mpf {
  if (man === 0n) return ZERO;
  const tz = trailingZeros(man);
  if (!tz) return { man, exp };
  const t = BigInt(tz);
  return { man: man >> t, exp: exp + t };
}

/**
 * Round man*2**exp to prec bits (half to even). `sticky` marks that the
 * true value is slightly larger in magnitude than man*2**exp (lost bits).
 */
export function normalize(man: bigint, expIn: number | bigint, prec: number, sticky = false): Mpf {
  let exp = big(expIn);
  if (man === 0n) return ZERO;
  const neg = man < 0n;
  let m = neg ? -man : man;
  const bc = bitLength(m);
  if (bc > prec) {
    const n = bc - prec;
    const N = BigInt(n);
    const t = m >> (N - 1n);
    const half = t & 1n;
    const rest = (m & ((1n << (N - 1n)) - 1n)) !== 0n || sticky;
    m = t >> 1n;
    if (half && (rest || (m & 1n))) m += 1n;
    exp += N;
  }
  const r = strip(m, exp);
  return neg ? { man: -r.man, exp: r.exp } : r;
}

export function fromInt(n: bigint, prec?: number): Mpf {
  return prec === undefined ? strip(n, 0n) : normalize(n, 0n, prec);
}

/** Exact value of a JS double. */
export function fromNumber(v: number): Mpf {
  if (!Number.isFinite(v)) throw new RangeError('fromNumber: non-finite value');
  if (v === 0) return ZERO;
  const buf = new DataView(new ArrayBuffer(8));
  buf.setFloat64(0, v);
  const hi = buf.getUint32(0);
  const lo = buf.getUint32(4);
  const expBits = (hi >>> 20) & 0x7ff;
  let mant = (BigInt(hi & 0xfffff) << 32n) | BigInt(lo);
  let e: bigint;
  if (expBits === 0) e = -1074n;
  else {
    mant |= 1n << 52n;
    e = BigInt(expBits - 1075);
  }
  return strip(hi >>> 31 ? -mant : mant, e);
}

/** p/q rounded to prec bits. */
export function fromRational(pIn: bigint, qIn: bigint, prec: number): Mpf {
  let p = pIn;
  let q = qIn;
  if (q < 0n) {
    p = -p;
    q = -q;
  }
  if (p === 0n) return ZERO;
  const shift = Math.max(0, prec + 3 + bitLength(q) - bitLength(p));
  const n = babs(p) << BigInt(shift);
  const quo = n / q;
  const rem = n % q;
  const r = normalize(quo, -BigInt(shift), prec, rem !== 0n);
  return p < 0n ? neg(r) : r;
}

export function neg(a: Mpf): Mpf {
  return { man: -a.man, exp: a.exp };
}

export function abs(a: Mpf): Mpf {
  return a.man < 0n ? neg(a) : a;
}

export const isZero = (a: Mpf): boolean => a.man === 0n;
export const sign = (a: Mpf): number => (a.man > 0n ? 1 : a.man < 0n ? -1 : 0);

/**
 * Exponent of the leading bit plus one: |a| in [2**(mag-1), 2**mag), as a
 * number (approximate when it is beyond 2**53; use magExact there).
 */
export function mag(a: Mpf): number {
  return a.man === 0n ? -Infinity : Number(a.exp) + bitLength(a.man);
}

/** mag of a != 0 as an exact bigint. */
export function magExact(a: Mpf): bigint {
  return a.exp + BigInt(bitLength(a.man));
}

export function round(a: Mpf, prec: number): Mpf {
  return normalize(a.man, a.exp, prec);
}

export function add(aIn: Mpf, bIn: Mpf, prec?: number): Mpf {
  let a = aIn;
  let b = bIn;
  if (a.man === 0n) return prec === undefined ? b : round(b, prec);
  if (b.man === 0n) return prec === undefined ? a : round(a, prec);
  if (a.exp < b.exp) [a, b] = [b, a];
  // a has the larger exponent; check whether b is far below a's precision
  if (prec !== undefined) {
    const t = BigInt(Math.max(0, prec + 4 - bitLength(a.man)) + 2);
    if (magExact(b) < a.exp - t) {
      const man = (a.man << t) + (b.man < 0n ? -1n : 1n);
      return normalize(man, a.exp - t, prec);
    }
  }
  const man = (a.man << (a.exp - b.exp)) + b.man;
  return prec === undefined ? strip(man, b.exp) : normalize(man, b.exp, prec);
}

export function sub(a: Mpf, b: Mpf, prec?: number): Mpf {
  return add(a, neg(b), prec);
}

export function mul(a: Mpf, b: Mpf, prec?: number): Mpf {
  const man = a.man * b.man;
  return prec === undefined ? strip(man, a.exp + b.exp) : normalize(man, a.exp + b.exp, prec);
}

export function mulInt(a: Mpf, n: bigint, prec?: number): Mpf {
  return mul(a, { man: n, exp: 0n }, prec);
}

/** Multiply by 2**k exactly. */
export function ldexp(a: Mpf, k: number | bigint): Mpf {
  return a.man === 0n ? a : { man: a.man, exp: a.exp + big(k) };
}

export function div(a: Mpf, b: Mpf, prec: number): Mpf {
  if (b.man === 0n) throw new RangeError('mpf division by zero');
  if (a.man === 0n) return ZERO;
  const shift = Math.max(0, prec + 3 + bitLength(b.man) - bitLength(a.man));
  const n = babs(a.man) << BigInt(shift);
  const d = babs(b.man);
  const quo = n / d;
  const rem = n % d;
  const r = normalize(quo, a.exp - b.exp - BigInt(shift), prec, rem !== 0n);
  return (a.man < 0n) !== (b.man < 0n) ? neg(r) : r;
}

/**
 * Integer square root with remainder: [s, n - s**2] where s = floor(sqrt(n)),
 * by Zimmermann's divide-and-conquer SqrtRem (Brent & Zimmermann, Modern
 * Computer Arithmetic, Algorithm 1.12) on binary digits: the square root of
 * the top half gives the top half of the root, one division by twice it gives
 * the next quarter of the bits, and a single correction step fixes the result.
 * It costs a few multiplications of the size of n, so large roots (the
 * constants at high precision) do not pay for a Newton iteration at full
 * precision per step.
 */
export function sqrtrem(n: bigint): [bigint, bigint] {
  if (n < 0n) throw new RangeError('isqrt of negative');
  if (n < 0x1000000000000n) {
    // n < 2**48: the double square root is within 2**-28 of the exact root,
    // which is at least 2**-25 below the next integer, so the floor is exact
    const s = BigInt(Math.floor(Math.sqrt(Number(n))));
    return [s, n - s * s];
  }
  // n = a3 2**(3l) + a2 2**(2l) + a1 2**l + a0 with a3 >= 2**l
  const l = (bitLength(n) - 1) >> 2;
  const bl = BigInt(l);
  const mask = (1n << bl) - 1n;
  const [s1, r1] = sqrtrem(n >> (2n * bl));
  const num = (r1 << bl) + ((n >> bl) & mask);
  const den = s1 << 1n;
  const q = num / den;
  const u = num - q * den;
  let s = (s1 << bl) + q;
  let r = (u << bl) + (n & mask) - q * q;
  if (r < 0n) {
    r += 2n * s - 1n;
    s -= 1n;
  }
  return [s, r];
}

/** Integer square root floor(sqrt(n)). */
export function isqrt(n: bigint): bigint {
  return sqrtrem(n)[0];
}

export function sqrt(a: Mpf, prec: number): Mpf {
  if (a.man < 0n) throw new RangeError('mpf sqrt of negative');
  if (a.man === 0n) return ZERO;
  // make the exponent even and the mantissa large enough
  let shift = BigInt(Math.max(0, 2 * prec + 4 - bitLength(a.man)));
  if ((a.exp - shift) & 1n) shift++;
  const n = a.man << shift;
  const [r, rem] = sqrtrem(n);
  return normalize(r, (a.exp - shift) / 2n, prec, rem !== 0n);
}

/** Compare a and b (mpmath mpf_cmp: by sign and magnitude first, so huge exponents are not shifted). */
export function cmp(a: Mpf, b: Mpf): number {
  const sa = sign(a);
  const sb = sign(b);
  if (sa !== sb || sa === 0) return Math.sign(sa - sb);
  const ma = magExact(a);
  const mb = magExact(b);
  if (ma !== mb) return ma > mb ? sa : -sa;
  return sign(sub(a, b));
}

/** Integer power (exact when cheap, otherwise with guard bits). */
export function powInt(a: Mpf, n: bigint, prec: number): Mpf {
  if (n === 0n) return ONE;
  if (n < 0n) return div(ONE, powInt(a, -n, prec + 20), prec);
  if (bitLength(a.man) * Number(n) < 4 * prec + 2000) {
    return normalize(a.man ** n, a.exp * n, prec);
  }
  const wp = prec + 10 + bitLength(n) * 2;
  let r = ONE;
  let b = a;
  let k = n;
  while (k > 0n) {
    if (k & 1n) r = mul(r, b, wp);
    k >>= 1n;
    if (k) b = mul(b, b, wp);
  }
  return round(r, prec);
}

/** Nearest JS double (+-Infinity or +-0 beyond its range). */
export function toNumber(a: Mpf): number {
  if (a.man === 0n) return 0;
  const r = normalize(a.man, a.exp, 53);
  let v = Number(r.man);
  if (r.exp > 1100n || r.exp < -1200n) return r.exp > 0n ? v * Infinity : v * 0;
  let e = Number(r.exp);
  while (e > 0) {
    const k = Math.min(e, 1000);
    v *= 2 ** k;
    e -= k;
  }
  while (e < 0) {
    const k = Math.min(-e, 1000);
    v /= 2 ** k;
    e += k;
  }
  return v;
}

/** Floor to an integer. */
export function floor(a: Mpf): bigint {
  if (a.exp >= 0n) return a.man << a.exp;
  return a.man >> -a.exp;
}

/** Exact rational (p, q). */
export function toRational(a: Mpf): [bigint, bigint] {
  if (a.exp >= 0n) return [a.man << a.exp, 1n];
  return [a.man, 1n << -a.exp];
}

/** Fixed-point integer floor(a * 2**prec). */
export function toFixed(a: Mpf, prec: number): bigint {
  const off = a.exp + BigInt(prec);
  return off >= 0n ? a.man << off : a.man >> -off;
}

export function fromFixed(x: bigint, prec: number, outPrec?: number): Mpf {
  return outPrec === undefined ? strip(x, -BigInt(prec)) : normalize(x, -BigInt(prec), outPrec);
}

// ---------------------------------------------------------------------------
// Precision conversions (mpmath libmpf)
// ---------------------------------------------------------------------------

export function precToDps(n: number): number {
  return Math.max(1, Math.round(n / 3.3219280948873626) - 1);
}

export function dpsToPrec(n: number): number {
  return Math.max(1, Math.round((n + 1) * 3.3219280948873626));
}

// ---------------------------------------------------------------------------
// Decimal conversion
// ---------------------------------------------------------------------------

/** Parse a decimal literal (Python float syntax) to prec bits. */
export function fromStr(s0: string, prec: number): Mpf {
  const s = s0.toLowerCase().trim().replace(/_/g, '');
  if (s.includes('/')) {
    const [p, q] = pair(s.split('/'));
    return fromRational(BigInt(p), BigInt(q), prec);
  }
  const m = /^([+-]?)(\d*)(?:\.(\d*))?(?:e([+-]?\d+))?$/.exec(s);
  if (!m || (m[2] === '' && (m[3] ?? '') === '')) throw new SyntaxError(`invalid float literal: ${s0}`);
  const frac = (m[3] ?? '').replace(/0+$/, '');
  let man = BigInt((m[2] || '0') + frac);
  if (m[1] === '-') man = -man;
  const exp = BigInt(m[4] ?? '0') - BigInt(frac.length);
  // mpmath from_str: a large decimal exponent by a power of ten with 10 guard bits
  if (exp > 400n || exp < -400n) return mul(fromInt(man, prec + 10), powInt(fromInt(10n), exp, prec + 10), prec);
  if (exp >= 0n) return normalize(man * 10n ** exp, 0n, prec);
  return fromRational(man, 10n ** -exp, prec);
}

/** atanh(1/n) * 2**wp in fixed point (n >= 3). */
function atanhInvFixed(n: bigint, wp: number): bigint {
  const n2 = n * n;
  let p = (1n << BigInt(wp)) / n;
  let s = p;
  for (let k = 3n; p; k += 2n) {
    p /= n2;
    s += p / k;
  }
  return s;
}

/**
 * floor(e * log10(2)) for an exponent e beyond the double range of exact integers, with
 * log10(2) = ln 2 / ln 10 to bitLength(e) + 5 bits like mpmath (ln 2 = 2 atanh(1/3),
 * ln 10 = 3 ln 2 + 2 atanh(1/9)).
 */
function decimalExponent(e: bigint): bigint {
  const wp = bitLength(e) + 15;
  const ln2 = 2n * atanhInvFixed(3n, wp);
  const ln10 = 3n * ln2 + 2n * atanhInvFixed(9n, wp);
  const q = e * ln2;
  return q >= 0n ? q / ln10 : -((-q + ln10 - 1n) / ln10);
}

/** mpmath to_digits_exp of a != 0: (sign, digits, exponent), digits rounded toward zero. */
function toDigitsExp(aIn: Mpf, dps: number): [string, string, bigint] {
  let a = aIn;
  let sgn = '';
  if (a.man < 0n) {
    sgn = '-';
    a = neg(a);
  }
  const bitprec = Math.floor(dps * Math.log2(10)) + 10;
  let exponent = 0n;
  const expFrom1 = magExact(a);
  if (expFrom1 > 3500n || expFrom1 < -3500n) {
    const b = decimalExponent(a.exp);
    a = div(a, powInt(fromInt(10n), b, bitprec + 64), bitprec);
    exponent = b;
  }
  const fixprec = Math.max(bitprec - mag(a), 0);
  const fixdps = Math.floor(fixprec / Math.log2(10) + 0.5);
  const sf = toFixed(a, fixprec);
  const sd = (sf * 10n ** BigInt(fixdps)) >> BigInt(fixprec);
  const digits = sd.toString();
  exponent += BigInt(digits.length - fixdps - 1);
  return [sgn, digits, exponent];
}

/** mpmath to_str. */
export function toStr(a: Mpf, dps: number, stripZeros = true, minFixedIn?: number, maxFixedIn?: number): string {
  let minFixed = minFixedIn;
  let maxFixed = maxFixedIn;
  if (a.man === 0n) return dps ? '0.0' : '.0';
  minFixed ??= Math.min(-Math.floor(dps / 3), -5);
  maxFixed ??= dps;
  let [sgn, digits, exponent] = toDigitsExp(a, dps + 3);
  if (!dps) {
    if ('56789'.includes(at(digits, 0))) exponent += 1n;
    digits = '.0';
  } else {
    if (digits.length > dps && '56789'.includes(at(digits, dps))) {
      digits = digits.slice(0, dps);
      let i = dps - 1;
      while (i >= 0 && digits[i] === '9') i--;
      if (i >= 0) digits = digits.slice(0, i) + String(Number(digits[i]) + 1) + '0'.repeat(dps - i - 1);
      else {
        digits = '1' + '0'.repeat(dps - 1);
        exponent += 1n;
      }
    } else digits = digits.slice(0, dps);
    let split: number;
    if (BigInt(minFixed) < exponent && exponent < BigInt(maxFixed)) {
      const ex = Number(exponent);
      if (ex < 0) {
        digits = '0'.repeat(-ex) + digits;
        split = 1;
      } else {
        split = ex + 1;
        if (split > dps) digits += '0'.repeat(split - dps);
      }
      exponent = 0n;
    } else split = 1;
    digits = digits.slice(0, split) + '.' + digits.slice(split);
    if (stripZeros) {
      digits = digits.replace(/0+$/, '');
      if (digits.endsWith('.')) digits += '0';
    }
  }
  if (exponent === 0n && dps) return sgn + digits;
  if (exponent >= 0n) return `${sgn}${digits}e+${exponent}`;
  return `${sgn}${digits}e${exponent}`;
}

/** SymPy StrPrinter._print_Float. */
export function floatToString(a: Mpf, prec: number, stripZeros: boolean): string {
  const dps = prec < 5 ? 0 : precToDps(prec);
  let rv = toStr(a, dps, stripZeros);
  if (rv.startsWith('-.0')) rv = '-0.' + rv.slice(3);
  else if (rv.startsWith('.0')) rv = '0.' + rv.slice(2);
  return rv;
}

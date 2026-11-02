// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Arbitrary-precision binary floating point (a port of the parts of
 * mpmath's libmpf that SymPy relies on).
 *
 * A value is `man * 2**exp` with a signed bigint mantissa. Normalized
 * values have an odd mantissa (or are exactly zero). All rounding is
 * round-half-to-even, like mpmath's `round_nearest`.
 */

import { at, pair } from '../core/guard';

export interface Mpf {
  readonly man: bigint;
  readonly exp: number;
}

export const ZERO: Mpf = { man: 0n, exp: 0 };
export const ONE: Mpf = { man: 1n, exp: 0 };

const babs = (n: bigint): bigint => (n < 0n ? -n : n);

/** Number of bits of |n| (0 for 0). */
export function bitLength(nIn: bigint): number {
  let n = nIn;
  if (n < 0n) n = -n;
  if (n === 0n) return 0;
  const s = n.toString(16);
  const top = parseInt(s.charAt(0), 16);
  return (s.length - 1) * 4 + (32 - Math.clz32(top));
}

function trailingZeros(nIn: bigint): number {
  let n = nIn;
  if (n === 0n) return 0;
  let k = 0;
  while ((n & 0xffffffffn) === 0n) {
    n >>= 32n;
    k += 32;
  }
  while ((n & 1n) === 0n) {
    n >>= 1n;
    k++;
  }
  return k;
}

/** Strip trailing zero bits without rounding. */
function strip(man: bigint, exp: number): Mpf {
  if (man === 0n) return ZERO;
  const tz = trailingZeros(man);
  return tz ? { man: man >> BigInt(tz), exp: exp + tz } : { man, exp };
}

/**
 * Round man*2**exp to prec bits (half to even). `sticky` marks that the
 * true value is slightly larger in magnitude than man*2**exp (lost bits).
 */
export function normalize(man: bigint, expIn: number, prec: number, sticky = false): Mpf {
  let exp = expIn;
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
    exp += n;
  }
  const r = strip(m, exp);
  return neg ? { man: -r.man, exp: r.exp } : r;
}

export function fromInt(n: bigint, prec?: number): Mpf {
  return prec === undefined ? strip(n, 0) : normalize(n, 0, prec);
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
  let e: number;
  if (expBits === 0) e = -1074;
  else {
    mant |= 1n << 52n;
    e = expBits - 1075;
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
  const r = normalize(quo, -shift, prec, rem !== 0n);
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

/** Exponent of the leading bit plus one: |a| in [2**(mag-1), 2**mag). */
export function mag(a: Mpf): number {
  return a.man === 0n ? -Infinity : a.exp + bitLength(a.man);
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
    const t = Math.max(0, prec + 4 - bitLength(a.man)) + 2;
    if (mag(b) < a.exp - t) {
      const man = (a.man << BigInt(t)) + (b.man < 0n ? -1n : 1n);
      return normalize(man, a.exp - t, prec);
    }
  }
  const man = (a.man << BigInt(a.exp - b.exp)) + b.man;
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
  return mul(a, { man: n, exp: 0 }, prec);
}

/** Multiply by 2**k exactly. */
export function ldexp(a: Mpf, k: number): Mpf {
  return a.man === 0n ? a : { man: a.man, exp: a.exp + k };
}

export function div(a: Mpf, b: Mpf, prec: number): Mpf {
  if (b.man === 0n) throw new RangeError('mpf division by zero');
  if (a.man === 0n) return ZERO;
  const shift = Math.max(0, prec + 3 + bitLength(b.man) - bitLength(a.man));
  const n = babs(a.man) << BigInt(shift);
  const d = babs(b.man);
  const quo = n / d;
  const rem = n % d;
  const r = normalize(quo, a.exp - b.exp - shift, prec, rem !== 0n);
  return (a.man < 0n) !== (b.man < 0n) ? neg(r) : r;
}

/** Integer square root floor(sqrt(n)). */
export function isqrt(n: bigint): bigint {
  if (n < 0n) throw new RangeError('isqrt of negative');
  if (n < 2n) return n;
  let x = 1n << BigInt(Math.ceil(bitLength(n) / 2));
  for (;;) {
    const y = (x + n / x) >> 1n;
    if (y >= x) return x;
    x = y;
  }
}

export function sqrt(a: Mpf, prec: number): Mpf {
  if (a.man < 0n) throw new RangeError('mpf sqrt of negative');
  if (a.man === 0n) return ZERO;
  // make the exponent even and the mantissa large enough
  let shift = Math.max(0, 2 * prec + 4 - bitLength(a.man));
  if ((a.exp - shift) % 2 !== 0) shift++;
  const n = a.man << BigInt(shift);
  const r = isqrt(n);
  return normalize(r, (a.exp - shift) / 2, prec, r * r !== n);
}

export function cmp(a: Mpf, b: Mpf): number {
  return sign(sub(a, b));
}

/** Integer power (exact when cheap, otherwise with guard bits). */
export function powInt(a: Mpf, n: bigint, prec: number): Mpf {
  if (n === 0n) return ONE;
  if (n < 0n) return div(ONE, powInt(a, -n, prec + 20), prec);
  if (bitLength(a.man) * Number(n) < 4 * prec + 2000) {
    return normalize(a.man ** n, a.exp * Number(n), prec);
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

/** Nearest JS double. */
export function toNumber(a: Mpf): number {
  if (a.man === 0n) return 0;
  const r = normalize(a.man, a.exp, 53);
  let v = Number(r.man);
  let e = r.exp;
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
  if (a.exp >= 0) return a.man << BigInt(a.exp);
  return a.man >> BigInt(-a.exp);
}

/** Exact rational (p, q). */
export function toRational(a: Mpf): [bigint, bigint] {
  if (a.exp >= 0) return [a.man << BigInt(a.exp), 1n];
  return [a.man, 1n << BigInt(-a.exp)];
}

/** Fixed-point integer floor(a * 2**prec). */
export function toFixed(a: Mpf, prec: number): bigint {
  const off = a.exp + prec;
  return off >= 0 ? a.man << BigInt(off) : a.man >> BigInt(-off);
}

export function fromFixed(x: bigint, prec: number, outPrec?: number): Mpf {
  return outPrec === undefined ? strip(x, -prec) : normalize(x, -prec, outPrec);
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
  const exp = Number(m[4] ?? '0') - frac.length;
  if (exp >= 0) return normalize(man * 10n ** BigInt(exp), 0, prec);
  return fromRational(man, 10n ** BigInt(-exp), prec);
}

/** mpmath to_digits_exp: (sign, digits, exponent), digits rounded toward zero. */
function toDigitsExp(aIn: Mpf, dps: number): [string, string, number] {
  let a = aIn;
  let sgn = '';
  if (a.man < 0n) {
    sgn = '-';
    a = neg(a);
  }
  if (a.man === 0n) return ['', '0', 0];
  const bitprec = Math.floor(dps * Math.log2(10)) + 10;
  let exponent = 0;
  const bc = bitLength(a.man);
  const expFrom1 = a.exp + bc;
  if (Math.abs(expFrom1) > 3500) {
    const b = Math.floor((a.exp * Math.LN2) / Math.LN10);
    a = div(a, powInt(fromInt(10n), BigInt(b), bitprec + 64), bitprec);
    exponent = b;
  }
  const fixprec = Math.max(bitprec - a.exp - bitLength(a.man), 0);
  const fixdps = Math.floor(fixprec / Math.log2(10) + 0.5);
  const sf = toFixed(a, fixprec);
  const sd = (sf * 10n ** BigInt(fixdps)) >> BigInt(fixprec);
  const digits = sd.toString();
  exponent += digits.length - fixdps - 1;
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
    if ('56789'.includes(at(digits, 0))) exponent += 1;
    digits = '.0';
  } else {
    if (digits.length > dps && '56789'.includes(at(digits, dps))) {
      digits = digits.slice(0, dps);
      let i = dps - 1;
      while (i >= 0 && digits[i] === '9') i--;
      if (i >= 0) digits = digits.slice(0, i) + String(Number(digits[i]) + 1) + '0'.repeat(dps - i - 1);
      else {
        digits = '1' + '0'.repeat(dps - 1);
        exponent += 1;
      }
    } else digits = digits.slice(0, dps);
    let split: number;
    if (minFixed < exponent && exponent < maxFixed) {
      if (exponent < 0) {
        digits = '0'.repeat(-exponent) + digits;
        split = 1;
      } else {
        split = exponent + 1;
        if (split > dps) digits += '0'.repeat(split - dps);
      }
      exponent = 0;
    } else split = 1;
    digits = digits.slice(0, split) + '.' + digits.slice(split);
    if (stripZeros) {
      digits = digits.replace(/0+$/, '');
      if (digits.endsWith('.')) digits += '0';
    }
  }
  if (exponent === 0 && dps) return sgn + digits;
  if (exponent >= 0) return `${sgn}${digits}e+${exponent}`;
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

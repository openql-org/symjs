// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Number utilities compatible with SymPy: exact rationals from
 * floats and decimal strings, integer_log, Integer truncation and the
 * range syntax of symbols().
 */

import { Rational, impl } from './nodes';

/** Exact rational value of a double (SymPy Rational(0.2) = 3602879701896397/18014398509481984). */
export function rationalFromFloat(v: number): Rational {
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
  return e >= 0 ? Rational.of(sign * mant * (1n << BigInt(e))) : Rational.of(sign * mant, 1n << BigInt(-e));
}

/** Exact rational from a decimal string, e.g. '1.23' -> 123/100, '1e-2' -> 1/100, '1e-2/3.2' -> 1/320. */
export function rationalFromString(s0: string): Rational {
  const s = s0.trim();
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

/** SymPy integer_log(n, b): (e, exact) with b**e <= |n| and exact when b**e == n. */
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
  const names = splitNames(spec);
  return names.flatMap(expandOne);
}

function splitNames(spec: string): string[] {
  const out: string[] = [];
  let depth = 0;
  let cur = '';
  for (const ch of spec) {
    if (ch === '(') depth++;
    if (ch === ')') depth--;
    if (depth === 0 && (ch === ',' || /\s/.test(ch))) {
      if (cur) out.push(cur);
      cur = '';
    } else cur += ch;
  }
  if (cur) out.push(cur);
  return out;
}

function expandOne(name: string): string[] {
  if (!name.includes(':')) return [name.replace(/[()]/g, '')];
  // split into literal parts and range parts; ranges are either inside () or a bare a:b
  const tokens: (string | string[])[] = [];
  let i = 0;
  while (i < name.length) {
    if (name[i] === '(') {
      const j = name.indexOf(')', i);
      const inner = name.slice(i + 1, j);
      tokens.push(inner.includes(':') ? rangeValues(inner) : inner);
      i = j + 1;
      continue;
    }
    // bare segment until next '('
    const j = name.indexOf('(', i);
    const seg = name.slice(i, j < 0 ? name.length : j);
    i = j < 0 ? name.length : j;
    const colon = seg.indexOf(':');
    if (colon < 0) {
      tokens.push(seg);
      continue;
    }
    const before = seg.slice(0, colon);
    const hi = seg.slice(colon + 1);
    let prefix: string;
    let lo: string;
    if (/^[A-Za-z]$/.test(hi)) {
      // letter range: the character before ':' (if any) is the start
      lo = before.length ? before.slice(-1) : 'a';
      prefix = before.length ? before.slice(0, -1) : '';
    } else {
      const m = /^(.*?)(\d*)$/.exec(before)!;
      prefix = m[1]!;
      lo = m[2]!;
    }
    tokens.push(prefix);
    tokens.push(rangeValues(`${lo}:${hi}`));
  }
  let acc = [''];
  for (const t of tokens) {
    const vals = typeof t === 'string' ? [t] : t;
    acc = acc.flatMap((a) => vals.map((v) => a + v));
  }
  return acc;
}

function rangeValues(r: string): string[] {
  const [lo, hi] = r.split(':') as [string, string];
  if (/^[A-Za-z]$/.test(hi) || /^[A-Za-z]$/.test(lo)) {
    const a = (lo || 'a').charCodeAt(0);
    const b = hi.charCodeAt(0);
    const out: string[] = [];
    for (let c = a; c <= b; c++) out.push(String.fromCharCode(c));
    return out;
  }
  const a = lo === '' ? 0 : Number(lo);
  const b = Number(hi);
  return Array.from({ length: Math.max(0, b - a) }, (_, k) => String(a + k));
}
impl.rationalFromFloat = (f) => rationalFromFloat(f.value);

const babs = (n: bigint): bigint => (n < 0n ? -n : n);

/** Greatest common divisor of integers (SymPy igcd). */
export function igcd(...xs: bigint[]): bigint {
  let g = 0n;
  for (let x of xs) {
    x = babs(x);
    let a = g;
    while (x) [a, x] = [x, a % x];
    g = a;
  }
  return g;
}

/** Least common multiple of integers (SymPy ilcm). */
export function ilcm(...xs: bigint[]): bigint {
  let l = 1n;
  for (const x of xs) {
    if (x === 0n) return 0n;
    l = babs((l / igcd(l, x)) * x);
  }
  return l;
}

/** (floor(y**(1/n)), exact) for nonnegative integers (SymPy integer_nthroot). */
export function integerNthroot(y: bigint, n: number): [bigint, boolean] {
  if (y < 0n) throw new RangeError('integer_nthroot: y must be nonnegative');
  if (y < 2n) return [y, true];
  const N = BigInt(n);
  let x = 1n << BigInt(Math.ceil(y.toString(2).length / n) + 1);
  for (;;) {
    const z = ((N - 1n) * x + y / x ** (N - 1n)) / N;
    if (z >= x) break;
    x = z;
  }
  while (x ** N > y) x--;
  while ((x + 1n) ** N <= y) x++;
  return [x, x ** N === y];
}

/** Number of trailing zero bits (SymPy trailing). */
export function trailing(n: bigint): number {
  n = babs(n);
  if (n === 0n) return 0;
  let k = 0;
  while ((n & 1n) === 0n) {
    n >>= 1n;
    k++;
  }
  return k;
}

/** Number of digits of |n| in the given base (SymPy num_digits). */
export function numDigits(n: bigint, base = 10): number {
  return babs(n).toString(base).length;
}

/** Inverse of a modulo m (SymPy mod_inverse); for non-integers 1/a when m > 1. */
export function modInverse(a: Rational, m: Rational): Rational {
  if (a.isInteger && m.isInteger) {
    let [r0, r1] = [a.p, m.p];
    let [s0, s1] = [1n, 0n];
    while (r1) {
      const q = r0 / r1;
      [r0, r1] = [r1, r0 - q * r1];
      [s0, s1] = [s1, s0 - q * s1];
    }
    if (babs(r0) !== 1n) throw new RangeError('mod_inverse: inverse does not exist');
    const mm = babs(m.p);
    let c = (s0 * r0) % mm;
    if (c < 0n) c += mm;
    return Rational.of(c);
  }
  if (m.p > m.q) return Rational.of(a.q, a.p);
  throw new RangeError('mod_inverse: inverse does not exist');
}

/** Closest rational with denominator at most maxDen (Python Fraction.limit_denominator). */
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

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Arbitrary-precision constants and elementary functions on Mpf
 * (real) and Mpc (complex) values. Each function returns a result
 * rounded to `prec` bits, computed with internal guard bits; the evalf
 * driver re-evaluates at higher precision to certify digits.
 */

import * as F from './mpf';
import type { Mpf } from './mpf';
import { ONE, ZERO } from './mpf';

// ---------------------------------------------------------------------------
// Constants (fixed point, cached)
// ---------------------------------------------------------------------------

/** Cache a fixed-point constant computed at the largest precision requested so far. */
function cachedFixed(compute: (prec: number) => bigint): (prec: number) => bigint {
  let bestPrec = -1;
  let best = 0n;
  return (prec) => {
    if (prec > bestPrec) {
      const p = Math.max(prec, Math.ceil(bestPrec * 1.5), 128) + 20;
      best = compute(p);
      bestPrec = p;
    }
    return best >> BigInt(bestPrec - prec);
  };
}

/** atan(1/n) as fixed point. */
function acotFixed(n: bigint, prec: number, hyperbolic = false): bigint {
  const one = 1n << BigInt(prec);
  let s = 0n;
  let t = one / n;
  const n2 = n * n;
  let k = 1n;
  let sgn = 1n;
  while (t !== 0n) {
    s += (sgn * t) / k;
    t /= n2;
    k += 2n;
    if (!hyperbolic) sgn = -sgn;
  }
  return s;
}

export const piFixed = cachedFixed((p) => {
  const wp = p + 10;
  return (16n * acotFixed(5n, wp) - 4n * acotFixed(239n, wp)) >> 10n;
});

export const ln2Fixed = cachedFixed((p) => {
  const wp = p + 10;
  return (18n * acotFixed(26n, wp, true) - 2n * acotFixed(4801n, wp, true) + 8n * acotFixed(8749n, wp, true)) >> 10n;
});

export const eulerFixed = cachedFixed((p0) => {
  const extra = 30;
  const prec = p0 + extra;
  const p = Math.floor(Math.log2((prec / 4) * Math.LN2)) + 1;
  const n = 1n << BigInt(p);
  const n2 = n * n;
  let A = -BigInt(p) * ln2Fixed(prec);
  let U = A;
  let B = 1n << BigInt(prec);
  let V = B;
  let k = 1n;
  for (;;) {
    B = (B * n2) / (k * k);
    A = ((A * n2) / k + B) / k;
    U += A;
    V += B;
    const aa = A < 0n ? -A : A;
    if (aa < 100n && B < 100n) break;
    k += 1n;
  }
  return (U << BigInt(prec - extra)) / V;
});

export const catalanFixed = cachedFixed((p) => {
  const prec = p + 20;
  let a = 1n << BigInt(prec);
  let s = 0n;
  let t = 1n;
  let n = 1n;
  while (t !== 0n) {
    a *= 32n * n ** 3n * (2n * n - 1n);
    a /= (3n - 16n * n + 16n * n * n) ** 2n;
    t = (a * (n % 2n === 1n ? 1n : -1n) * (40n * n * n - 24n * n + 3n)) / (n ** 3n * (2n * n - 1n));
    s += t;
    n += 1n;
  }
  return s >> 26n;
});

const fromFx = (x: bigint, wp: number, prec: number): Mpf => F.fromFixed(x, wp, prec);

export function mpPi(prec: number): Mpf {
  return fromFx(piFixed(prec + 10), prec + 10, prec);
}
export function mpLn2(prec: number): Mpf {
  return fromFx(ln2Fixed(prec + 10), prec + 10, prec);
}
export function mpEuler(prec: number): Mpf {
  return fromFx(eulerFixed(prec + 10), prec + 10, prec);
}
export function mpCatalan(prec: number): Mpf {
  return fromFx(catalanFixed(prec + 10), prec + 10, prec);
}
export function mpE(prec: number): Mpf {
  return exp(ONE, prec);
}
export function mpPhi(prec: number): Mpf {
  const wp = prec + 10;
  return F.round(F.ldexp(F.add(ONE, F.sqrt(F.fromInt(5n), wp), wp), -1), prec);
}
export function mpTribonacci(prec: number): Mpf {
  const wp = prec + 15;
  const s33 = F.mul(F.fromInt(3n), F.sqrt(F.fromInt(33n), wp), wp);
  const a = cbrt(F.add(F.fromInt(19n), s33, wp), wp);
  const b = cbrt(F.sub(F.fromInt(19n), s33, wp), wp);
  return F.div(F.add(F.add(ONE, a, wp), b, wp), F.fromInt(3n), prec);
}

/** Real cube root. */
export function cbrt(x: Mpf, prec: number): Mpf {
  if (F.isZero(x)) return ZERO;
  if (x.man < 0n) return F.neg(cbrt(F.neg(x), prec));
  return nthRoot(x, 3n, prec);
}

/** x**(1/n) for x > 0 via an integer root. */
export function nthRoot(x: Mpf, n: bigint, prec: number): Mpf {
  const N = Number(n);
  let shift = Math.max(0, N * (prec + 4) - F.bitLength(x.man));
  while ((((x.exp - shift) % N) + N) % N !== 0) shift++;
  const m = x.man << BigInt(shift);
  let r = iroot(m, n);
  const exact = r ** n === m;
  return F.normalize(r, (x.exp - shift) / N, prec, !exact);
}

function iroot(m: bigint, n: bigint): bigint {
  if (m < 2n) return m;
  const bl = F.bitLength(m);
  let x = 1n << BigInt(Math.ceil(bl / Number(n)) + 1);
  for (;;) {
    const y = ((n - 1n) * x + m / x ** (n - 1n)) / n;
    if (y >= x) break;
    x = y;
  }
  while (x ** n > m) x--;
  while ((x + 1n) ** n <= m) x++;
  return x;
}

// ---------------------------------------------------------------------------
// Real elementary functions
// ---------------------------------------------------------------------------

export function exp(x: Mpf, prec: number): Mpf {
  if (F.isZero(x)) return ONE;
  const mg = F.mag(x);
  if (mg > 60) throw new RangeError('exp: argument too large');
  const wp = prec + 20 + Math.max(0, mg);
  // n = round(x / ln2)
  const ln2 = mpLn2(wp + 10);
  const n = F.floor(F.add(F.div(x, ln2, 64 + Math.max(0, mg)), { man: 1n, exp: -1 }));
  let r = F.sub(x, F.mulInt(ln2, n), wp);
  // further reduce by 2**-s
  const s = Math.max(0, Math.floor(Math.sqrt(wp)) + 4 + Math.min(0, F.mag(r)) * 0);
  r = F.ldexp(r, -s);
  const wp2 = wp + 2 * s;
  // Taylor series in fixed point
  const one = 1n << BigInt(wp2);
  const rf = F.toFixed(r, wp2);
  let term = one;
  let sum = one;
  for (let k = 1n; ; k++) {
    term = ((term * rf) >> BigInt(wp2)) / k;
    if (term === 0n) break;
    sum += term;
  }
  for (let i = 0; i < s; i++) sum = (sum * sum) >> BigInt(wp2);
  return F.normalize(sum, -wp2 + Number(n), prec);
}

/** exp(x) - 1 with relative accuracy for small x. */
export function expm1(x: Mpf, prec: number): Mpf {
  if (F.isZero(x)) return ZERO;
  const mg = F.mag(x);
  if (mg > -2) return F.sub(exp(x, prec + 10), ONE, prec);
  const wp = prec + 10;
  let term = x;
  let sum = x;
  for (let k = 2n; ; k++) {
    term = F.div(F.mul(term, x, wp), F.fromInt(k), wp);
    if (F.isZero(term) || F.mag(term) < F.mag(sum) - wp) break;
    sum = F.add(sum, term, wp);
  }
  return F.round(sum, prec);
}

export function log(x: Mpf, prec: number): Mpf {
  if (x.man <= 0n) throw new RangeError('log of non-positive');
  // x = m * 2**k with m in [1/sqrt2, sqrt2)
  let k = F.mag(x) - 1;
  let m = F.ldexp(x, -k);
  if (F.toNumber(m) > Math.SQRT2) {
    m = F.ldexp(m, -1);
    k += 1;
  }
  if (F.cmp(m, ONE) === 0) return k === 0 ? ZERO : F.round(F.mulInt(mpLn2(prec + 10), BigInt(k)), prec);
  const wp0 = prec + 20;
  const d = F.sub(m, ONE);
  const wp = wp0 + Math.max(0, -F.mag(d));
  const z = F.div(d, F.add(m, ONE), wp);
  const z2 = F.mul(z, z, wp);
  let pw = z;
  let sum = z;
  for (let j = 3n; ; j += 2n) {
    pw = F.mul(pw, z2, wp);
    const t = F.div(pw, F.fromInt(j), wp);
    if (F.isZero(t) || F.mag(t) < F.mag(sum) - wp) break;
    sum = F.add(sum, t, wp);
  }
  const lm = F.ldexp(sum, 1);
  if (k === 0) return F.round(lm, prec);
  return F.add(F.mulInt(mpLn2(wp + 10), BigInt(k)), lm, prec);
}

/** Reduce x modulo pi/2: returns [r, n mod 4] with x = r + n*pi/2. */
function reduceHalfPi(x: Mpf, wp: number): [Mpf, number] {
  const mg = Math.max(0, F.mag(x));
  const p = wp + mg + 10;
  const halfPi = F.ldexp(mpPi(p), -1);
  if (mg <= 0 && F.cmp(F.abs(x), { man: 3n, exp: -2 }) <= 0) return [F.round(x, wp), 0];
  const q = F.div(x, halfPi, mg + 20);
  const n = F.floor(F.add(q, { man: 1n, exp: -1 }));
  const r = F.sub(x, F.mulInt(halfPi, n), p);
  return [F.round(r, wp), Number(((n % 4n) + 4n) % 4n)];
}

/** sin and cos of a reduced argument |r| <= pi/4 (floating series). */
function sinCosSeries(r: Mpf, wp: number): [Mpf, Mpf] {
  if (F.isZero(r)) return [ZERO, ONE];
  const r2 = F.mul(r, r, wp);
  let s = r;
  let t = r;
  for (let k = 2n; ; k += 2n) {
    t = F.neg(F.div(F.mul(t, r2, wp), F.fromInt(k * (k + 1n)), wp));
    if (F.isZero(t) || F.mag(t) < F.mag(s) - wp - 2) break;
    s = F.add(s, t, wp);
  }
  let c: Mpf = ONE;
  t = ONE;
  for (let k = 1n; ; k += 2n) {
    t = F.neg(F.div(F.mul(t, r2, wp), F.fromInt(k * (k + 1n)), wp));
    if (F.isZero(t) || F.mag(t) < -wp - 2) break;
    c = F.add(c, t, wp);
  }
  return [s, c];
}

export function sinCos(x: Mpf, prec: number): [Mpf, Mpf] {
  const wp = prec + 15;
  const [r, n] = reduceHalfPi(x, wp);
  const [s, c] = sinCosSeries(r, wp);
  const out: [Mpf, Mpf][] = [
    [s, c],
    [c, F.neg(s)],
    [F.neg(s), F.neg(c)],
    [F.neg(c), s],
  ];
  const [a, b] = out[n]!;
  return [F.round(a, prec), F.round(b, prec)];
}

export const sin = (x: Mpf, prec: number): Mpf => sinCos(x, prec)[0];
export const cos = (x: Mpf, prec: number): Mpf => sinCos(x, prec)[1];
export function tan(x: Mpf, prec: number): Mpf {
  const [s, c] = sinCos(x, prec + 10);
  return F.div(s, c, prec);
}

export function atan(x: Mpf, prec: number): Mpf {
  if (F.isZero(x)) return ZERO;
  const wp = prec + 20;
  if (x.man < 0n) return F.neg(atan(F.neg(x), prec));
  if (F.mag(x) > 1) {
    // atan(x) = pi/2 - atan(1/x)
    const inv = F.div(ONE, x, wp);
    return F.sub(F.ldexp(mpPi(wp), -1), atan(inv, wp), prec);
  }
  // halve the argument: atan(x) = 2*atan(x / (1 + sqrt(1 + x^2)))
  let y = x;
  let halvings = 0;
  while (F.mag(y) > -8) {
    y = F.div(y, F.add(ONE, F.sqrt(F.add(ONE, F.mul(y, y, wp), wp), wp), wp), wp);
    halvings++;
  }
  const y2 = F.mul(y, y, wp);
  let pw = y;
  let sum = y;
  for (let j = 3n; ; j += 2n) {
    pw = F.neg(F.mul(pw, y2, wp));
    const t = F.div(pw, F.fromInt(j), wp);
    if (F.isZero(t) || F.mag(t) < F.mag(sum) - wp) break;
    sum = F.add(sum, t, wp);
  }
  return F.round(F.ldexp(sum, halvings), prec);
}

export function atan2(y: Mpf, x: Mpf, prec: number): Mpf {
  const wp = prec + 15;
  if (F.isZero(x)) {
    if (F.isZero(y)) return ZERO;
    const hp = F.ldexp(mpPi(prec), -1);
    return y.man > 0n ? hp : F.neg(hp);
  }
  const a = atan(F.div(y, x, wp), wp);
  if (x.man > 0n) return F.round(a, prec);
  const pi = mpPi(wp);
  return y.man >= 0n ? F.add(a, pi, prec) : F.sub(a, pi, prec);
}

export function sinh(x: Mpf, prec: number): Mpf {
  if (F.isZero(x)) return ZERO;
  const wp = prec + 15;
  if (F.mag(x) < 0) {
    const x2 = F.mul(x, x, wp);
    let t = x;
    let s = x;
    for (let k = 2n; ; k += 2n) {
      t = F.div(F.mul(t, x2, wp), F.fromInt(k * (k + 1n)), wp);
      if (F.isZero(t) || F.mag(t) < F.mag(s) - wp) break;
      s = F.add(s, t, wp);
    }
    return F.round(s, prec);
  }
  const e = exp(x, wp);
  return F.ldexp(F.sub(e, F.div(ONE, e, wp), prec), -1);
}

export function cosh(x: Mpf, prec: number): Mpf {
  const wp = prec + 15;
  const e = exp(x, wp);
  return F.ldexp(F.add(e, F.div(ONE, e, wp), prec), -1);
}

export function tanh(x: Mpf, prec: number): Mpf {
  const wp = prec + 15;
  return F.div(sinh(x, wp), cosh(x, wp), prec);
}

/** x**y for x > 0. */
export function powReal(x: Mpf, y: Mpf, prec: number): Mpf {
  const wp = prec + 20 + Math.max(0, F.mag(y)) + Math.max(0, Math.ceil(Math.log2(Math.abs(F.mag(x)) + 1)));
  return exp(F.mul(y, log(x, wp), wp), prec);
}

// ---------------------------------------------------------------------------
// Complex functions (Mpc = [re, im])
// ---------------------------------------------------------------------------

export type Mpc = readonly [Mpf, Mpf];

export const C0: Mpc = [ZERO, ZERO];
export const C1: Mpc = [ONE, ZERO];
export const CI: Mpc = [ZERO, ONE];

export const isReal = (z: Mpc): boolean => F.isZero(z[1]);

export function cadd(a: Mpc, b: Mpc, prec: number): Mpc {
  return [F.add(a[0], b[0], prec), F.add(a[1], b[1], prec)];
}
export function csub(a: Mpc, b: Mpc, prec: number): Mpc {
  return [F.sub(a[0], b[0], prec), F.sub(a[1], b[1], prec)];
}
export function cneg(a: Mpc): Mpc {
  return [F.neg(a[0]), F.neg(a[1])];
}
export function cmul(a: Mpc, b: Mpc, prec: number): Mpc {
  if (isReal(b)) return [F.mul(a[0], b[0], prec), F.mul(a[1], b[0], prec)];
  if (isReal(a)) return [F.mul(a[0], b[0], prec), F.mul(a[0], b[1], prec)];
  // exact products, single rounding
  const re = F.sub(F.mul(a[0], b[0]), F.mul(a[1], b[1]), prec);
  const im = F.add(F.mul(a[0], b[1]), F.mul(a[1], b[0]), prec);
  return [re, im];
}
export function cdiv(a: Mpc, b: Mpc, prec: number): Mpc {
  if (isReal(b)) return [F.div(a[0], b[0], prec), F.div(a[1], b[0], prec)];
  const wp = prec + 10;
  const d = F.add(F.mul(b[0], b[0]), F.mul(b[1], b[1]));
  const re = F.add(F.mul(a[0], b[0]), F.mul(a[1], b[1]));
  const im = F.sub(F.mul(a[1], b[0]), F.mul(a[0], b[1]));
  return [F.div(re, d, wp), F.div(im, d, wp)].map((v) => F.round(v, prec)) as unknown as Mpc;
}
export function cabs(z: Mpc, prec: number): Mpf {
  if (F.isZero(z[1])) return F.round(F.abs(z[0]), prec);
  if (F.isZero(z[0])) return F.round(F.abs(z[1]), prec);
  return F.sqrt(F.add(F.mul(z[0], z[0]), F.mul(z[1], z[1])), prec);
}
export function carg(z: Mpc, prec: number): Mpf {
  return atan2(z[1], z[0], prec);
}

export function cexp(z: Mpc, prec: number): Mpc {
  if (isReal(z)) return [exp(z[0], prec), ZERO];
  const wp = prec + 10;
  const [s, c] = sinCos(z[1], wp);
  if (F.isZero(z[0])) return [F.round(c, prec), F.round(s, prec)];
  const m = exp(z[0], wp);
  return [F.mul(m, c, prec), F.mul(m, s, prec)];
}

export function clog(z: Mpc, prec: number): Mpc {
  if (isReal(z) && z[0].man > 0n) return [log(z[0], prec), ZERO];
  const wp = prec + 15;
  if (isReal(z)) return [log(F.neg(z[0]), prec), mpPi(prec)];
  // log|z| with care near |z| = 1
  const n2 = F.add(F.mul(z[0], z[0]), F.mul(z[1], z[1]));
  const re = F.ldexp(log(n2, wp), -1);
  return [F.round(re, prec), carg(z, prec)];
}

export function csqrt(z: Mpc, prec: number): Mpc {
  if (isReal(z)) {
    if (z[0].man >= 0n) return [F.sqrt(z[0], prec), ZERO];
    return [ZERO, F.sqrt(F.neg(z[0]), prec)];
  }
  const wp = prec + 20;
  const r = cabs(z, wp);
  const [a, b] = z;
  if (a.man >= 0n) {
    const t = F.sqrt(F.ldexp(F.add(r, a, wp), -1), wp);
    return [F.round(t, prec), F.div(b, F.ldexp(t, 1), prec)];
  }
  let t = F.sqrt(F.ldexp(F.sub(r, a, wp), -1), wp);
  if (b.man < 0n) t = F.neg(t);
  return [F.div(b, F.ldexp(t, 1), prec), F.round(t, prec)];
}

export function cpowInt(z: Mpc, n: bigint, prec: number): Mpc {
  if (isReal(z)) return [F.powInt(z[0], n, prec), ZERO];
  if (n < 0n) return cdiv(C1, cpowInt(z, -n, prec + 20), prec);
  const wp = prec + 10 + 2 * F.bitLength(n);
  let r: Mpc = C1;
  let b = z;
  let k = n;
  while (k > 0n) {
    if (k & 1n) r = cmul(r, b, wp);
    k >>= 1n;
    if (k) b = cmul(b, b, wp);
  }
  return [F.round(r[0], prec), F.round(r[1], prec)];
}

export function cpow(z: Mpc, w: Mpc, prec: number): Mpc {
  if (F.isZero(z[0]) && F.isZero(z[1])) {
    if (w[0].man > 0n) return C0;
    throw new RangeError('0 ** non-positive');
  }
  if (isReal(w)) {
    const [p, q] = F.toRational(w[0]);
    if (q === 1n) return cpowInt(z, p, prec);
    if (isReal(z) && z[0].man > 0n) return [powReal(z[0], w[0], prec), ZERO];
    if (q === 2n) {
      const s = csqrt(z, prec + 20);
      return cpowInt(s, p, prec);
    }
  }
  const wp = prec + 25 + Math.max(0, F.mag(w[0]), F.mag(w[1]));
  return cexp(cmul(w, clog(z, wp), wp), prec);
}

export function csin(z: Mpc, prec: number): Mpc {
  if (isReal(z)) return [sin(z[0], prec), ZERO];
  const wp = prec + 15;
  const [s, c] = sinCos(z[0], wp);
  const sh = sinh(z[1], wp);
  const ch = cosh(z[1], wp);
  return [F.mul(s, ch, prec), F.mul(c, sh, prec)];
}
export function ccos(z: Mpc, prec: number): Mpc {
  if (isReal(z)) return [cos(z[0], prec), ZERO];
  const wp = prec + 15;
  const [s, c] = sinCos(z[0], wp);
  const sh = sinh(z[1], wp);
  const ch = cosh(z[1], wp);
  return [F.mul(c, ch, prec), F.neg(F.mul(s, sh, prec))];
}
export function ctan(z: Mpc, prec: number): Mpc {
  if (isReal(z)) return [tan(z[0], prec), ZERO];
  const wp = prec + 15;
  return cdiv(csin(z, wp), ccos(z, wp), prec);
}
export function csinh(z: Mpc, prec: number): Mpc {
  if (isReal(z)) return [sinh(z[0], prec), ZERO];
  // sinh(a+bi) = sinh a cos b + i cosh a sin b
  const wp = prec + 15;
  const [s, c] = sinCos(z[1], wp);
  return [F.mul(sinh(z[0], wp), c, prec), F.mul(cosh(z[0], wp), s, prec)];
}
export function ccosh(z: Mpc, prec: number): Mpc {
  if (isReal(z)) return [cosh(z[0], prec), ZERO];
  const wp = prec + 15;
  const [s, c] = sinCos(z[1], wp);
  return [F.mul(cosh(z[0], wp), c, prec), F.mul(sinh(z[0], wp), s, prec)];
}
export function ctanh(z: Mpc, prec: number): Mpc {
  if (isReal(z)) return [tanh(z[0], prec), ZERO];
  const wp = prec + 15;
  return cdiv(csinh(z, wp), ccosh(z, wp), prec);
}

const mulI = (z: Mpc): Mpc => [F.neg(z[1]), z[0]];
const mulNegI = (z: Mpc): Mpc => [z[1], F.neg(z[0])];

/** asin z = -i log(iz + sqrt(1 - z^2)) */
export function casin(z: Mpc, prec: number): Mpc {
  const wp = prec + 20;
  if (isReal(z) && F.cmp(F.abs(z[0]), ONE) <= 0) {
    if (F.cmp(F.abs(z[0]), ONE) === 0) {
      const hp = F.ldexp(mpPi(prec), -1);
      return [z[0].man > 0n ? hp : F.neg(hp), ZERO];
    }
    const s = F.sqrt(F.sub(ONE, F.mul(z[0], z[0]), wp), wp);
    return [atan(F.div(z[0], s, wp), prec), ZERO];
  }
  const one_z2 = csub(C1, cmul(z, z, wp), wp);
  const r = mulNegI(clog(cadd(mulI(z), csqrt(one_z2, wp), wp), wp));
  return [F.round(r[0], prec), F.round(r[1], prec)];
}

export function cacos(z: Mpc, prec: number): Mpc {
  const wp = prec + 20;
  const a = casin(z, wp);
  return [F.sub(F.ldexp(mpPi(wp), -1), a[0], prec), F.round(F.neg(a[1]), prec)];
}

/** atan z = i/2 (log(1 - iz) - log(1 + iz)) */
export function catan(z: Mpc, prec: number): Mpc {
  if (isReal(z)) return [atan(z[0], prec), ZERO];
  const wp = prec + 20;
  const iz = mulI(z);
  const d = csub(clog(csub(C1, iz, wp), wp), clog(cadd(C1, iz, wp), wp), wp);
  const r = mulI(d);
  return [F.round(F.ldexp(r[0], -1), prec), F.round(F.ldexp(r[1], -1), prec)];
}

/** asinh z = log(z + sqrt(z^2 + 1)) */
export function casinh(z: Mpc, prec: number): Mpc {
  const wp = prec + 20;
  if (isReal(z)) {
    const x = z[0];
    if (x.man < 0n) return cneg(casinh(cneg(z), prec));
    return [log(F.add(x, F.sqrt(F.add(F.mul(x, x), ONE), wp), wp), prec), ZERO];
  }
  const r = clog(cadd(z, csqrt(cadd(cmul(z, z, wp), C1, wp), wp), wp), wp);
  return [F.round(r[0], prec), F.round(r[1], prec)];
}

/** acosh z = log(z + sqrt(z + 1) sqrt(z - 1)) */
export function cacosh(z: Mpc, prec: number): Mpc {
  const wp = prec + 20;
  const r = clog(cadd(z, cmul(csqrt(cadd(z, C1, wp), wp), csqrt(csub(z, C1, wp), wp), wp), wp), wp);
  return [F.round(r[0], prec), F.round(r[1], prec)];
}

/** atanh z = (log(1 + z) - log(1 - z)) / 2 */
export function catanh(z: Mpc, prec: number): Mpc {
  const wp = prec + 20;
  const r = csub(clog(cadd(C1, z, wp), wp), clog(csub(C1, z, wp), wp), wp);
  return [F.round(F.ldexp(r[0], -1), prec), F.round(F.ldexp(r[1], -1), prec)];
}

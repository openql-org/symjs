// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from mpmath 1.3.0 (functions/zeta.py: polylog, polylog_series,
// polylog_continuation, polylog_unitcircle, polylog_general, lerchphi,
// altzeta), Copyright (c) 2005-2023 Fredrik Johansson and mpmath contributors,
// BSD 3-Clause License (see LICENSE).

/**
 * @file The polylogarithm Li_s(z) and the Lerch transcendent Phi(z, s, a) at
 * arbitrary precision (mpmath polylog, lerchphi), registered as polylog and
 * lerchphi for numeric evaluation.
 */

import * as F from './mpf';
import type { Mpf } from './mpf';
import { ZERO } from './mpf';
import * as M from './mpfun';
import { type Mpc, cadd, cdiv, cmul, csub } from './mpfun';
import { bernoulli, cgamma, czeta } from './mpspecial';
import { cexpint } from './mpexpint';
import { quadZeroInf } from './mpquad';

const real = (x: Mpf): Mpc => [x, ZERO];
const int = (n: bigint | number): Mpc => [F.fromInt(BigInt(n)), ZERO];
const czero = (a: Mpc): boolean => F.isZero(a[0]) && F.isZero(a[1]);
const isInt = (s: Mpc): boolean => F.isZero(s[1]) && F.toRational(s[0])[1] === 1n;
const toInt = (s: Mpc): number => Number(F.floor(s[0]));
const eq = (a: Mpc, n: number): boolean => F.isZero(a[1]) && F.cmp(a[0], F.fromInt(BigInt(n))) === 0;
const absD = (z: Mpc): number => F.toNumber(M.cabs(z, 53));
/** |t| < 2**(1 - wp) (mpmath eps). */
const tiny = (t: Mpc, wp: number): boolean => czero(t) || Math.max(F.mag(t[0]), F.mag(t[1])) < 1 - wp;
const realPart = (z: Mpc, a: Mpc): Mpc => (F.isZero(z[1]) && z[0].man < 0n ? [a[0], ZERO] : a);

const factorial = (n: number): bigint => {
  let r = 1n;
  for (let i = 2n; i <= BigInt(n); i++) r *= i;
  return r;
};
const bern = (n: number, wp: number): Mpc => {
  const [p, q] = bernoulli(n);
  return real(F.fromRational(p, q, wp));
};

/** zeta(s), exact from the Bernoulli numbers at the integers s <= 0. */
function zetaAt(s: Mpc, wp: number): Mpc {
  if (isInt(s) && s[0].man <= 0n) {
    const k = -toInt(s);
    const [p, q] = bernoulli(k + 1);
    return real(F.fromRational(k % 2 ? -p : p, q * BigInt(k + 1), wp));
  }
  if (s[0].man < 0n) {
    // the functional equation: 2^s pi^(s-1) sin(pi s/2) Gamma(1-s) zeta(1-s)
    const w = wp + 10;
    const pi = real(M.mpPi(w));
    const s1 = csub(M.C1, s, w);
    const f = cmul(M.cpow(int(2), s, w), M.cpow(pi, csub(s, M.C1, w), w), w);
    const sn = M.csin(cmul(pi, cmul(real({ man: 1n, exp: -1n }), s, w), w), w);
    return cmul(cmul(f, sn, w), cmul(cgamma(s1, w), czeta(s1, w), w), wp);
  }
  return czeta(s, wp);
}

/** sum_k z^k/k^s, valid for |z| < 1. */
function polylogSeries(s: Mpc, z: Mpc, wp: number): Mpc {
  let l: Mpc = M.C0;
  let zk = z;
  const ms = M.cneg(s);
  for (let k = 1; ; k++) {
    const term = cmul(zk, M.cpow(int(k), ms, wp), wp);
    l = cadd(l, term, wp);
    if (tiny(term, wp)) return l;
    zk = cmul(zk, z, wp);
  }
}

/** The Bernoulli polynomial B_n(x). */
function bernpoly(n: number, x: Mpc, wp: number): Mpc {
  let s: Mpc = M.C0;
  let c = 1n;
  let xp: Mpc = M.C1;
  // sum_k C(n, k) B_(n-k) x^k
  for (let k = 0; k <= n; k++) {
    s = cadd(s, cmul(cmul(int(c), bern(n - k, wp), wp), xp, wp), wp);
    xp = cmul(xp, x, wp);
    c = (c * BigInt(n - k)) / BigInt(k + 1);
  }
  return s;
}

/** The analytic continuation term of Li_n(z) for |z| > 1. */
function polylogContinuation(n: number, z: Mpc, wp: number): Mpc {
  if (n < 0) return M.C0;
  const twopij: Mpc = [ZERO, F.ldexp(M.mpPi(wp), 1)];
  const lz = M.clog(z, wp);
  let a = M.cneg(cdiv(cmul(M.cpowInt(twopij, BigInt(n), wp), bernpoly(n, cdiv(lz, twopij, wp), wp), wp), int(factorial(n)), wp));
  a = realPart(z, a);
  if (z[1].man < 0n || (F.isZero(z[1]) && F.cmp(z[0], F.ONE) >= 0)) {
    a = csub(a, cdiv(cmul(twopij, M.cpowInt(lz, BigInt(n - 1), wp), wp), int(factorial(n - 1)), wp), wp);
  }
  return a;
}

/** Li_n(z) near the unit circle by the series in log z. */
function polylogUnitcircle(n: number, z: Mpc, wp: number): Mpc {
  const logz = M.clog(z, wp);
  let l: Mpc = M.C0;
  if (n > 1) {
    let logmz: Mpc = M.C1;
    for (let m = 0; ; m++) {
      if (n - m !== 1) {
        const term = cdiv(cmul(zetaAt(int(n - m), wp), logmz, wp), int(factorial(m)), wp);
        if (!czero(term) && tiny(term, wp)) break;
        l = cadd(l, term, wp);
      }
      logmz = cmul(logmz, logz, wp);
    }
    let h: Mpc = M.C0;
    for (let k = 1; k < n; k++) h = cadd(h, real(F.fromRational(1n, BigInt(k), wp)), wp);
    const tail = cmul(cdiv(M.cpowInt(logz, BigInt(n - 1), wp), int(factorial(n - 1)), wp), csub(h, M.clog(M.cneg(logz), wp), wp), wp);
    l = cadd(l, tail, wp);
  } else {
    l = cmul(int(factorial(-n)), M.cpowInt(M.cneg(logz), BigInt(n - 1), wp), wp);
    let logkz: Mpc = M.C1;
    for (let k = 0; ; k++) {
      const b = bern(k - n + 1, wp);
      if (!czero(b)) {
        const term = cdiv(cmul(b, logkz, wp), int(factorial(k) * BigInt(k - n + 1)), wp);
        if (tiny(term, wp)) break;
        l = csub(l, term, wp);
      }
      logkz = cmul(logkz, logz, wp);
    }
  }
  return realPart(z, l);
}

/** Li_s(z) for a non-integer s and |z| >= 0.9. */
function polylogGeneral(s: Mpc, z: Mpc, wp: number): Mpc {
  const u = M.clog(z, wp);
  if (absD(u) >= 5) {
    const v = csub(M.C1, s, wp);
    const twopi = F.ldexp(M.mpPi(wp), 1);
    const y = cdiv(M.clog(M.cneg(z), wp), [ZERO, twopi], wp);
    const half = real({ man: 1n, exp: -1n });
    const jv = M.cpow(M.CI, v, wp);
    const jmv = M.cpow(M.CI, M.cneg(v), wp);
    const sum = cadd(cmul(jv, czeta(v, wp, cadd(half, y, wp)), wp), cmul(jmv, czeta(v, wp, csub(half, y, wp)), wp), wp);
    return cdiv(cmul(cgamma(v, wp), sum, wp), M.cpow(real(twopi), v, wp), wp);
  }
  let v: Mpc = M.C0;
  let t: Mpc = M.C1;
  for (let k = 0; ; k++) {
    const term = cmul(zetaAt(csub(s, int(k), wp), wp), t, wp);
    if (tiny(term, wp)) break;
    v = cadd(v, term, wp);
    t = cdiv(cmul(t, u, wp), int(k + 1), wp);
  }
  return cadd(cmul(cgamma(csub(M.C1, s, wp), wp), M.cpow(M.cneg(u), csub(s, M.C1, wp), wp), wp), v, wp);
}

/** eta(s) = (1 - 2**(1 - s)) zeta(s), eta(1) = log 2 (mpmath altzeta). */
export function caltzeta(s: Mpc, prec: number): Mpc {
  if (eq(s, 1)) return [M.mpLn2(prec), ZERO];
  const wp = prec + 20 + Math.max(0, -Math.max(F.mag(F.sub(s[0], F.ONE)), F.mag(s[1])));
  const f = csub(M.C1, M.cpow(int(2), csub(M.C1, s, wp), wp), wp);
  return cmul(f, zetaAt(s, wp), prec);
}

/** Li_s(z) (mpmath polylog). */
export function cpolylog(s: Mpc, z: Mpc, prec: number): Mpc {
  const wp = prec + 20;
  const rnd = (v: Mpc): Mpc => [F.round(v[0], prec), F.round(v[1], prec)];
  if (eq(z, 1)) {
    if (eq(s, 1)) throw new RangeError('polylog(1, 1) is oo');
    return rnd(zetaAt(s, wp));
  }
  if (eq(z, -1)) return M.cneg(caltzeta(s, prec));
  if (eq(s, 0)) return cdiv(z, csub(M.C1, z, wp), prec);
  if (eq(s, 1)) return M.cneg(M.clog(csub(M.C1, z, wp), prec));
  if (eq(s, -1)) {
    const d = csub(M.C1, z, wp);
    return cdiv(z, cmul(d, d, wp), prec);
  }
  const az = absD(z);
  const integer = isInt(s);
  if (az <= 0.75 || (!integer && az < 0.9)) return rnd(polylogSeries(s, z, wp));
  if (az >= 1.4 && integer) {
    const n = toInt(s);
    const ser = polylogSeries(s, cdiv(M.C1, z, wp), wp);
    return rnd(cadd(n % 2 ? ser : M.cneg(ser), polylogContinuation(n, z, wp), wp));
  }
  if (integer) return rnd(polylogUnitcircle(toInt(s), z, wp));
  return rnd(polylogGeneral(s, z, wp));
}

/**
 * Phi(z, s, a) = sum_k z^k/(a + k)^s (mpmath lerchphi): the reductions to
 * zeta and polylog, the recurrence for re(a) < 1 and the series for |z| < 1.
 * mpmath evaluates the other cases by numerical integration, which symjs does
 * not have.
 */
export function clerchphi(z: Mpc, s: Mpc, a: Mpc, prec: number): Mpc {
  const wp = prec + 20;
  if (czero(z)) return M.cpow(a, M.cneg(s), prec);
  if (eq(z, 1)) return czeta(s, prec, a);
  if (eq(a, 1)) return cdiv(cpolylog(s, z, wp), z, prec);
  if (F.cmp(a[0], F.ONE) < 0) {
    if (isInt(a) && a[0].man <= 0n) throw new RangeError('Lerch transcendent complex infinity');
    // m = ceil(1 - re a)
    const m = Number(-F.floor(F.sub(a[0], F.ONE)));
    let v: Mpc = M.C0;
    let zpow: Mpc = M.C1;
    for (let n = 0; n < m; n++) {
      v = cadd(v, cdiv(zpow, M.cpow(cadd(a, int(n), wp), s, wp), wp), wp);
      zpow = cmul(zpow, z, wp);
    }
    return cadd(cmul(zpow, clerchphi(z, s, cadd(a, int(m), wp), wp), wp), v, prec);
  }
  if (absD(z) >= 0.9) return lerchphiIntegral(z, s, a, prec);
  let sum: Mpc = M.C0;
  let zk: Mpc = M.C1;
  const ms = M.cneg(s);
  for (let k = 0; ; k++) {
    const term = cmul(zk, M.cpow(cadd(a, int(k), wp), ms, wp), wp);
    sum = cadd(sum, term, wp);
    if (tiny(term, wp + Math.max(0, F.mag(M.cabs(sum, 53))))) return [F.round(sum[0], prec), F.round(sum[1], prec)];
    zk = cmul(zk, z, wp);
  }
}

/**
 * mpmath lerchphi for Re a >= 1 (used here for |z| >= 0.9, where the series converges slowly or
 * diverges): with g = log z,
 * Phi = 1/(2 a^s) + Gamma(1 - s, -a g) (-g)^(s-1) / z^a
 *       + 2 int_0^oo sin(s atan(t/a) - t g) / ((a^2 + t^2)^(s/2) (exp(2 pi t) - 1)) dt,
 * the incomplete Gamma function as w^(1-s) E_s(w). (mpmath chops parts below 100 eps |Phi| for
 * real arguments with z > 1; evalf drops such rounding noise as it shrinks with the precision.)
 */
function lerchphiIntegral(z: Mpc, s: Mpc, a: Mpc, prec: number): Mpc {
  const wp = prec + 30;
  const g = M.clog(z, wp);
  const w = M.cneg(cmul(a, g, wp));
  const upper = cmul(M.cpow(w, csub(M.C1, s, wp), wp), cexpint(s, w, wp), wp);
  let v = cdiv(M.C1, cmul(int(2), M.cpow(a, s, wp), wp), wp);
  v = cadd(v, cdiv(cmul(upper, M.cpow(M.cneg(g), csub(s, M.C1, wp), wp), wp), M.cpow(z, a, wp), wp), wp);
  const h = cmul(real({ man: 1n, exp: -1n }), s, wp);
  const a2 = cmul(a, a, wp);
  const integrand = (t: Mpf, p: number): Mpc => {
    const tc = real(t);
    const num = M.csin(csub(cmul(s, M.catan(cdiv(tc, a, p), p), p), cmul(tc, g, p), p), p);
    const den = cmul(M.cpow(cadd(a2, real(F.mul(t, t, p)), p), h, p), real(expm1(F.mul(F.ldexp(M.mpPi(p), 1), t, p), p)), p);
    return cdiv(num, den, p);
  };
  const q = quadZeroInf(integrand, wp);
  v = cadd(v, cmul(int(2), q, wp), wp);
  return [F.round(v[0], prec), F.round(v[1], prec)];
}

/** exp(x) - 1 for x > 0, with the bits the subtraction cancels for a small x. */
function expm1(x: Mpf, wp: number): Mpf {
  return F.sub(M.exp(x, wp + Math.max(0, -F.mag(x)) + 10), F.ONE, wp);
}

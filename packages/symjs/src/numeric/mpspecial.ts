// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Arbitrary-precision special functions on complex values: gamma,
 * loggamma, polygamma, zeta, error functions, Fresnel integrals and the
 * exponential / trigonometric integrals. Power series are summed with
 * enough extra bits to absorb cancellation; gamma-type functions use the
 * Stirling / Euler-Maclaurin expansions after shifting the argument.
 */

import { at } from '../core/guard';
import * as F from './mpf';
import type { Mpf } from './mpf';
import { ONE, ZERO } from './mpf';
import * as M from './mpfun';
import { C0, C1, type Mpc, cadd, cdiv, cexp, clog, cmul, cneg, csub } from './mpfun';

const real = (x: Mpf): Mpc => [x, ZERO];
const int = (n: bigint | number): Mpc => [F.fromInt(BigInt(n)), ZERO];
const cmag = (z: Mpc): number => Math.max(F.mag(z[0]), F.mag(z[1]));
const cabsD = (z: Mpc): number => Math.hypot(F.toNumber(z[0]), F.toNumber(z[1]));
const rnd = (z: Mpc, p: number): Mpc => [F.round(z[0], p), F.round(z[1], p)];
const isZeroC = (z: Mpc): boolean => F.isZero(z[0]) && F.isZero(z[1]);
const scale = (z: Mpc, k: number): Mpc => [F.ldexp(z[0], k), F.ldexp(z[1], k)];

// ---------------------------------------------------------------------------
// Bernoulli numbers B_{2k} as exact fractions
// ---------------------------------------------------------------------------

const bern: [bigint, bigint][] = [[1n, 1n]]; // B_0, B_1 = -1/2 handled separately
function gcd(aIn: bigint, bIn: bigint): bigint {
  let a = aIn;
  let b = bIn;
  if (a < 0n) a = -a;
  while (b) [a, b] = [b, a % b];
  return a;
}
/** B_n (with B_1 = -1/2) as [p, q]. */
function bernoulli(n: number): [bigint, bigint] {
  while (bern.length <= n) {
    const m = bern.length;
    // B_m = -1/(m+1) sum_{k<m} C(m+1,k) B_k
    let p = 0n;
    let q = 1n;
    let c = 1n; // C(m+1, k)
    for (let k = 0; k < m; k++) {
      const [bp, bq] = k === 1 ? [-1n, 2n] : at(bern, k);
      // p/q += c * bp/bq
      p = p * bq + c * bp * q;
      q = q * bq;
      const g = gcd(p, q);
      p /= g;
      q /= g;
      c = (c * BigInt(m + 1 - k)) / BigInt(k + 1);
    }
    p = -p;
    q = q * BigInt(m + 1);
    const g = gcd(p, q);
    bern.push(m === 1 ? [-1n, 2n] : [p / g, q / g]);
  }
  return at(bern, n);
}

function ratC(p: bigint, q: bigint, wp: number): Mpc {
  return [F.fromRational(p, q, wp), ZERO];
}

// ---------------------------------------------------------------------------
// Gamma family
// ---------------------------------------------------------------------------

/** Shift count N so that Re(z) + N is large enough for the asymptotic series. */
function shiftCount(z: Mpc, wp: number): number {
  const target = Math.ceil(wp / 6) + 10;
  const re = F.toNumber(z[0]);
  return Math.max(0, Math.ceil(target - re));
}

/** Stirling series for log Gamma(w), Re w large. */
function stirling(w: Mpc, wp: number): Mpc {
  const logw = clog(w, wp);
  let s = csub(cmul(csub(w, real({ man: 1n, exp: -1 }), wp), logw, wp), w, wp);
  s = cadd(s, real(F.ldexp(M.log(F.ldexp(M.mpPi(wp), 1), wp), -1)), wp);
  const w2 = cmul(w, w, wp);
  let wpow = w; // w^(2k-1)
  for (let k = 1; k < 500; k++) {
    const [bp, bq] = bernoulli(2 * k);
    const t = cdiv(ratC(bp, bq * BigInt(2 * k * (2 * k - 1)), wp), wpow, wp);
    if (isZeroC(t) || cmag(t) < cmag(s) - wp - 4) break;
    s = cadd(s, t, wp);
    wpow = cmul(wpow, w2, wp);
  }
  return s;
}

/** log Gamma(z) (principal branch: loggamma(z+1) = loggamma(z) + log(z)). */
export function cloggamma(z: Mpc, prec: number): Mpc {
  const wp = prec + 30 + Math.max(0, Math.ceil(Math.log2(cabsD(z) + 2)));
  const N = shiftCount(z, wp);
  let s = stirling(cadd(z, int(N), wp), wp);
  if (N > 0) {
    // subtract sum log(z + k) via one log of the product, fixing the branch
    let P: Mpc = C1;
    let argSum = 0;
    for (let k = 0; k < N; k++) {
      const zk = cadd(z, int(k), wp);
      P = cmul(P, zk, wp);
      argSum += Math.atan2(F.toNumber(zk[1]), F.toNumber(zk[0]));
    }
    const lp = clog(P, wp);
    const m = Math.round((argSum - F.toNumber(lp[1])) / (2 * Math.PI));
    const lpFixed: Mpc = m ? [lp[0], F.add(lp[1], F.mulInt(M.mpPi(wp + 10), BigInt(2 * m)), wp)] : lp;
    s = csub(s, lpFixed, wp);
  }
  return rnd(s, prec);
}

export function cgamma(z: Mpc, prec: number): Mpc {
  const wp = prec + 30 + Math.max(0, Math.ceil(Math.log2(cabsD(z) + 2)) * 2);
  const N = shiftCount(z, wp);
  const lg = stirling(cadd(z, int(N), wp), wp);
  const wp2 = wp + Math.max(0, cmag(lg));
  let g = cexp(stirling(cadd(z, int(N), wp2), wp2), wp2);
  if (N > 0) {
    let P: Mpc = C1;
    for (let k = 0; k < N; k++) P = cmul(P, cadd(z, int(k), wp2), wp2);
    g = cdiv(g, P, wp2);
  }
  return rnd(g, prec);
}

/** polygamma(n, z) for integer n >= 0. */
export function cpolygamma(n: number, z: Mpc, prec: number): Mpc {
  const wp = prec + 30 + 2 * n;
  const N = shiftCount(z, wp) + n;
  const w = cadd(z, int(N), wp);
  let s: Mpc;
  if (n === 0) {
    // psi(w) = log w - 1/(2w) - sum B_2k / (2k w^2k)
    s = csub(clog(w, wp), cdiv(C1, scale(w, 1), wp), wp);
    const w2 = cmul(w, w, wp);
    let wpow = w2;
    for (let k = 1; k < 500; k++) {
      const [bp, bq] = bernoulli(2 * k);
      const t = cdiv(ratC(bp, bq * BigInt(2 * k), wp), wpow, wp);
      if (isZeroC(t) || cmag(t) < cmag(s) - wp - 4) break;
      s = csub(s, t, wp);
      wpow = cmul(wpow, w2, wp);
    }
    for (let k = 0; k < N; k++) s = csub(s, cdiv(C1, cadd(z, int(k), wp), wp), wp);
    return rnd(s, prec);
  }
  // (-1)^(n+1) [ (n-1)!/w^n + n!/(2 w^(n+1)) + sum B_2k (2k+n-1)!/((2k)! w^(2k+n)) ]
  const fact = (m: number): bigint => {
    let r = 1n;
    for (let i = 2; i <= m; i++) r *= BigInt(i);
    return r;
  };
  const wn = M.cpowInt(w, BigInt(n), wp);
  s = cdiv(int(fact(n - 1)), wn, wp);
  s = cadd(s, cdiv(int(fact(n)), scale(cmul(wn, w, wp), 1), wp), wp);
  const w2 = cmul(w, w, wp);
  let wpow = cmul(wn, w2, wp);
  for (let k = 1; k < 500; k++) {
    const [bp, bq] = bernoulli(2 * k);
    const t = cdiv(ratC(bp * fact(2 * k + n - 1), bq * fact(2 * k), wp), wpow, wp);
    if (isZeroC(t) || cmag(t) < cmag(s) - wp - 4) break;
    s = cadd(s, t, wp);
    wpow = cmul(wpow, w2, wp);
  }
  if ((n + 1) % 2 === 1) s = cneg(s);
  // psi^(n)(z) = psi^(n)(z+N) - (-1)^n n! sum 1/(z+k)^(n+1)
  let corr: Mpc = C0;
  for (let k = 0; k < N; k++) corr = cadd(corr, cdiv(C1, M.cpowInt(cadd(z, int(k), wp), BigInt(n + 1), wp), wp), wp);
  corr = cmul(corr, int(fact(n)), wp);
  s = n % 2 === 0 ? csub(s, corr, wp) : cadd(s, corr, wp);
  return rnd(s, prec);
}

/** Hurwitz zeta sum_n (n + a)^-s (Riemann zeta for a = 1) by Euler-Maclaurin summation. */
export function czeta(s: Mpc, prec: number, a: Mpc = C1): Mpc {
  // zeta(3) (Apery's constant, as mpmath does) and zeta(5) are summed by binary splitting
  if (a === C1 && M.isReal(s) && F.cmp(s[0], F.fromInt(3n)) === 0) return [M.mpApery(prec), ZERO];
  if (a === C1 && M.isReal(s) && F.cmp(s[0], F.fromInt(5n)) === 0) return [M.mpZeta5(prec), ZERO];
  const wp = prec + 30 + Math.max(0, Math.ceil(Math.log2(cabsD(s) + 2)) * 2);
  const M0 = Math.ceil(wp / 3) + Math.ceil(cabsD(s)) + 9;
  let sum: Mpc = C0;
  const negS = cneg(s);
  for (let n = 0; n < M0; n++) sum = cadd(sum, M.cpow(cadd(a, int(n), wp), negS, wp), wp);
  const Nc = cadd(a, int(M0), wp);
  const Nms = M.cpow(Nc, negS, wp);
  sum = cadd(sum, cdiv(cmul(Nms, Nc, wp), csub(s, C1, wp), wp), wp);
  sum = cadd(sum, scale(Nms, -1), wp);
  // sum_k B_2k/(2k)! s(s+1)...(s+2k-2) N^(-s-2k+1)
  let poch: Mpc = s; // s(s+1)...(s+2k-2)
  let npow = cdiv(Nms, Nc, wp); // N^(-s-1)
  let fact = 2n;
  const N2 = cmul(Nc, Nc, wp);
  for (let k = 1; k < 1000; k++) {
    const [bp, bq] = bernoulli(2 * k);
    const t = cmul(cmul(ratC(bp, bq * fact, wp), poch, wp), npow, wp);
    if (isZeroC(t) || cmag(t) < cmag(sum) - wp - 4) break;
    sum = cadd(sum, t, wp);
    poch = cmul(cmul(poch, cadd(s, int(2 * k - 1), wp), wp), cadd(s, int(2 * k), wp), wp);
    npow = cdiv(npow, N2, wp);
    fact *= BigInt((2 * k + 1) * (2 * k + 2));
  }
  return rnd(sum, prec);
}

// ---------------------------------------------------------------------------
// Power series helpers
// ---------------------------------------------------------------------------

/**
 * Sum t_0 + t_1 + ... where t_{k+1} = t_k * next(k). Stops once terms
 * are below 2**-wp relative to the sum and decreasing.
 */
function series(t0: Mpc, next: (k: number) => Mpc, wp: number, weight?: (k: number) => Mpc): Mpc {
  let t = t0;
  let s = weight ? cmul(t0, weight(0), wp) : t0;
  let prevMag = Infinity;
  for (let k = 0; k < 100000; k++) {
    t = cmul(t, next(k), wp);
    const term = weight ? cmul(t, weight(k + 1), wp) : t;
    const mg = cmag(term);
    if (isZeroC(term) || (mg < cmag(s) - wp - 4 && mg < prevMag)) break;
    prevMag = mg;
    s = cadd(s, term, wp);
  }
  return s;
}

const invInt = (n: number, wp: number): Mpc => [F.fromRational(1n, BigInt(n), wp), ZERO];

/** Extra working bits for a series whose terms peak near exp(c*|z|^2). */
const extraBits = (z: Mpc, c: number): number => Math.ceil(c * cabsD(z) ** 2 * 1.4427) + 10;

/** sum (-1)^n z^(2n+1) / (n! (2n+1)), i.e. erf(z) * sqrt(pi)/2 (sgn = -1) or erfi (sgn = +1). */
function erfSeries(z: Mpc, wp: number, sgn: number): Mpc {
  const z2 = cmul(z, z, wp);
  const mz2 = sgn < 0 ? cneg(z2) : z2;
  return series(z, (k) => cdiv(mz2, int(k + 1), wp), wp, (k) => invInt(2 * k + 1, wp));
}

const twoOverSqrtPi = (wp: number): Mpf => F.div(F.fromInt(2n), F.sqrt(M.mpPi(wp), wp), wp);

export function cerf(z: Mpc, prec: number): Mpc {
  const wp = prec + extraBits(z, 1) + 10;
  return rnd(cmul(erfSeries(z, wp, -1), real(twoOverSqrtPi(wp)), wp), prec);
}

export function cerfc(z: Mpc, prec: number): Mpc {
  // 1 - erf(z) loses about |z|^2 log2(e) bits for large positive real part
  const wp = prec + 2 * extraBits(z, 1) + 10;
  return rnd(csub(C1, cerf(z, wp), wp), prec);
}

export function cerfi(z: Mpc, prec: number): Mpc {
  const wp = prec + extraBits(z, 1) + 10;
  return rnd(cmul(erfSeries(z, wp, 1), real(twoOverSqrtPi(wp)), wp), prec);
}

/** erfinv(x) for real |x| < 1 by Newton iteration. */
export function erfinv(x: Mpf, prec: number): Mpf {
  const xv = F.toNumber(x);
  if (Math.abs(xv) >= 1) throw new RangeError('erfinv domain');
  let y = F.fromNumber(erfinvDouble(xv));
  let wp = 60;
  // erf(y) - x cancels about -log2(1 - |x|) bits near the ends of the domain
  const wp2 = prec + 20 + Math.max(0, -F.mag(F.sub(F.ONE, F.abs(x))));
  for (let i = 0; i < 60; i++) {
    wp = Math.min(wp * 2, wp2);
    // y -= (erf(y) - x) * sqrt(pi)/2 * exp(y^2)
    const e = cerf(real(y), wp)[0];
    const d = F.mul(F.sub(e, x, wp), F.ldexp(F.mul(F.sqrt(M.mpPi(wp), wp), M.exp(F.mul(y, y, wp), wp), wp), -1), wp);
    y = F.sub(y, d, wp);
    if (wp === wp2 && (F.isZero(d) || F.mag(d) < F.mag(y) - wp2 + 4)) break;
  }
  return F.round(y, prec);
}

function erfinvDouble(x: number): number {
  // Giles' approximation refined by two Newton steps
  let w = -Math.log((1 - x) * (1 + x));
  let p: number;
  if (w < 5) {
    w -= 2.5;
    p = 2.81022636e-8;
    for (const c of [3.43273939e-7, -3.5233877e-6, -4.39150654e-6, 0.00021858087, -0.00125372503, -0.00417768164, 0.246640727, 1.50140941]) p = c + p * w;
  } else {
    w = Math.sqrt(w) - 3;
    p = -0.000200214257;
    for (const c of [0.000100950558, 0.00134934322, -0.00367342844, 0.00573950773, -0.0076224613, 0.00943887047, 1.00167406, 2.83297682]) p = c + p * w;
  }
  return p * x;
}

/** Fresnel S (which = 'S') or C. */
export function cfresnel(which: 'S' | 'C', z: Mpc, prec: number): Mpc {
  const wp = prec + extraBits(z, Math.PI / 2) + 10;
  const pi2 = real(F.ldexp(M.mpPi(wp), -1));
  const z2 = cmul(z, z, wp);
  // u = pi/2 z^2; S = sum (-1)^n u^(2n+1) z / ((2n+1)! (4n+3)), C = sum (-1)^n u^(2n) z / ((2n)! (4n+1))
  const u = cmul(pi2, z2, wp);
  const mu2 = cneg(cmul(u, u, wp));
  if (which === 'S') {
    const t0 = cmul(u, z, wp);
    const s = series(t0, (k) => cdiv(mu2, int((2 * k + 2) * (2 * k + 3)), wp), wp, (k) => invInt(4 * k + 3, wp));
    return rnd(s, prec);
  }
  const s = series(z, (k) => cdiv(mu2, int((2 * k + 1) * (2 * k + 2)), wp), wp, (k) => invInt(4 * k + 1, wp));
  return rnd(s, prec);
}

/** gamma + (log z - log(1/z))/2: log z with the real-axis convention of Ei/Ci. */
function eulerLog(z: Mpc, wp: number): Mpc {
  const l1 = clog(z, wp);
  const l2 = clog(cdiv(C1, z, wp), wp);
  return cadd(real(M.mpEuler(wp)), scale(csub(l1, l2, wp), -1), wp);
}

/** Ei(z) = gamma + log z + sum z^k/(k k!). */
export function cei(z: Mpc, prec: number): Mpc {
  const wp = prec + Math.ceil(cabsD(z) * 1.4427) + 20;
  const s = series(z, (k) => cdiv(z, int(k + 2), wp), wp, (k) => invInt(k + 1, wp));
  return rnd(cadd(eulerLog(z, wp), s, wp), prec);
}

export function cli(z: Mpc, prec: number): Mpc {
  const wp = prec + 20;
  return cei(clog(z, wp), prec);
}

/** Si / Shi (hyperbolic) via sum (+-1)^k z^(2k+1)/((2k+1)(2k+1)!). */
export function csi(z: Mpc, prec: number, hyperbolic: boolean): Mpc {
  const wp = prec + Math.ceil(cabsD(z) * 1.4427) + 20;
  const z2 = cmul(z, z, wp);
  const m = hyperbolic ? z2 : cneg(z2);
  const s = series(z, (k) => cdiv(m, int((2 * k + 2) * (2 * k + 3)), wp), wp, (k) => invInt(2 * k + 1, wp));
  return rnd(s, prec);
}

/** Ci / Chi via gamma + log z + sum (+-1)^k z^(2k)/(2k (2k)!). */
export function cci(z: Mpc, prec: number, hyperbolic: boolean): Mpc {
  const wp = prec + Math.ceil(cabsD(z) * 1.4427) + 20;
  const z2 = cmul(z, z, wp);
  const m = hyperbolic ? z2 : cneg(z2);
  const t0 = scale(m, -1); // k = 1 term before weighting: z^2/2!
  const s = series(t0, (k) => cdiv(m, int((2 * k + 3) * (2 * k + 4)), wp), wp, (k) => invInt(2 * k + 2, wp));
  const base = cadd(real(M.mpEuler(wp)), clog(z, wp), wp);
  return rnd(cadd(base, s, wp), prec);
}

/** Lower incomplete gamma: z^s e^-z sum z^k / (s (s+1) ... (s+k)). */
export function clowergamma(s: Mpc, z: Mpc, prec: number): Mpc {
  const wp = prec + Math.ceil(cabsD(z) * 1.4427) + 30;
  const t0 = cdiv(C1, s, wp);
  const sum = series(t0, (k) => cdiv(z, cadd(s, int(k + 1), wp), wp), wp);
  const pre = cmul(M.cpow(z, s, wp), cexp(cneg(z), wp), wp);
  return rnd(cmul(pre, sum, wp), prec);
}

export function cuppergamma(s: Mpc, z: Mpc, prec: number): Mpc {
  const wp = prec + 2 * Math.ceil(cabsD(z) * 1.4427) + 30;
  return rnd(csub(cgamma(s, wp), clowergamma(s, z, wp), wp), prec);
}

export { ONE };

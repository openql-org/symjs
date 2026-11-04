// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from mpmath 1.3.0 (libmp/libhyper.py: mpf_ei, mpc_ei, mpf_expint,
// mpf_ci_si, mpc_ci_si_taylor; functions/expintegrals.py: ci, si, chi, shi,
// expint), Copyright (c) 2005-2023 Fredrik Johansson and mpmath contributors,
// BSD 3-Clause License (see LICENSE).

/**
 * @file Exponential and trigonometric integrals at arbitrary precision: Ei,
 * E1 and E_n (expint), li, Si, Ci, Shi, Chi. Small arguments use the Taylor
 * series in fixed point; large arguments use the asymptotic expansions, as
 * mpmath does, so that Ei(10**7) does not sum millions of terms.
 */

import * as F from './mpf';
import type { Mpf } from './mpf';
import { ONE, ZERO } from './mpf';
import * as M from './mpfun';
import { type Mpc, cadd, cdiv, cexp, clog, cmul, cneg, csub } from './mpfun';
import { cuppergamma } from './mpspecial';
import { MpSpecialValue } from './mpeval';

const rnd = (z: Mpc, p: number): Mpc => [F.round(z[0], p), F.round(z[1], p)];
const real = (x: Mpf): Mpc => [x, ZERO];
const babs = (n: bigint): bigint => (n < 0n ? -n : n);

/** Python floor division a // b. */
function fdiv(a: bigint, b: bigint): bigint {
  const q = a / b;
  return a % b !== 0n && a < 0n !== b < 0n ? q - 1n : q;
}

/** mpmath to_int: truncation toward zero. */
function trunc(x: Mpf): bigint {
  if (x.exp >= 0n) return x.man << x.exp;
  return x.man < 0n ? -(-x.man >> -x.exp) : x.man >> -x.exp;
}

const eulerFixed = (wp: number): bigint => F.toFixed(M.mpEuler(wp + 10), wp);
const halfPi = (wp: number): Mpf => F.ldexp(M.mpPi(wp), -1);

/** sum_{k>=1} x^k/(k k!) in fixed point (mpmath ei_taylor). */
function eiTaylor(x: bigint, prec: number): bigint {
  const P = BigInt(prec);
  let s = x;
  let t = x;
  for (let k = 2n; t !== 0n; k++) {
    t = fdiv((t * x) >> P, k);
    s += fdiv(t, k);
  }
  return s;
}

/** sum_k k!/x^k in fixed point (mpmath ei_asymptotic). */
function eiAsymptotic(xIn: bigint, prec: number): bigint {
  const P = BigInt(prec);
  const one = 1n << P;
  const x = fdiv(one << P, xIn);
  let t = x;
  let s = one + x;
  for (let k = 2n; t !== 0n; k++) {
    t = (k * t * x) >> P;
    s += t;
  }
  return s;
}

/** Ei(x) for real x != 0 (mpmath mpf_ei). */
export function realEi(x: Mpf, prec: number): Mpf {
  if (F.isZero(x)) throw new RangeError('Ei(0) is -oo');
  const xmag = F.mag(x);
  let wp = prec + 20;
  const asymptotic = xmag > wp || babs(trunc(x)) > BigInt(Math.floor(wp * 0.693) + 10);
  if (asymptotic) {
    // (for xmag > wp the sum is 1; exp(x) is then out of range anyway)
    const v = F.fromFixed(eiAsymptotic(F.toFixed(x, wp), wp), wp);
    return F.div(F.mul(v, M.exp(x, wp), wp), x, prec);
  }
  wp += 2 * Number(babs(trunc(x)));
  const v = eiTaylor(F.toFixed(x, wp), wp) + eulerFixed(wp);
  return F.add(F.fromFixed(v, wp), M.log(F.abs(x), wp), prec);
}

/** sum_k x^k/(k k!) for complex fixed-point x (mpmath complex_ei_taylor). */
function complexEiTaylor(zre: bigint, zim: bigint, prec: number): [bigint, bigint] {
  const P = BigInt(prec);
  let [sre, tre, sim, tim] = [zre, zre, zim, zim];
  for (let k = 2n; babs(tre) + babs(tim) > 5n; k++) {
    [tre, tim] = [fdiv(tre * zre - tim * zim, k) >> P, fdiv(tre * zim + tim * zre, k) >> P];
    sre += fdiv(tre, k);
    sim += fdiv(tim, k);
  }
  return [sre, sim];
}

/** sum_k k!/z^k for complex fixed-point z, or undefined when it does not converge (mpmath complex_ei_asymptotic). */
function complexEiAsymptotic(zre: bigint, zim: bigint, prec: number): [bigint, bigint] | undefined {
  const P = BigInt(prec);
  const one = 1n << P;
  const m = (zim * zim + zre * zre) >> P;
  const xre = fdiv(zre << P, m);
  const xim = fdiv(-zim << P, m);
  let [tre, tim] = [xre, xim];
  let [sre, sim] = [one + xre, xim];
  for (let k = 2n; babs(tre) + babs(tim) > 1000n; k++) {
    [tre, tim] = [((tre * xre - tim * xim) * k) >> P, ((tre * xim + tim * xre) * k) >> P];
    sre += tre;
    sim += tim;
    if (k > BigInt(prec)) return undefined;
  }
  return [sre, sim];
}

/**
 * Ei(z) (e1 = false) or E1(z) (e1 = true) for complex z != 0 (mpmath mpc_ei):
 * the asymptotic expansion for large |z|, else the Taylor series.
 */
function complexEi(zIn: Mpc, prec: number, e1: boolean): Mpc {
  const z = e1 ? cneg(zIn) : zIn;
  const [a, b] = z;
  if (F.isZero(b)) {
    if (!e1) return [realEi(a, prec), ZERO];
    // E1(x) = -Ei(-x) - i pi for x < 0
    return [F.neg(realEi(a, prec)), a.man > 0n ? F.neg(M.mpPi(prec)) : ZERO];
  }
  let wp = prec + 40;
  const zmag = Math.max(F.mag(a), F.mag(b));
  const asymptotic = zmag > wp || babs(trunc(a)) + babs(trunc(b)) > BigInt(Math.floor(wp * 0.693) + 20);
  if (asymptotic) {
    const s = complexEiAsymptotic(F.toFixed(a, wp), F.toFixed(b, wp), wp);
    if (s) {
      const v0: Mpc = [F.fromFixed(s[0], wp), F.fromFixed(s[1], wp)];
      const v = cdiv(cmul(v0, cexp(z, wp), wp), z, wp);
      if (e1) return rnd(cneg(v), prec);
      const pi = M.mpPi(wp);
      return [F.round(v[0], prec), b.man < 0n ? F.sub(v[1], pi, prec) : F.add(v[1], pi, prec)];
    }
  }
  wp += 2 * Number(trunc(M.cabs(z, 5)));
  const [vre, vim] = complexEiTaylor(F.toFixed(a, wp), F.toFixed(b, wp), wp);
  const v: Mpc = [F.fromFixed(vre + eulerFixed(wp), wp), F.fromFixed(vim, wp)];
  const r = cadd(v, clog(e1 ? zIn : z, wp), prec);
  return e1 ? cneg(r) : r;
}

/** Ei(z). */
export function cei(z: Mpc, prec: number): Mpc {
  return complexEi(z, prec, false);
}

/** E1(z) = expint(1, z). */
export function ce1(z: Mpc, prec: number): Mpc {
  return complexEi(z, prec, true);
}

/** li(z) = Ei(log z). */
export function cli(z: Mpc, prec: number): Mpc {
  return cei(clog(z, prec + 20), prec);
}

const factorial = (n: number): bigint => {
  let r = 1n;
  for (let i = 2n; i <= BigInt(n); i++) r *= i;
  return r;
};

/**
 * E_n(z) for an integer n (mpmath mpf_expint without the gamma option): the
 * asymptotic series for a large real z (finite for n <= 0, so exact for any z),
 * E1 for n = 1, and E_n from E1 by the finite sum for n > 1.
 */
function expintInt(n: number, z: Mpc, prec: number): Mpc {
  let wp = prec + 20;
  const zmag = Math.max(F.mag(z[0]), F.mag(z[1]));
  const ez = cexp(cneg(z), wp);
  if (n === 0) return cdiv(ez, z, prec);
  if (n < 0 || (M.isReal(z) && asymptoticExpint(n, z[0], wp))) {
    // exp(-z)/z sum_k n (n+1) ... (n+k-1) (-1/z)^k in fixed point
    const P = BigInt(wp);
    const r: Mpc = cdiv(real(F.fromInt(-1n)), z, wp);
    const rre = F.toFixed(r[0], wp);
    const rim = F.toFixed(r[1], wp);
    let m = BigInt(n);
    let [tre, tim] = [rre * m, rim * m];
    let [sre, sim] = [1n << P, 0n];
    while (m !== 0n && (tre !== 0n || tim !== 0n)) {
      sre += tre;
      sim += tim;
      m++;
      [tre, tim] = [(m * (rre * tre - rim * tim)) >> P, (m * (rre * tim + rim * tre)) >> P];
    }
    const v = cmul(cdiv(ez, z, wp), [F.fromFixed(sre, wp), F.fromFixed(sim, wp)], prec);
    if (n < 0 || z[0].man > 0n) return v;
    // the branch-cut term of E_n(x) for x < 0: -pi (-x)^(n-1)/(n-1)! i
    const im = F.div(F.mul(M.mpPi(wp), F.powInt(F.neg(z[0]), BigInt(n - 1), wp), wp), F.fromInt(-factorial(n - 1)), prec);
    return [v[0], im];
  }
  if (n === 1) return ce1(z, prec);
  // E_n(z) = ((-z)^(n-1) E1(z) + exp(-z) sum_{k=0}^{n-2} (n-k-2)! (-z)^k) / (n-1)!,
  // which cancels about (n - 1) log2|z| bits
  wp += (n - 1) * Math.max(0, zmag) + 10;
  const mz = cneg(z);
  let s: Mpc = M.C0;
  let pw: Mpc = M.C1;
  for (let k = 0; k <= n - 2; k++) {
    s = cadd(s, cmul(pw, real(F.fromInt(factorial(n - k - 2))), wp), wp);
    pw = cmul(pw, mz, wp);
  }
  const t1 = cmul(pw, ce1(z, wp), wp);
  return cdiv(cadd(t1, cmul(cexp(mz, wp), s, wp), wp), real(F.fromInt(factorial(n - 1))), prec);
}

/** True when the asymptotic series of E_n(x), n > 0, reaches 2**-wp (mpmath mpf_expint). */
function asymptoticExpint(n: number, x: Mpf, wp: number): boolean {
  const xmag = F.mag(x);
  const nmag = F.bitLength(BigInt(n));
  const xi = Number(babs(trunc(x)));
  const m = Math.min(Math.max(1, xi - n), 2 * wp);
  const siz = -n * nmag + (m + n) * F.bitLength(BigInt(m + n)) - m * xmag - Math.floor((144 * m) / 100);
  return siz < -wp - 10;
}

/** expint(nu, z) = E_nu(z) (mpmath expint): z**(nu - 1) Gamma(1 - nu, z) for a non-integer order. */
export function cexpint(nu: Mpc, z: Mpc, prec: number): Mpc {
  if (F.isZero(z[0]) && F.isZero(z[1])) {
    // the integral from 1 to infinity of t**-nu
    // mpmath gives +inf for re(nu) <= 1 (SymPy expint(1, 0).evalf() == oo)
    if (F.cmp(nu[0], ONE) <= 0) throw new MpSpecialValue('inf');
    return cdiv(M.C1, csub(nu, M.C1, prec + 10), prec);
  }
  const [np, nq] = F.toRational(nu[0]);
  if (M.isReal(nu) && nq === 1n && np >= -100000n && np <= 100000n) return expintInt(Number(np), z, prec);
  const wp = prec + 20;
  return cmul(M.cpow(z, csub(nu, M.C1, wp), wp), cuppergamma(csub(M.C1, nu, wp), z, wp), prec);
}

// ---------------------------------------------------------------------------
// Si, Ci, Shi, Chi
// ---------------------------------------------------------------------------

/** Ci(x) - (euler + log x) (which = 0) or Si(x) (which = 1) by the Taylor series (mpmath mpf_ci_si_taylor). */
function ciSiTaylor(xIn: Mpf, wp: number, which: 0 | 1): Mpf {
  const P = BigInt(wp);
  const x = F.toFixed(xIn, wp);
  const x2 = -(x * x) >> P;
  let [s, t, k] = which === 0 ? [0n, 1n << P, 2n] : [x, x, 3n];
  while (t !== 0n) {
    t = fdiv(t * x2, k * (k - 1n)) >> P;
    s += fdiv(t, k);
    k += 2n;
  }
  return F.fromFixed(s, wp);
}

/** [Ci(x), Si(x)] for real x != 0 (mpmath mpf_ci_si; Ci of a negative x without its i pi). */
export function realCiSi(x: Mpf, prec: number): [Mpf, Mpf] {
  if (F.isZero(x)) throw new RangeError('Ci(0) is -oo');
  let wp = prec + 20;
  const mag = F.mag(x);
  const neg = x.man < 0n;
  if (mag < -wp) {
    // Ci(x) ~ euler + log|x|, Si(x) ~ x
    return [F.add(M.mpEuler(wp), M.log(F.abs(x), wp), prec), F.round(x, prec)];
  }
  if (mag > wp) {
    // Ci(x) ~ sin(x)/x, Si(x) ~ pi/2
    const si = F.round(halfPi(prec + 10), prec);
    return [F.div(M.sin(x, wp), x, prec), neg ? F.neg(si) : si];
  }
  wp += Math.abs(mag);
  if (!(mag - 1 > Math.log2(wp))) {
    const si = F.round(ciSiTaylor(x, wp, 1), prec);
    const ci = F.add(F.add(ciSiTaylor(x, wp, 0), M.mpEuler(wp), wp), M.log(F.abs(x), wp), prec);
    return [ci, si];
  }
  // the asymptotic series for |x| >> 1
  const ax = F.abs(x);
  const P = BigInt(wp);
  const xr = fdiv(1n << (2n * P), F.toFixed(ax, wp));
  let s1 = 1n << P;
  let s2 = xr;
  let t = xr;
  for (let k = 2n; t !== 0n; ) {
    t = (-t * xr * k) >> P;
    k++;
    s1 += t;
    t = (t * xr * k) >> P;
    k++;
    s2 += t;
  }
  const f1 = F.div(F.fromFixed(s1, wp), ax, wp);
  const f2 = F.div(F.fromFixed(s2, wp), ax, wp);
  const [sin, cos] = M.sinCos(ax, wp);
  // Ci(x) = sin(x) f1 - cos(x) f2, Si(x) = pi/2 - cos(x) f1 - sin(x) f2
  const si = F.sub(halfPi(wp), F.add(F.mul(cos, f1, wp), F.mul(sin, f2, wp), wp), wp);
  return [F.sub(F.mul(sin, f1, wp), F.mul(cos, f2, wp), prec), F.round(neg ? F.neg(si) : si, prec)];
}

/** Ci(z) - (euler + log z) (which = 0) or Si(z) (which = 1) for complex z with |z| < 4 (mpmath mpc_ci_si_taylor). */
function complexCiSiTaylor(z: Mpc, wpIn: number, which: 0 | 1): Mpc {
  const mag = Math.max(F.mag(z[0]), F.mag(z[1]));
  const wp = wpIn + (2 - mag);
  const P = BigInt(wp);
  const zre = F.toFixed(z[0], wp);
  const zim = F.toFixed(z[1], wp);
  const z2re = (zim * zim - zre * zre) >> P;
  const z2im = (-2n * zre * zim) >> P;
  let [sre, sim, tre, tim, k] = which === 0 ? [0n, 0n, 1n << P, 0n, 2n] : [zre, zim, zre, zim, 3n];
  while ((babs(tre) > babs(tim) ? babs(tre) : babs(tim)) > 2n) {
    const f = k * (k - 1n);
    [tre, tim] = [fdiv(tre * z2re - tim * z2im, f) >> P, fdiv(tre * z2im + tim * z2re, f) >> P];
    sre += fdiv(tre, k);
    sim += fdiv(tim, k);
    k += 2n;
  }
  return [F.fromFixed(sre, wp), F.fromFixed(sim, wp)];
}

/** True when the complex Taylor series applies (mpmath: 2**-wp <= |z| < 4). */
const taylorRange = (z: Mpc, wp: number): boolean => {
  const mag = Math.max(F.mag(z[0]), F.mag(z[1]));
  return mag <= 2 && mag >= -wp;
};

const iTimes = (z: Mpc): Mpc => [F.neg(z[1]), z[0]];
const addIm = (v: Mpc, im: Mpf, prec: number): Mpc => [F.round(v[0], prec), F.add(v[1], im, prec)];

/** Ci(z) (mpmath ci). */
export function cci(z: Mpc, prec: number): Mpc {
  const [re, im] = z;
  if (F.isZero(im)) {
    const ci = realCiSi(re, prec)[0];
    return [ci, re.man < 0n ? M.mpPi(prec) : ZERO];
  }
  const wp = prec + 20;
  if (taylorRange(z, wp)) {
    const [cre, cim] = complexCiSiTaylor(z, wp, 0);
    return cadd([F.add(cre, M.mpEuler(wp), wp), cim], clog(z, wp), prec);
  }
  // (Ei(iz) + Ei(-iz))/2 with the branch terms of mpmath _ci_generic
  const jz = iTimes(z);
  const sum = cadd(cei(jz, wp), cei(cneg(jz), wp), wp);
  const h: Mpc = [F.ldexp(sum[0], -1), F.ldexp(sum[1], -1)];
  const pi = M.mpPi(wp);
  if (F.isZero(re)) return addIm(h, im.man > 0n ? F.ldexp(pi, -1) : F.neg(F.ldexp(pi, -1)), prec);
  if (re.man < 0n) return addIm(h, im.man >= 0n ? pi : F.neg(pi), prec);
  return rnd(h, prec);
}

/** Si(z) (mpmath si). */
export function csi(z: Mpc, prec: number): Mpc {
  const [re, im] = z;
  if (F.isZero(im)) return [realCiSi(re, prec)[1], ZERO];
  const wp = prec + 20;
  if (taylorRange(z, wp)) return rnd(complexCiSiTaylor(z, wp, 1), prec);
  // -i/2 (Ei(iz) - Ei(-iz)) -+ pi/2
  const jz = iTimes(z);
  const d = csub(cei(jz, wp), cei(cneg(jz), wp), wp);
  const v: Mpc = [F.ldexp(d[1], -1), F.neg(F.ldexp(d[0], -1))];
  if (F.isZero(re)) return rnd(v, prec);
  const hp = halfPi(wp);
  return [re.man > 0n ? F.sub(v[0], hp, prec) : F.add(v[0], hp, prec), F.round(v[1], prec)];
}

/** sum_k z^(2k+1)/((2k+1) (2k+1)!) = Shi(z) for small z. */
function shiSeries(z: Mpc, wp: number): Mpc {
  const z2 = cmul(z, z, wp);
  let t = z;
  let s = z;
  for (let k = 1; ; k++) {
    t = cdiv(cmul(t, z2, wp), real(F.fromInt(BigInt(2 * k * (2 * k + 1)))), wp);
    const term = cdiv(t, real(F.fromInt(BigInt(2 * k + 1))), wp);
    if (F.isZero(term[0]) && F.isZero(term[1])) return s;
    if (Math.max(F.mag(term[0]), F.mag(term[1])) < Math.max(F.mag(s[0]), F.mag(s[1])) - wp) return s;
    s = cadd(s, term, wp);
  }
}

/** Shi(z) (mpmath shi). */
export function cshi(z: Mpc, prec: number): Mpc {
  const wp = prec + 20;
  if (Math.max(F.mag(z[0]), F.mag(z[1])) < -1) return rnd(shiSeries(z, wp), prec);
  const d = csub(cei(z, wp), cei(cneg(z), wp), wp);
  const v: Mpc = [F.ldexp(d[0], -1), F.ldexp(d[1], -1)];
  const sgn = F.sign(z[1]);
  if (sgn === 0) return rnd(v, prec);
  const hp = halfPi(wp);
  return addIm(v, sgn > 0 ? F.neg(hp) : hp, prec);
}

/** Chi(z) (mpmath chi). */
export function cchi(z: Mpc, prec: number): Mpc {
  const wp = prec + 20;
  const s = cadd(cei(z, wp), cei(cneg(z), wp), wp);
  const v: Mpc = [F.ldexp(s[0], -1), F.ldexp(s[1], -1)];
  const sgn = F.sign(z[1]);
  if (sgn > 0) return addIm(v, halfPi(wp), prec);
  if (sgn < 0) return addIm(v, F.neg(halfPi(wp)), prec);
  if (z[0].man < 0n) return addIm(v, M.mpPi(wp), prec);
  return rnd(v, prec);
}

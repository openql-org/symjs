// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from mpmath 1.3.0 (functions/orthogonal.py: spherharm), Copyright (c)
// 2005-2023 Fredrik Johansson and mpmath contributors, BSD 3-Clause License
// (see LICENSE).

/**
 * @file The spherical harmonic Y_l^m(theta, phi) at arbitrary precision
 * (mpmath spherharm), for integer and non-integer degree and order.
 */

import { EvalfValueError, NotImplementedError } from '../core/errors';
import { at, defined } from '../core/guard';
import * as F from './mpf';
import type { Mpf } from './mpf';
import { ZERO } from './mpf';
import * as M from './mpfun';
import type { Mpc } from './mpfun';
import { chyp2f1 } from './mporthopoly';
import { MpSpecialValue, type MpPart } from './mpeval';
import { cgamma } from './mpspecial';

const real = (x: Mpf): Mpc => [x, ZERO];
const half: Mpc = [{ man: 1n, exp: -1n }, ZERO];
const intOf = (z: Mpc): bigint | undefined => {
  const [p, q] = F.toRational(z[0]);
  return F.isZero(z[1]) && q === 1n ? p : undefined;
};
const isInt = (z: Mpc): boolean => intOf(z) !== undefined;
/** A nonpositive integer (mpmath isnpint). */
const isNpInt = (z: Mpc): boolean => {
  const n = intOf(z);
  return n !== undefined && n <= 0n;
};
const rgamma = (z: Mpc, wp: number): Mpc => (isNpInt(z) ? M.C0 : M.cdiv(M.C1, cgamma(z, wp), wp));
const absD = (z: Mpc): number => F.toNumber(M.cabs(z, 53));
const fac = (n: bigint): bigint => {
  let r = 1n;
  for (let i = 2n; i <= n; i++) r *= i;
  return r;
};

/**
 * The regularized 2F1(a, b; c; z)/Gamma(c), also for a nonpositive integer c (DLMF 15.2.3_5) and,
 * by the 1 - z transformation (DLMF 15.8.4), near z = 1; at an integer c - a - b, chyp2f1 takes the
 * limit as mpmath hypercomb does (a perturbation of a that cancels at twice the precision).
 */
export function hyp2f1Regularized(a: Mpc, b: Mpc, c: Mpc, z: Mpc, wp: number): Mpc {
  const s = M.csub(M.csub(c, a, wp), b, wp);
  const w = M.csub(M.C1, z, wp);
  if (absD(z) >= 0.9 && absD(w) < 0.9 && !isInt(s)) {
    // Gamma(s)/(Gamma(c - a) Gamma(c - b)) F(a, b; 1 - s; 1 - z) + (1 - z)**s Gamma(-s)/(Gamma(a) Gamma(b)) F(c - a, c - b; 1 + s; 1 - z)
    const t1 = M.cmul(M.cmul(cgamma(s, wp), M.cmul(rgamma(M.csub(c, a, wp), wp), rgamma(M.csub(c, b, wp), wp), wp), wp), chyp2f1(a, b, M.csub(M.C1, s, wp), w, wp), wp);
    const g2 = M.cmul(cgamma(M.cneg(s), wp), M.cmul(rgamma(a, wp), rgamma(b, wp), wp), wp);
    const t2 = M.cmul(M.cmul(M.cpow(w, s, wp), g2, wp), chyp2f1(M.csub(c, a, wp), M.csub(c, b, wp), M.cadd(M.C1, s, wp), w, wp), wp);
    return M.cadd(t1, t2, wp);
  }
  if (!isNpInt(c)) return M.cmul(chyp2f1(a, b, c, z, wp), rgamma(c, wp), wp);
  // (a)_k (b)_k z**k / k! 2F1(a + k, b + k; k + 1; z) with k = 1 - c
  const k = 1n - defined(intOf(c), 'the integer c');
  let f: Mpc = M.C1;
  for (let j = 0n; j < k; j++) {
    const aj = M.cadd(a, real(F.fromInt(j)), wp);
    const bj = M.cadd(b, real(F.fromInt(j)), wp);
    f = M.cdiv(M.cmul(f, M.cmul(M.cmul(aj, bj, wp), z, wp), wp), real(F.fromInt(j + 1n)), wp);
  }
  const kk = real(F.fromInt(k));
  return M.cmul(f, chyp2f1(M.cadd(a, kk, wp), M.cadd(b, kk, wp), M.cadd(kk, M.C1, wp), z, wp), wp);
}

/** Y_l^m for a natural l and an integer m (functions.wolfram.com/Polynomials/SphericalHarmonicY/26/01/02/0004/). */
function natural(l: bigint, m: bigint, theta: Mpc, phi: Mpc, prec: number): Mpc {
  const am = m < 0n ? -m : m;
  if (am > l) return M.C0;
  const wp = prec + 30;
  // C = (-1)**(m if m > 0) expj(m phi) sqrt((2l + 1)(l + |m|)!/(pi (l - |m|)!)) (sin(theta)**2)**(|m|/2) / |m|! / 2**(|m| + 1)
  const st = M.csin(theta, wp);
  const s2 = M.cmul(st, st, wp);
  let c = M.cexp(M.cmul(M.CI, M.cmul(real(F.fromInt(m)), phi, wp), wp), wp);
  if (m > 0n && m % 2n === 1n) c = M.cneg(c);
  const norm = F.sqrt(F.div(F.fromInt((2n * l + 1n) * fac(l + am)), F.mul(M.mpPi(wp), F.fromInt(fac(l - am)), wp), wp), wp);
  c = M.cmul(c, real(norm), wp);
  if (am > 0n) c = M.cmul(c, M.cpow(s2, real(F.fromRational(am, 2n, wp)), wp), wp);
  c = M.cdiv(c, real(F.fromInt(fac(am) * 2n ** (am + 1n))), wp);
  // the terminating 2F1(|m| - l, l + |m| + 1; |m| + 1; sin(theta/2)**2)
  const sh = M.csin(M.cmul(half, theta, wp), wp);
  const x = M.cmul(sh, sh, wp);
  let term: Mpc = M.C1;
  let sum: Mpc = M.C1;
  for (let k = 0n; k < l - am; k++) {
    const r = F.div(F.fromInt((am - l + k) * (l + am + 1n + k)), F.fromInt((am + 1n + k) * (k + 1n)), wp);
    term = M.cmul(term, M.cmul(real(r), x, wp), wp);
    sum = M.cadd(sum, term, wp);
  }
  return M.cmul(c, sum, prec);
}

/**
 * Y_l^m for any l and m (functions.wolfram.com/HypergeometricFunctions/SphericalHarmonicYGeneral/26/01/02/0001/):
 * expj(m phi)/2 sqrt((2l + 1)/pi) sqrt(Gamma(l - m + 1)/Gamma(l + m + 1)) (cos(theta/2)**2)**(m/2)
 * (sin(theta/2)**2)**(-m/2) 2F1(-l, l + 1; 1 - m; sin(theta/2)**2)/Gamma(1 - m).
 */
function general(l: Mpc, m: Mpc, theta: Mpc, phi: Mpc, prec: number): Mpc {
  const wp = prec + 30;
  const g1 = M.cadd(M.csub(l, m, wp), M.C1, wp);
  const g2 = M.cadd(M.cadd(l, m, wp), M.C1, wp);
  // (SymPy raises the ValueError of mpmath's hypercomb)
  if (isNpInt(g1) || isNpInt(g2)) {
    throw new EvalfValueError(
      `hypercomb() failed to converge to the requested ${prec} bits of accuracy\nusing a working precision of ${wp} bits. The function value may be zero or\ninfinite; try passing zeroprec=N or infprec=M to bound finite values between\n2^(-N) and 2^M. Otherwise try a higher maxprec or maxterms.`,
    );
  }
  const hm = M.cmul(half, m, wp);
  const ch = M.ccos(M.cmul(half, theta, wp), wp);
  const sh = M.csin(M.cmul(half, theta, wp), wp);
  const c2 = M.cmul(ch, ch, wp);
  const s2 = M.cmul(sh, sh, wp);
  const fa = M.cneg(l);
  const fb = M.cadd(l, M.C1, wp);
  const fc = M.csub(M.C1, m, wp);
  // z = sin(theta/2)**2 is 1 at the working precision (theta = pi)
  const z1 = Math.max(F.mag(M.csub(M.C1, s2, wp)[0]), F.mag(s2[1])) < 8 - wp;
  const factors = (): XVal[] => {
    const realL = M.isReal(l);
    const realM = M.isReal(m);
    const realTheta = M.isReal(theta);
    const positive = (v: Mpc): boolean => M.isReal(v) && F.sign(v[0]) > 0;
    const norm = M.cdiv(M.cadd(M.cmul(real(F.fromInt(2n)), l, wp), M.C1, wp), real(M.mpPi(wp)), wp);
    const gg1 = cgamma(g1, wp);
    const gg2 = cgamma(g2, wp);
    // mpmath hypercomb: rgamma(1 - m) and the powers of C = [expj(m phi)/2, (2l + 1)/pi, Gamma(l - m + 1),
    // Gamma(l + m + 1), cos(theta/2)**2, sin(theta/2)**2], each an mpf (real) or an mpc as mpmath has it
    return [
      // at a pole (an integer m > 0) mpmath perturbs m by 2h > 0: 1/Gamma(1 - m - 2h) has the sign (-1)**m
      isNpInt(fc) ? { re: F.fromInt(defined(intOf(m), 'the integer m') % 2n === 0n ? 1n : -1n) } : xval(rgamma(fc, wp), realM),
      xval(M.cmul(half, M.cexp(M.cmul(M.CI, M.cmul(m, phi, wp), wp), wp), wp), false),
      xval(M.cpow(norm, half, wp), realL && positive(norm)),
      xval(M.cpow(gg1, half, wp), realL && realM && positive(gg1)),
      xval(M.cpow(gg2, M.cneg(half), wp), realL && realM && positive(gg2)),
      // (at theta = pi, cos(theta/2)**2 is 0: its power is inf for Re(m) < 0)
      z1 && F.sign(m[0]) < 0 ? { re: 'inf' } : xval(M.cpow(c2, hm, wp), realTheta && realM && positive(c2)),
      czero(s2) ? { re: 'inf' } : xval(M.cpow(s2, M.cneg(hm), wp), realTheta && realM && positive(s2)),
    ];
  };
  if (z1) {
    // z = 1 (mpmath _hyp2f1): Gauss's sum if it converges or terminates, else mpmath's
    // hyp2f1(a, b, c, 1 - 2*eps)*inf, whose sign is that of Gamma(c) Gamma(m)/(Gamma(a) Gamma(b))
    if (isNpInt(fc)) throw new NotImplementedError('spherharm at theta = pi for a positive integer order');
    // a terminating 2F1 with Re(m) > 0: the factor cos(theta/2)**m vanishes (SymPy prints mpmath's rounding
    // noise, Ynm(2, 1/2, pi, 1).evalf() = 2.36230655933323e-9 + 1.29053395513806e-9*I, which changes with the precision)
    if (F.sign(m[0]) > 0 && (isNpInt(fa) || isNpInt(fb))) return M.C0;
    if (F.sign(m[0]) < 0) {
      // Gauss: Gamma(c) Gamma(c - a - b)/(Gamma(c - a) Gamma(c - b)); the power of cos(theta/2)**2 = 0 is inf
      const gauss = M.cmul(cgamma(M.cneg(m), wp), M.cmul(cgamma(fc, wp), M.cmul(rgamma(M.csub(fc, fa, wp), wp), rgamma(M.csub(fc, fb, wp), wp), wp), wp), wp);
      throw special([xval(gauss, M.isReal(l) && M.isReal(m)), ...factors()]);
    }
    let k = M.cmul(cgamma(fc, wp), M.cmul(rgamma(fa, wp), rgamma(fb, wp), wp), wp);
    if (!czero(m)) k = M.cmul(k, cgamma(m, wp), wp);
    const hyper: XVal = M.isReal(l) && M.isReal(m) ? { re: timesInf(k[0]) } : { re: timesInf(k[0]), im: timesInf(k[1]) };
    throw special([hyper, ...factors()]);
  }
  if (czero(s2) && F.sign(m[0]) > 0) {
    // theta = 0: (sin(theta/2)**2)**(-m/2) is mpmath's inf
    if (!M.isReal(m)) throw new NotImplementedError('spherharm at theta = 0 for a complex order');
    throw special([{ re: F.ONE }, ...factors()]);
  }
  const f = hyp2f1Regularized(fa, fb, fc, s2, wp);
  const ratio = M.cdiv(M.cpow(cgamma(g1, wp), half, wp), M.cpow(cgamma(g2, wp), half, wp), wp);
  const norm = M.cpow(M.cdiv(M.cadd(M.cmul(real(F.fromInt(2n)), l, wp), M.C1, wp), real(M.mpPi(wp)), wp), half, wp);
  let c = M.cmul(half, M.cexp(M.cmul(M.CI, M.cmul(m, phi, wp), wp), wp), wp);
  c = M.cmul(M.cmul(c, norm, wp), ratio, wp);
  // (mpmath power(0, 0) = 1)
  if (!czero(hm)) c = M.cmul(c, M.cmul(M.cpow(c2, hm, wp), M.cpow(s2, M.cneg(hm), wp), wp), wp);
  return M.cmul(c, f, prec);
}

// ---- mpmath's arithmetic with inf and nan (the special values of Y at theta = 0 and pi) ----

/** A value as mpmath holds it: an mpf (no imaginary part) or an mpc, with inf and nan parts. */
export interface XVal {
  re: MpPart;
  im?: MpPart;
}
const xval = (v: Mpc, isReal: boolean): XVal => (isReal ? { re: v[0] } : { re: v[0], im: v[1] });
const czero = (z: Mpc): boolean => F.isZero(z[0]) && F.isZero(z[1]);
/** x*inf for a finite x (mpf_mul: 0*inf = nan). */
const timesInf = (x: Mpf): MpPart => (F.isZero(x) ? 'nan' : F.sign(x) > 0 ? 'inf' : '-inf');
const signOf = (p: MpPart): number => (typeof p !== 'string' ? F.sign(p) : p === 'inf' ? 1 : -1);

/** @internal */
export function mulPart(a: MpPart, b: MpPart, wp: number): MpPart {
  if (a === 'nan' || b === 'nan') return 'nan';
  if (typeof a !== 'string' && typeof b !== 'string') return F.mul(a, b, wp);
  const s = signOf(a) * signOf(b);
  return s === 0 ? 'nan' : s > 0 ? 'inf' : '-inf';
}
/** @internal */
export function addPart(a: MpPart, b: MpPart, wp: number): MpPart {
  if (typeof a !== 'string' && typeof b !== 'string') return F.add(a, b, wp);
  const sp = [a, b].filter((p): p is 'inf' | '-inf' | 'nan' => typeof p === 'string');
  return sp.includes('nan') || new Set(sp).size > 1 ? 'nan' : at(sp, 0);
}
/** @internal */
export const negPart = (a: MpPart): MpPart => (typeof a !== 'string' ? F.neg(a) : a === 'nan' ? a : a === 'inf' ? '-inf' : 'inf');

/** x*y as mpmath multiplies an mpf or mpc by an mpf or mpc. */
export function mulX(x: XVal, y: XVal, wp: number): XVal {
  if (x.im === undefined && y.im === undefined) return { re: mulPart(x.re, y.re, wp) };
  if (x.im === undefined) return { re: mulPart(x.re, y.re, wp), im: mulPart(x.re, defined(y.im), wp) };
  if (y.im === undefined) return { re: mulPart(x.re, y.re, wp), im: mulPart(x.im, y.re, wp) };
  return {
    re: addPart(mulPart(x.re, y.re, wp), negPart(mulPart(x.im, y.im, wp)), wp),
    im: addPart(mulPart(x.re, y.im, wp), mulPart(x.im, y.re, wp), wp),
  };
}

/** The product of the factors in mpmath's order (fprod), as a special value. */
function special(factors: readonly XVal[]): MpSpecialValue {
  const one: XVal = { re: F.ONE };
  const p = factors.reduce((acc, v) => mulX(acc, v, 200), one);
  // (expj(m phi) makes the product an mpc)
  return new MpSpecialValue(p.re, defined(p.im, 'the imaginary part'));
}

/** Y_l^m(theta, phi) (mpmath spherharm). */
export function mpSpherharm(args: Mpc[], prec: number): Mpc {
  const [lc, mc, theta, phi] = [at(args, 0), at(args, 1), at(args, 2), at(args, 3)];
  const l0 = intOf(lc);
  const m = intOf(mc);
  // Y_{-l-1}^m = Y_l^m for an integer l
  if (l0 !== undefined && l0 < 0n && m !== undefined) return mpSpherharm([real(F.fromInt(-(l0 + 1n))), mc, theta, phi], prec);
  if (m !== undefined && m < 0n && F.isZero(theta[0]) && F.isZero(theta[1])) return M.C0;
  if (l0 !== undefined && m !== undefined) return natural(l0, m, theta, phi, prec);
  return general(lc, mc, theta, phi, prec);
}

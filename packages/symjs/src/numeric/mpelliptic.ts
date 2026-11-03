// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from mpmath 1.3.0 (libmp/libhyper.py: mpc_agm, mpf_ellipk,
// mpc_ellipk, mpf_ellipe, mpc_ellipe), Copyright (c) 2005-2023 Fredrik
// Johansson and mpmath contributors, BSD 3-Clause License (see LICENSE).

/**
 * @file Complete elliptic integrals K(m) and E(m) at arbitrary precision
 * (mpmath ellipk, ellipe), registered as elliptic_k and elliptic_e for
 * numeric evaluation.
 */

import { NotImplementedError } from '../core/errors';
import * as F from './mpf';
import type { Mpf } from './mpf';
import { ONE, ZERO } from './mpf';
import * as M from './mpfun';
import { type Mpc, cadd, cdiv, cmul, csub } from './mpfun';

const isRealLeOne = (z: Mpc): boolean => F.isZero(z[1]) && F.cmp(z[0], ONE) <= 0;

/** agm(1, a) (mpmath mpc_agm with the principal square root). */
function agm1(a0: Mpc, prec: number): Mpc {
  const wp = prec + 20;
  let a: Mpc = M.C1;
  let b = a0;
  for (;;) {
    const a1: Mpc = [F.ldexp(F.add(a[0], b[0], wp), -1), F.ldexp(F.add(a[1], b[1], wp), -1)];
    const b1 = M.csqrt(cmul(a, b, wp), wp);
    a = a1;
    b = b1;
    const size = Math.max(F.mag(M.cabs(a, 10)), F.mag(M.cabs(b, 10)));
    const err = F.mag(M.cabs(csub(a, b, 10), 10));
    if (err < size - wp + 10) return a;
  }
}

/** K(m) = pi/(2 agm(1, sqrt(1 - m))); K(1) = oo. */
export function cellipk(m: Mpc, prec: number): Mpc {
  if (F.isZero(m[1]) && F.cmp(m[0], ONE) === 0) throw new RangeError('elliptic_k(1) is oo');
  const wp = prec + 15;
  const v = agm1(M.csqrt(csub(M.C1, m, wp), wp), wp);
  const r = cdiv([M.mpPi(wp), ZERO], v, prec);
  return [F.ldexp(r[0], -1), F.ldexp(r[1], -1)];
}

/** E(m) = (1 - m)(K(m) + 2 m K'(m)) with K' by a finite difference (mpmath mpf_ellipe, mpc_ellipe). */
export function cellipe(m: Mpc, prec: number): Mpc {
  if (F.isZero(m[1]) && F.cmp(m[0], ONE) === 0) return M.C1;
  const real = isRealLeOne(m);
  const wp = prec + (real ? 20 : 15);
  const mag = real ? F.mag(m[0]) : F.mag(M.cabs(m, 1));
  if (real && mag < -wp) return [F.ldexp(M.mpPi(prec), -1), ZERO];
  const p = Math.max(mag, 0) - wp;
  const h: Mpc = [{ man: 1n, exp: p }, ZERO];
  const K = cellipk(m, 2 * wp);
  // the real case steps to m - h, away from the branch cut m > 1
  const Kh = cellipk(real ? csub(m, h, 2 * wp) : cadd(m, h, 2 * wp), 2 * wp);
  const d = real ? csub(K, Kh, wp) : csub(Kh, K, wp);
  const kdiff: Mpc = [F.ldexp(d[0], -p), F.ldexp(d[1], -p)];
  const b = cmul(kdiff, [F.ldexp(m[0], 1), F.ldexp(m[1], 1)], wp);
  return cmul(csub(M.C1, m, wp), cadd(K, b, wp), prec);
}

// ---------------------------------------------------------------------------
// Carlson symmetric integrals and the incomplete elliptic integrals
// (mpmath functions/elliptic.py: RF_calc, RC_calc, RJ_calc, ellipf, ellipe,
// ellippi)
// ---------------------------------------------------------------------------

const ceq = (a: Mpc, b: Mpc): boolean => F.cmp(a[0], b[0]) === 0 && F.cmp(a[1], b[1]) === 0;
const czero = (a: Mpc): boolean => F.isZero(a[0]) && F.isZero(a[1]);
const isRealC = (a: Mpc): boolean => F.isZero(a[1]);
const cmagE = (a: Mpc): number => Math.max(F.mag(a[0]), F.mag(a[1]));
const quarter = (a: Mpc): Mpc => [F.ldexp(a[0], -2), F.ldexp(a[1], -2)];
const rc = (n: bigint, d: bigint, wp: number): Mpc => [F.fromRational(n, d, wp), ZERO];
const absF = (a: Mpc, wp: number): Mpf => M.cabs(a, wp);
const maxF = (xs: Mpf[]): Mpf => xs.reduce((m, v) => (F.cmp(v, m) > 0 ? v : m));
/** (k r)^(-1/6) for the tolerance r of mpmath's Carlson iterations. */
const rootTol = (k: Mpf, r: Mpf, wp: number): Mpf => M.powReal(F.mul(k, r, wp), F.fromRational(-1n, 6n, wp), wp);

/** RC(x, y) (Cauchy principal value for y < 0). */
function carlsonRC(x: Mpc, y: Mpc, r: Mpf, wpIn: number): Mpc {
  if (isRealC(y) && y[0].man < 0n) {
    const xy = csub(x, y, wpIn);
    return cmul(M.csqrt(cdiv(x, xy, wpIn), wpIn), carlsonRC(xy, M.cneg(y), r, wpIn), wpIn);
  }
  if (ceq(x, y)) return cdiv(M.C1, M.csqrt(x, wpIn), wpIn);
  const wp = wpIn + 2 * Math.max(0, cmagE(x) - cmagE(csub(x, y, wpIn)));
  if (isRealC(x) && isRealC(y)) {
    const a = M.csqrt(cdiv(x, y, wp), wp);
    if (F.cmp(x[0], y[0]) < 0) return cdiv(M.cacos(a, wp), M.csqrt(csub(y, x, wp), wp), wpIn);
    return cdiv(M.cacosh(a, wp), M.csqrt(csub(x, y, wp), wp), wpIn);
  }
  const sx = M.csqrt(x, wp);
  const sy = M.csqrt(y, wp);
  return cdiv(M.cacos(cdiv(sx, sy, wp), wp), cmul(M.csqrt(csub(M.C1, cdiv(x, y, wp), wp), wp), sy, wp), wpIn);
}

/** RF(x, y, z). */
function carlsonRF(x: Mpc, y: Mpc, z: Mpc, r: Mpf, wp: number): Mpc {
  if (ceq(y, z)) return carlsonRC(x, y, r, wp);
  if (ceq(x, z)) return carlsonRC(y, x, r, wp);
  if (ceq(x, y)) return carlsonRC(z, x, r, wp);
  const A0 = cdiv(cadd(cadd(x, y, wp), z, wp), rc(3n, 1n, wp), wp);
  const Q = F.mul(rootTol(F.fromInt(3n), r, wp), maxF([x, y, z].map((v) => absF(csub(A0, v, wp), wp))), wp);
  let [xm, ym, zm, Am] = [x, y, z, A0];
  let pow4 = F.ONE;
  for (;;) {
    const [xs, ys, zs] = [M.csqrt(xm, wp), M.csqrt(ym, wp), M.csqrt(zm, wp)];
    const lm = cadd(cadd(cmul(xs, ys, wp), cmul(xs, zs, wp), wp), cmul(ys, zs, wp), wp);
    const Am1 = quarter(cadd(Am, lm, wp));
    [xm, ym, zm] = [quarter(cadd(xm, lm, wp)), quarter(cadd(ym, lm, wp)), quarter(cadd(zm, lm, wp))];
    if (F.cmp(F.mul(pow4, Q, wp), absF(Am, wp)) < 0) break;
    Am = Am1;
    pow4 = F.ldexp(pow4, -2);
  }
  const t = cdiv([pow4, ZERO], Am, wp);
  const X = cmul(csub(A0, x, wp), t, wp);
  const Y = cmul(csub(A0, y, wp), t, wp);
  const Z = M.cneg(cadd(X, Y, wp));
  const E2 = csub(cmul(X, Y, wp), cmul(Z, Z, wp), wp);
  const E3 = cmul(cmul(X, Y, wp), Z, wp);
  const n = (k: bigint): Mpc => [F.fromInt(k), ZERO];
  let P = n(9240n);
  P = csub(P, cmul(n(924n), E2, wp), wp);
  P = cadd(P, cmul(n(385n), cmul(E2, E2, wp), wp), wp);
  P = cadd(P, cmul(n(660n), E3, wp), wp);
  P = csub(P, cmul(n(630n), cmul(E2, E3, wp), wp), wp);
  return cmul(M.cpow(Am, rc(-1n, 2n, wp), wp), cdiv(P, n(9240n), wp), wp);
}

/** RJ(x, y, z, p) where mpmath does not need its numerical-integration correction. */
function carlsonRJ(x: Mpc, y: Mpc, z: Mpc, p: Mpc, r: Mpf, wp: number): Mpc {
  if (czero(p) || [x, y, z].filter(czero).length > 1) throw new RangeError('RJ is infinite');
  const nonneg = (v: Mpc) => v[0].man >= 0n;
  /** r is real and nonnegative and a, b are complex conjugates. */
  const realConj = (r: Mpc, a: Mpc, b: Mpc): boolean => {
    if (!isRealC(r) || r[0].man < 0n) return false;
    return ceq([a[0], F.neg(a[1])], b);
  };
  let ok = nonneg(x) && nonneg(y) && nonneg(z) && p[0].man > 0n;
  ok ||= ceq(x, p) || ceq(y, p) || ceq(z, p);
  if (!ok && (!F.isZero(p[1]) || p[0].man >= 0n)) {
    const triples: [Mpc, Mpc, Mpc][] = [
      [x, y, z],
      [y, x, z],
      [z, x, y],
    ];
    ok = triples.some(([r0, a0, b0]) => realConj(r0, a0, b0));
  }
  if (!ok) throw new NotImplementedError('elliptic integral needing the integral correction of RJ');
  const two = rc(2n, 1n, wp);
  const A0 = cdiv(cadd(cadd(cadd(x, y, wp), z, wp), cmul(two, p, wp), wp), rc(5n, 1n, wp), wp);
  const delta = cmul(cmul(csub(p, x, wp), csub(p, y, wp), wp), csub(p, z, wp), wp);
  const Q = F.mul(rootTol(F.fromRational(1n, 4n, wp), r, wp), maxF([x, y, z, p].map((v) => absF(csub(A0, v, wp), wp))), wp);
  let [xm, ym, zm, pm, Am] = [x, y, z, p, A0];
  let pow4 = F.ONE;
  let S: Mpc = M.C0;
  for (;;) {
    const [sx, sy, sz, sp] = [M.csqrt(xm, wp), M.csqrt(ym, wp), M.csqrt(zm, wp), M.csqrt(pm, wp)];
    const lm = cadd(cadd(cmul(sx, sy, wp), cmul(sx, sz, wp), wp), cmul(sy, sz, wp), wp);
    const Am1 = quarter(cadd(Am, lm, wp));
    [xm, ym, zm, pm] = [quarter(cadd(xm, lm, wp)), quarter(cadd(ym, lm, wp)), quarter(cadd(zm, lm, wp)), quarter(cadd(pm, lm, wp))];
    const dm = cmul(cmul(cadd(sp, sx, wp), cadd(sp, sy, wp), wp), cadd(sp, sz, wp), wp);
    const em = cdiv(cmul(delta, [F.mul(F.mul(pow4, pow4, wp), pow4, wp), ZERO], wp), cmul(dm, dm, wp), wp);
    if (F.cmp(F.mul(pow4, Q, wp), absF(Am, wp)) < 0) break;
    S = cadd(S, cdiv(cmul(carlsonRC(M.C1, cadd(M.C1, em, wp), r, wp), [pow4, ZERO], wp), dm, wp), wp);
    pow4 = F.ldexp(pow4, -2);
    Am = Am1;
  }
  const t = cdiv([pow4, ZERO], Am, wp);
  const X = cmul(csub(A0, x, wp), t, wp);
  const Y = cmul(csub(A0, y, wp), t, wp);
  const Z = cmul(csub(A0, z, wp), t, wp);
  const P = [F.ldexp(F.neg(cadd(cadd(X, Y, wp), Z, wp)[0]), -1), F.ldexp(F.neg(cadd(cadd(X, Y, wp), Z, wp)[1]), -1)] as Mpc;
  const n = (k: bigint): Mpc => [F.fromInt(k), ZERO];
  const XYZ = cmul(cmul(X, Y, wp), Z, wp);
  const P2 = cmul(P, P, wp);
  const P3 = cmul(P2, P, wp);
  const E2 = csub(cadd(cadd(cmul(X, Y, wp), cmul(X, Z, wp), wp), cmul(Y, Z, wp), wp), cmul(n(3n), P2, wp), wp);
  const E3 = cadd(cadd(XYZ, cmul(n(2n), cmul(E2, P, wp), wp), wp), cmul(n(4n), P3, wp), wp);
  const E4 = cmul(cadd(cadd(cmul(n(2n), XYZ, wp), cmul(E2, P, wp), wp), cmul(n(3n), P3, wp), wp), P, wp);
  const E5 = cmul(XYZ, P2, wp);
  let Pn = n(24024n);
  Pn = csub(Pn, cmul(n(5148n), E2, wp), wp);
  Pn = cadd(Pn, cmul(n(2457n), cmul(E2, E2, wp), wp), wp);
  Pn = cadd(Pn, cmul(n(4004n), E3, wp), wp);
  Pn = csub(Pn, cmul(n(4158n), cmul(E2, E3, wp), wp), wp);
  Pn = csub(Pn, cmul(n(3276n), E4, wp), wp);
  Pn = cadd(Pn, cmul(n(2772n), E5, wp), wp);
  const v1 = cmul(cmul([pow4, ZERO], M.cpow(Am, rc(-3n, 2n, wp), wp), wp), cdiv(Pn, n(24024n), wp), wp);
  return cadd(v1, cmul(n(6n), S, wp), wp);
}

/** The Carlson integrals at working precision prec + 20 with mpmath's tolerance eps 2**10. */
const carlsonTol = (wp: number): Mpf => ({ man: 1n, exp: 11 - wp });
/** mpmath elliprc. */
export const RC = (x: Mpc, y: Mpc, prec: number): Mpc => carlsonRC(x, y, carlsonTol(prec + 20), prec + 20);
/** mpmath elliprf. */
export const RF = (x: Mpc, y: Mpc, z: Mpc, prec: number): Mpc => carlsonRF(x, y, z, carlsonTol(prec + 20), prec + 20);
/** mpmath elliprj. */
export const RJ = (x: Mpc, y: Mpc, z: Mpc, p: Mpc, prec: number): Mpc => carlsonRJ(x, y, z, p, carlsonTol(prec + 20), prec + 20);

/** Sum terms evaluated at working precision wp, again with the cancellation of the first sum added (mpmath sum_accurately). */
function sumAccurately(terms: (wp: number) => Mpc[], wp: number): Mpc {
  const sum = (ts: Mpc[], p: number) => ts.reduce((s, t) => cadd(s, t, p), M.C0);
  const first = terms(wp + 10);
  const s = sum(first, wp + 10);
  const cancel = Math.max(0, Math.max(...first.map(cmagE)) - cmagE(s));
  // (an exactly zero sum gives an infinite cancellation)
  const extra = Math.min(cancel, 4 * wp);
  return sum(terms(wp + 10 + extra), wp + 10 + extra);
}

/** phi reduced to |re phi| <= pi/2 and the number d of half periods removed (mpmath nint(re(phi)/pi)). */
function reducePhi(phi: Mpc, wp: number): [Mpc, bigint] {
  const pi = M.mpPi(wp);
  const x = phi[0];
  if (F.cmp(F.abs(x), F.ldexp(pi, -1)) <= 0) return [phi, 0n];
  const q = F.div(x, pi, wp);
  const d = F.floor(F.add(q, { man: 1n, exp: -1 }));
  return [[F.sub(x, F.mulInt(pi, d), wp), phi[1]], d];
}

/** F(phi | m) (mpmath ellipf). */
export function cellipf(phi: Mpc, m: Mpc, prec: number): Mpc {
  if (czero(m) || czero(phi)) return phi;
  const wp = prec + 10 + Math.max(0, F.mag(phi[0]));
  const [z, d] = reducePhi(phi, wp);
  if (d !== 0n && ceq(m, M.C1)) throw new RangeError('elliptic_f(phi, 1) is infinite for |re(phi)| > pi/2');
  const s = M.csin(z, wp);
  const c = M.ccos(z, wp);
  const v = cmul(s, RF(cmul(c, c, wp), csub(M.C1, cmul(m, cmul(s, s, wp), wp), wp), M.C1, wp), wp);
  if (d === 0n) return M.cadd(v, M.C0, prec);
  return cadd(v, cmul([F.fromInt(2n * d), ZERO], cellipk(m, wp), wp), prec);
}

/** E(phi | m) (mpmath ellipe with two arguments). */
export function cellipeInc(phi: Mpc, m: Mpc, prec: number): Mpc {
  if (czero(m) || czero(phi)) return phi;
  const wp = prec + 10 + Math.max(0, F.mag(phi[0]));
  const [z, d] = reducePhi(phi, wp);
  const v = sumAccurately((p) => {
    const s = M.csin(z, p);
    const c = M.ccos(z, p);
    const x = cmul(c, c, p);
    const y = csub(M.C1, cmul(m, cmul(s, s, p), p), p);
    const s3 = cmul(cmul(s, s, p), s, p);
    return [cmul(s, RF(x, y, M.C1, p), p), cdiv(cmul(M.cneg(m), cmul(s3, RJ(x, y, M.C1, M.C1, p), p), p), rc(3n, 1n, p), p)];
  }, wp);
  if (d === 0n) return M.cadd(v, M.C0, prec);
  return cadd(v, cmul([F.fromInt(2n * d), ZERO], cellipe(m, wp), wp), prec);
}

/** Pi(n | m) (complete) or Pi(n; phi | m) (mpmath ellippi). */
export function cellippi(n: Mpc, phi: Mpc | undefined, m: Mpc, prec: number): Mpc {
  const wp = prec + 10 + (phi ? Math.max(0, F.mag(phi[0])) : 0);
  if (!phi) {
    if (czero(m)) {
      if (ceq(n, M.C1)) throw new RangeError('elliptic_pi(1, 0) is infinite');
      return cdiv([M.mpPi(wp), ZERO], cmul(rc(2n, 1n, wp), M.csqrt(csub(M.C1, n, wp), wp), wp), prec);
    }
    if (czero(n)) return cellipk(m, prec);
    if (ceq(m, M.C1)) throw new RangeError('elliptic_pi(n, 1) is infinite');
  } else if (czero(phi)) return phi;
  const [z, d] = phi ? reducePhi(phi, wp) : [undefined, 0n];
  const v = sumAccurately((p) => {
    const [c, s] = z ? [M.ccos(z, p), M.csin(z, p)] : [M.C0, M.C1];
    const s2 = cmul(s, s, p);
    const x = cmul(c, c, p);
    const y = csub(M.C1, cmul(m, s2, p), p);
    const rj = RJ(x, y, M.C1, csub(M.C1, cmul(n, s2, p), p), p);
    return [cmul(s, RF(x, y, M.C1, p), p), cdiv(cmul(n, cmul(cmul(s2, s, p), rj, p), p), rc(3n, 1n, p), p)];
  }, wp);
  if (d === 0n) return M.cadd(v, M.C0, prec);
  return cadd(v, cmul([F.fromInt(2n * d), ZERO], cellippi(n, undefined, m, wp), wp), prec);
}

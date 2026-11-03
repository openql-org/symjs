// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from mpmath 1.3.0 (functions/functions.py: lambertw,
// _lambertw_series, _lambertw_approx_hybrid), Copyright (c) 2005-2023
// Fredrik Johansson and mpmath contributors, BSD 3-Clause License (see LICENSE).

/**
 * @file The Lambert W function W_k(z) at arbitrary precision (mpmath
 * lambertw): a starting value from the series at the branch point -1/e, a
 * double-precision approximation or the asymptotic expansion, refined by
 * Halley iteration.
 */

import { at } from '../core/guard';
import * as F from './mpf';
import type { Mpf } from './mpf';
import { ZERO } from './mpf';
import * as M from './mpfun';
import { type Mpc, cadd, cdiv, cmul, csub } from './mpfun';
import { lambertwStart } from './complex';

/** mpmath mag: the exponent of a real value, one more than the larger part's for a complex one. */
const cmagW = (z: Mpc): number => (F.isZero(z[1]) ? F.mag(z[0]) : Math.max(F.mag(z[0]), F.mag(z[1])) + 1);
const real = (x: Mpf): Mpc => [x, ZERO];
const rat = (p: number, q: number, wp: number): Mpc => real(F.fromRational(BigInt(p), BigInt(q), wp));

/**
 * The series of W at the branch point in p = +-sqrt(2 (e z + 1)) (Corless et
 * al.): [value, converged], with the extra working bits that the cancellation
 * in z + 1/e calls for.
 */
function branchSeries(z: Mpc, k: number, wp: number, tol: number): [Mpc, boolean, number] {
  const delta = cadd(z, real(M.exp(F.neg(F.ONE), 2 * wp)), 2 * wp);
  const cancellation = Math.max(0, -cmagW(delta));
  const wp2 = wp + cancellation;
  const ez1 = cadd(cmul(real(M.mpE(wp2 + 10)), z, wp2 + 10), M.C1, wp2);
  let p = M.csqrt(cmul(real(F.fromInt(2n)), ez1, wp2), wp2);
  if (k !== 0) p = M.cneg(p);
  const u: Mpc[] = [real(F.neg(F.ONE)), real(F.ONE)];
  const a: Mpc[] = [real(F.fromInt(2n)), real(F.neg(F.ONE))];
  let s: Mpc = M.C0;
  let pl: Mpc = M.C1;
  for (let l = 0; l < Math.max(2, cancellation); l++) {
    if (l >= 2) {
      let al: Mpc = M.C0;
      for (let j = 2; j < l; j++) al = cadd(al, cmul(at(u, j), at(u, l + 1 - j), wp2), wp2);
      a[l] = al;
      const t1 = cdiv(cmul(real(F.fromInt(BigInt(l - 1))), cadd(cmul(rat(1, 2, wp2), at(u, l - 2), wp2), cmul(rat(1, 4, wp2), at(a, l - 2), wp2), wp2), wp2), real(F.fromInt(BigInt(l + 1))), wp2);
      u[l] = csub(csub(t1, cmul(rat(1, 2, wp2), al, wp2), wp2), cdiv(at(u, l - 1), real(F.fromInt(BigInt(l + 1))), wp2), wp2);
    }
    const term = cmul(at(u, l), pl, wp2);
    s = cadd(s, term, wp2);
    if (cmagW(term) < -tol) return [s, true, wp2];
    pl = cmul(pl, p, wp2);
  }
  return [s, false, wp + Math.floor(cancellation / 2)];
}

/** W_k(z) (mpmath lambertw); W_k(0) for k != 0 is -oo. */
export function clambertw(z: Mpc, k: number, prec: number): Mpc {
  if (F.isZero(z[0]) && F.isZero(z[1])) {
    if (k !== 0) throw new RangeError('LambertW(0, k) is -oo for k != 0');
    return z;
  }
  let wp = prec + 20 + F.bitLength(BigInt(k === 0 ? 1 : Math.abs(k)));
  const tol = wp - 5;
  const magz = cmagW(z);
  const x = F.toNumber(z[0]);
  const y = F.toNumber(z[1]);
  const imz = F.sign(z[1]);
  let w: Mpc | undefined;
  if (-10 < magz && magz < 900 && -1000 < k && k < 1000) {
    if (magz < 1 && Math.hypot(x + 0.36787944117144, y) < 0.05 && (k === 0 || (k === -1 && imz >= 0) || (k === 1 && imz < 0))) {
      const [s, done, wp2] = branchSeries(z, k, wp, tol);
      if (done) return [F.round(s[0], prec), F.round(s[1], prec)];
      w = s;
      wp = wp2;
    } else if (k === 0 || k === -1) {
      const d = lambertwStart(x, y, k);
      w = [F.fromNumber(d.re), F.fromNumber(d.im)];
    }
  }
  if (w === undefined) {
    if (k === 0 && magz < -1) w = cmul(z, csub(M.C1, z, wp), wp);
    else if (k === -1 && imz === 0 && -0.36787944117144 < x && x < 0) {
      const L1 = M.log(F.neg(z[0]), wp);
      w = real(F.sub(L1, M.log(F.neg(L1), wp), wp));
    } else {
      const L1 = cadd(M.clog(z, wp), [ZERO, F.mulInt(M.mpPi(wp + 10), BigInt(2 * k))], wp);
      const L2 = M.clog(L1, wp);
      const t3 = cdiv(cmul(L2, csub(L2, real(F.fromInt(2n)), wp), wp), cmul(real(F.fromInt(2n)), cmul(L1, L1, wp), wp), wp);
      w = cadd(cadd(csub(L1, L2, wp), cdiv(L2, L1, wp), wp), t3, wp);
    }
  }
  // Halley iteration for w exp(w) = z
  const two = real(F.fromInt(2n));
  for (let i = 0; i < 100; i++) {
    const ew = M.cexp(w, wp);
    const wew = cmul(w, ew, wp);
    const wewz = csub(wew, z, wp);
    const den = csub(cadd(wew, ew, wp), cdiv(cmul(cadd(w, two, wp), wewz, wp), cadd(cmul(two, w, wp), two, wp), wp), wp);
    const wn = csub(w, cdiv(wewz, den, wp), wp);
    const d = csub(wn, w, wp);
    w = wn;
    if (cmagW(d) <= cmagW(wn) - tol) break;
  }
  return [F.round(w[0], prec), F.round(w[1], prec)];
}

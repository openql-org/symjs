// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from mpmath 1.3.0 (functions/orthogonal.py: legendre, legenp,
// jacobi, gegenbauer, chebyt, chebyu), Copyright (c) 2005-2023 Fredrik
// Johansson and mpmath contributors, BSD 3-Clause License (see LICENSE).

/**
 * @file Legendre, associated Legendre, Jacobi, Gegenbauer and Chebyshev
 * functions of any degree through the Gauss hypergeometric function 2F1, as
 * mpmath defines them. 2F1 is summed directly for |z| < 0.9 (or when it
 * terminates), after the Pfaff transformation for |z/(z - 1)| < 0.9 and after
 * the 1 - z transformation for |1 - z| < 0.9 (its limit at an integer
 * c - a - b) and the 1/z transformation for |z| > 1.12 (its limit at an
 * integer a - b); the other arguments (|z| about 1 away from z = 1, such as exp(+-i pi/3))
 * by mpmath's Gosper recurrence.
 */

import { NotImplementedError } from '../core/errors';
import * as F from './mpf';
import { ZERO } from './mpf';
import * as M from './mpfun';
import { type Mpc, cadd, cdiv, cmul, csub } from './mpfun';
import { cgamma } from './mpspecial';

const int = (n: bigint | number): Mpc => [F.fromInt(BigInt(n)), ZERO];
const half: Mpc = [{ man: 1n, exp: -1n }, ZERO];
const czero = (a: Mpc): boolean => F.isZero(a[0]) && F.isZero(a[1]);
const cmagO = (a: Mpc): number => Math.max(F.mag(a[0]), F.mag(a[1]));
const absD = (z: Mpc): number => F.toNumber(M.cabs(z, 53));
/** A nonpositive integer (mpmath isnpint). */
const isNpInt = (a: Mpc): boolean => F.isZero(a[1]) && a[0].man <= 0n && F.toRational(a[0])[1] === 1n;
const isInt = (a: Mpc): boolean => F.isZero(a[1]) && F.toRational(a[0])[1] === 1n;
const rnd = (z: Mpc, p: number): Mpc => [F.round(z[0], p), F.round(z[1], p)];

/** 1/Gamma(z), zero at the poles. */
const rgamma = (z: Mpc, wp: number): Mpc => (isNpInt(z) ? M.C0 : cdiv(M.C1, cgamma(z, wp), wp));
/** Gamma(z), or NotImplementedError at a pole (mpmath hypercomb takes a limit there). */
function gammaOrLimit(z: Mpc, wp: number): Mpc {
  if (isNpInt(z)) throw new NotImplementedError('a limit of the hypergeometric combination');
  return cgamma(z, wp);
}

/** sum_k (a)_k (b)_k / ((c)_k k!) z^k and the size of its largest term. */
function series2f1(a: Mpc, b: Mpc, c: Mpc, z: Mpc, wp: number): [Mpc, number] {
  let t: Mpc = M.C1;
  let s: Mpc = M.C1;
  let big = 0;
  for (let k = 0; ; k++) {
    t = cdiv(cmul(cmul(t, cadd(a, int(k), wp), wp), cmul(cadd(b, int(k), wp), z, wp), wp), cmul(cadd(c, int(k), wp), int(k + 1), wp), wp);
    if (czero(t)) return [s, big];
    big = Math.max(big, cmagO(t));
    s = cadd(s, t, wp);
    if (cmagO(t) < cmagO(s) - wp - 4 && k > 2) return [s, big];
  }
}

/** The series summed again with the bits it lost to cancellation. */
function sum2f1(a: Mpc, b: Mpc, c: Mpc, z: Mpc, wp: number): Mpc {
  const [s, big] = series2f1(a, b, c, z, wp);
  const lost = Math.max(0, big - cmagO(s));
  return lost > 10 ? series2f1(a, b, c, z, wp + lost + 10)[0] : s;
}

/** 2F1(a, b; c; z); c must not be a nonpositive integer. */
export function chyp2f1(a: Mpc, b: Mpc, c: Mpc, z: Mpc, prec: number): Mpc {
  const wp = prec + 20;
  if (isNpInt(a) || isNpInt(b) || absD(z) < 0.9) return rnd(sum2f1(a, b, c, z, wp), prec);
  // Gauss's theorem at z = 1 (where the series converges, Re(c - a - b) > 0)
  if (F.isZero(z[1]) && F.cmp(z[0], F.ONE) === 0) {
    const g = cmul(cmul(cgamma(c, wp), cgamma(csub(csub(c, a, wp), b, wp), wp), wp), cmul(rgamma(csub(c, a, wp), wp), rgamma(csub(c, b, wp), wp), wp), wp);
    return rnd(g, prec);
  }
  // Pfaff: (1 - z)^-a 2F1(a, c - b; c; z/(z - 1))
  const w = cdiv(z, csub(z, M.C1, wp), wp);
  if (absD(w) < 0.9) return cmul(M.cpow(csub(M.C1, z, wp), M.cneg(a), wp), sum2f1(a, csub(c, b, wp), c, w, wp), prec);
  // near z = 1: the 1 - z transformation (DLMF 15.8.4)
  const omz = csub(M.C1, z, wp);
  if (absD(omz) < 0.9) return rnd(hyp2f1OneMinusZ(a, b, c, omz, wp), prec);
  // |z| > 1: the 1/z transformation (DLMF 15.8.2)
  if (absD(z) > 1.12) return rnd(hyp2f1InvZ(a, b, c, z, wp), prec);
  // the rest of the unit circle: Gosper's recurrence
  return rnd(hyp2f1Gosper(a, b, c, z, prec), prec);
}

/**
 * 2F1(a, b; c; z) by Gosper's recurrence (mpmath _hyp2f1_gosper), which converges on the
 * part of the unit circle that none of the transformations reaches; the precision grows with
 * the cancellation until it is below the extra bits.
 */
function hyp2f1Gosper(a: Mpc, b: Mpc, c: Mpc, z: Mpc, prec: number): Mpc {
  for (let extra = 10; ; ) {
    const wp = prec + extra;
    const [f, cancellation] = gosperSum(a, b, c, z, wp);
    if (cancellation < extra) return f;
    extra += cancellation;
  }
}

/** The sum of Gosper's recurrence at wp bits and the bits it lost to cancellation. */
function gosperSum(a: Mpc, b: Mpc, c: Mpc, z: Mpc, wp: number): [Mpc, number] {
  const q = (u: Mpc, v: Mpc): Mpc => cmul(u, v, wp);
  let d: Mpc = M.C0;
  let e: Mpc = M.C1;
  let f: Mpc = M.C0;
  const abz = q(q(a, b), z);
  const ch = q(c, half);
  const c1h = q(cadd(c, M.C1, wp), half);
  const nz = csub(M.C1, z, wp);
  const g = cdiv(z, nz, wp);
  const abg = q(q(a, b), g);
  const cba = csub(csub(c, b, wp), a, wp);
  const z2 = csub(z, int(2), wp);
  const tol = -wp - 10;
  let maxmag = -Infinity;
  for (let k = 0; ; k++) {
    const kk = int(k);
    const kch = cadd(kk, ch, wp);
    const kakbz = cdiv(q(q(cadd(kk, a, wp), cadd(kk, b, wp)), z), q(q(int(4 * (k + 1)), kch), cadd(kk, c1h, wp)), wp);
    const d1 = q(kakbz, csub(e, q(q(cadd(kk, cba, wp), d), g), wp));
    const e1 = q(kakbz, cadd(q(d, abg), q(cadd(kk, c, wp), e), wp));
    const inner = csub(q(kk, cadd(q(cba, z), csub(q(kk, z2), c, wp), wp)), abz, wp);
    const ft = cdiv(q(d, inner), q(q(int(2), kch), nz), wp);
    const f1 = csub(cadd(f, e, wp), ft, wp);
    maxmag = Math.max(maxmag, cmagO(f1));
    const df = csub(f1, f, wp);
    if (czero(df) || cmagO(df) < tol) return [f1, maxmag - cmagO(f1)];
    d = d1;
    e = e1;
    f = f1;
  }
}

/**
 * The working precision and the perturbation of a for a transformation whose two terms grow like
 * 1/(d - m) near an integer m and cancel: extra bits for the cancellation near an integer, and at an
 * integer d the limit taken as mpmath's hypercomb takes it, by perturbing a by h = 2**-(wp + 10) at
 * twice the precision (the error is O(h)).
 */
function limitPrecision(d: Mpc, a: Mpc, wp: number): [number, Mpc] {
  if (isInt(d)) {
    const w2 = 2 * wp + 20;
    return [w2, cadd(a, [{ man: 1n, exp: BigInt(-(wp + 10)) }, ZERO], w2)];
  }
  const dist = Math.hypot(F.toNumber(d[1]), F.toNumber(d[0]) - Math.round(F.toNumber(d[0])));
  return [wp + Math.ceil(Math.max(0, -Math.log2(dist))) + 10, a];
}

/** 2F1(a, b; c; z) for |z| > 1 by the 1/z transformation (DLMF 15.8.2), its limit at an integer a - b. */
function hyp2f1InvZ(a: Mpc, b: Mpc, c: Mpc, z: Mpc, wp: number): Mpc {
  const [w2, a1] = limitPrecision(csub(a, b, wp), a, wp);
  const iz = cdiv(M.C1, z, w2);
  const mz = M.cneg(z);
  const part = (u: Mpc, v: Mpc): Mpc => {
    const g = cmul(cmul(cgamma(c, w2), cgamma(csub(v, u, w2), w2), w2), cmul(rgamma(v, w2), rgamma(csub(c, u, w2), w2), w2), w2);
    return cmul(cmul(g, M.cpow(mz, M.cneg(u), w2), w2), sum2f1(u, cadd(csub(u, c, w2), M.C1, w2), cadd(csub(u, v, w2), M.C1, w2), iz, w2), w2);
  };
  return cadd(part(a1, b), part(b, a1), wp);
}

/**
 * 2F1(a, b; c; z) for |1 - z| < 0.9 from w = 1 - z:
 * Gamma(c) Gamma(s)/(Gamma(c - a) Gamma(c - b)) 2F1(a, b; 1 - s; w)
 * + w^s Gamma(c) Gamma(-s)/(Gamma(a) Gamma(b)) 2F1(c - a, c - b; 1 + s; w), s = c - a - b.
 * The two terms cancel near an integer s (limitPrecision).
 */
function hyp2f1OneMinusZ(a: Mpc, b: Mpc, c: Mpc, w: Mpc, wp: number): Mpc {
  const [w2, a1] = limitPrecision(csub(csub(c, a, wp), b, wp), a, wp);
  const s = csub(csub(c, a1, w2), b, w2);
  const gc = cgamma(c, w2);
  const t1 = cmul(cmul(cmul(gc, cgamma(s, w2), w2), cmul(rgamma(csub(c, a1, w2), w2), rgamma(csub(c, b, w2), w2), w2), w2), sum2f1(a1, b, csub(M.C1, s, w2), w, w2), w2);
  const g2 = cmul(cmul(gc, cgamma(M.cneg(s), w2), w2), cmul(rgamma(a1, w2), rgamma(b, w2), w2), w2);
  const t2 = cmul(cmul(M.cpow(w, s, w2), g2, w2), sum2f1(csub(c, a1, w2), csub(c, b, w2), cadd(M.C1, s, w2), w, w2), w2);
  return cadd(t1, t2, wp);
}

/** 2F1(a, b; c; z)/Gamma(c), also for a nonpositive integer c (DLMF 15.2.3_5). */
function hyp2f1r(a: Mpc, b: Mpc, c: Mpc, z: Mpc, wp: number): Mpc {
  if (!isNpInt(c)) return cmul(chyp2f1(a, b, c, z, wp), rgamma(c, wp), wp);
  const m1 = 1 - Number(F.floor(c[0]));
  // (a)_m1 (b)_m1 z^m1 / m1! 2F1(a + m1, b + m1; m1 + 1; z)
  let f: Mpc = M.C1;
  for (let k = 0; k < m1; k++) f = cdiv(cmul(f, cmul(cmul(cadd(a, int(k), wp), cadd(b, int(k), wp), wp), z, wp), wp), int(k + 1), wp);
  if (czero(f)) return M.C0;
  return cmul(f, chyp2f1(cadd(a, int(m1), wp), cadd(b, int(m1), wp), int(m1 + 1), z, wp), wp);
}

const oneMinusHalf = (x: Mpc, wp: number): Mpc => cmul(half, csub(M.C1, x, wp), wp);

/** P_n(x) = 2F1(-n, n + 1; 1; (1 - x)/2) (mpmath legendre). */
export function clegendre(n: Mpc, x: Mpc, prec: number): Mpc {
  const wp = prec + 20;
  return chyp2f1(M.cneg(n), cadd(n, M.C1, wp), M.C1, oneMinusHalf(x, wp), prec);
}

/** P_n^m(x) of type 2 (mpmath legenp, SymPy assoc_legendre). */
export function clegenp(n: Mpc, m: Mpc, x: Mpc, prec: number): Mpc {
  if (czero(m)) return clegendre(n, x, prec);
  const wp = prec + 20;
  const g = cmul(half, m, wp);
  const pre = cmul(M.cpow(cadd(M.C1, x, wp), g, wp), M.cpow(csub(M.C1, x, wp), M.cneg(g), wp), wp);
  return cmul(pre, hyp2f1r(M.cneg(n), cadd(n, M.C1, wp), csub(M.C1, m, wp), oneMinusHalf(x, wp), wp), prec);
}

/** P_n^(a,b)(x) (mpmath jacobi). */
export function cjacobi(n: Mpc, a: Mpc, b: Mpc, x: Mpc, prec: number): Mpc {
  const wp = prec + 20;
  const abn1 = cadd(cadd(a, b, wp), cadd(n, M.C1, wp), wp);
  if (!isNpInt(a)) {
    // Gamma(a + n + 1)/(Gamma(n + 1) Gamma(a + 1)) 2F1(-n, a + b + n + 1; a + 1; (1 - x)/2)
    const g = cmul(gammaOrLimit(cadd(cadd(a, n, wp), M.C1, wp), wp), rgamma(cadd(n, M.C1, wp), wp), wp);
    return cmul(g, hyp2f1r(M.cneg(n), abn1, cadd(a, M.C1, wp), oneMinusHalf(x, wp), wp), prec);
  }
  if (!isInt(b)) {
    // Gamma(-b)/(Gamma(n + 1) Gamma(-b - n)) 2F1(-n, a + b + n + 1; b + 1; (x + 1)/2)
    const g = cmul(cmul(gammaOrLimit(M.cneg(b), wp), rgamma(cadd(n, M.C1, wp), wp), wp), rgamma(csub(M.cneg(b), n, wp), wp), wp);
    return cmul(g, hyp2f1r(M.cneg(n), abn1, cadd(b, M.C1, wp), cmul(half, cadd(x, M.C1, wp), wp), wp), prec);
  }
  throw new NotImplementedError('jacobi with integer a <= 0 and integer b (a limit of binomials)');
}

/** C_n^(a)(z) (mpmath gegenbauer). */
export function cgegenbauer(n: Mpc, a: Mpc, z: Mpc, prec: number): Mpc {
  if (isNpInt(a)) return M.C0;
  const wp = prec + 20;
  if (isNpInt(cadd(a, half, wp))) throw new NotImplementedError('gegenbauer at a + 1/2 a nonpositive integer (a limit)');
  const a2 = cmul(int(2), a, wp);
  // Gamma(n + 2a)/(Gamma(n + 1) Gamma(2a)) 2F1(-n, n + 2a; a + 1/2; (1 - z)/2)
  const g = cmul(cmul(gammaOrLimit(cadd(n, a2, wp), wp), rgamma(cadd(n, M.C1, wp), wp), wp), rgamma(a2, wp), wp);
  return cmul(g, chyp2f1(M.cneg(n), cadd(n, a2, wp), cadd(a, half, wp), oneMinusHalf(z, wp), wp), prec);
}

/** T_n(x) = 2F1(-n, n; 1/2; (1 - x)/2) (mpmath chebyt). */
export function cchebyt(n: Mpc, x: Mpc, prec: number): Mpc {
  return chyp2f1(M.cneg(n), n, half, oneMinusHalf(x, prec + 20), prec);
}

/** U_n(x) = (n + 1) 2F1(-n, n + 2; 3/2; (1 - x)/2) (mpmath chebyu). */
export function cchebyu(n: Mpc, x: Mpc, prec: number): Mpc {
  const wp = prec + 20;
  const f = chyp2f1(M.cneg(n), cadd(n, int(2), wp), [F.fromRational(3n, 2n, wp), ZERO], oneMinusHalf(x, wp), wp);
  return cmul(cadd(n, M.C1, wp), f, prec);
}

/** sum_k (a)_k / ((c)_k k!) z^k and the size of its largest term (c not a nonpositive integer). */
function series1f1(a: Mpc, c: Mpc, z: Mpc, wp: number): [Mpc, number] {
  let t: Mpc = M.C1;
  let s: Mpc = M.C1;
  let big = 0;
  for (let k = 0; ; k++) {
    t = cdiv(cmul(cmul(t, cadd(a, int(k), wp), wp), z, wp), cmul(cadd(c, int(k), wp), int(k + 1), wp), wp);
    if (czero(t)) return [s, big];
    big = Math.max(big, cmagO(t));
    s = cadd(s, t, wp);
    if (cmagO(t) < cmagO(s) - wp - 4 && k > absD(z)) return [s, big];
  }
}

/** 1F1(a; c; z)/Gamma(c) by its power series, also for a nonpositive integer c (DLMF 13.2.5). */
export function chyp1f1r(a: Mpc, c: Mpc, z: Mpc, prec: number): Mpc {
  const wp = prec + 20;
  let pre: Mpc = M.C1;
  let a1 = a;
  let c1 = c;
  if (isNpInt(c)) {
    // (a)_m1 z^m1 / m1! 1F1(a + m1; m1 + 1; z) with m1 = 1 - c
    const m1 = 1 - Number(F.floor(c[0]));
    for (let k = 0; k < m1; k++) pre = cdiv(cmul(pre, cmul(cadd(a, int(k), wp), z, wp), wp), int(k + 1), wp);
    if (czero(pre)) return M.C0;
    a1 = cadd(a, int(m1), wp);
    c1 = int(m1 + 1);
  } else {
    pre = rgamma(c, wp);
  }
  const [s, big] = series1f1(a1, c1, z, wp);
  const lost = Math.max(0, big - cmagO(s));
  const f = lost > 10 ? series1f1(a1, c1, z, wp + lost + 10)[0] : s;
  return rnd(cmul(pre, f, wp), prec);
}

/** L_n^(a)(z) = Gamma(n + a + 1)/Gamma(n + 1) 1F1(-n; a + 1; z)/Gamma(a + 1) (mpmath laguerre). */
export function claguerre(n: Mpc, a: Mpc, z: Mpc, prec: number): Mpc {
  const wp = prec + 20;
  const g = cmul(gammaOrLimit(cadd(cadd(n, a, wp), M.C1, wp), wp), rgamma(cadd(n, M.C1, wp), wp), wp);
  return cmul(g, chyp1f1r(M.cneg(n), cadd(a, M.C1, wp), z, wp), prec);
}

/**
 * H_n(z) = 2^n sqrt(pi) (1F1(-n/2; 1/2; z^2)/Gamma((1 - n)/2) - 2 z 1F1((1 - n)/2; 3/2; z^2)/Gamma(-n/2))
 * (DLMF 18.5.13 continued to any n; mpmath hermite).
 */
export function chermite(n: Mpc, z: Mpc, prec: number): Mpc {
  const terms = (wp: number): [Mpc, number] => {
    const z2 = cmul(z, z, wp);
    const hn = cmul(half, n, wp);
    const a0 = M.cneg(hn);
    const a1 = csub(half, hn, wp);
    // 1F1 = Gamma(c) 1F1r with Gamma(1/2) = sqrt(pi) and Gamma(3/2) = sqrt(pi)/2
    const t0 = cmul(chyp1f1r(a0, half, z2, wp), rgamma(a1, wp), wp);
    const t1 = cmul(cmul(z, chyp1f1r(a1, [F.fromRational(3n, 2n, wp), ZERO], z2, wp), wp), rgamma(a0, wp), wp);
    const s = csub(t0, t1, wp);
    // the bits the difference loses to cancellation
    return [s, Math.max(cmagO(t0), cmagO(t1)) - cmagO(s)];
  };
  const wp = prec + 20;
  const [s0, lost] = terms(wp);
  const s = lost > 10 ? terms(wp + lost + 10)[0] : s0;
  const w = wp + Math.max(0, lost);
  // 2^n sqrt(pi) times the sqrt(pi) of both Gamma(c)
  return cmul(cmul(M.cpow(int(2), n, w), [M.mpPi(w), ZERO], w), s, prec);
}

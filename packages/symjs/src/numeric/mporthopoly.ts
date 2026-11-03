// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from mpmath 1.3.0 (functions/orthogonal.py: legendre, legenp,
// jacobi, gegenbauer, chebyt, chebyu), Copyright (c) 2005-2023 Fredrik
// Johansson and mpmath contributors, BSD 3-Clause License (see LICENSE).

/**
 * @file Legendre, associated Legendre, Jacobi, Gegenbauer and Chebyshev
 * functions of any degree through the Gauss hypergeometric function 2F1, as
 * mpmath defines them. 2F1 is summed directly for |z| < 0.9 (or when it
 * terminates) and after the Pfaff transformation for |z/(z - 1)| < 0.9; the
 * other arguments need mpmath's analytic continuation (NotImplementedError).
 */

import { NotImplementedError } from '../core/errors';
import * as F from './mpf';
import { ZERO } from './mpf';
import * as M from './mpfun';
import { type Mpc, cadd, cdiv, cmul, csub } from './mpfun';
import { cgamma } from './mpspecial';

const int = (n: bigint | number): Mpc => [F.fromInt(BigInt(n)), ZERO];
const half: Mpc = [{ man: 1n, exp: -1 }, ZERO];
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
  // Pfaff: (1 - z)^-a 2F1(a, c - b; c; z/(z - 1))
  const w = cdiv(z, csub(z, M.C1, wp), wp);
  if (absD(w) < 0.9) return cmul(M.cpow(csub(M.C1, z, wp), M.cneg(a), wp), sum2f1(a, csub(c, b, wp), c, w, wp), prec);
  throw new NotImplementedError('2F1 near z = 1 or for large z (mpmath analytic continuation)');
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

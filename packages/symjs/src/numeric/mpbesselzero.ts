// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from mpmath 1.3.0 (functions/bessel.py: mcmahon, bessel_zero,
// generalized_bisection), Copyright (c) 2005-2023 Fredrik Johansson and
// mpmath contributors, BSD 3-Clause License (see LICENSE).

/**
 * @file Positive zeros of the Bessel function J_v(x) of a real order v >= 0
 * at arbitrary precision (mpmath besseljzero), used by SymPy jn_zeros.
 */

import { InvariantError } from '../core/errors';
import { at, defined } from '../core/guard';
import * as F from './mpf';
import type { Mpf } from './mpf';
import { ZERO } from './mpf';
import { mpFns } from './mpeval';
import './mpspecialfns';

/** J_v(x) at prec bits (real order and argument). */
function besselJ(v: Mpf, x: Mpf, prec: number): Mpf {
  return defined(mpFns['besselj'], 'mp besselj')([[v, ZERO], [x, ZERO]], prec)[0];
}

/** McMahon's asymptotic estimate of the m-th zero of J_v and its error (mpmath mcmahon, kind 1, not prime). */
export function mcmahon(v: number, m: number): [number, number] {
  const u = 4 * v * v;
  const b = ((4 * m + 2 * v - 1) * Math.PI) / 4;
  const terms = [
    b,
    -(u - 1) / (8 * b),
    (-4 * (u - 1) * (7 * u - 31)) / (3 * (8 * b) ** 3),
    (-32 * (u - 1) * (83 * u ** 2 - 982 * u + 3779)) / (15 * (8 * b) ** 5),
    (-64 * (u - 1) * (6949 * u ** 3 - 153855 * u ** 2 + 1585743 * u - 6277237)) / (105 * (8 * b) ** 7),
  ];
  let s = b;
  for (let i = 1; i < terms.length; i++) {
    const t = at(terms, i);
    if (Math.abs(t) < Math.abs(at(terms, i - 1))) s += t;
  }
  // (mpmath takes the last term as the error estimate)
  return [s, Math.abs(at(terms, 4))];
}

/** The sign of J_v(x) in double precision (evaluated with guard bits). */
const signJ = (v: Mpf, x: number): number => F.sign(besselJ(v, F.fromNumber(x), 64));

/**
 * n intervals isolating the n simple zeros of J_v in [a, b] (mpmath generalized_bisection),
 * with at most maxPoints sample points.
 */
export function isolate(v: Mpf, a: number, b: number, n: number, maxPoints = 1 << 16): [number, number][] {
  for (let N = n + 1; N <= maxPoints; N *= 2) {
    const points = Array.from({ length: N }, (_, i) => a + ((b - a) * i) / (N - 1));
    const signs = points.map((x) => signJ(v, x));
    const out: [number, number][] = [];
    for (let i = 0; i + 1 < N; i++) if (at(signs, i) * at(signs, i + 1) === -1) out.push([at(points, i), at(points, i + 1)]);
    if (out.length === n) return out;
  }
  throw new InvariantError('besseljzero: the zeros could not be isolated');
}

/** The zero in [a, b] (a sign change): bisection in double precision, then Newton steps at prec bits. */
function refine(v: Mpf, ab: [number, number], prec: number): Mpf {
  let [a, b] = ab;
  const sa = signJ(v, a);
  for (let i = 0; i < 64 && b - a > 1e-15 * Math.abs(b); i++) {
    const c = (a + b) / 2;
    if (signJ(v, c) === sa) a = c;
    else b = c;
  }
  const wp = prec + 20;
  let x = F.fromNumber((a + b) / 2);
  const one = F.fromInt(1n);
  // Newton: x -= J_v(x)/J_v'(x) with J_v' = (v/x) J_v - J_{v+1}; each step doubles the correct bits
  for (let bits = 40; ; bits *= 2) {
    const p = Math.min(wp, bits + 20);
    const j = besselJ(v, x, p);
    const d = F.sub(F.div(F.mul(v, j, p), x, p), besselJ(F.add(v, one, p), x, p), p);
    x = F.sub(x, F.div(j, d, p), p);
    if (p >= wp) break;
  }
  return F.round(x, prec);
}

/**
 * The first k positive zeros of J_v (v >= 0) at prec bits (mpmath besseljzero(v, m) for m = 1..k).
 */
export function besselJZeros(v: number, k: number, prec: number): Mpf[] {
  if (!(v >= 0)) throw new RangeError('v cannot be negative');
  const vm = F.fromNumber(v);
  const tol = 0.01;
  const out: Mpf[] = [];
  let intervals: [number, number][] | undefined;
  for (let m = 1; m <= k; m++) {
    const [r, err] = mcmahon(v, m);
    if (err < tol) {
      out.push(refine(vm, [r - tol, r + tol], prec));
      continue;
    }
    // an n with an accurate estimate and the n zeros below it (0 < 2.4 < j_{v,1}); the zeros
    // m' >= n have accurate estimates themselves, so the intervals cover every later m
    intervals ??= (() => {
      let n = m + 1;
      while (mcmahon(v, n)[1] >= tol) n *= 2;
      return isolate(vm, 2.4, (mcmahon(v, n)[0] + mcmahon(v, n + 1)[0]) / 2, n);
    })();
    out.push(refine(vm, at(intervals, m - 1), prec));
  }
  return out;
}

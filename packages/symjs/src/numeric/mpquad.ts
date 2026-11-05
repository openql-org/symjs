// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// After mpmath 1.3.0 (calculus/quadrature.py: TanhSinh, QuadratureRule.summation and quad), Copyright (c) 2005-2023
// Fredrik Johansson and mpmath contributors, BSD 3-Clause License (see LICENSE).

/**
 * @file Numerical integration over (0, oo) at arbitrary precision by the
 * double exponential substitution x = exp(pi/2 sinh t) (the exp-sinh form of
 * mpmath's tanh-sinh rule for a half-infinite interval). The step is halved
 * until two successive levels agree, which for the double exponential rule
 * means the error of the last level is far smaller still. quad is mpmath's quad with the
 * tanh-sinh rule on a path of points, with its error estimate.
 */

import * as F from './mpf';
import type { Mpf } from './mpf';
import { ZERO } from './mpf';
import * as M from './mpfun';
import { at } from '../core/guard';
import { type Mpc, cadd, cmul } from './mpfun';

const cmag = (z: Mpc): number => Math.max(F.mag(z[0]), F.mag(z[1]));

/**
 * The integral of f over (0, oo) to prec bits for f analytic in a neighbourhood of the half line,
 * bounded at 0 and decaying at least exponentially at oo; f(x, wp) is f at x with wp bits.
 * At most maxLevel halvings of the step are made.
 */
export function quadZeroInf(f: (x: Mpf, wp: number) => Mpc, prec: number, maxLevel = 12): Mpc {
  const wp = prec + 20;
  const halfPi = F.ldexp(M.mpPi(wp), -1);
  /** The weighted value w(t) f(x(t)) at the node t. */
  const node = (t: Mpf): Mpc => {
    const u = F.mul(halfPi, M.sinh(t, wp), wp);
    const x = M.exp(u, wp);
    const w = F.mul(F.mul(halfPi, M.cosh(t, wp), wp), x, wp);
    return cmul(f(x, wp), [w, ZERO], wp);
  };
  /** The sum of the nodes k h, k = start, start + step, ... in one direction until they vanish. */
  const sweep = (h: Mpf, start: number, step: number, ref: number): Mpc => {
    let s: Mpc = M.C0;
    let small = 0;
    for (let k = start; small < 2; k += step) {
      const v = node(F.mulInt(h, BigInt(k)));
      s = cadd(s, v, wp);
      // two negligible terms in a row end the sweep (the terms decay double exponentially)
      small = cmag(v) < Math.max(ref, cmag(s)) - wp - 10 ? small + 1 : 0;
    }
    return s;
  };
  // level 0: h = 1 and the nodes 0, +-1, +-2, ...
  let total = node(ZERO);
  total = cadd(total, sweep(F.ONE, 1, 1, cmag(total)), wp);
  total = cadd(total, sweep(F.ONE, -1, -1, cmag(total)), wp);
  let estimate = total;
  for (let level = 1; ; level++) {
    // the new nodes of h = 2**-level are the odd multiples of h
    const h = F.ldexp(F.ONE, -level);
    total = cadd(total, sweep(h, 1, 2, cmag(total)), wp);
    total = cadd(total, sweep(h, -1, -2, cmag(total)), wp);
    const next = cmul(total, [h, ZERO], wp);
    const diff = M.csub(next, estimate, wp);
    estimate = next;
    // (at maxLevel halvings the last estimate is returned, as mpmath's quad does)
    if (level >= maxLevel || (level > 2 && cmag(diff) < cmag(next) - prec - 10)) break;
  }
  return [F.round(estimate[0], prec), F.round(estimate[1], prec)];
}

/** mpmath TanhSinh.calc_nodes: the nodes (x, w) of degree k on [-1, 1] (only the new ones for k > 1). */
const nodeCache = new Map<string, [Mpf, Mpf][]>();
function tanhSinhNodes(degree: number, prec: number): [Mpf, Mpf][] {
  const key = `${degree},${prec}`;
  const cached = nodeCache.get(key);
  if (cached) return cached;
  const wp = prec + 40;
  const tol = F.ldexp(F.ONE, -prec - 10);
  const pi = M.mpPi(wp);
  const pi4 = F.ldexp(pi, -2);
  const t0 = F.ldexp(F.ONE, -degree);
  const nodes: [Mpf, Mpf][] = [];
  if (degree === 1) nodes.push([ZERO, F.ldexp(pi, -1)]);
  const h = degree === 1 ? t0 : F.ldexp(t0, 1);
  const expt0 = M.exp(t0, wp);
  let a = F.mul(pi4, expt0, wp);
  let b = F.div(pi4, expt0, wp);
  const udelta = M.exp(h, wp);
  const urdelta = F.div(F.ONE, udelta, wp);
  for (let k = 0; k <= 20 * 2 ** degree; k++) {
    const c = M.exp(F.sub(a, b, wp), wp);
    const d = F.div(F.ONE, c, wp);
    const co = F.ldexp(F.add(c, d, wp), -1);
    const si = F.ldexp(F.sub(c, d, wp), -1);
    const x = F.div(si, co, wp);
    const w = F.div(F.add(a, b, wp), F.mul(co, co, wp), wp);
    if (F.cmp(F.abs(F.sub(x, F.ONE, wp)), tol) <= 0) break;
    nodes.push([x, w], [F.neg(x), w]);
    a = F.mul(a, udelta, wp);
    b = F.mul(b, urdelta, wp);
  }
  nodeCache.set(key, nodes);
  return nodes;
}

/** mpmath QuadratureRule.transform_nodes: the nodes moved from [-1, 1] to [a, b] (b finite or +oo). */
function transformNodes(nodes: readonly [Mpf, Mpf][], a: Mpc, b: Mpc | 'inf', wp: number): [Mpc, Mpc][] {
  if (b === 'inf') {
    const a1 = M.csub(a, M.C1, wp);
    return nodes.map(([x, w]) => {
      const u = F.div(F.fromInt(2n), F.add(x, F.ONE, wp), wp);
      return [cadd(a1, [u, ZERO], wp), [F.mul(w, F.ldexp(F.mul(u, u, wp), -1), wp), ZERO]];
    });
  }
  const C = M.cmul(M.csub(b, a, wp), [F.ldexp(F.ONE, -1), ZERO], wp);
  const D = M.cmul(cadd(b, a, wp), [F.ldexp(F.ONE, -1), ZERO], wp);
  return nodes.map(([x, w]) => [cadd(D, cmul(C, [x, ZERO], wp), wp), cmul(C, [w, ZERO], wp)]);
}

/** log10 |z| (-Infinity at 0). */
function log10abs(z: Mpc): number {
  const m = cmag(z);
  if (m === -Infinity) return -Infinity;
  return (m + Math.log2(Math.hypot(F.toNumber(F.ldexp(z[0], -m)), F.toNumber(F.ldexp(z[1], -m))))) * Math.LOG10E * Math.LN2;
}

/** mpmath QuadratureRule.estimate_error of the last results (prec bits, computed at wp). */
export function estimateError(results: readonly Mpc[], prec: number, wp: number): Mpf {
  const n = results.length;
  const r = (i: number): Mpc => at(results, n - i);
  if (n === 2) return M.cabs(M.csub(r(1), r(2), wp), wp);
  const same = (u: Mpc, v: Mpc): boolean => F.cmp(u[0], v[0]) === 0 && F.cmp(u[1], v[1]) === 0;
  if (same(r(1), r(2)) && same(r(2), r(3))) return ZERO;
  const D1 = log10abs(M.csub(r(1), r(2), wp));
  const D2 = log10abs(M.csub(r(1), r(3), wp));
  const D4 = Math.trunc(Math.min(0, Math.max((D1 * D1) / D2, 2 * D1, -prec)));
  return D4 === 0 ? F.ONE : F.div(F.ONE, F.powInt(F.fromInt(10n), BigInt(-D4), wp), wp);
}

/**
 * mpmath quad(f, points, error=True) with the tanh-sinh rule: the sum of the integrals over the
 * segments of the path (straight lines between the complex points, then from the last one to +oo
 * in the real direction when toInfinity is set), each by degrees 1, 2, ... up to mpmath's
 * guess_degree until the error estimate is below eps/8; [the value to prec bits, the total error estimate]. f(x, wp) is f at
 * x with wp bits.
 */
export function quad(f: (x: Mpc, wp: number) => Mpc, points: readonly Mpc[], toInfinity: boolean, prec: number): [Mpc, Mpf] {
  const path: (Mpc | 'inf')[] = toInfinity ? [...points, 'inf'] : [...points];
  const wp = prec + 20;
  const epsilon = F.ldexp(F.ONE, -2 - prec);
  const maxDegree = Math.trunc(4 + Math.max(0, Math.log2(prec / 30))) + 2;
  let I: Mpc = M.C0;
  let totalErr: Mpf = ZERO;
  for (let i = 0; i + 1 < path.length; i++) {
    const a = at(points, i);
    const b = at(path, i + 1);
    if (b !== 'inf' && F.cmp(a[0], b[0]) === 0 && F.cmp(a[1], b[1]) === 0) continue;
    const results: Mpc[] = [];
    let err: Mpf = ZERO;
    for (let degree = 1; degree <= maxDegree; degree++) {
      const nodes = transformNodes(tanhSinhNodes(degree, prec), a, b, prec + 20);
      const h = F.ldexp(F.ONE, -degree);
      let S: Mpc = results.length ? M.cmul(at(results, results.length - 1), [F.ldexp(F.ONE, degree - 1), ZERO], wp) : M.C0;
      for (const [x, w] of nodes) S = cadd(S, cmul(w, f(x, wp), wp + 10), wp + 10);
      results.push(M.cmul(S, [h, ZERO], wp));
      if (degree > 1) {
        err = estimateError(results, prec, wp);
        if (F.cmp(err, epsilon) <= 0) break;
      }
    }
    I = cadd(I, at(results, results.length - 1), wp);
    totalErr = F.add(totalErr, err, wp);
  }
  return [[F.round(I[0], prec), F.round(I[1], prec)], totalErr];
}

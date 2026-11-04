// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// After mpmath 1.3.0 (calculus/quadrature.py: TanhSinh), Copyright (c) 2005-2023
// Fredrik Johansson and mpmath contributors, BSD 3-Clause License (see LICENSE).

/**
 * @file Numerical integration over (0, oo) at arbitrary precision by the
 * double exponential substitution x = exp(pi/2 sinh t) (the exp-sinh form of
 * mpmath's tanh-sinh rule for a half-infinite interval). The step is halved
 * until two successive levels agree, which for the double exponential rule
 * means the error of the last level is far smaller still.
 */

import * as F from './mpf';
import type { Mpf } from './mpf';
import { ZERO } from './mpf';
import * as M from './mpfun';
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

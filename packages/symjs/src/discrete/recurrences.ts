// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 sympy/discrete/recurrences.py, Copyright (c) SymPy Development Team, BSD-3-Clause (see LICENSE).

/**
 * @file Linear recurrences with constant coefficients (SymPy
 * sympy.discrete.recurrences): linrec.
 */

import type { Expr, ExprLike } from '../core/nodes';
import { S } from '../core/nodes';
import { at } from '../core/guard';
import { add, mul } from '../core/ops';
import type { IntLike } from '../ntheory/intutil';
import { asIntValue, sympifySeq } from './transforms';

/**
 * The value at n of the homogeneous linear recurrence with constant
 * coefficients y(n) = c[0]*y(n-1) + c[1]*y(n-2) + ... + c[k-1]*y(n-k) whose
 * initial values y(0), y(1), ... are `init` (missing ones are 0) (SymPy
 * linrec). x^n is reduced modulo the characteristic polynomial by
 * exponentiation by squaring.
 *
 * `linrec([1, 1], [0, 1], 10)` is `55`.
 */
export function linrec(coeffs: Iterable<ExprLike>, init: Iterable<ExprLike>, nIn: IntLike): Expr {
  const c = sympifySeq(coeffs, 'Expected a sequence of coefficients for the recurrence');
  if (c.length === 0) return S.Zero;
  const b = sympifySeq(init, 'Expected a sequence of values for the initialization of the recurrence');
  const n = asIntValue(nIn);
  if (n < 0n) throw new RangeError('Point of evaluation of recurrence must be a non-negative integer');
  const k = c.length;
  if (b.length > k) throw new TypeError('Count of initial values should not exceed the order of the recurrence');
  while (b.length < k) b.push(S.Zero);
  if (n < BigInt(k)) return at(b, Number(n));
  const terms = linrecCoeffs(c, n).map((u, i) => mul(u, at(b, i)));
  return terms.slice(0, -1).reduce((s, t) => add(s, t), at(terms, k - 1));
}

/**
 * The coefficients cf of x^n reduced modulo the characteristic polynomial
 * x^k - c[0]*x^(k-1) - ... - c[k-1], so that y(n) = cf[0]*y(0) + cf[1]*y(1)
 * + ... + cf[k-1]*y(k-1) (SymPy linrec_coeffs), by binary exponentiation.
 */
export function linrecCoeffs(c: readonly Expr[], n: bigint): Expr[] {
  const k = c.length;

  // squares u_0 + u_1 x + ... + u_{k-1} x^(k-1) (and multiplies by x when
  // offset is 1), then reduces the result of length up to 2k to k terms
  // with x^k = c_0 x^(k-1) + c_1 x^(k-2) + ... + c_{k-1}
  const squareAndReduce = (u: readonly Expr[], offset: number): Expr[] => {
    const w: Expr[] = [];
    for (let i = 0; i < 2 * u.length - 1 + offset; i++) w.push(S.Zero);
    u.forEach((p, i) => {
      u.forEach((q, j) => {
        w[offset + i + j] = add(at(w, offset + i + j), mul(p, q));
      });
    });
    for (let j = w.length - 1; j > k - 1; j--) {
      for (let i = 0; i < k; i++) w[j - i - 1] = add(at(w, j - i - 1), mul(at(w, j), at(c, i)));
    }
    return w.slice(0, k);
  };

  const finalCoeffs = (m: bigint): Expr[] => {
    if (m < BigInt(k)) {
      const out: Expr[] = [];
      for (let i = 0; i < k; i++) out.push(BigInt(i) === m ? S.One : S.Zero);
      return out;
    }
    return squareAndReduce(finalCoeffs(m / 2n), Number(m % 2n));
  };

  return finalCoeffs(n);
}

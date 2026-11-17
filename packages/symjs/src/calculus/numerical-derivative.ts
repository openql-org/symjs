// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import type { ExprLike, Sym } from '../core/nodes';
import { sympify } from '../core/ops';

/** Compare the symbolic derivative with a five-point numerical derivative inside a complex rectangle. */
export function testDerivativeNumerically(f: ExprLike, z: Sym, tol = 1e-6, a = 2, b = -1, c = 3, d = 1): boolean {
  if (!Number.isFinite(tol) || tol <= 0) throw new RangeError('tolerance must be finite and positive');
  if (![a, b, c, d].every(Number.isFinite)) throw new RangeError('sampling bounds must be finite');
  const e = sympify(f);
  const derivative = e.diff(z);
  for (const t of [0.375, 0.625]) {
    const point = { re: a + t * (c - a), im: b + t * (d - b) };
    const h = 1e-4 * Math.max(1, Math.hypot(point.re, point.im));
    const at = (offset: number) => e.toComplex(new Map([[z, { re: point.re + offset * h, im: point.im }]]));
    const m2 = at(-2), m1 = at(-1), p1 = at(1), p2 = at(2);
    const re = (m2.re - 8 * m1.re + 8 * p1.re - p2.re) / (12 * h);
    const im = (m2.im - 8 * m1.im + 8 * p1.im - p2.im) / (12 * h);
    const symbolic = derivative.toComplex(new Map([[z, point]]));
    const error = Math.hypot(symbolic.re - re, symbolic.im - im);
    if (!(error <= tol * Math.max(1, Math.hypot(symbolic.re, symbolic.im)))) return false;
  }
  return true;
}

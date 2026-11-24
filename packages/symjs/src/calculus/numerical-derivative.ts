// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import type { ExprLike, Sym } from '../core/nodes';
import { S } from '../core/nodes';
import { add, mul, sympify } from '../core/ops';
import { xreplace } from '../core/traverse';

/**
 * Compare the symbolic derivative with a five-point numerical derivative inside a complex rectangle.
 *
 * @param f - The function or expression to transform.
 * @param z - The differentiation variable.
 * @param tol - The tolerance for the numerical comparison.
 * @param a - The coordinate of the first corner (real component for `a`, imaginary for `b`).
 * @param b - The coordinate of the first corner (real component for `a`, imaginary for `b`).
 * @param c - The coordinate of the opposite corner (real component for `c`, imaginary for `d`).
 * @param d - The coordinate of the opposite corner (real component for `c`, imaginary for `d`).
 * @returns True if the sampled derivatives agree within tolerance.
 * @throws RangeError when the tolerance is nonpositive or a sampling bound or tolerance is nonfinite.
 * @see SymPy `sympy.core.random.test_derivative_numerically`
 * @example
 * ```ts
 * import { ex, symbols, testDerivativeNumerically } from '@symjs/symjs';
 *
 * testDerivativeNumerically(ex`sin(x)`, symbols('x')[0]); // => True
 * ```
 */
export function testDerivativeNumerically(f: ExprLike, z: Sym, tol = 1e-6, a = 2, b = -1, c = 3, d = 1): boolean {
  if (!Number.isFinite(tol) || tol <= 0) throw new RangeError('tolerance must be finite and positive');
  if (![a, b, c, d].every(Number.isFinite)) throw new RangeError('sampling bounds must be finite');
  const e = sympify(f);
  const derivative = e.diff(z);
  const evaluate = (expression: typeof e, re: number, im: number) => {
    try {
      return expression.toComplex(new Map([[z, { re, im }]]));
    } catch (error) {
      if (!(error instanceof TypeError)) throw error;
      return xreplace(expression, [[z, add(re, mul(im, S.I))]]).evalf(20).toComplex();
    }
  };
  for (const t of [0.375, 0.625]) {
    const point = { re: a + t * (c - a), im: b + t * (d - b) };
    const h = 1e-4 * Math.max(1, Math.hypot(point.re, point.im));
    const at = (offset: number) => evaluate(e, point.re + offset * h, point.im);
    const m2 = at(-2), m1 = at(-1), p1 = at(1), p2 = at(2);
    const re = (m2.re - 8 * m1.re + 8 * p1.re - p2.re) / (12 * h);
    const im = (m2.im - 8 * m1.im + 8 * p1.im - p2.im) / (12 * h);
    const symbolic = evaluate(derivative, point.re, point.im);
    const error = Math.hypot(symbolic.re - re, symbolic.im - im);
    if (!(error <= tol * Math.max(1, Math.hypot(symbolic.re, symbolic.im)))) return false;
  }
  return true;
}

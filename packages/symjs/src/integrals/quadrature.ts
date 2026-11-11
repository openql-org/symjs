// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 (integrals/quadrature.py), BSD-3-Clause; see LICENSE.

import type { Expr, ExprLike } from '../core/nodes';
import { Dummy, S } from '../core/nodes';
import { add, mul, pow, sqrt, sympify } from '../core/ops';
import { subs } from '../core/traverse';
import { diff } from '../calculus/diff';
import { cos, sin } from '../functions/elementary/elementary';
import { factorial, gamma } from '../functions/special/special';
import { evalf } from '../numeric/evalf';
import { nroots } from '../polys/nroots';
import { hermitePoly, jacobiPoly, laguerrePoly, legendrePoly } from '../polys/orthopolys';

/** Nodes and weights of a Gaussian quadrature rule. */
export type QuadratureRule = [Expr[], Expr[]];

function validate(n: number, nDigits: number, minimum = 1): void {
  if (!Number.isSafeInteger(n) || n < minimum) throw new RangeError(`quadrature: n must be an integer >= ${minimum}`);
  if (!Number.isSafeInteger(nDigits) || nDigits < 1) throw new RangeError('quadrature: nDigits must be a positive integer');
}

function parameter(value: ExprLike): Expr {
  const a = sympify(value);
  const z = a.toComplex();
  if (z.im !== 0 || !Number.isFinite(z.re) || z.re <= -1) throw new RangeError('quadrature: weight parameters must be real and greater than -1');
  return a;
}

/** Evaluate weights with guard digits before rounding both outputs. */
function rule(p: Expr, weight: Expr, x: Dummy, nDigits: number): QuadratureRule {
  const roots = nroots(p, nDigits + 15, x);
  return [roots.map((r) => evalf(r, nDigits)), roots.map((r) => evalf(subs(weight, [[x, r]]), nDigits))];
}

/** Gauss-Legendre quadrature on [-1, 1], with weight 1. */
export function gaussLegendre(n: number, nDigits: number): QuadratureRule {
  validate(n, nDigits);
  const x = new Dummy('x');
  const p = legendrePoly(n, x);
  return rule(p, mul(2, pow(mul(add(1, mul(-1, pow(x, 2))), pow(diff(p, x), 2)), -1)), x, nDigits);
}

/** Gauss-Laguerre quadrature on [0, infinity), with weight exp(-x). */
export function gaussLaguerre(n: number, nDigits: number): QuadratureRule {
  validate(n, nDigits);
  const x = new Dummy('x');
  return rule(laguerrePoly(n, x), mul(x, pow(mul((n + 1) ** 2, pow(laguerrePoly(n + 1, x), 2)), -1)), x, nDigits);
}

/** Gauss-Hermite quadrature on the real line, with weight exp(-x**2). */
export function gaussHermite(n: number, nDigits: number): QuadratureRule {
  validate(n, nDigits);
  const x = new Dummy('x');
  const weight = mul(pow(2, n - 1), factorial(n), sqrt(S.Pi), pow(mul(n ** 2, pow(hermitePoly(n - 1, x), 2)), -1));
  return rule(hermitePoly(n, x), weight, x, nDigits);
}

/** Generalized Gauss-Laguerre quadrature, with weight x**alpha*exp(-x). */
export function gaussGenLaguerre(n: number, alpha: ExprLike, nDigits: number): QuadratureRule {
  validate(n, nDigits);
  const a = parameter(alpha);
  const x = new Dummy('x');
  const weight = mul(gamma(add(a, n)), pow(mul(n, gamma(n), laguerrePoly(n - 1, x, a), laguerrePoly(n - 1, x, add(a, 1))), -1));
  return rule(laguerrePoly(n, x, a), weight, x, nDigits);
}

/** Gauss-Jacobi quadrature on [-1, 1], with weight (1-x)**alpha*(1+x)**beta. */
export function gaussJacobi(n: number, alpha: ExprLike, beta: ExprLike, nDigits: number): QuadratureRule {
  validate(n, nDigits);
  const a = parameter(alpha), b = parameter(beta);
  const x = new Dummy('x');
  const p = jacobiPoly(n, a, b, x);
  const weight = mul(-1, add(2 * n + 2, a, b), gamma(add(n + 1, a)), gamma(add(n + 1, b)), pow(2, add(a, b)),
    pow(mul(add(n + 1, a, b), gamma(add(n + 1, a, b)), gamma(n + 2), diff(p, x), jacobiPoly(n + 1, a, b, x)), -1));
  return rule(p, weight, x, nDigits);
}

/** Gauss-Chebyshev quadrature with weight 1/sqrt(1-x**2), in descending node order. */
export function gaussChebyshevT(n: number, nDigits: number): QuadratureRule {
  validate(n, nDigits);
  const nodes = Array.from({ length: n }, (_, i) => evalf(cos(mul(2 * i + 1, S.Pi, pow(2 * n, -1))), nDigits));
  return [nodes, Array.from({ length: n }, () => evalf(mul(S.Pi, pow(n, -1)), nDigits))];
}

/** Gauss-Chebyshev quadrature with weight sqrt(1-x**2), in descending node order. */
export function gaussChebyshevU(n: number, nDigits: number): QuadratureRule {
  validate(n, nDigits);
  const angles = Array.from({ length: n }, (_, i) => mul(i + 1, S.Pi, pow(n + 1, -1)));
  return [angles.map((a) => evalf(cos(a), nDigits)), angles.map((a) => evalf(mul(S.Pi, pow(n + 1, -1), pow(sin(a), 2)), nDigits))];
}

/** Gauss-Lobatto quadrature including both endpoints of [-1, 1]. */
export function gaussLobatto(n: number, nDigits: number): QuadratureRule {
  validate(n, nDigits, 2);
  const x = new Dummy('x');
  const p = legendrePoly(n - 1, x);
  const endpoint = evalf(mul(2, pow(n * (n - 1), -1)), nDigits);
  const [nodes, weights] = n === 2 ? [[], []] : rule(diff(p, x), mul(2, pow(mul(n * (n - 1), pow(p, 2)), -1)), x, nDigits);
  return [[S.NegOne, ...nodes, S.One], [endpoint, ...weights, endpoint]];
}

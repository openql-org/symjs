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

/**
 * Gauss-Legendre quadrature on [-1, 1], with weight 1.
 *
 * @param n - The number of quadrature nodes.
 * @param nDigits - Number of significant digits of the points and weights to return.
 * @returns The nodes and corresponding weights.
 * @throws RangeError when the node count or precision is invalid.
 * @see SymPy `sympy.integrals.quadrature.gauss_legendre`
 * @example
 * ```ts
 * import { gaussLegendre } from '@symjs/symjs';
 * gaussLegendre(3, 5)[0]; // => [-0.77460, 0, 0.77460]
 * ```
 */
export function gaussLegendre(n: number, nDigits: number): QuadratureRule {
  validate(n, nDigits);
  const x = new Dummy('x');
  const p = legendrePoly(n, x);
  return rule(p, mul(2, pow(mul(add(1, mul(-1, pow(x, 2))), pow(diff(p, x), 2)), -1)), x, nDigits);
}

/**
 * Gauss-Laguerre quadrature on [0, infinity), with weight exp(-x).
 *
 * @param n - The number of quadrature nodes.
 * @param nDigits - Number of significant digits of the points and weights to return.
 * @returns The nodes and corresponding weights.
 * @throws RangeError when the node count or precision is invalid.
 * @see SymPy `sympy.integrals.quadrature.gauss_laguerre`
 * @example
 * ```ts
 * import { gaussLaguerre } from '@symjs/symjs';
 * gaussLaguerre(3, 5)[0]; // => [0.41577, 2.2943, 6.2899]
 * ```
 */
export function gaussLaguerre(n: number, nDigits: number): QuadratureRule {
  validate(n, nDigits);
  const x = new Dummy('x');
  return rule(laguerrePoly(n, x), mul(x, pow(mul((n + 1) ** 2, pow(laguerrePoly(n + 1, x), 2)), -1)), x, nDigits);
}

/**
 * Gauss-Hermite quadrature on the real line, with weight exp(-x**2).
 *
 * @param n - The number of quadrature nodes.
 * @param nDigits - Number of significant digits of the points and weights to return.
 * @returns The nodes and corresponding weights.
 * @throws RangeError when the node count or precision is invalid.
 * @see SymPy `sympy.integrals.quadrature.gauss_hermite`
 * @example
 * ```ts
 * import { gaussHermite } from '@symjs/symjs';
 * gaussHermite(3, 5)[0]; // => [-1.2247, 0, 1.2247]
 * ```
 */
export function gaussHermite(n: number, nDigits: number): QuadratureRule {
  validate(n, nDigits);
  const x = new Dummy('x');
  const weight = mul(pow(2, n - 1), factorial(n), sqrt(S.Pi), pow(mul(n ** 2, pow(hermitePoly(n - 1, x), 2)), -1));
  return rule(hermitePoly(n, x), weight, x, nDigits);
}

/**
 * Generalized Gauss-Laguerre quadrature, with weight x**alpha*exp(-x).
 *
 * @param n - The number of quadrature nodes.
 * @param alpha - The exponent parameter of the weight function.
 * @param nDigits - Number of significant digits of the points and weights to return.
 * @returns The nodes and corresponding weights.
 * @throws RangeError when the node count or precision is invalid, or a weight parameter is not real and greater than −1.
 * @see SymPy `sympy.integrals.quadrature.gauss_gen_laguerre`
 * @example
 * ```ts
 * import { ex, gaussGenLaguerre } from '@symjs/symjs';
 * gaussGenLaguerre(4, ex`3/2`, 5)[0]; // => [0.97851, 2.9904, 6.3193, 11.712]
 * ```
 */
export function gaussGenLaguerre(n: number, alpha: ExprLike, nDigits: number): QuadratureRule {
  validate(n, nDigits);
  const a = parameter(alpha);
  const x = new Dummy('x');
  const weight = mul(gamma(add(a, n)), pow(mul(n, gamma(n), laguerrePoly(n - 1, x, a), laguerrePoly(n - 1, x, add(a, 1))), -1));
  return rule(laguerrePoly(n, x, a), weight, x, nDigits);
}

/**
 * Gauss-Jacobi quadrature on [-1, 1], with weight (1-x)**alpha*(1+x)**beta.
 *
 * @param n - The number of quadrature nodes.
 * @param alpha - The exponent parameter of the weight function.
 * @param beta - The exponent parameter of the weight function.
 * @param nDigits - The number of significant decimal digits for nodes and weights.
 * @returns The nodes and corresponding weights.
 * @throws RangeError when the node count or precision is invalid, or a weight parameter is not real and greater than −1.
 * @see SymPy `sympy.integrals.quadrature.gauss_jacobi`
 * @example
 * ```ts
 * import { gaussJacobi } from '@symjs/symjs';
 * gaussJacobi(6, 1, 1, 5)[0]; // => [-0.87174, -0.59170, -0.20930, 0.20930, 0.59170, 0.87174]
 * ```
 */
export function gaussJacobi(n: number, alpha: ExprLike, beta: ExprLike, nDigits: number): QuadratureRule {
  validate(n, nDigits);
  const a = parameter(alpha), b = parameter(beta);
  const x = new Dummy('x');
  const p = jacobiPoly(n, a, b, x);
  const weight = mul(-1, add(2 * n + 2, a, b), gamma(add(n + 1, a)), gamma(add(n + 1, b)), pow(2, add(a, b)),
    pow(mul(add(n + 1, a, b), gamma(add(n + 1, a, b)), gamma(n + 2), diff(p, x), jacobiPoly(n + 1, a, b, x)), -1));
  return rule(p, weight, x, nDigits);
}

/**
 * Gauss-Chebyshev quadrature with weight 1/sqrt(1-x**2), in descending node order.
 *
 * @param n - The number of quadrature nodes.
 * @param nDigits - Number of significant digits of the points and weights to return.
 * @returns The nodes and corresponding weights.
 * @throws RangeError when the node count or precision is invalid.
 * @see SymPy `sympy.integrals.quadrature.gauss_chebyshev_t`
 * @example
 * ```ts
 * import { gaussChebyshevT } from '@symjs/symjs';
 * gaussChebyshevT(3, 5)[0]; // => [0.86602, 0, -0.86602]
 * ```
 */
export function gaussChebyshevT(n: number, nDigits: number): QuadratureRule {
  validate(n, nDigits);
  const nodes = Array.from({ length: n }, (_, i) => evalf(cos(mul(2 * i + 1, S.Pi, pow(2 * n, -1))), nDigits));
  return [nodes, Array.from({ length: n }, () => evalf(mul(S.Pi, pow(n, -1)), nDigits))];
}

/**
 * Gauss-Chebyshev quadrature with weight sqrt(1-x**2), in descending node order.
 *
 * @param n - The number of quadrature nodes.
 * @param nDigits - The number of significant decimal digits for nodes and weights.
 * @returns The nodes and corresponding weights.
 * @throws RangeError when the node count or precision is invalid.
 * @see SymPy `sympy.integrals.quadrature.gauss_chebyshev_u`
 * @example
 * ```ts
 * import { gaussChebyshevU } from '@symjs/symjs';
 * gaussChebyshevU(3, 5)[0]; // => [0.70711, 0, -0.70711]
 * ```
 */
export function gaussChebyshevU(n: number, nDigits: number): QuadratureRule {
  validate(n, nDigits);
  const angles = Array.from({ length: n }, (_, i) => mul(i + 1, S.Pi, pow(n + 1, -1)));
  return [angles.map((a) => evalf(cos(a), nDigits)), angles.map((a) => evalf(mul(S.Pi, pow(n + 1, -1), pow(sin(a), 2)), nDigits))];
}

/**
 * Gauss-Lobatto quadrature including both endpoints of [-1, 1].
 *
 * @param n - The number of quadrature nodes.
 * @param nDigits - The number of significant decimal digits for nodes and weights.
 * @returns The nodes and corresponding weights.
 * @throws RangeError when the node count or precision is invalid.
 * @see SymPy `sympy.integrals.quadrature.gauss_lobatto`
 * @example
 * ```ts
 * import { gaussLobatto } from '@symjs/symjs';
 * gaussLobatto(3, 5)[0]; // => [-1, 0, 1]
 * ```
 */
export function gaussLobatto(n: number, nDigits: number): QuadratureRule {
  validate(n, nDigits, 2);
  const x = new Dummy('x');
  const p = legendrePoly(n - 1, x);
  const endpoint = evalf(mul(2, pow(n * (n - 1), -1)), nDigits);
  const [nodes, weights] = n === 2 ? [[], []] : rule(diff(p, x), mul(2, pow(mul(n * (n - 1), pow(p, 2)), -1)), x, nDigits);
  return [[S.NegOne, ...nodes, S.One], [endpoint, ...weights, endpoint]];
}

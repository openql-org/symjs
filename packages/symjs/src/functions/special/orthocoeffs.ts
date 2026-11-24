// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (the dense generators of polys/orthopolys.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License (see
// LICENSE).

/**
 * @file The coefficients of the orthogonal polynomials (SymPy dup_jacobi,
 * dup_chebyshevt, ... of polys/orthopolys.py), from which
 * functions/special/polynomials.ts evaluates the orthogonal polynomials and
 * polys/orthopolys.ts builds its Poly results. They are kept apart from the
 * special functions so that the polynomial algorithms (minimal polynomials of
 * cos(p*pi/q)) do not load them.
 */

import { at } from '../../core/guard';
import type { Expr } from '../../core/nodes';
import { Rational, S } from '../../core/nodes';
import { add, mul, pow } from '../../core/ops';
import { expand } from '../../simplify/expand';

/** Coefficients, lowest power first. */
export type Coeffs = Expr[];

const big = (cs: readonly bigint[]): Coeffs => cs.map((c) => Rational.of(c));

/** Constructs a polynomial in `x` from its coefficients in ascending order of degree. */
export function coeffsExpr(cs: readonly Expr[], x: Expr): Expr {
  return add(...cs.map((c, k) => mul(c, pow(x, k))));
}

const shift = (p: readonly bigint[]): bigint[] => [0n, ...p];
/** p - q for a p at least as long as q (the recurrences subtract a lower-degree polynomial). */
const sub = (p: readonly bigint[], q: readonly bigint[]): bigint[] => p.map((v, i) => v - (q[i] ?? 0n));
const scale = (p: readonly bigint[], c: bigint): bigint[] => p.map((v) => v * c);

/** m1 <- next(m1, m2, i) for i = 2..n from m2 = 1 and m1 (SymPy's three-term recurrences). */
function recurrence(n: number, m1Start: bigint[], next: (m1: bigint[], m2: bigint[], i: number) => bigint[]): bigint[] {
  if (n < 1) return [1n];
  let m2: bigint[] = [1n];
  let m1 = m1Start;
  for (let i = 2; i <= n; i++) [m2, m1] = [m1, next(m1, m2, i)];
  return m1;
}

/** T_n (SymPy dup_chebyshevt). */
export const chebyshevtCoeffs = (n: number): Coeffs => big(recurrence(n, [0n, 1n], (m1, m2) => sub(scale(shift(m1), 2n), m2)));
/** U_n (SymPy dup_chebyshevu). */
export const chebyshevuCoeffs = (n: number): Coeffs => big(recurrence(n, [0n, 2n], (m1, m2) => sub(scale(shift(m1), 2n), m2)));
/** H_n (SymPy dup_hermite). */
export const hermiteCoeffs = (n: number): Coeffs =>
  big(recurrence(n, [0n, 2n], (m1, m2, i) => scale(sub(shift(m1), scale(m2, BigInt(i - 1))), 2n)));
/** He_n (SymPy dup_hermite_prob). */
export const hermiteProbCoeffs = (n: number): Coeffs => big(recurrence(n, [0n, 1n], (m1, m2, i) => sub(shift(m1), scale(m2, BigInt(i - 1)))));

function binom(n: number, k: number): bigint {
  let r = 1n;
  for (let i = 0; i < k; i++) r = (r * BigInt(n - i)) / BigInt(i + 1);
  return r;
}
function fact(n: number): bigint {
  let r = 1n;
  for (let i = 2; i <= n; i++) r *= BigInt(i);
  return r;
}

/** P_n = 2^-n sum_k (-1)^k C(n, k) C(2n - 2k, n) x^(n - 2k) (the coefficients of SymPy dup_legendre). */
export function legendreCoeffs(n: number): Coeffs {
  const cs: Coeffs = Array.from({ length: n + 1 }, () => S.Zero);
  for (let k = 0; 2 * k <= n; k++) cs[n - 2 * k] = Rational.of((k % 2 ? -1n : 1n) * binom(n, k) * binom(2 * n - 2 * k, n), 2n ** BigInt(n));
  return cs;
}

/** (a)_k as a product of k linear factors. */
const rising = (a: Expr, k: number): Expr => mul(...Array.from({ length: k }, (_, i) => add(a, i)));

/**
 * P_n^(a,b) = 1/n! sum_k C(n, k) (a + b + n + 1)_k (a + k + 1)_(n - k) ((x - 1)/2)^k, the
 * polynomial of SymPy dup_jacobi with coefficients expanded in a and b.
 */
export function jacobiCoeffs(n: number, a: Expr, b: Expr): Coeffs {
  const terms: Expr[][] = Array.from({ length: n + 1 }, () => []);
  for (let k = 0; k <= n; k++) {
    const r = mul(Rational.of(binom(n, k), fact(n) * 2n ** BigInt(k)), rising(add(a, b, n + 1), k), rising(add(a, k + 1), n - k));
    for (let j = 0; j <= k; j++) at(terms, j).push(mul(Rational.of(((k - j) % 2 ? -1n : 1n) * binom(k, j)), r));
  }
  return terms.map((t) => expand(add(...t)));
}

/** C_n^(a) = sum_k (-1)^k (a)_(n - k) (2x)^(n - 2k)/(k! (n - 2k)!) (SymPy dup_gegenbauer). */
export function gegenbauerCoeffs(n: number, a: Expr): Coeffs {
  const cs: Coeffs = Array.from({ length: n + 1 }, () => S.Zero);
  for (let k = 0; 2 * k <= n; k++) {
    const c = Rational.of((k % 2 ? -1n : 1n) * 2n ** BigInt(n - 2 * k), fact(k) * fact(n - 2 * k));
    cs[n - 2 * k] = expand(mul(c, rising(a, n - k)));
  }
  return cs;
}

/** L_n^(a) = sum_k (-1)^k (a + k + 1)_(n - k) x^k/(k! (n - k)!) (SymPy dup_laguerre). */
export function laguerreCoeffs(n: number, alpha: Expr): Coeffs {
  return Array.from({ length: n + 1 }, (_, k) => expand(mul(Rational.of(k % 2 ? -1n : 1n, fact(k) * fact(n - k)), rising(add(alpha, k + 1), n - k))));
}

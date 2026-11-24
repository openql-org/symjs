// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Integer helpers of the exact values of cos(pi/n) for products of
 * Fermat primes (SymPy sympy.functions.elementary._trigonometric_special):
 * the extended gcd of several integers, integer partial fractions and the
 * Fermat prime factors of n.
 */

import type { Expr, ExprLike } from '../../core/nodes';
import { S } from '../../core/nodes';
import { add, mul, pow, sqrt } from '../../core/ops';
import { igcdex } from '../../core/numberutils';
import type { NoMatchResult } from '../../core/truth';
import { NoMatch } from '../../core/truth';
import type { IntLike } from '../../ntheory/intutil';
import { asInt } from '../../ntheory/intutil';

/**
 * Computes Bézout coefficients expressing the GCD of several integers as their linear combination.
 *
 * @remarks
 * For `migcdex(4)`, SymPy displays `((1,), 4)`. For `migcdex(4, 6)`, SymPy displays `((-1, 1), 2)`.
 * @param xIn - The integers in the Bézout identity.
 * @returns The coefficient vector and GCD.
 * @see SymPy `sympy.functions.elementary._trigonometric_special.migcdex`
 * @example
 * ```ts
 * import { migcdex } from '@symjs/symjs';
 *
 * migcdex(4); // => [[1], 4]
 * migcdex(4, 6); // => [[-1, 1], 2]
 * ```
 */
export function migcdex(...xIn: IntLike[]): [bigint[], bigint] {
  const x = xIn.map((v) => asInt(v));
  const [x0, x1] = x;
  if (x0 === undefined) return [[], 0n];
  if (x1 === undefined) return [[1n], x0];
  if (x.length === 2) {
    const [u, v, h] = igcdex(x0, x1);
    return [[u, v], h];
  }
  const [y, g] = migcdex(...x.slice(1));
  const [u, v, h] = igcdex(x0, g);
  return [[u, ...y.map((i) => v * i)], h];
}

/**
 * Integers a_i with sum(a_i/d_i) = 1/(d_1*...*d_n) for
 * pairwise coprime denominators d_i.
 *
 * @remarks
 * For `numers`, SymPy displays `(1, 7, -14)`.
 * @param denomsIn - The pairwise coprime denominators.
 * @returns The integer partial-fraction coefficients in denominator order.
 * @see SymPy `sympy.functions.elementary._trigonometric_special.ipartfrac`
 * @example
 * ```ts
 * import { ipartfrac } from '@symjs/symjs';
 *
 * ipartfrac(2, 3, 5); // => [1, 7, -14]
 * ```
 */
export function ipartfrac(...denomsIn: IntLike[]): bigint[] {
  if (!denomsIn.length) return [];
  const denoms = denomsIn.map((v) => asInt(v));
  const d = denoms.reduce((a, b) => a * b, 1n);
  return migcdex(...denoms.map((x) => d / x))[0];
}

/**
 * Factors the integer into distinct Fermat primes when possible.
 *
 * @param nIn - The index.
 * @returns The prime factors or `NoMatch`.
 * @see SymPy `sympy.functions.elementary._trigonometric_special.fermat_coords`
 */
export function fermatCoords(nIn: IntLike): number[] | NoMatchResult {
  let n = asInt(nIn);
  const primes: number[] = [];
  for (const p of [3n, 5n, 17n, 257n, 65537n]) {
    if (n % p === 0n) {
      n /= p;
      primes.push(Number(p));
      if (n === 1n) return primes;
    }
  }
  return NoMatch;
}

/**
 * Expresses the cosine of `pi/3` exactly in radicals.
 *
 * @returns The exact cosine expressed using rational arithmetic and square roots.
 * @see SymPy `sympy.functions.elementary._trigonometric_special.cos_3`
 */
export function cos3(): Expr {
  return S.Half;
}

/**
 * Expresses the cosine of `pi/5` exactly in radicals.
 *
 * @returns The exact cosine expressed using rational arithmetic and square roots.
 * @see SymPy `sympy.functions.elementary._trigonometric_special.cos_5`
 */
export function cos5(): Expr {
  return mul(add(sqrt(5), 1), pow(4, -1));
}

/**
 * Expresses the cosine of `pi/17` exactly in radicals.
 *
 * @returns The exact cosine expressed using rational arithmetic and square roots.
 * @see SymPy `sympy.functions.elementary._trigonometric_special.cos_17`
 */
export function cos17(): Expr {
  const r = sqrt(17), a = sqrt(add(17, mul(-1, r))), b = sqrt(add(17, r));
  const inner = sqrt(add(mul(sqrt(2), add(mul(-8, b), mul(-1, add(1, mul(-1, r)), a))), mul(6, r), 34));
  return sqrt(mul(add(15, r, mul(sqrt(2), add(a, inner))), pow(32, -1)));
}

/**
 * Expresses the cosine of `pi/257` exactly in radicals.
 *
 * @returns The exact cosine expressed using rational arithmetic and square roots.
 * @see SymPy `sympy.functions.elementary._trigonometric_special.cos_257`
 */
export function cos257(): Expr {
  const f1 = (a: ExprLike, b: ExprLike): [Expr, Expr] => {
    return [mul(add(a, sqrt(add(pow(a, 2), b))), pow(2, -1)), mul(add(a, mul(-1, sqrt(add(pow(a, 2), b)))), pow(2, -1))];
  };
  const f2 = (a: ExprLike, b: ExprLike): Expr => {
    return mul(add(a, mul(-1, sqrt(add(pow(a, 2), b)))), pow(2, -1));
  };
  const [t1, t2] = f1(S.NegOne, 256);
  const [z1, z3] = f1(t1, 64);
  const [z2, z4] = f1(t2, 64);
  const [y1, y5] = f1(z1, mul(4, add(add(5, t1), mul(2, z1))));
  const [y6, y2] = f1(z2, mul(4, add(add(5, t2), mul(2, z2))));
  const [y3, y7] = f1(z3, mul(4, add(add(5, t1), mul(2, z3))));
  const [y8, y4] = f1(z4, mul(4, add(add(5, t2), mul(2, z4))));
  const [x1, x9] = f1(y1, mul(mul(-1, 4), add(add(add(t1, y1), y3), mul(2, y6))));
  const [x2, x10] = f1(y2, mul(mul(-1, 4), add(add(add(t2, y2), y4), mul(2, y7))));
  const [x3, x11] = f1(y3, mul(mul(-1, 4), add(add(add(t1, y3), y5), mul(2, y8))));
  const [x4, x12] = f1(y4, mul(mul(-1, 4), add(add(add(t2, y4), y6), mul(2, y1))));
  const [x5, x13] = f1(y5, mul(mul(-1, 4), add(add(add(t1, y5), y7), mul(2, y2))));
  const [x6, x14] = f1(y6, mul(mul(-1, 4), add(add(add(t2, y6), y8), mul(2, y3))));
  const [x15, x7] = f1(y7, mul(mul(-1, 4), add(add(add(t1, y7), y1), mul(2, y4))));
  const [x8, x16] = f1(y8, mul(mul(-1, 4), add(add(add(t2, y8), y2), mul(2, y5))));
  const v1 = f2(x1, mul(mul(-1, 4), add(add(add(x1, x2), x3), x6)));
  const v2 = f2(x2, mul(mul(-1, 4), add(add(add(x2, x3), x4), x7)));
  const v3 = f2(x8, mul(mul(-1, 4), add(add(add(x8, x9), x10), x13)));
  const v4 = f2(x9, mul(mul(-1, 4), add(add(add(x9, x10), x11), x14)));
  const v5 = f2(x10, mul(mul(-1, 4), add(add(add(x10, x11), x12), x15)));
  const v6 = f2(x16, mul(mul(-1, 4), add(add(add(x16, x1), x2), x5)));
  const u1 = mul(-1, f2(mul(-1, v1), mul(mul(-1, 4), add(v2, v3))));
  const u2 = mul(-1, f2(mul(-1, v4), mul(mul(-1, 4), add(v5, v6))));
  const w1 = mul(mul(-1, 2), f2(mul(-1, u1), mul(mul(-1, 4), u2)));
  return sqrt(add(mul(mul(sqrt(2), sqrt(add(w1, 4))), pow(8, -1)), S.Half));
}

/**
 * Builds a table of deferred exact cosine values for Fermat-prime denominators.
 *
 * @returns A map from Fermat primes to functions computing the corresponding cosine.
 * @see SymPy `sympy.functions.elementary._trigonometric_special.cos_table`
 */
export function cosTable(): Map<number, () => Expr> {
  return new Map([[3, cos3], [5, cos5], [17, cos17], [257, cos257]]);
}

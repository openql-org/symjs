// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/subresultants_qq_zz.py), BSD 3-Clause License.

import { at } from '../core/guard';
import type { Expr, ExprLike } from '../core/nodes';
import { Rational, S } from '../core/nodes';
import { add, mul, pow } from '../core/ops';
import { abs } from '../functions/elementary/elementary';
import { Matrix } from '../matrices/matrix';
import { Poly } from './sympoly';

const pair = (f: ExprLike, g: ExprLike, x: Expr): [Poly, Poly] => [Poly.from(f, [x]), Poly.from(g, [x])];

/**
 * Sylvester's coefficient matrix of 1840 (method 1) or 1853 (method 2).
 *
 * @param f - Polynomial to operate on.
 * @param g - Second polynomial operand.
 * @param x - Polynomial generator.
 * @param method - Algorithm to use.
 * @returns The Sylvester matrix for the selected convention.
 * @see SymPy `sympy.polys.subresultants_qq_zz.sylvester`
 */
export function sylvester(f: ExprLike, g: ExprLike, x: Expr, method = 1): Matrix {
  const [p, q] = pair(f, g, x);
  const m = p.degree(), n = q.degree();
  if (Math.max(m, n) <= 0) return Matrix.of([]);
  if (p.isZero || q.isZero) return Matrix.of([[0]]);
  const size = method <= 1 ? m + n : 2 * Math.max(m, n);
  const rows = Array.from({ length: size }, () => Array<Expr>(size).fill(S.Zero));
  const put = (row: number, start: number, coefficients: Expr[]): void => {
    coefficients.forEach((c, k) => { at(rows, row)[start + k] = c; });
  };
  if (method <= 1) {
    for (let i = 0; i < n; i++) put(i, i, p.allCoeffs());
    for (let i = 0; i < m; i++) put(n + i, i, q.allCoeffs());
  } else {
    const degree = Math.max(m, n);
    for (let i = 0; i < degree; i++) {
      put(2 * i, i + degree - m, p.allCoeffs());
      put(2 * i + 1, i + degree - n, q.allCoeffs());
    }
  }
  return Matrix.of(rows);
}

/**
 * The Bezout matrix of (f(x)g(y)-f(y)g(x))/(x-y), in ascending or PRS order.
 *
 * @param f - Polynomial to operate on.
 * @param g - Second polynomial operand.
 * @param x - Polynomial generator.
 * @param method - Algorithm to use.
 * @returns The Bezout matrix of (f(x)g(y)-f(y)g(x))/(x-y), in ascending or PRS order.
 * @see SymPy `sympy.polys.subresultants_qq_zz.bezout`
 */
export function bezout(f: ExprLike, g: ExprLike, x: Expr, method = 'bz'): Matrix {
  const [p, q] = pair(f, g, x);
  const degree = Math.max(p.degree(), q.degree());
  if (degree <= 0) return Matrix.of([]);
  if (p.isZero || q.isZero) return Matrix.of([[0]]);
  const rows = Array.from({ length: degree }, () => Array<Expr>(degree).fill(S.Zero));
  for (let i = 1; i <= degree; i++) for (let j = 0; j < i; j++) {
    const coefficient = add(mul(p.nth(i), q.nth(j)), mul(-1, p.nth(j), q.nth(i)));
    for (let k = 0; k < i - j; k++) {
      const a = i - 1 - k, b = j + k;
      const r = method === 'prs' ? degree - 1 - a : a;
      const c = method === 'prs' ? degree - 1 - b : b;
      at(rows, r)[c] = add(at(at(rows, r), c), coefficient);
    }
  }
  return Matrix.of(rows);
}

/**
 * The anti-diagonal identity matrix.
 *
 * @param n - Size of the square matrix.
 * @returns The anti-diagonal identity matrix.
 * @see SymPy `sympy.polys.subresultants_qq_zz.backward_eye`
 */
export function backwardEye(n: number): Matrix {
  return Matrix.of(Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, j) => i + j === n - 1 ? 1 : 0)));
}

/**
 * The resultant over rational or integer coefficients.
 *
 * @param f - Polynomial to operate on.
 * @param g - Second polynomial operand.
 * @param x - Polynomial generator.
 * @returns The resultant over rational or integer coefficients.
 * @see SymPy `sympy.polys.subresultants_qq_zz.res`
 */
export function res(f: ExprLike, g: ExprLike, x: Expr): Expr {
  const [p, q] = pair(f, g, x);
  return p.resultant(q);
}
/**
 * The resultant of the two polynomials.
 *
 * @param f - Polynomial to operate on.
 * @param g - Second polynomial operand.
 * @param x - Polynomial generator.
 * @returns The resultant of the two polynomials.
 * @see SymPy `sympy.polys.subresultants_qq_zz.res_q`
 */
export const resQ = res;
/**
 * The resultant of the two polynomials.
 *
 * @param f - Polynomial to operate on.
 * @param g - Second polynomial operand.
 * @param x - Polynomial generator.
 * @returns The resultant of the two polynomials.
 * @see SymPy `sympy.polys.subresultants_qq_zz.res_z`
 */
export const resZ = res;

/**
 * Subresultant PRS, with the initial pair retained for zero and constant inputs.
 *
 * @param f - Polynomial to operate on.
 * @param g - Second polynomial operand.
 * @param x - Polynomial generator.
 * @returns Subresultant PRS, with the initial pair retained for zero and constant inputs.
 * @see SymPy `sympy.polys.subresultants_qq_zz.subresultants_sylv`
 */
export function subresultantsSylv(f: ExprLike, g: ExprLike, x: Expr): Expr[] {
  let [p, q] = pair(f, g, x);
  if (p.isZero || q.isZero) return [p.asExpr(), q.asExpr()];
  if (p.degree() < q.degree()) [p, q] = [q, p];
  if (q.degree() === 0) return [p.asExpr(), q.asExpr()];
  return p.subresultants(q).map((v) => v.asExpr());
}
/**
 * The subresultant polynomial remainder sequence.
 *
 * @param f - Polynomial to operate on.
 * @param g - Second polynomial operand.
 * @param x - Polynomial generator.
 * @returns The subresultant polynomial remainder sequence.
 * @see SymPy `sympy.polys.subresultants_qq_zz.subresultants_bezout`
 */
export const subresultantsBezout = subresultantsSylv;
/**
 * The subresultant polynomial remainder sequence.
 *
 * @param f - Polynomial to operate on.
 * @param g - Second polynomial operand.
 * @param x - Polynomial generator.
 * @returns The subresultant polynomial remainder sequence.
 * @see SymPy `sympy.polys.subresultants_qq_zz.subresultants_pg`
 */
export const subresultantsPg = subresultantsSylv;
/**
 * The subresultant polynomial remainder sequence.
 *
 * @param f - Polynomial to operate on.
 * @param g - Second polynomial operand.
 * @param x - Polynomial generator.
 * @returns The subresultant polynomial remainder sequence.
 * @see SymPy `sympy.polys.subresultants_qq_zz.subresultants_amv`
 */
export const subresultantsAmv = subresultantsSylv;
/**
 * The subresultant polynomial remainder sequence.
 *
 * @param f - Polynomial to operate on.
 * @param g - Second polynomial operand.
 * @param x - Polynomial generator.
 * @returns The subresultant polynomial remainder sequence.
 * @see SymPy `sympy.polys.subresultants_qq_zz.subresultants_amv_q`
 */
export const subresultantsAmvQ = subresultantsSylv;
/**
 * The subresultant polynomial remainder sequence.
 *
 * @param f - Dividend polynomial.
 * @param g - Divisor polynomial.
 * @param x - Polynomial generator.
 * @returns The subresultant polynomial remainder sequence.
 * @see SymPy `sympy.polys.subresultants_qq_zz.subresultants_rem`
 */
export const subresultantsRem = subresultantsSylv;
/**
 * The subresultant polynomial remainder sequence.
 *
 * @param f - Polynomial to operate on.
 * @param g - Second polynomial operand.
 * @param x - Polynomial generator.
 * @returns The subresultant polynomial remainder sequence.
 * @see SymPy `sympy.polys.subresultants_qq_zz.subresultants_vv`
 */
export const subresultantsVv = subresultantsSylv;
/**
 * The subresultant polynomial remainder sequence.
 *
 * @param f - Polynomial to operate on.
 * @param g - Second polynomial operand.
 * @param x - Polynomial generator.
 * @returns The subresultant polynomial remainder sequence.
 * @see SymPy `sympy.polys.subresultants_qq_zz.subresultants_vv_2`
 */
export const subresultantsVv2 = subresultantsSylv;

/**
 * Modified subresultants: the signed minors of the 1853 Sylvester matrix.
 *
 * @param f - Polynomial to operate on.
 * @param g - Second polynomial operand.
 * @param x - Polynomial generator.
 * @returns Modified subresultants: the signed minors of the 1853 Sylvester matrix.
 * @see SymPy `sympy.polys.subresultants_qq_zz.modified_subresultants_sylv`
 */
export function modifiedSubresultantsSylv(f: ExprLike, g: ExprLike, x: Expr): Expr[] {
  const seq = subresultantsSylv(f, g, x).map((p) => Poly.from(p, [x]));
  if (seq.length === 2) return seq.map((p) => p.asExpr());
  const first = at(seq, 0), second = at(seq, 1);
  const factor = pow(first.LC(), first.degree() - second.degree());
  return seq.map((p, i) => {
    if (i < 2) return p.asExpr();
    const j = first.degree() - at(seq, i - 1).degree() + 1;
    return p.mul(mul((-1) ** (j * (j - 1) / 2), factor)).asExpr();
  });
}
/**
 * The modified subresultant polynomial remainder sequence.
 *
 * @param f - Polynomial to operate on.
 * @param g - Second polynomial operand.
 * @param x - Polynomial generator.
 * @returns The modified subresultant polynomial remainder sequence.
 * @see SymPy `sympy.polys.subresultants_qq_zz.modified_subresultants_bezout`
 */
export const modifiedSubresultantsBezout = modifiedSubresultantsSylv;
/**
 * The modified subresultant polynomial remainder sequence.
 *
 * @param f - Polynomial to operate on.
 * @param g - Second polynomial operand.
 * @param x - Polynomial generator.
 * @returns The modified subresultant polynomial remainder sequence.
 * @see SymPy `sympy.polys.subresultants_qq_zz.modified_subresultants_pg`
 */
export const modifiedSubresultantsPg = modifiedSubresultantsSylv;
/**
 * The modified subresultant polynomial remainder sequence.
 *
 * @param f - Polynomial to operate on.
 * @param g - Second polynomial operand.
 * @param x - Polynomial generator.
 * @returns The modified subresultant polynomial remainder sequence.
 * @see SymPy `sympy.polys.subresultants_qq_zz.modified_subresultants_amv`
 */
export const modifiedSubresultantsAmv = modifiedSubresultantsSylv;

function rationalPrs(f: ExprLike, g: ExprLike, x: Expr, negative: boolean): Expr[] {
  let [p, q] = pair(f, g, x);
  if (!p.isZero && p.degree() < q.degree()) [p, q] = [q, p];
  const seq = [p.asExpr(), q.asExpr()];
  while (!q.isZero && q.degree() > 0) {
    const r = negative ? p.rem(q).neg() : p.rem(q);
    if (r.isZero) break;
    seq.push(r.asExpr());
    [p, q] = [q, r];
  }
  return seq;
}
/**
 * The Euclidean PRS over QQ.
 *
 * @param f - Polynomial to operate on.
 * @param g - Second polynomial operand.
 * @param x - Polynomial generator.
 * @returns The Euclidean PRS over QQ.
 * @see SymPy `sympy.polys.subresultants_qq_zz.euclid_q`
 */
export function euclidQ(f: ExprLike, g: ExprLike, x: Expr): Expr[] { return rationalPrs(f, g, x, false); }
/**
 * The signed Euclidean (Sturm) PRS over QQ.
 *
 * @param f - Polynomial to operate on.
 * @param g - Second polynomial operand.
 * @param x - Polynomial generator.
 * @returns The signed Euclidean (Sturm) PRS over QQ.
 * @see SymPy `sympy.polys.subresultants_qq_zz.sturm_q`
 */
export function sturmQ(f: ExprLike, g: ExprLike, x: Expr): Expr[] { return rationalPrs(f, g, x, true); }

/**
 * The pseudo-quotient using the absolute leading coefficient of the divisor.
 *
 * @param f - Dividend polynomial.
 * @param g - Divisor polynomial.
 * @param x - Polynomial generator.
 * @returns The pseudo-quotient using the absolute leading coefficient of the divisor.
 * @see SymPy `sympy.polys.subresultants_qq_zz.quo_z`
 */
export function quoZ(f: ExprLike, g: ExprLike, x: Expr): Expr {
  const [p, q] = pair(f, g, x);
  if (![...p.allCoeffs(), ...q.allCoeffs()].every((c) => c instanceof Rational)) return p.pquo(q).asExpr();
  return p.mul(pow(abs(q.LC()), p.degree() - q.degree() + 1)).quo(q).asExpr();
}
/**
 * The pseudo-remainder using the absolute leading coefficient of the divisor.
 *
 * @param f - Dividend polynomial.
 * @param g - Divisor polynomial.
 * @param x - Polynomial generator.
 * @returns The pseudo-remainder using the absolute leading coefficient of the divisor.
 * @see SymPy `sympy.polys.subresultants_qq_zz.rem_z`
 */
export function remZ(f: ExprLike, g: ExprLike, x: Expr): Expr {
  const [p, q] = pair(f, g, x);
  if (![...p.allCoeffs(), ...q.allCoeffs()].every((c) => c instanceof Rational)) return p.prem(q).asExpr();
  return p.mul(pow(abs(q.LC()), p.degree() - q.degree() + 1)).rem(q).asExpr();
}

/**
 * An integer-scaled Euclidean PRS, with positive scaling of each rational remainder.
 *
 * @param f - Polynomial to operate on.
 * @param g - Second polynomial operand.
 * @param x - Polynomial generator.
 * @returns An integer-scaled Euclidean PRS, with positive scaling of each rational remainder.
 * @see SymPy `sympy.polys.subresultants_qq_zz.euclid_amv`
 */
export function euclidAmv(f: ExprLike, g: ExprLike, x: Expr): Expr[] {
  const rational = euclidQ(f, g, x);
  const subres = subresultantsSylv(f, g, x);
  return subres.map((p, i) => {
    if (i < 2) return p;
    const a = Poly.from(p, [x]), b = Poly.from(at(rational, i), [x]);
    const scale = mul(a.LC(), pow(b.LC(), -1));
    return b.mul(abs(scale)).asExpr();
  });
}
/**
 * The integer-scaled Euclidean remainder sequence.
 *
 * @param f - Polynomial to operate on.
 * @param g - Second polynomial operand.
 * @param x - Polynomial generator.
 * @returns The integer-scaled Euclidean remainder sequence.
 * @see SymPy `sympy.polys.subresultants_qq_zz.euclid_pg`
 */
export const euclidPg = euclidAmv;

/**
 * Integer-scaled Sturm PRS; method 0 uses the modified-subresultant scale.
 *
 * @param f - Polynomial to operate on.
 * @param g - Second polynomial operand.
 * @param x - Polynomial generator.
 * @param method - Algorithm to use.
 * @returns Integer-scaled Sturm PRS; method 0 uses the modified-subresultant scale.
 * @see SymPy `sympy.polys.subresultants_qq_zz.sturm_amv`
 */
export function sturmAmv(f: ExprLike, g: ExprLike, x: Expr, method = 0): Expr[] {
  const seq = euclidAmv(f, g, x);
  const p = Poly.from(at(seq, 0), [x]), q = Poly.from(at(seq, 1), [x]);
  const scale = method === 0 && seq.length > 2 ? abs(pow(p.LC(), p.degree() - q.degree())) : S.One;
  return seq.map((v, i) => i < 2 ? v : Poly.from(v, [x]).mul(mul(Math.floor(i / 2) % 2 ? -1 : 1, scale)).asExpr());
}
/**
 * The integer-scaled Sturm sequence.
 *
 * @param f - Polynomial to operate on.
 * @param g - Second polynomial operand.
 * @param x - Polynomial generator.
 * @param method - Algorithm to use.
 * @returns The integer-scaled Sturm sequence.
 * @see SymPy `sympy.polys.subresultants_qq_zz.sturm_pg`
 */
export const sturmPg = sturmAmv;

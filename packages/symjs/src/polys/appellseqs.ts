// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0, polys/appellseqs.py, Copyright (c) 2006-2023
// SymPy Development Team, BSD 3-Clause License (see LICENSE).

import type { Expr, ExprLike } from '../core/nodes';
import { Dummy, Rational, Float } from '../core/nodes';
import { add, mul, pow, sympify } from '../core/ops';
import type { IntLike } from '../ntheory/intutil';
import type { NamedPolyOptions, NamedPolyResult } from './orthopolys';
import { Poly } from './sympoly';
import { domainArith, domainNeg, QQ, ZZ, type Domain } from './domains';
import { dupMulGround, dupSubGround, dupQuoGround } from './densearith';
import { dupEval, dupIntegrate } from './densetools';

/**
 * Dense Bernoulli polynomial over K, with coefficients in descending order.
 *
 * @param n - Nonnegative index of the polynomial family.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The dense coefficient list, leading coefficient first.
 * @see SymPy `sympy.polys.appellseqs.dup_bernoulli`
 */
export function dupBernoulli(n: number, K: Domain): unknown[] {
  if (n < 1) return [K.convert(1)];
  let p: unknown[] = [K.convert(1), K.convert(Rational.of(-1, 2))];
  for (let i = 2; i <= n; i++) {
    p = dupIntegrate(dupMulGround(p, K.convert(i), K), 1, K);
    if (i % 2 === 0) p = dupSubGround(p, domainArith(K, 'mul', dupEval(p, K.convert(Rational.of(1, 2)), K), K.convert(Rational.of(2n ** BigInt(i - 1), 2n ** BigInt(i) - 1n))), K);
  }
  return p;
}

/**
 * Dense central Bernoulli polynomial over K.
 *
 * @param n - Nonnegative index of the polynomial family.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The dense coefficient list, leading coefficient first.
 * @see SymPy `sympy.polys.appellseqs.dup_bernoulli_c`
 */
export function dupBernoulliC(n: number, K: Domain): unknown[] {
  let p: unknown[] = [K.convert(1)];
  for (let i = 1; i <= n; i++) {
    p = dupIntegrate(dupMulGround(p, K.convert(i), K), 1, K);
    if (i % 2 === 0) p = dupSubGround(p, domainArith(K, 'mul', dupEval(p, K.one, K), K.convert(Rational.of(2n ** BigInt(i - 1) - 1n, 2n ** BigInt(i) - 1n))), K);
  }
  return p;
}

/**
 * Dense Genocchi polynomial over K; G_0 is represented by a single zero.
 *
 * @param n - Nonnegative index of the polynomial family.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The dense coefficient list, leading coefficient first.
 * @see SymPy `sympy.polys.appellseqs.dup_genocchi`
 */
export function dupGenocchi(n: number, K: Domain): unknown[] {
  if (n < 1) return [K.convert(0)];
  let p: unknown[] = [domainNeg(K, K.one)];
  for (let i = 2; i <= n; i++) {
    p = dupIntegrate(dupMulGround(p, K.convert(i), K), 1, K);
    if (i % 2 === 0) p = dupSubGround(p, domainArith(K, 'quo', dupEval(p, K.one, K), K.convert(2)), K);
  }
  return p;
}

/**
 * Dense Euler polynomial over K, computed from the integer Genocchi polynomial.
 *
 * @param n - Nonnegative index of the polynomial family.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The dense coefficient list, leading coefficient first.
 * @see SymPy `sympy.polys.appellseqs.dup_euler`
 */
export function dupEuler(n: number, K: Domain): unknown[] {
  return dupQuoGround(dupGenocchi(n + 1, ZZ), K.convert(-n - 1), K);
}

/**
 * Dense Andre polynomial over K.
 *
 * @param n - Nonnegative index of the polynomial family.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns The dense coefficient list, leading coefficient first.
 * @see SymPy `sympy.polys.appellseqs.dup_andre`
 */
export function dupAndre(n: number, K: Domain): unknown[] {
  let p: unknown[] = [K.convert(1)];
  for (let i = 1; i <= n; i++) {
    p = dupIntegrate(dupMulGround(p, K.convert(i), K), 1, K);
    if (i % 2 === 0) p = dupSubGround(p, dupEval(p, K.one, K), K);
  }
  return p;
}

type Kind = 'bernoulli' | 'central' | 'genocchi' | 'euler' | 'andre';
const denseCoefficients = { bernoulli: dupBernoulli, central: dupBernoulliC, genocchi: dupGenocchi, euler: dupEuler, andre: dupAndre };

function appell(n: IntLike, x: ExprLike | undefined, opts: NamedPolyOptions, kind: Kind): Expr | Poly {
  const index = sympify(n);
  if (!(index instanceof Rational || index instanceof Float)) throw new TypeError('polynomial index must be numeric');
  const value = index.toNumber(), degree = Math.trunc(value);
  if (!Number.isSafeInteger(degree) || value < 0) throw new RangeError('polynomial index must be nonnegative');
  const v = x === undefined ? new Dummy('x') : sympify(x);
  const K = kind === 'andre' || kind === 'genocchi' ? ZZ : QQ;
  const e = add(...denseCoefficients[kind](degree, K).reverse().map((c,k) => mul(K.toSympy(c), pow(v,k))));
  return opts.polys ? Poly.from(e, [v], { domain: String(K), pure: x === undefined }) : e;
}

/**
 * Bernoulli polynomial B_n(x), with B_1(x) = x - 1/2.
 *
 * @param n - Nonnegative index of the polynomial family.
 * @param x - Variable or evaluation point of the polynomial.
 * @param opts - Set `polys` to return a polynomial object.
 * @returns The polynomial as an expression, or a `Poly` with `polys: true`.
 * @throws TypeError when the index is not numeric.
 * @throws RangeError when the index is negative or its integer part is outside the safe integer range.
 * @see SymPy `sympy.polys.appellseqs.bernoulli_poly`
 * @example
 * ```ts
 * import { bernoulliPoly, ex } from '@symjs/symjs';
 *
 * bernoulliPoly(5, ex`x`); // => x**5 - 5*x**4/2 + 5*x**3/3 - x/6
 * ```
 */
export function bernoulliPoly<O extends NamedPolyOptions = Record<string, never>>(n: IntLike, x?: ExprLike, opts?: O): NamedPolyResult<O>;
export function bernoulliPoly(n: IntLike, x?: ExprLike, opts: NamedPolyOptions = {}): Expr | Poly { return appell(n,x,opts,'bernoulli'); }
/**
 * Central Bernoulli polynomial 2^n B_n((x+1)/2).
 *
 * @param n - Nonnegative index of the polynomial family.
 * @param x - Variable or evaluation point of the polynomial.
 * @param opts - Set `polys` to return a polynomial object.
 * @returns The polynomial as an expression, or a `Poly` with `polys: true`.
 * @throws TypeError when the index is not numeric.
 * @throws RangeError when the index is negative or its integer part is outside the safe integer range.
 * @see SymPy `sympy.polys.appellseqs.bernoulli_c_poly`
 */
export function bernoulliCPoly<O extends NamedPolyOptions = Record<string, never>>(n: IntLike, x?: ExprLike, opts?: O): NamedPolyResult<O>;
export function bernoulliCPoly(n: IntLike, x?: ExprLike, opts: NamedPolyOptions = {}): Expr | Poly { return appell(n,x,opts,'central'); }
/**
 * Genocchi polynomial G_n(x).
 *
 * @param n - Nonnegative index of the polynomial family.
 * @param x - Variable or evaluation point of the polynomial.
 * @param opts - Set `polys` to return a polynomial object.
 * @returns The polynomial as an expression, or a `Poly` with `polys: true`.
 * @throws TypeError when the index is not numeric.
 * @throws RangeError when the index is negative or its integer part is outside the safe integer range.
 * @see SymPy `sympy.polys.appellseqs.genocchi_poly`
 */
export function genocchiPoly<O extends NamedPolyOptions = Record<string, never>>(n: IntLike, x?: ExprLike, opts?: O): NamedPolyResult<O>;
export function genocchiPoly(n: IntLike, x?: ExprLike, opts: NamedPolyOptions = {}): Expr | Poly { return appell(n,x,opts,'genocchi'); }
/**
 * Euler polynomial E_n(x).
 *
 * @param n - Nonnegative index of the polynomial family.
 * @param x - Variable or evaluation point of the polynomial.
 * @param opts - Set `polys` to return a polynomial object.
 * @returns The polynomial as an expression, or a `Poly` with `polys: true`.
 * @throws TypeError when the index is not numeric.
 * @throws RangeError when the index is negative or its integer part is outside the safe integer range.
 * @see SymPy `sympy.polys.appellseqs.euler_poly`
 */
export function eulerPoly<O extends NamedPolyOptions = Record<string, never>>(n: IntLike, x?: ExprLike, opts?: O): NamedPolyResult<O>;
export function eulerPoly(n: IntLike, x?: ExprLike, opts: NamedPolyOptions = {}): Expr | Poly { return appell(n,x,opts,'euler'); }
/**
 * Andre polynomial, the Appell sequence of Euler numbers.
 *
 * @param n - Nonnegative index of the polynomial family.
 * @param x - Variable or evaluation point of the polynomial.
 * @param opts - Set `polys` to return a polynomial object.
 * @returns The polynomial as an expression, or a `Poly` with `polys: true`.
 * @throws TypeError when the index is not numeric.
 * @throws RangeError when the index is negative or its integer part is outside the safe integer range.
 * @see SymPy `sympy.polys.appellseqs.andre_poly`
 * @example
 * ```ts
 * import { andrePoly, ex } from '@symjs/symjs';
 *
 * andrePoly(9, ex`x`); // => x**9 - 36*x**7 + 630*x**5 - 5124*x**3 + 12465*x
 * ```
 */
export function andrePoly<O extends NamedPolyOptions = Record<string, never>>(n: IntLike, x?: ExprLike, opts?: O): NamedPolyResult<O>;
export function andrePoly(n: IntLike, x?: ExprLike, opts: NamedPolyOptions = {}): Expr | Poly { return appell(n,x,opts,'andre'); }

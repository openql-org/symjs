// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/rootisolation.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License (see LICENSE).
/** Exact bounds on the roots of dense univariate polynomials. */
import type { ExprLike } from '../core/nodes';
import { Rational, S, Sym } from '../core/nodes';
import { at, first, expectType } from '../core/guard';
import { add, mul, pow, sympify } from '../core/ops';
import { DomainError, PolynomialError } from '../core/errors';
import type { Domain } from './domains';
import { IntegerRing, RationalField } from './domains';
import { Poly } from './sympoly';

/**
 * Cauchy upper bound on the absolute values of all complex roots.
 *
 * @param f - Polynomial to operate on.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns Cauchy upper bound on the absolute values of all complex roots.
 * @throws PolynomialError when the polynomial has no roots.
 * @see SymPy `sympy.polys.rootisolation.dup_cauchy_upper_bound`
 */
export function dupCauchyUpperBound(f: readonly ExprLike[], K: Domain): Rational {
  if (f.length < 2) throw new PolynomialError('Polynomial has no roots.');
  checkBoundDomain(K);
  const cs = f.map(c => expectType(sympify(c), (v): v is Rational => v instanceof Rational));
  let end = cs.length;
  while (at(cs, end - 1).isZero) end--;
  if (end === 1) return S.Zero;
  const lc = first(cs);
  let maximum = S.Zero;
  for (const c of cs.slice(1, end)) {
    const ratio = Rational.of(c.p * lc.q, c.q * lc.p);
    const value = Rational.of(ratio.p < 0n ? -ratio.p : ratio.p, ratio.q);
    if (value.p * maximum.q > maximum.p * value.q) maximum = value;
  }
  return Rational.of(maximum.p + maximum.q, maximum.q);
}

/**
 * Cauchy lower bound on the absolute values of nonzero roots.
 *
 * @param f - Polynomial to operate on.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns Cauchy lower bound on the absolute values of nonzero roots.
 * @throws PolynomialError when there are no nonzero roots.
 * @see SymPy `sympy.polys.rootisolation.dup_cauchy_lower_bound`
 */
export function dupCauchyLowerBound(f: readonly ExprLike[], K: Domain): Rational {
  const reversed = [...f].reverse();
  while (reversed.length && sympify(first(reversed)).key === S.Zero.key) reversed.shift();
  if (reversed.length < 2) throw new PolynomialError('Polynomial has no non-zero roots.');
  const bound = dupCauchyUpperBound(reversed, K);
  return Rational.of(bound.q, bound.p);
}

/**
 * Square of Mignotte's lower bound on separation of distinct roots.
 *
 * @param f - Polynomial to operate on.
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns Square of Mignotte's lower bound on separation of distinct roots.
 * @throws PolynomialError when the polynomial degree is less than two.
 * @see SymPy `sympy.polys.rootisolation.dup_mignotte_sep_bound_squared`
 */
export function dupMignotteSepBoundSquared(f: readonly ExprLike[], K: Domain): Rational {
  const n = f.length - 1;
  if (n < 2) throw new PolynomialError('Polynomials of degree < 2 have no distinct roots.');
  checkBoundDomain(K);
  const x = new Sym('x');
  const cs = f.map(c => expectType(sympify(c), (v): v is Rational => v instanceof Rational));
  const p = Poly.from(add(...cs.map((c, i) => mul(c, pow(x, n - i)))), [x]);
  const disc = expectType(p.discriminant(), (v): v is Rational => v instanceof Rational);
  const norm = cs.reduce((s, c) => Rational.of(s.p * c.q ** 2n + c.p ** 2n * s.q, s.q * c.q ** 2n), S.Zero);
  const numerator = 3n * (disc.p < 0n ? -disc.p : disc.p) * norm.q ** BigInt(n - 1);
  return Rational.of(numerator, disc.q * BigInt(n) ** BigInt(n + 1) * norm.p ** BigInt(n - 1));
}

function checkBoundDomain(K: Domain): void {
  if (!(K instanceof IntegerRing || K instanceof RationalField)) throw new DomainError(`Root bound not supported over ${K.toString()}`);
}

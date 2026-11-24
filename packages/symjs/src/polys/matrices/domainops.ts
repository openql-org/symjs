// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/domains/domain.py, ring.py, field.py,
// integerring.py, rationalfield.py, polynomialring.py, fractionfield.py:
// the ring operations the DomainMatrix modules use), Copyright (c) 2006-2023
// SymPy Development Team, BSD 3-Clause License (see LICENSE).

/**
 * @file The ring operations of the ground domains that the DomainMatrix
 * modules need beyond the arithmetic of `Domain` (SymPy `K.exquo`,
 * `K.quo`, `K.div`, `K.gcd`, `K.lcm`, `K.gcdex`, `K.canonical_unit`,
 * `K.get_ring`, `K.numer`, `K.denom`, `K.convert_from`, ...), and the
 * printed forms of domain elements.
 * @internal
 */

import { ExactQuotientFailed, NotImplementedError } from '../../core/errors';
import { at, cast, expectType, first } from '../../core/guard';
import type { Expr, ExprLike } from '../../core/nodes';
import { Float, Rational, S } from '../../core/nodes';
import { sympify } from '../../core/ops';
import { gcd as igcd, lcm as ilcm } from '../../core/numbers';
import { igcdex } from '../../core/numberutils';
import { str } from '../../printing/str';
import { fraction } from '../../simplify/rational';
import type { Domain } from '../domains';
import { FractionField, IntegerRing, PolynomialRing, RationalField, RealField } from '../domains';
import { Poly } from '../sympoly';
import { FiniteField } from '../domains/finitefield';
import { GaussianIntegerRing, GaussianRationalField } from '../domains/gaussiandomains';
import { floatToString } from '../../numeric/mpf';
import { constructDomain } from '../constructor';

const isRational = (e: unknown): e is Rational => e instanceof Rational;
/** The element of ZZ or QQ as a Rational. */
export const rat = (e: Expr): Rational => expectType(e, isRational, 'rational domain element');

/** Equal domain elements (elements are kept in canonical form). */
export const elemEq = (a: Expr, b: Expr): boolean => a.key === b.key;

export const isZZ = (K: Domain): boolean => K instanceof IntegerRing;
export const isQQ = (K: Domain): boolean => K instanceof RationalField;

/**
 * Tests whether the matrix coefficient domain uses exact arithmetic.
 *
 * @see SymPy `sympy.polys.domains.domain.Domain.is_Exact`
 */
export const isExact = (K: Domain): boolean => K.ground !== 'RR';

/** The polynomial of a polynomial-ring or fraction-field element over its symbols (lex order). */
const polyOf = (K: Domain, a: Expr): Poly => Poly.from(a, K.symbols, { domain: K.ground });

/**
 * Tests whether a matrix coefficient is negative, using the leading ground coefficient for a
 * polynomial or for the numerator of a rational function.
 *
 * @see SymPy `sympy.polys.domains.domain.Domain.is_negative`
 */
export function isNegative(K: Domain, a: Expr): boolean {
  if (K instanceof PolynomialRing) return K.isNegative(polyOf(K, a).LC());
  if (K instanceof FractionField) return K.isNegative(polyOf(K, fraction(a)[0]).LC());
  return K.isNegative(a);
}

/**
 * Returns the canonical unit of `a` as a matrix coefficient expression.
 *
 * @see SymPy `sympy.polys.domains.domain.Domain.canonical_unit`
 */
export function canonicalUnit(K: Domain, a: Expr): Expr {
  return K.toSympy(K.canonicalUnit(a));
}

/** The multiplicative inverse in a field (SymPy a**-1). */
export const inv = (K: Domain, a: Expr): Expr => K.quo(K.one, a);

/** Divides the field element `a` by the field element `b`. */
export const fdiv = (K: Domain, a: Expr, b: Expr): Expr => K.quo(a, b);

/** Python floor division and modulo of integers. */
function floorDivmod(a: bigint, b: bigint): [bigint, bigint] {
  let q = a / b;
  let r = a % b;
  if (r !== 0n && r < 0n !== b < 0n) {
    q -= 1n;
    r += b;
  }
  return [q, r];
}

/**
 * Returns the quotient and remainder of `a` divided by `b` in `K`. Integers use floor division,
 * and division in a field has zero remainder.
 *
 * @see SymPy `sympy.polys.domains.domain.Domain.div`
 */
export function div(K: Domain, a: Expr, b: Expr): [Expr, Expr] {
  if (K.isZero(b)) throw new RangeError('division by zero');
  if (isZZ(K)) {
    const [q, r] = floorDivmod(rat(a).p, rat(b).p);
    return [Rational.of(q), Rational.of(r)];
  }
  if (K instanceof PolynomialRing) {
    const [q, r] = polyOf(K, a).divAuto(polyOf(K, b), false);
    return [q.asExpr(), r.asExpr()];
  }
  if (K.isField) return [K.quo(a, b), K.zero];
  const [q, r] = K.div(a, b);
  return [K.toSympy(q), K.toSympy(r)];
}

/**
 * Computes the quotient of `a` by `b` in `K`, rounding down for integer coefficients.
 *
 * @see SymPy `sympy.polys.domains.domain.Domain.quo`
 */
export const quo = (K: Domain, a: Expr, b: Expr): Expr => first(div(K, a, b));
/**
 * Computes the remainder of `a` divided by `b` in `K`.
 *
 * @see SymPy `sympy.polys.domains.domain.Domain.rem`
 */
export const rem = (K: Domain, a: Expr, b: Expr): Expr => at(div(K, a, b), 1);

/**
 * Computes the exact quotient of `a` by `b` in `K`, raising `ExactQuotientFailed` if a nonzero
 * `b` does not divide `a`.
 *
 * @see SymPy `sympy.polys.domains.domain.Domain.exquo`
 */
export function exquo(K: Domain, a: Expr, b: Expr): Expr {
  if (K.isZero(b)) throw new RangeError('division by zero');
  if (K.isField) return K.quo(a, b);
  if (isZZ(K)) {
    const [p, q] = [rat(a).p, rat(b).p];
    if (p % q !== 0n) throw new ExactQuotientFailed(`${p} does not divide ${q} exactly in ZZ`);
    return Rational.of(p / q);
  }
  const q = K.quo(a, b);
  try {
    return K.fromSympy(q);
  } catch {
    throw new ExactQuotientFailed(`${str(b)} does not divide ${str(a)} in ${K.toString()}`);
  }
}

/**
 * Returns the numerator of a field element as an element of its associated ring.
 *
 * @see SymPy `sympy.polys.domains.domain.Domain.numer`
 */
export function numer(K: Domain, a: Expr): Expr {
  if (isQQ(K)) return Rational.of(rat(a).p);
  return K.getRing().canon(fraction(a)[0]);
}

/**
 * Returns the denominator in the associated ring for a rational number or rational function, and
 * one for a ring element.
 *
 * @see SymPy `sympy.polys.domains.domain.Domain.denom`
 */
export function denom(K: Domain, a: Expr): Expr {
  if (isQQ(K)) return Rational.of(rat(a).q);
  if (K instanceof FractionField) return K.getRing().canon(fraction(a)[1]);
  return K.one;
}

/**
 * Tests whether the coefficient domain is the rational field or a rational function field with
 * an associated ring.
 *
 * @see SymPy `sympy.polys.domains.domain.Domain.has_assoc_Ring`
 */
export const hasAssocRing = (K: Domain): boolean => isQQ(K) || K instanceof FractionField;

/**
 * Tests whether the coefficient domain is the integer ring or a polynomial ring with an
 * associated fraction field.
 *
 * @see SymPy `sympy.polys.domains.domain.Domain.has_assoc_Field`
 */
export const hasAssocField = (K: Domain): boolean => isZZ(K) || K instanceof PolynomialRing;

/**
 * Tests whether the matrix algorithms recognize `K` as a principal ideal domain, including the
 * integers, exact fields and univariate polynomial rings over exact fields.
 *
 * @see SymPy `sympy.polys.domains.domain.Domain.is_PID`
 */
export function isPID(K: Domain): boolean {
  if (isZZ(K)) return true;
  if (K instanceof PolynomialRing) return K.symbols.length === 1 && K.ground !== 'ZZ' && K.ground !== 'RR';
  return K.isField && isExact(K);
}

/**
 * Computes the greatest common divisor in `K`. In a rational number or rational function field
 * it divides the GCD of the numerators by the LCM of the denominators.
 *
 * @see SymPy `sympy.polys.domains.domain.Domain.gcd`
 */
export function gcd(K: Domain, a: Expr, b: Expr): Expr {
  if (isZZ(K)) return Rational.of(igcd(rat(a).p, rat(b).p));
  if (isQQ(K)) {
    const [x, y] = [rat(a), rat(b)];
    return Rational.of(igcd(x.p, y.p), ilcm(x.q, y.q));
  }
  if (K instanceof PolynomialRing) return K.canon(polyOf(K, a).gcd(polyOf(K, b)).asExpr());
  if (K instanceof FractionField) {
    const R = K.getRing();
    return K.quo(gcd(R, numer(K, a), numer(K, b)), lcm(R, denom(K, a), denom(K, b)));
  }
  if (K instanceof GaussianIntegerRing || K instanceof GaussianRationalField) return K.toSympy(K.gcd(a, b));
  return K.one;
}

/**
 * Computes the least common multiple of two matrix coefficients in `K`.
 *
 * @see SymPy `sympy.polys.domains.domain.Domain.lcm`
 */
export function lcm(K: Domain, a: Expr, b: Expr): Expr {
  if (isZZ(K)) return Rational.of(ilcm(rat(a).p, rat(b).p));
  if (isQQ(K)) {
    const [x, y] = [rat(a), rat(b)];
    return Rational.of(ilcm(x.p, y.p), igcd(x.q, y.q));
  }
  if (K instanceof PolynomialRing) return exquo(K, K.mul(a, b), gcd(K, a, b));
  if (K instanceof FractionField) {
    const R = K.getRing();
    return K.quo(lcm(R, numer(K, a), numer(K, b)), gcd(R, denom(K, a), denom(K, b)));
  }
  return K.mul(a, b);
}

/**
 * Computes Bézout coefficients and the greatest common divisor as `[s, t, g]` satisfying
 * `s*a + t*b = g`.
 *
 * @see SymPy `sympy.polys.domains.domain.Domain.gcdex`
 */
export function gcdex(K: Domain, a: Expr, b: Expr): [Expr, Expr, Expr] {
  if (K instanceof PolynomialRing && K.symbols.length === 1 && K.dom.isField) {
    const [s, t, g] = polyOf(K, a).gcdex(polyOf(K, b), false);
    return [s.asExpr(), t.asExpr(), g.asExpr()];
  }
  if (!isZZ(K)) throw new NotImplementedError(`gcdex in ${K.toString()}`);
  const [s, t, g] = igcdex(rat(a).p, rat(b).p);
  return [Rational.of(s), Rational.of(t), Rational.of(g)];
}

/**
 * Returns the greatest common divisor `g` and the cofactors `a/g` and `b/g`. When both inputs
 * are zero, all three results are zero.
 *
 * @see SymPy `sympy.polys.domains.domain.Domain.cofactors`
 */
export function cofactors(K: Domain, a: Expr, b: Expr): [Expr, Expr, Expr] {
  const g = gcd(K, a, b);
  if (K.isZero(g)) return [g, K.zero, K.zero];
  return [g, exquo(K, a, g), exquo(K, b, g)];
}

/**
 * Converts an element of the source domain `K0` to the destination domain `K`.
 *
 * @see SymPy `sympy.polys.domains.domain.Domain.convert_from`
 */
export function convertFrom(K: Domain, a: Expr, K0: Domain): Expr {
  if (K.equals(K0)) return a;
  return K.fromSympy(K0.toSympy(a));
}

/** Formats an element of `K` as a string. */
export function elemStr(K: Domain, a: Expr): string {
  if (K instanceof FiniteField) return String(K.convert(a));
  if (K instanceof RealField) {
    const value = cast(K.fromSympy(a), Float);
    return floatToString(value.mpf, value.prec, true);
  }
  return str(K.toSympy(a));
}

/** Formats a rational coefficient as `MPQ(p,q)` and other coefficients in their usual string form. */
export function elemRepr(K: Domain, a: Expr): string {
  if (isQQ(K)) {
    const r = rat(a);
    return `MPQ(${r.p},${r.q})`;
  }
  return elemStr(K, a);
}

/** The bit length of the absolute value of an integer (Python int.bit_length). */
export const bitLength = (n: bigint): number => (n === 0n ? 0 : (n < 0n ? -n : n).toString(2).length);

/**
 * Chooses a common coefficient domain for the expressions and returns it with the converted
 * elements in the expression form used by domain matrices.
 *
 * @see SymPy `sympy.polys.constructor.construct_domain`
 */
export function domainOfExprs(exprsIn: readonly ExprLike[], opts: { field?: boolean } = {}): [Domain, Expr[]] {
  const exprs = exprsIn.map((e) => sympify(e));
  const [K] = constructDomain(exprs.length ? exprs : [S.Zero], opts.field ? { field: true } : {});
  return [K, exprs.map((e) => K.fromSympy(e))];
}

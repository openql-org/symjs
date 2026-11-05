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
import { at, expectType, first } from '../../core/guard';
import type { Expr, ExprLike } from '../../core/nodes';
import { Rational, S } from '../../core/nodes';
import { sympify } from '../../core/ops';
import { gcd as igcd, lcm as ilcm } from '../../core/numbers';
import { igcdex } from '../../core/numberutils';
import { str } from '../../printing/str';
import { fraction } from '../../simplify/rational';
import type { Domain } from '../domains';
import { FractionField, IntegerRing, PolynomialRing, RationalField } from '../domains';
import { Poly } from '../sympoly';
import { constructDomain } from '../constructor';

const isRational = (e: unknown): e is Rational => e instanceof Rational;
/** The element of ZZ or QQ as a Rational. */
export const rat = (e: Expr): Rational => expectType(e, isRational, 'rational domain element');

/** Equal domain elements (elements are kept in canonical form). */
export const elemEq = (a: Expr, b: Expr): boolean => a.key === b.key;

export const isZZ = (K: Domain): boolean => K instanceof IntegerRing;
export const isQQ = (K: Domain): boolean => K instanceof RationalField;

/** SymPy K.is_Exact: every domain but the floating-point ones. */
export const isExact = (K: Domain): boolean => K.ground !== 'RR';

/** The polynomial of a polynomial-ring or fraction-field element over its symbols (lex order). */
const polyOf = (K: Domain, a: Expr): Poly => Poly.from(a, K.symbols, { domain: K.ground });

/** SymPy K.is_negative: the sign of the leading ground coefficient. */
export function isNegative(K: Domain, a: Expr): boolean {
  if (K instanceof PolynomialRing) return K.isNegative(polyOf(K, a).LC());
  if (K instanceof FractionField) return K.isNegative(polyOf(K, fraction(a)[0]).LC());
  return K.isNegative(a);
}

/** SymPy K.canonical_unit: -1 for a negative element (by its leading coefficient), else 1. */
export function canonicalUnit(K: Domain, a: Expr): Expr {
  return isNegative(K, a) ? K.neg(K.one) : K.one;
}

/** The multiplicative inverse in a field (SymPy a**-1). */
export const inv = (K: Domain, a: Expr): Expr => K.quo(K.one, a);

/** a/b in a field (SymPy a/b of field elements). */
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

/** SymPy K.div: floor division with remainder in ZZ, exact division in a field. */
export function div(K: Domain, a: Expr, b: Expr): [Expr, Expr] {
  if (K.isZero(b)) throw new RangeError('division by zero');
  if (isZZ(K)) {
    const [q, r] = floorDivmod(rat(a).p, rat(b).p);
    return [Rational.of(q), Rational.of(r)];
  }
  if (K.isField) return [K.quo(a, b), K.zero];
  throw new NotImplementedError(`div in ${K.toString()}`);
}

/** SymPy K.quo (floor division in ZZ). */
export const quo = (K: Domain, a: Expr, b: Expr): Expr => first(div(K, a, b));
/** SymPy K.rem. */
export const rem = (K: Domain, a: Expr, b: Expr): Expr => at(div(K, a, b), 1);

/** SymPy K.exquo: the exact quotient; throws ExactQuotientFailed when b does not divide a. */
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

/** SymPy K.numer: the numerator of a field element in the associated ring. */
export function numer(K: Domain, a: Expr): Expr {
  if (isQQ(K)) return Rational.of(rat(a).p);
  return K.getRing().canon(fraction(a)[0]);
}

/** SymPy K.denom: the denominator of a field element in the associated ring (1 for a ring element). */
export function denom(K: Domain, a: Expr): Expr {
  if (isQQ(K)) return Rational.of(rat(a).q);
  if (K instanceof FractionField) return K.getRing().canon(fraction(a)[1]);
  return K.one;
}

/** SymPy K.has_assoc_Ring: a field with a ring of which it is the fraction field (QQ, K(x)). */
export const hasAssocRing = (K: Domain): boolean => isQQ(K) || K instanceof FractionField;

/** SymPy K.has_assoc_Field: ZZ and the polynomial rings. */
export const hasAssocField = (K: Domain): boolean => isZZ(K) || K instanceof PolynomialRing;

/** SymPy K.is_PID: ZZ, the exact fields and univariate polynomial rings over a field. */
export function isPID(K: Domain): boolean {
  if (isZZ(K)) return true;
  if (K instanceof PolynomialRing) return K.symbols.length === 1 && K.ground !== 'ZZ' && K.ground !== 'RR';
  return K.isField && isExact(K);
}

/** SymPy K.gcd (over a field with an associated ring: gcd of numerators over lcm of denominators). */
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
  return K.one;
}

/** SymPy K.lcm. */
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

/** SymPy ZZ.gcdex: [s, t, g] with s*a + t*b = g = gcd(a, b). */
export function gcdex(K: Domain, a: Expr, b: Expr): [Expr, Expr, Expr] {
  if (!isZZ(K)) throw new NotImplementedError(`gcdex in ${K.toString()}`);
  const [s, t, g] = igcdex(rat(a).p, rat(b).p);
  return [Rational.of(s), Rational.of(t), Rational.of(g)];
}

/** SymPy K.cofactors: [gcd(a, b), a/gcd, b/gcd]. */
export function cofactors(K: Domain, a: Expr, b: Expr): [Expr, Expr, Expr] {
  const g = gcd(K, a, b);
  if (K.isZero(g)) return [g, K.zero, K.zero];
  return [g, exquo(K, a, g), exquo(K, b, g)];
}

/** SymPy K.convert_from(a, K0): an element of K0 as an element of K. */
export function convertFrom(K: Domain, a: Expr, K0: Domain): Expr {
  if (K.equals(K0)) return a;
  return K.fromSympy(K0.toSympy(a));
}

/** str() of a domain element. */
export const elemStr = (K: Domain, a: Expr): string => str(K.toSympy(a));

/** repr() of a domain element: MPQ(p,q) for QQ (SymPy's pure Python ground type), str otherwise. */
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
 * SymPy construct_domain for the DomainMatrix modules: the domain that
 * constructDomain chooses for the expressions (ZZ, QQ, RR, ZZ_I, QQ_I, a
 * polynomial ring, a fraction field or EX), with the expressions as its
 * elements in the expression form the matrices keep.
 */
export function domainOfExprs(exprsIn: readonly ExprLike[], opts: { field?: boolean } = {}): [Domain, Expr[]] {
  const exprs = exprsIn.map((e) => sympify(e));
  const [K] = constructDomain(exprs.length ? exprs : [S.Zero], opts.field ? { field: true } : {});
  return [K, exprs.map((e) => K.fromSympy(e))];
}

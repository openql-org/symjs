// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/compatibility.py, with the algorithms of
// polys/densearith.py, polys/densetools.py, polys/sqfreetools.py,
// polys/factortools.py and polys/euclidtools.py that its methods call),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License (see
// LICENSE).

/**
 * @file The `IPolys` compatibility layer of SymPy's polynomial rings: the
 * `R.dup_*` and `R.dmp_*` methods of a `PolyRing`, which run the dense
 * polynomial algorithms on ring elements. SymPy converts an element to the
 * recursive dense representation, calls the dense function and converts the
 * result back; here the same algorithms run on the sparse elements directly,
 * reading the polynomial as one in its first generator whose coefficients are
 * polynomials in the following generators. The file also holds the ground
 * domain operations (floor division, gcd, sign, printing) that the domains of
 * `polys/domains.ts` do not provide and the rings need.
 */

import { DomainError, ExactQuotientFailed, NotImplementedError, PolynomialError } from '../core/errors';
import { at, first, last } from '../core/guard';
import type { Expr, ExprLike } from '../core/nodes';
import { Dummy, Float, Rational, S, Sym, isNum } from '../core/nodes';
import { numCmp } from '../core/num';
import { gcd as igcd, iroot, lcm as ilcm } from '../core/numbers';
import { add, mul, pow, splitCoeff, sympify } from '../core/ops';
import { asInt } from '../ntheory/intutil';
import type { IntLike } from '../ntheory/intutil';
import { PREC, floatString, precedence, str } from '../printing/str';
import { expand } from '../simplify/expand';
import { cancel, fraction } from '../simplify/rational';
import type { Domain } from './domains';
import { EX, FractionField, groundRational, IntegerRing, PolynomialRing, QQ, RationalField, RealField, ZZ } from './domains';
import { AlgebraicField } from './domains/algebraicfield';
import { FiniteField } from './domains/finitefield';
import { GaussianIntegerRing, GaussianRationalField, QQ_I } from './domains/gaussiandomains';
import { mgcd } from './mpoly';
import { MultivariatePolynomialError } from './polyerrors';
import { Poly, discriminant, polyGcd, resultant } from './sympoly';
import { sortExtensionFactors } from './factortools';

import { dmpSqfNorm } from './sqfreetools';
import { dmpFromDict, dmpToDict } from './densebasic';
import { cyclotomicCoeffs } from './numberfields';
import { factorint, divisors } from '../ntheory/factor';
import type { Truth } from '../core/truth';
import { NoMatch } from '../core/truth';
import type { NoMatchResult } from '../core/truth';
import { FieldPoly } from './fieldpoly';

/** An exponent vector. */
export type Monom = readonly number[];

// ---------------------------------------------------------------------------
// ground domain operations (SymPy Domain methods)
// ---------------------------------------------------------------------------

/** A Python integer argument as a JavaScript number. */
export const intArg = (n: IntLike, name = 'value'): number => Number(asInt(n, name));

const isZZ = (K: Domain): boolean => K instanceof IntegerRing;

/** The rational value of a ZZ or QQ element. */
function rat(a: Expr): Rational {
  if (a instanceof Rational) return a;
  throw new PolynomialError(`expected a rational number, got ${str(a)}`);
}

/** Python floor division of integers. */
function floorDiv(a: bigint, b: bigint): bigint {
  const q = a / b;
  return (a % b !== 0n && (a < 0n) !== (b < 0n)) ? q - 1n : q;
}

/**
 * Converts a value to an element of the coefficient domain `K`, raising `CoercionFailed` if
 * conversion fails.
 *
 * @see SymPy `sympy.polys.domains.domain.Domain.convert`
 */
export function groundConvert(K: Domain, a: ExprLike): Expr {
  return K.fromSympy(sympify(a));
}

/**
 * Tests whether `a` is zero in the coefficient domain `K`.
 *
 * @see SymPy `sympy.polys.domains.domain.Domain.is_zero`
 */
export const groundIsZero = (K: Domain, a: Expr): boolean => K.isZero(a) || (a instanceof Rational && a.isZero);

/** Exact coefficient equality, including numeric units stored as either rationals or floats. */
export function groundEq(a: Expr, b: Expr): boolean {
  if (a.key === b.key) return true;
  const x = groundRational(a), y = groundRational(b);
  return x !== undefined && y !== undefined && x[0]*y[1] === y[0]*x[1];
}

/**
 * Tests whether a coefficient is negative in `K`, using the leading coefficient for polynomials
 * and the leading coefficient of the numerator for rational functions.
 *
 * @see SymPy `sympy.polys.domains.domain.Domain.is_negative`
 */
export function groundIsNegative(K: Domain, a: Expr): boolean {
  if (a instanceof Rational || a instanceof Float) return K.isNegative(a);
  if (K instanceof PolynomialRing || K instanceof FractionField) {
    // the sign of the leading coefficient of the numerator
    const num = K instanceof FractionField ? fraction(cancel(a))[0] : a;
    return groundIsNegative(QQ, Poly.from(num, K.symbols, { domain: 'QQ' }).LC());
  }
  // SymPy EX: the sign of the numeric coefficient
  return splitCoeff(a)[0].isNegative;
}

/**
 * Computes the quotient of `a` by `b` in `K`, using floor division for integers and exact
 * division for fields.
 *
 * @see SymPy `sympy.polys.domains.domain.Domain.quo`
 */
export function groundQuo(K: Domain, a: Expr, b: Expr): Expr {
  if (groundIsZero(K, b)) throw new RangeError('division by zero');
  if (isZZ(K)) return Rational.of(floorDiv(rat(a).p, rat(b).p));
  if (K.isField) return K.quo(a, b);
  // a polynomial ring: the exact quotient when b divides a
  return groundExquo(K, a, b);
}

/**
 * Computes the remainder of `a` divided by `b` in `K`. Integers use the remainder from floor
 * division, and field elements give zero for a nonzero divisor.
 *
 * @see SymPy `sympy.polys.domains.domain.Domain.rem`
 */
export function groundRem(K: Domain, a: Expr, b: Expr): Expr {
  if (groundIsZero(K, b)) throw new RangeError('division by zero');
  if (isZZ(K)) {
    const x = rat(a).p;
    const y = rat(b).p;
    return Rational.of(x - floorDiv(x, y) * y);
  }
  if (K.isField) return S.Zero;
  return K.sub(a, K.mul(groundExquo(K, a, b), b));
}

/**
 * Computes the exact quotient of `a` by `b` in `K`, raising `ExactQuotientFailed` if a nonzero
 * `b` does not divide `a`.
 *
 * @see SymPy `sympy.polys.domains.domain.Domain.exquo`
 */
export function groundExquo(K: Domain, a: Expr, b: Expr): Expr {
  if (groundIsZero(K, b)) throw new RangeError('division by zero');
  if (isZZ(K)) {
    const x = rat(a).p;
    const y = rat(b).p;
    if (x % y !== 0n) throw new ExactQuotientFailed(`${str(b)} does not divide ${str(a)} in ZZ`);
    return Rational.of(x / y);
  }
  if (K.isField) return K.quo(a, b);
  if (K instanceof GaussianIntegerRing) return K.toSympy(K.exquo(a, b));
  try {
    return K.fromSympy(cancel(K.quo(a, b)));
  } catch {
    throw new ExactQuotientFailed(`${str(b)} does not divide ${str(a)} in ${K.toString()}`);
  }
}

/**
 * Returns the absolute value of `a` according to the sign convention of `K`.
 *
 * @see SymPy `sympy.polys.domains.domain.Domain.abs`
 */
export const groundAbs = (K: Domain, a: Expr): Expr => (groundIsNegative(K, a) ? K.neg(a) : a);

/**
 * Computes the greatest common divisor in `K`. For integers the result is nonnegative, and for
 * rationals it is the GCD of the numerators divided by the LCM of the denominators.
 *
 * @see SymPy `sympy.polys.domains.domain.Domain.gcd`
 */
export function groundGcd(K: Domain, a: Expr, b: Expr): Expr {
  if (isZZ(K)) return Rational.of(igcd(rat(a).p, rat(b).p));
  if (K instanceof RationalField) {
    const x = rat(a);
    const y = rat(b);
    return Rational.of(igcd(x.p, y.p), ilcm(x.q, y.q));
  }
  if (K instanceof PolynomialRing) return K.canon(polyGcd(a, b));
  if (K instanceof GaussianIntegerRing || K instanceof GaussianRationalField) return K.toSympy(K.gcd(a, b));
  return K.one;
}

/**
 * Computes the least common multiple of two coefficients in `K`.
 *
 * @see SymPy `sympy.polys.domains.domain.Domain.lcm`
 */
export function groundLcm(K: Domain, a: Expr, b: Expr): Expr {
  if (isZZ(K)) return Rational.of(ilcm(rat(a).p, rat(b).p));
  if (K instanceof RationalField) {
    const x = rat(a);
    const y = rat(b);
    return Rational.of(ilcm(x.p, y.p), igcd(x.q, y.q));
  }
  if (K instanceof PolynomialRing) return groundIsZero(K, a) || groundIsZero(K, b) ? K.zero : groundExquo(K, K.mul(a, b), groundGcd(K, a, b));
  return K.mul(a, b);
}

/**
 * Returns the positive denominator of a rational coefficient in lowest terms.
 *
 * @see SymPy `sympy.polys.domains.rationalfield.RationalField.denom`
 */
export const groundDenom = (a: Expr): Expr => Rational.of(rat(a).q);

/**
 * Raises `a` to the integer power `n` and normalizes the result in `K`.
 *
 * @see SymPy `sympy.polys.domains.domain.Domain.pow`
 */
export const groundPow = (K: Domain, a: Expr, n: number): Expr => K.canon(pow(a, n));

/**
 * Returns the integer ring for rational coefficients and otherwise returns the input domain.
 *
 * @see SymPy `sympy.polys.domains.domain.Domain.get_ring`
 */
export function groundRing(K: Domain): Domain {
  if (K instanceof RationalField) return ZZ;
  return K;
}

/**
 * Tests whether the domain supplies an associated ring.
 *
 * @param K - Coefficient domain for the polynomial arithmetic.
 * @returns True if an associated ring exists.
 * @see SymPy `sympy.polys.domains.domain.Domain.has_assoc_Ring`
 */
export const hasAssocRing = (K: Domain): boolean => K instanceof RationalField || K instanceof IntegerRing;

/**
 * Returns the unit that normalizes `a` in `K`. Gaussian elements rotate into the first quadrant,
 * and other coefficients use their sign.
 *
 * @see SymPy `sympy.polys.domains.domain.Domain.canonical_unit`
 */
export function canonicalUnit(K: Domain, a: Expr): Expr {
  if (K instanceof GaussianIntegerRing || K instanceof GaussianRationalField) return K.toSympy(K.canonicalUnit(a));
  return groundIsNegative(K, a) ? K.neg(K.one) : K.one;
}

/**
 * Tests a coefficient for invertibility, accepting any nonzero element in a field and the
 * elements 1 and −1 in other domains.
 *
 * @see SymPy `sympy.polys.domains.ring.Ring.is_unit`
 */
export function groundIsUnit(K: Domain, a: Expr): boolean {
  if (K.isField) return !groundIsZero(K, a);
  return groundEq(a, K.one) || groundEq(a, K.neg(K.one));
}

/** The printed form of an element of K (SymPy printer._print of a domain element). */
export function groundStr(K: Domain, a: Expr): string {
  if (K instanceof FiniteField) return String(K.convert(a));
  if (K instanceof RealField && a instanceof Float) return floatString(a, true);
  if (K === EX) return `EX(${str(a)})`;
  if (K instanceof PolynomialRing && K.dom === EX && !K.symbols.some((s) => a.has(s))) return groundStr(EX, a);
  return str(a);
}

/** The printing precedence of an element of K (SymPy precedence of a domain element). */
export function groundPrecedence(K: Domain, a: Expr): number {
  if (K === EX || K instanceof FiniteField) return PREC.ATOM;
  if (K instanceof PolynomialRing || K instanceof FractionField) {
    const e = expand(a);
    return precedence(e);
  }
  return precedence(a);
}

// ---------------------------------------------------------------------------
// the ring interface the compatibility layer runs on
// ---------------------------------------------------------------------------

/** The element operations the compatibility layer uses (SymPy PolyElement). */
export interface CompatElement<P> {
  readonly ring: { readonly symbols: readonly Expr[] };
  readonly isZero: boolean;
  readonly LC: Expr;
  add(o: P | ExprLike): P;
  sub(o: P | ExprLike): P;
  mul(o: P | ExprLike): P;
  neg(): P;
  pow(n: IntLike): P;
  mulGround(c: ExprLike): P;
  degree(x?: P | IntLike | string): number;
  coeffWrt(x: P | IntLike | string, deg: IntLike): P;
  listterms(): [Monom, Expr][];
  asExpr(): Expr;
  equals(o: unknown): boolean;
}

/**
 * The compatibility methods of a polynomial ring: `R.dup_*`
 * work on univariate polynomials, `R.dmp_*` on multivariate ones read as
 * polynomials in the first generator.
 *
 * @see SymPy `sympy.polys.compatibility.IPolys`
 */
export abstract class IPolys<P extends CompatElement<P>> {
  /** The number of generators. */
  abstract readonly ngens: number;
  /** The coefficient domain. */
  abstract readonly domain: Domain;
  /** The symbols naming the generators, in order. */
  abstract readonly symbols: readonly Expr[];
  /** The ordered generators. */
  abstract readonly gens: readonly P[];
  /**
   * Represents zero in this ring.
   *
   * @returns The additive identity.
   */
  abstract get zero(): P;
  /**
   * Represents one in this ring.
   *
   * @returns The multiplicative identity.
   */
  abstract get one(): P;
  /**
   * Constructs a constant polynomial from the ground coefficient.
   *
   * @param c - Coefficient of the term.
   * @returns The corresponding constant element.
   * @see SymPy `sympy.polys.compatibility.IPolys.ground_new`
   */
  abstract groundNew(c: ExprLike): P;
  /**
   * Builds a polynomial from terms, combining equal monomials and dropping zero coefficients.
   *
   * @param terms - Monomial and coefficient pairs.
   * @returns The resulting polynomial.
   */
  abstract fromTerms(terms: Iterable<readonly [Monom, ExprLike]>): P;
  /**
   * Selects a slice of generators, yielding the coefficient domain if none remain.
   *
   * @param start - Inclusive starting index.
   * @param end - Exclusive ending index.
   * @returns The ring with the generators start..end.
   */
  abstract slice(start: number, end?: number): IPolys<P> | Domain;
  /**
   * Changes the coefficient domain while retaining the ring generators.
   *
   * @param K - Coefficient domain for the polynomial arithmetic.
   * @returns The ring over the new domain.
   */
  abstract withDomain(K: Domain): IPolys<P>;
  /** The element with the same terms in another ring with as many generators. */
  protected abstract moveTo(f: P, R: IPolys<P>): P;

  /** An element of this ring from an element or a ground value (SymPy wrap). */
  protected wrap(f: P | ExprLike): P {
    return isElement<P>(f) ? f : this.groundNew(f);
  }

  /** x_j**k. */
  protected genPow(j: number, k: number): P {
    return this.fromTerms([[this.unit(j, k), this.domain.one]]);
  }

  private unit(j: number, k: number): number[] {
    const m = new Array<number>(this.ngens).fill(0);
    m[j] = k;
    return m;
  }

  /** f with its terms of degree k in x_j only (as a polynomial without x_j). */
  protected coeffIn(f: P, j: number, k: number): P {
    return f.coeffWrt(j, k);
  }

  /** The degree of f in x_j (-Infinity for zero). */
  protected degIn(f: P, j: number): number {
    return f.isZero ? -Infinity : f.degree(j);
  }

  /** The leading coefficient of f in x_j, a polynomial without x_j. */
  protected lcIn(f: P, j: number): P {
    return this.coeffIn(f, j, this.degIn(f, j));
  }

  /** The constant value of a polynomial known to be constant. */
  protected groundOf(f: P): Expr {
    const ts = f.listterms();
    return ts.length ? first(ts)[1] : this.domain.zero;
  }

  /** Apply fn to every ground coefficient. */
  protected mapCoeffs(f: P, fn: (c: Expr, m: Monom) => Expr): P {
    return this.fromTerms(f.listterms().map(([m, c]) => [m, fn(c, m)] as const));
  }

  // ---- densearith ---------------------------------------------------------

  /**
   * Adds a monomial term to the polynomial.
   *
   * @param f - Polynomial to operate on.
   * @param c - Coefficient of the monomial to add, subtract or multiply.
   * @param i - Exponent of the term in the main variable.
   * @returns The sum with `c*x**i`.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_add_term`
   */
  dupAddTerm(f: P, c: ExprLike, i: IntLike): P {
    return f.add(this.groundNew(c).mul(this.genPow(0, intArg(i))));
  }
  /**
   * Adds a term in the main variable whose coefficient uses the remaining generators.
   *
   * @param f - Polynomial to operate on.
   * @param c - Coefficient of the monomial to add, subtract or multiply.
   * @param i - Exponent of the term in the main variable.
   * @returns The sum of the polynomial and the term `c*x**i`.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_add_term`
   */
  dmpAddTerm(f: P, c: P | ExprLike, i: IntLike): P {
    return f.add(this.wrap(c).mul(this.genPow(0, intArg(i))));
  }
  /**
   * Subtracts a monomial term from the polynomial.
   *
   * @param f - Polynomial to operate on.
   * @param c - Coefficient of the monomial to add, subtract or multiply.
   * @param i - Exponent of the term in the main variable.
   * @returns The difference polynomial.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_sub_term`
   */
  dupSubTerm(f: P, c: ExprLike, i: IntLike): P {
    return f.sub(this.groundNew(c).mul(this.genPow(0, intArg(i))));
  }
  /**
   * Subtracts a term of the specified degree in the main variable.
   *
   * @param f - Polynomial to operate on.
   * @param c - Coefficient of the monomial to add, subtract or multiply.
   * @param i - Exponent of the term in the main variable.
   * @returns The difference between the polynomial and the term `c*x**i`.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_sub_term`
   */
  dmpSubTerm(f: P, c: P | ExprLike, i: IntLike): P {
    return f.sub(this.wrap(c).mul(this.genPow(0, intArg(i))));
  }
  /**
   * Multiplies the polynomial by a monomial term.
   *
   * @param f - Polynomial to operate on.
   * @param c - Coefficient of the monomial to add, subtract or multiply.
   * @param i - Exponent of the term in the main variable.
   * @returns The product with `c*x**i`.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_mul_term`
   */
  dupMulTerm(f: P, c: ExprLike, i: IntLike): P {
    return f.mul(this.groundNew(c).mul(this.genPow(0, intArg(i))));
  }
  /**
   * Multiplies by a term of the specified degree in the main variable.
   *
   * @param f - Polynomial to operate on.
   * @param c - Coefficient of the monomial to add, subtract or multiply.
   * @param i - Exponent of the term in the main variable.
   * @returns The product of the polynomial and the term `c*x**i`.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_mul_term`
   */
  dmpMulTerm(f: P, c: P | ExprLike, i: IntLike): P {
    return f.mul(this.wrap(c).mul(this.genPow(0, intArg(i))));
  }
  /**
   * Adds a ground value to the constant coefficient.
   *
   * @param f - Polynomial to operate on.
   * @param c - Coefficient of the term.
   * @returns The updated polynomial.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_add_ground`
   */
  dupAddGround(f: P, c: ExprLike): P {
    return f.add(this.groundNew(c));
  }
  /**
   * Adds a ground value to the constant coefficient.
   *
   * @param f - Polynomial to operate on.
   * @param c - Coefficient of the term.
   * @returns The updated polynomial.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_add_ground`
   */
  dmpAddGround(f: P, c: ExprLike): P {
    return f.add(this.groundNew(c));
  }
  /**
   * Subtracts a ground value from the constant coefficient.
   *
   * @param f - Polynomial to operate on.
   * @param c - Coefficient of the term.
   * @returns The updated polynomial.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_sub_ground`
   */
  dupSubGround(f: P, c: ExprLike): P {
    return f.sub(this.groundNew(c));
  }
  /**
   * Subtracts a ground value from the constant coefficient.
   *
   * @param f - Polynomial to operate on.
   * @param c - Coefficient of the term.
   * @returns The updated polynomial.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_sub_ground`
   */
  dmpSubGround(f: P, c: ExprLike): P {
    return f.sub(this.groundNew(c));
  }
  /**
   * Multiplies every coefficient by the ground scalar.
   *
   * @param f - Polynomial to operate on.
   * @param c - Coefficient of the term.
   * @returns The scaled polynomial.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_mul_ground`
   */
  dupMulGround(f: P, c: ExprLike): P {
    return f.mulGround(groundConvert(this.domain, c));
  }
  /**
   * Multiplies every coefficient by the ground scalar.
   *
   * @param f - Polynomial to operate on.
   * @param c - Coefficient of the term.
   * @returns The scaled polynomial.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_mul_ground`
   */
  dmpMulGround(f: P, c: ExprLike): P {
    return this.dupMulGround(f, c);
  }
  /**
   * Divides every coefficient by the ground divisor.
   *
   * @param f - Dividend polynomial.
   * @param c - Coefficient of the term.
   * @returns The quotient polynomial.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_quo_ground`
   */
  dupQuoGround(f: P, c: ExprLike): P {
    const K = this.domain;
    const d = groundConvert(K, c);
    return this.mapCoeffs(f, (a) => groundQuo(K, a, d));
  }
  /**
   * Divides every coefficient by the ground divisor.
   *
   * @param f - Dividend polynomial.
   * @param c - Coefficient of the term.
   * @returns The quotient polynomial.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_quo_ground`
   */
  dmpQuoGround(f: P, c: ExprLike): P {
    return this.dupQuoGround(f, c);
  }
  /**
   * Divides every coefficient exactly by the ground divisor.
   *
   * @param f - Dividend polynomial.
   * @param c - Coefficient of the term.
   * @returns The exact quotient polynomial.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_exquo_ground`
   */
  dupExquoGround(f: P, c: ExprLike): P {
    const K = this.domain;
    const d = groundConvert(K, c);
    return this.mapCoeffs(f, (a) => groundExquo(K, a, d));
  }
  /**
   * Divides every coefficient exactly by the ground divisor.
   *
   * @param f - Dividend polynomial.
   * @param c - Coefficient of the term.
   * @returns The exact quotient polynomial.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_exquo_ground`
   */
  dmpExquoGround(f: P, c: ExprLike): P {
    return this.dupExquoGround(f, c);
  }
  /**
   * Multiplies the polynomial by a power of its generator.
   *
   * @param f - Polynomial to operate on.
   * @param n - Number of powers to shift.
   * @returns The polynomial multiplied by the specified power of the generator.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_lshift`
   */
  dupLshift(f: P, n: IntLike): P {
    return f.mul(this.genPow(0, intArg(n)));
  }
  /**
   * Divides by a power of the generator, discarding lower-degree terms.
   *
   * @param f - Polynomial to operate on.
   * @param n - Number of powers to shift.
   * @returns The polynomial after discarding the specified number of trailing coefficients.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_rshift`
   */
  dupRshift(f: P, n: IntLike): P {
    const k = intArg(n);
    return this.fromTerms(f.listterms().filter(([m]) => first(m) >= k).map(([m, c]) => [[first(m) - k, ...m.slice(1)], c] as const));
  }
  /**
   * Takes the absolute value of each coefficient.
   *
   * @param f - Polynomial to operate on.
   * @returns The coefficientwise absolute polynomial.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_abs`
   */
  dupAbs(f: P): P {
    return this.mapCoeffs(f, (c) => groundAbs(this.domain, c));
  }
  /**
   * Takes the absolute value of each coefficient.
   *
   * @param f - Polynomial to operate on.
   * @returns The coefficientwise absolute polynomial.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_abs`
   */
  dmpAbs(f: P): P {
    return this.dupAbs(f);
  }
  /**
   * Negates every coefficient of the polynomial.
   *
   * @param f - Polynomial to operate on.
   * @returns The additive inverse.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_neg`
   */
  dupNeg(f: P): P {
    return f.neg();
  }
  /**
   * Negates every coefficient of the polynomial.
   *
   * @param f - Polynomial to operate on.
   * @returns The additive inverse.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_neg`
   */
  dmpNeg(f: P): P {
    return f.neg();
  }
  /**
   * Adds the corresponding coefficients of two polynomials.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The sum polynomial.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_add`
   */
  dupAdd(f: P, g: P): P {
    return f.add(g);
  }
  /**
   * Adds the corresponding coefficients of two polynomials.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The sum polynomial.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_add`
   */
  dmpAdd(f: P, g: P): P {
    return f.add(g);
  }
  /**
   * Subtracts the second polynomial from the first.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The difference polynomial.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_sub`
   */
  dupSub(f: P, g: P): P {
    return f.sub(g);
  }
  /**
   * Subtracts the second polynomial from the first.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The difference polynomial.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_sub`
   */
  dmpSub(f: P, g: P): P {
    return f.sub(g);
  }
  /**
   * Adds the product of the last two polynomials to the first.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @param h - Third polynomial operand.
   * @returns The polynomial `f + g*h`.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_add_mul`
   */
  dupAddMul(f: P, g: P, h: P): P {
    return f.add(g.mul(h));
  }
  /**
   * Adds the product of the last two polynomials to the first.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @param h - Third polynomial operand.
   * @returns The polynomial `f + g*h`.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_add_mul`
   */
  dmpAddMul(f: P, g: P, h: P): P {
    return f.add(g.mul(h));
  }
  /**
   * Subtracts the product of the last two polynomials from the first.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @param h - Third polynomial operand.
   * @returns The polynomial `f - g*h`.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_sub_mul`
   */
  dupSubMul(f: P, g: P, h: P): P {
    return f.sub(g.mul(h));
  }
  /**
   * Subtracts the product of the last two polynomials from the first.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @param h - Third polynomial operand.
   * @returns The polynomial `f - g*h`.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_sub_mul`
   */
  dmpSubMul(f: P, g: P, h: P): P {
    return f.sub(g.mul(h));
  }
  /**
   * Multiplies the two input polynomials.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The product polynomial.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_mul`
   */
  dupMul(f: P, g: P): P {
    return f.mul(g);
  }
  /**
   * Multiplies the two input polynomials.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The product polynomial.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_mul`
   */
  dmpMul(f: P, g: P): P {
    return f.mul(g);
  }
  /**
   * Multiplies the polynomial by itself.
   *
   * @param f - Polynomial to operate on.
   * @returns The squared polynomial.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_sqr`
   */
  dupSqr(f: P): P {
    return f.mul(f);
  }
  /**
   * Multiplies the polynomial by itself.
   *
   * @param f - Polynomial to operate on.
   * @returns The squared polynomial.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_sqr`
   */
  dmpSqr(f: P): P {
    return f.mul(f);
  }
  /**
   * Raises the polynomial to a nonnegative integer power.
   *
   * @param f - Polynomial to operate on.
   * @param n - Exponent or degree.
   * @returns The polynomial power.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_pow`
   */
  dupPow(f: P, n: IntLike): P {
    return this.dmpPow(f, n);
  }
  /**
   * Raises the polynomial to a nonnegative integer power.
   *
   * @param f - Polynomial to operate on.
   * @param n - Exponent or degree.
   * @returns The polynomial power.
   * @throws RangeError when the exponent is negative.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_pow`
   */
  dmpPow(f: P, n: IntLike): P {
    const k = intArg(n);
    if (k < 0) throw new RangeError("can't raise polynomial to a negative power");
    return k === 0 || f.isZero ? (k === 0 ? this.one : f) : f.pow(k);
  }
  /**
   * Multiplies all the supplied polynomial factors.
   *
   * @param polys - Input polynomials.
   * @returns Their product.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_expand`
   */
  dupExpand(polys: readonly P[]): P {
    return polys.reduce((a, b) => a.mul(b), this.one);
  }
  /**
   * Multiplies all the supplied polynomial factors.
   *
   * @param polys - Input polynomials.
   * @returns Their product.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_expand`
   */
  dmpExpand(polys: readonly P[]): P {
    return this.dupExpand(polys);
  }
  /**
   * Eliminates the algebraic coefficient generator by taking the resultant with its minimal polynomial.
   *
   * @param f - Polynomial to operate on.
   * @returns The lifted norm polynomial.
   * @throws DomainError when the coefficient domain is not algebraic.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_lift`
   */
  dmpLift(f: P): P {
    const K0 = this.domain;
    const K = K0 instanceof AlgebraicField ? K0 : K0 instanceof GaussianRationalField || K0 instanceof GaussianIntegerRing ? new AlgebraicField(QQ, S.I) : undefined;
    if (K === undefined) throw new DomainError('computation can be done only in an algebraic domain');
    const a = new Dummy('a');
    const inA = (rep: readonly { numerator: bigint; denominator: bigint }[]): Expr => add(...rep.map((c, i) => mul(Rational.of(c.numerator, c.denominator), pow(a, rep.length - 1 - i))));
    const F = add(...f.listterms().map(([m, c]) => mul(inA(K.convert(K0.toSympy(c)).rep), ...m.map((e, j) => pow(at(this.symbols, j), e)))));
    const r = resultant(F, inA(K.mod), a);
    return this.withDomain(K0.dom).fromTerms(Poly.from(r, [...this.symbols]).terms());
  }

  /** Pseudo-division in x_0 (SymPy dup_pdiv/dmp_pdiv). */
  private pdivIn(f: P, g: P, withQuotient: boolean): [P, P] {
    const df = this.degIn(f, 0);
    const dg = this.degIn(g, 0);
    if (g.isZero) throw new RangeError('polynomial division');
    let q = this.zero;
    let r = f;
    let dr = df;
    if (df < dg) return [q, r];
    let N = df - dg + 1;
    const lcG = this.lcIn(g, 0);
    for (;;) {
      const lcR = this.lcIn(r, 0);
      const j = dr - dg;
      N -= 1;
      if (withQuotient) q = q.mul(lcG).add(lcR.mul(this.genPow(0, j)));
      r = r.mul(lcG).sub(g.mul(lcR).mul(this.genPow(0, j)));
      dr = this.degIn(r, 0);
      if (dr < dg) break;
    }
    const c = lcG.pow(N);
    return [q.mul(c), r.mul(c)];
  }
  /**
   * Performs univariate polynomial pseudo-division.
   *
   * @param f - Dividend polynomial.
   * @param g - Divisor polynomial.
   * @returns The pseudo-quotient and pseudo-remainder.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_pdiv`
   */
  dupPdiv(f: P, g: P): [P, P] {
    return this.pdivIn(f, g, true);
  }
  /**
   * Performs pseudo-division in the main variable and retains the remainder.
   *
   * @param f - Dividend polynomial.
   * @param g - Divisor polynomial.
   * @returns The pseudo-remainder.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_prem`
   */
  dupPrem(f: P, g: P): P {
    return this.pdivIn(f, g, false)[1];
  }
  /**
   * Performs pseudo-division in the main variable and retains the quotient.
   *
   * @param f - Dividend polynomial.
   * @param g - Divisor polynomial.
   * @returns The pseudo-quotient.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_pquo`
   */
  dupPquo(f: P, g: P): P {
    return this.pdivIn(f, g, true)[0];
  }
  /**
   * Performs exact pseudo-division in the main variable.
   *
   * @param f - Dividend polynomial.
   * @param g - Divisor polynomial.
   * @returns The exact pseudo-quotient.
   * @throws ExactQuotientFailed when the divisor does not divide the dividend exactly.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_pexquo`
   */
  dupPexquo(f: P, g: P): P {
    const [q, r] = this.pdivIn(f, g, true);
    if (!r.isZero) throw new ExactQuotientFailed(`${str(g.asExpr())} does not divide ${str(f.asExpr())}`);
    return q;
  }
  /**
   * Performs pseudo-division in the principal generator.
   *
   * @param f - Dividend polynomial.
   * @param g - Divisor polynomial.
   * @returns The pseudo-quotient and pseudo-remainder.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_pdiv`
   */
  dmpPdiv(f: P, g: P): [P, P] {
    return this.dupPdiv(f, g);
  }
  /**
   * Performs pseudo-division in the main variable and retains the remainder.
   *
   * @param f - Dividend polynomial.
   * @param g - Divisor polynomial.
   * @returns The pseudo-remainder.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_prem`
   */
  dmpPrem(f: P, g: P): P {
    return this.dupPrem(f, g);
  }
  /**
   * Performs pseudo-division in the main variable and retains the quotient.
   *
   * @param f - Dividend polynomial.
   * @param g - Divisor polynomial.
   * @returns The pseudo-quotient.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_pquo`
   */
  dmpPquo(f: P, g: P): P {
    return this.dupPquo(f, g);
  }
  /**
   * Performs exact pseudo-division in the main variable.
   *
   * @param f - Dividend polynomial.
   * @param g - Divisor polynomial.
   * @returns The exact pseudo-quotient.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_pexquo`
   */
  dmpPexquo(f: P, g: P): P {
    return this.dupPexquo(f, g);
  }

  /**
   * Division with remainder in x_j whose coefficients (polynomials in
   * x_{j+1}, ...) are divided recursively (SymPy dmp_rr_div, dmp_ff_div):
   * the division stops at the first leading coefficient that does not divide.
   */
  private divIn(f: P, g: P, j: number): [P, P] {
    if (g.isZero) throw new RangeError('polynomial division');
    const df = this.degIn(f, j);
    const dg = this.degIn(g, j);
    let q = this.zero;
    let r = f;
    let dr = df;
    if (df < dg) return [q, r];
    const lcG = this.lcIn(g, j);
    for (;;) {
      const lcR = this.lcIn(r, j);
      let c: P;
      if (j === this.ngens - 1) {
        // ground coefficients
        const K = this.domain;
        const a = this.groundOf(lcR);
        const b = this.groundOf(lcG);
        if (!K.isField && !groundIsZero(K, groundRem(K, a, b))) break;
        c = this.groundNew(groundQuo(K, a, b));
      } else {
        const [cq, cr] = this.divIn(lcR, lcG, j + 1);
        if (!cr.isZero) break;
        c = cq;
      }
      const t = c.mul(this.genPow(j, dr - dg));
      q = q.add(t);
      r = r.sub(g.mul(t));
      dr = this.degIn(r, j);
      if (dr < dg) break;
    }
    return [q, r];
  }
  /**
   * Divides polynomials using arithmetic in the coefficient ring.
   *
   * @param f - Dividend polynomial.
   * @param g - Divisor polynomial.
   * @returns The quotient and remainder.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_rr_div`
   */
  dupRrDiv(f: P, g: P): [P, P] {
    return this.divIn(f, g, 0);
  }
  /**
   * Divides polynomials using arithmetic in the coefficient ring.
   *
   * @param f - Dividend polynomial.
   * @param g - Divisor polynomial.
   * @returns The quotient and remainder.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_rr_div`
   */
  dmpRrDiv(f: P, g: P): [P, P] {
    return this.divIn(f, g, 0);
  }
  /**
   * Divides polynomials using arithmetic in the coefficient field.
   *
   * @param f - Dividend polynomial.
   * @param g - Divisor polynomial.
   * @returns The quotient and remainder.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_ff_div`
   */
  dupFfDiv(f: P, g: P): [P, P] {
    return this.divIn(f, g, 0);
  }
  /**
   * Divides polynomials using arithmetic in the coefficient field.
   *
   * @param f - Dividend polynomial.
   * @param g - Divisor polynomial.
   * @returns The quotient and remainder.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_ff_div`
   */
  dmpFfDiv(f: P, g: P): [P, P] {
    return this.divIn(f, g, 0);
  }
  /**
   * Divides one polynomial by another in the given domain.
   *
   * @param f - Dividend polynomial.
   * @param g - Divisor polynomial.
   * @returns The quotient and remainder.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_div`
   */
  dupDiv(f: P, g: P): [P, P] {
    return this.divIn(f, g, 0);
  }
  /**
   * Computes what remains after polynomial division.
   *
   * @param f - Dividend polynomial.
   * @param g - Divisor polynomial.
   * @returns The remainder.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_rem`
   */
  dupRem(f: P, g: P): P {
    return this.divIn(f, g, 0)[1];
  }
  /**
   * Divides the dividend by the divisor and keeps the quotient.
   *
   * @param f - Dividend polynomial.
   * @param g - Divisor polynomial.
   * @returns The polynomial quotient.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_quo`
   */
  dupQuo(f: P, g: P): P {
    return this.divIn(f, g, 0)[0];
  }
  /**
   * Divides the polynomial by a divisor that divides it exactly.
   *
   * @param f - Dividend polynomial.
   * @param g - Divisor polynomial.
   * @returns The exact quotient.
   * @throws ExactQuotientFailed when the divisor does not divide the dividend exactly.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_exquo`
   */
  dupExquo(f: P, g: P): P {
    const [q, r] = this.divIn(f, g, 0);
    if (!r.isZero) throw new ExactQuotientFailed(`${str(g.asExpr())} does not divide ${str(f.asExpr())}`);
    return q;
  }
  /**
   * Divides one polynomial by another in the given domain.
   *
   * @param f - Dividend polynomial.
   * @param g - Divisor polynomial.
   * @returns The quotient and remainder.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_div`
   */
  dmpDiv(f: P, g: P): [P, P] {
    return this.divIn(f, g, 0);
  }
  /**
   * Computes what remains after polynomial division.
   *
   * @param f - Dividend polynomial.
   * @param g - Divisor polynomial.
   * @returns The remainder.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_rem`
   */
  dmpRem(f: P, g: P): P {
    return this.divIn(f, g, 0)[1];
  }
  /**
   * Divides the dividend by the divisor and keeps the quotient.
   *
   * @param f - Dividend polynomial.
   * @param g - Divisor polynomial.
   * @returns The polynomial quotient.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_quo`
   */
  dmpQuo(f: P, g: P): P {
    return this.divIn(f, g, 0)[0];
  }
  /**
   * Divides the polynomial by a divisor that divides it exactly.
   *
   * @param f - Dividend polynomial.
   * @param g - Divisor polynomial.
   * @returns The exact quotient.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_exquo`
   */
  dmpExquo(f: P, g: P): P {
    return this.dupExquo(f, g);
  }

  /**
   * Computes the maximum norm from the polynomial's coefficients.
   *
   * @param f - Polynomial to operate on.
   * @returns The largest absolute coefficient.
   * @throws DomainError when the coefficient domain is unordered.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_max_norm`
   */
  dupMaxNorm(f: P): Expr {
    const K = this.domain;
    const cs = f.listterms().map(([, c]) => groundAbs(K, c));
    return cs.reduce((a, b) => {
      if (!isNum(a) || !isNum(b)) throw new DomainError('max_norm requires ordered coefficients');
      return numCmp(a, b) >= 0 ? a : b;
    }, K.zero);
  }
  /**
   * Computes the maximum norm from the polynomial's coefficients.
   *
   * @param f - Polynomial to operate on.
   * @returns The largest absolute coefficient.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_max_norm`
   */
  dmpMaxNorm(f: P): Expr {
    return this.dupMaxNorm(f);
  }
  /**
   * Computes the polynomial's L1 norm.
   *
   * @param f - Polynomial to operate on.
   * @returns The sum of absolute coefficients.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_l1_norm`
   */
  dupL1Norm(f: P): Expr {
    const K = this.domain;
    return f.listterms().reduce((s, [, c]) => K.add(s, groundAbs(K, c)), K.zero);
  }
  /**
   * Computes the polynomial's L1 norm.
   *
   * @param f - Polynomial to operate on.
   * @returns The sum of absolute coefficients.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_l1_norm`
   */
  dmpL1Norm(f: P): Expr {
    return this.dupL1Norm(f);
  }
  /**
   * Computes the squared Euclidean norm of the coefficient vector.
   *
   * @param f - Polynomial to operate on.
   * @returns The sum of squared coefficients.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_l2_norm_squared`
   */
  dupL2NormSquared(f: P): Expr {
    const K = this.domain;
    return f.listterms().reduce((s, [, c]) => K.add(s, K.mul(c, c)), K.zero);
  }
  /**
   * Computes the squared Euclidean norm of the coefficient vector.
   *
   * @param f - Polynomial to operate on.
   * @returns The sum of squared coefficients.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_l2_norm_squared`
   */
  dmpL2NormSquared(f: P): Expr {
    return this.dupL2NormSquared(f);
  }

  // ---- densetools ---------------------------------------------------------

  /** The m-th integral in x_j (SymPy dmp_integrate_in). */
  private integrateIn(f: P, m: number, j: number): P {
    const K = this.domain;
    if (m <= 0 || f.isZero) return f;
    return this.fromTerms(
      f.listterms().map(([mon, c]) => {
        const e = [...mon];
        e[j] = at(mon, j) + m;
        return [e, groundExquo(K, c, groundConvert(K, fallingFrom(at(mon, j), m)))] as const;
      }),
    );
  }
  /**
   * Integrates the polynomial `m` times.
   *
   * @param f - Polynomial to operate on.
   * @param m - Number of integrations.
   * @returns The repeated antiderivative.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_integrate`
   */
  dupIntegrate(f: P, m: IntLike): P {
    return this.integrateIn(f, intArg(m), 0);
  }
  /**
   * Integrates `m` times in the principal generator.
   *
   * @param f - Polynomial to operate on.
   * @param m - Number of integrations.
   * @returns The antiderivative in `x_0`.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_integrate`
   */
  dmpIntegrate(f: P, m: IntLike): P {
    return this.integrateIn(f, intArg(m), 0);
  }
  /**
   * Integrates `m` times with respect to the selected generator.
   *
   * @param f - Polynomial to operate on.
   * @param m - Number of integrations.
   * @param j - Index of the polynomial variable.
   * @returns The antiderivative in `x_j`.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_integrate_in`
   */
  dmpIntegrateIn(f: P, m: IntLike, j: IntLike): P {
    return this.integrateIn(f, intArg(m), this.checkLevel(j));
  }

  private checkLevel(j: IntLike): number {
    const k = intArg(j);
    if (k < 0 || k >= this.ngens) throw new RangeError(`0 <= j <= ${this.ngens - 1} expected, got ${k}`);
    return k;
  }

  /** The m-th derivative in x_j (SymPy dmp_diff_in). */
  private diffIn(f: P, m: number, j: number): P {
    if (m <= 0) return f;
    const K = this.domain;
    return this.fromTerms(
      f.listterms()
        .filter(([mon]) => at(mon, j) >= m)
        .map(([mon, c]) => {
          const e = [...mon];
          e[j] = at(mon, j) - m;
          return [e, K.mul(c, groundConvert(K, fallingDown(at(mon, j), m)))] as const;
        }),
    );
  }
  /**
   * Differentiates the polynomial `m` times.
   *
   * @param f - Polynomial to operate on.
   * @param m - Number of differentiations.
   * @returns The derivative polynomial.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_diff`
   */
  dupDiff(f: P, m: IntLike): P {
    return this.diffIn(f, intArg(m), 0);
  }
  /**
   * Differentiates `m` times in the principal generator.
   *
   * @param f - Polynomial to operate on.
   * @param m - Number of differentiations.
   * @returns The derivative in `x_0`.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_diff`
   */
  dmpDiff(f: P, m: IntLike): P {
    return this.diffIn(f, intArg(m), 0);
  }
  /**
   * Differentiates `m` times with respect to the selected generator.
   *
   * @param f - Polynomial to operate on.
   * @param m - Number of differentiations.
   * @param j - Index of the polynomial variable.
   * @returns The derivative in `x_j`.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_diff_in`
   */
  dmpDiffIn(f: P, m: IntLike, j: IntLike): P {
    return this.diffIn(f, intArg(m), this.checkLevel(j));
  }

  /** f with x_j = a, as a polynomial of this ring without x_j. */
  private evalIn(f: P, a: Expr, j: number): P {
    const K = this.domain;
    return this.fromTerms(
      f.listterms().map(([mon, c]) => {
        const e = [...mon];
        e[j] = 0;
        return [e, K.mul(c, groundPow(K, a, at(mon, j)))] as const;
      }),
    );
  }
  /** The polynomial without the generator j in the ring without it. */
  private dropIn(f: P, j: number): P | Expr {
    const R = this.withoutGen(j);
    if (!(R instanceof IPolys)) return this.groundOf(f);
    return R.fromTerms(f.listterms().map(([m, c]) => [[...m.slice(0, j), ...m.slice(j + 1)], c] as const));
  }
  private withoutGen(j: number): IPolys<P> | Domain {
    return this.dropRing(j);
  }
  /** The ring without the generator j, or the domain when none remains (SymPy R.drop(j)). */
  protected abstract dropRing(j: number): IPolys<P> | Domain;

  /**
   * Evaluates the polynomial at the supplied ground value.
   *
   * @param f - Polynomial to operate on.
   * @param a - Value substituted for the generator.
   * @returns The value at the evaluation point.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_eval`
   */
  dupEval(f: P, a: ExprLike): Expr {
    return this.groundOf(this.evalIn(f, groundConvert(this.domain, a), 0));
  }
  /**
   * Substitutes a value for the principal generator.
   *
   * @param f - Polynomial to operate on.
   * @param a - Value substituted for the generator.
   * @returns The value in the remaining generators or the ground domain.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_eval`
   */
  dmpEval(f: P, a: ExprLike): P | Expr {
    return this.dropIn(this.evalIn(f, groundConvert(this.domain, a), 0), 0);
  }
  /**
   * Substitutes a ground value for the selected generator and drops it from the ring.
   *
   * @param f - Polynomial to operate on.
   * @param a - Value substituted for the generator.
   * @param j - Index of the polynomial variable.
   * @returns The specialized polynomial or ground value.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_eval_in`
   */
  dmpEvalIn(f: P, a: ExprLike, j: IntLike): P | Expr {
    const k = this.checkLevel(j);
    return this.dropIn(this.evalIn(f, groundConvert(this.domain, a), k), k);
  }
  /**
   * Evaluates the repeated partial derivative at the supplied generator value.
   *
   * @param f - Polynomial to operate on.
   * @param m - Number of differentiations.
   * @param a - Value substituted for the generator.
   * @param j - Index of the polynomial variable.
   * @returns The specialized derivative.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_diff_eval_in`
   */
  dmpDiffEvalIn(f: P, m: IntLike, a: ExprLike, j: IntLike): P | Expr {
    const k = this.checkLevel(j);
    return this.dropIn(this.evalIn(this.diffIn(f, intArg(m), k), groundConvert(this.domain, a), k), k);
  }
  /**
   * Evaluates the trailing generators at the supplied values.
   *
   * @param f - Polynomial to operate on.
   * @param A - Values for successive trailing variables.
   * @returns The specialized polynomial or ground value.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_eval_tail`
   */
  dmpEvalTail(f: P, A: readonly ExprLike[]): P | Expr {
    let g = f;
    const n = this.ngens;
    A.forEach((a, i) => {
      g = this.evalIn(g, groundConvert(this.domain, a), n - A.length + i);
    });
    const R = this.slice(0, n - A.length);
    if (!(R instanceof IPolys)) return this.groundOf(g);
    return R.fromTerms(g.listterms().map(([m, c]) => [m.slice(0, n - A.length), c] as const));
  }

  /**
   * Reduces each coefficient modulo `p`, choosing symmetric representatives over the integers.
   *
   * @param f - Polynomial to operate on.
   * @param p - Modulus for reducing coefficients.
   * @returns The reduced polynomial.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_trunc`
   */
  dupTrunc(f: P, p: ExprLike): P {
    const K = this.domain;
    const q = groundConvert(K, p);
    return this.mapCoeffs(f, (c) => {
      const r = groundRem(K, c, q);
      return isZZ(K) && rat(r).p > floorDiv(rat(q).p, 2n) ? K.sub(r, q) : r;
    });
  }
  /**
   * Reduces each coefficient in the main variable modulo `g` in the remaining generators.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The reduced polynomial.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_trunc`
   */
  dmpTrunc(f: P, g: P): P {
    const d = this.degIn(f, 0);
    const p = this.embed(g);
    let out = this.zero;
    for (let k = 0; k <= d; k++) out = out.add(this.divIn(this.coeffIn(f, 0, k), p, 1)[1].mul(this.genPow(0, k)));
    return out;
  }

  /** An element of a ring with some of the generators of this one as an element of this ring. */
  protected embed(g: P): P {
    const pos = g.ring.symbols.map((s) => this.symbols.findIndex((t) => t.key === s.key));
    if (pos.some((i) => i < 0)) throw new PolynomialError('the generators of the polynomial are not generators of the ring');
    return this.fromTerms(
      g.listterms().map(([m, c]) => {
        const e = new Array<number>(this.ngens).fill(0);
        m.forEach((k, i) => (e[at(pos, i)] = k));
        return [e, c] as const;
      }),
    );
  }
  /**
   * Reduces the ground coefficients modulo `p`.
   *
   * @param f - Polynomial to operate on.
   * @param p - Modulus for reducing coefficients.
   * @returns The reduced polynomial.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_ground_trunc`
   */
  dmpGroundTrunc(f: P, p: ExprLike): P {
    return this.dupTrunc(f, p);
  }
  /**
   * Divides by the leading coefficient to normalize the polynomial.
   *
   * @param f - Polynomial to operate on.
   * @returns The monic polynomial.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_monic`
   */
  dupMonic(f: P): P {
    if (f.isZero) return f;
    const lc = f.LC;
    return groundEq(lc, this.domain.one) ? f : this.dupExquoGround(f, lc);
  }
  /**
   * Normalizes the polynomial by its ground leading coefficient.
   *
   * @param f - Polynomial to operate on.
   * @returns The polynomial normalized by its ground leading coefficient.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_ground_monic`
   */
  dmpGroundMonic(f: P): P {
    return this.dupMonic(f);
  }
  /**
   * Computes the polynomial content as the GCD of its coefficients.
   *
   * @param f - Polynomial to operate on.
   * @returns The content.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_content`
   */
  dupContent(f: P): Expr {
    const K = this.domain;
    return f.listterms().reduce((g, [, c]) => groundGcd(K, g, c), K.zero);
  }
  /**
   * Finds the common divisor of the ground coefficients.
   *
   * @param f - Polynomial to operate on.
   * @returns The ground content.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_ground_content`
   */
  dmpGroundContent(f: P): Expr {
    return this.dupContent(f);
  }
  /**
   * Separates the coefficient GCD from the primitive polynomial.
   *
   * @param f - Polynomial to operate on.
   * @returns The content and primitive part.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_primitive`
   */
  dupPrimitive(f: P): [Expr, P] {
    const K = this.domain;
    const cont = this.dupContent(f);
    if (f.isZero || groundEq(cont, K.one)) return [cont, f];
    return [cont, this.dupQuoGround(f, cont)];
  }
  /**
   * Factors out the GCD of the ground coefficients.
   *
   * @param f - Polynomial to operate on.
   * @returns The ground content and primitive part.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_ground_primitive`
   */
  dmpGroundPrimitive(f: P): [Expr, P] {
    return this.dupPrimitive(f);
  }
  /**
   * Removes the content shared by both polynomials.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The common content and both quotients.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_extract`
   */
  dupExtract(f: P, g: P): [Expr, P, P] {
    const K = this.domain;
    const c = groundGcd(K, this.dupContent(f), this.dupContent(g));
    if (groundEq(c, K.one)) return [c, f, g];
    return [c, this.dupQuoGround(f, c), this.dupQuoGround(g, c)];
  }
  /**
   * Removes the ground content shared by both polynomials.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The common ground content and both quotients.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_ground_extract`
   */
  dmpGroundExtract(f: P, g: P): [Expr, P, P] {
    return this.dupExtract(f, g);
  }

  /**
   * Separates the components of `f(x + I*y)` in the first two generators.
   *
   * @param f - Polynomial to operate on.
   * @returns The real and imaginary polynomials.
   * @throws PolynomialError when the coefficients are outside the supported real domains or the ring does not have two generators or the input depends on another generator.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_real_imag`
   */
  dupRealImag(f: P): [P, P] {
    const K = this.domain;
    if (!(isZZ(K) || K instanceof RationalField)) throw new PolynomialError(`computing real and imaginary parts is not supported over ${K.toString()}`);
    if (this.ngens < 2) throw new PolynomialError('dup_real_imag needs a ring with two generators');
    const x = at(this.gens, 0);
    const y = at(this.gens, 1);
    let re = this.zero;
    let im = this.zero;
    for (const [m, c] of f.listterms()) {
      if (m.slice(1).some((e) => e !== 0)) throw new PolynomialError('dup_real_imag expects a univariate polynomial in the first generator');
      const n = first(m);
      // (x + I*y)**n = sum binomial(n, k) x**(n-k) (I*y)**k
      let b = 1n;
      for (let k = 0; k <= n; k++) {
        const t = x.pow(n - k).mul(y.pow(k)).mulGround(K.mul(c, Rational.of(b)));
        const s = k % 4;
        if (s === 0) re = re.add(t);
        else if (s === 1) im = im.add(t);
        else if (s === 2) re = re.sub(t);
        else im = im.sub(t);
        b = (b * BigInt(n - k)) / BigInt(k + 1);
      }
    }
    return [re, im];
  }
  /**
   * Negates the indeterminate of the polynomial.
   *
   * @param f - Polynomial to operate on.
   * @returns The polynomial evaluated at the negated generator.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_mirror`
   */
  dupMirror(f: P): P {
    return this.mapCoeffs(f, (c, m) => (first(m) % 2 ? this.domain.neg(c) : c));
  }
  /**
   * Scales the polynomial's argument by a ground factor.
   *
   * @param f - Polynomial to operate on.
   * @param a - Factor multiplying the generator.
   * @returns The polynomial evaluated at the scaled generator.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_scale`
   */
  dupScale(f: P, a: ExprLike): P {
    const K = this.domain;
    const b = groundConvert(K, a);
    return this.mapCoeffs(f, (c, m) => K.mul(c, groundPow(K, b, first(m))));
  }
  /**
   * Translates the polynomial's argument by the supplied value.
   *
   * @param f - Polynomial to operate on.
   * @param a - Translation added to the generator or generators.
   * @returns The translated polynomial.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_shift`
   */
  dupShift(f: P, a: ExprLike): P {
    return this.composeIn(f, [[0, at(this.gens, 0).add(this.groundNew(a))]]);
  }
  /**
   * Translates each polynomial generator by its corresponding shift.
   *
   * @param f - Polynomial to operate on.
   * @param a - Translation added to the generator or generators.
   * @returns The polynomial after translating each generator.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_shift`
   */
  dmpShift(f: P, a: readonly ExprLike[]): P {
    return this.composeIn(f, a.map((ai, i) => [i, at(this.gens, i).add(this.groundNew(ai))] as const));
  }
  /** f with x_j replaced by the given polynomials. */
  private composeIn(f: P, subs: readonly (readonly [number, P])[]): P {
    let out = this.zero;
    for (const [m, c] of f.listterms()) {
      const e = [...m];
      let t = this.one;
      for (const [j, g] of subs) {
        t = t.mul(g.pow(at(m, j)));
        e[j] = 0;
      }
      out = out.add(t.mul(this.fromTerms([[e, c]])));
    }
    return out;
  }
  /**
   * Substitutes the ratio of two polynomials and clears its denominator to the degree of the input.
   *
   * @param f - Polynomial in the original generator.
   * @param p - Numerator of the rational substitution.
   * @param q - Denominator of the rational substitution.
   * @returns The polynomial after the rational substitution and denominator clearing.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_transform`
   */
  dupTransform(f: P, p: P, q: P): P {
    if (f.isZero) return f;
    const n = this.degIn(f, 0);
    let out = this.zero;
    for (const [m, c] of f.listterms()) out = out.add(p.pow(first(m)).mul(q.pow(n - first(m))).mulGround(c));
    return out;
  }
  /**
   * Substitutes the second polynomial into the first.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The composition of the input polynomials.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_compose`
   */
  dupCompose(f: P, g: P): P {
    return this.composeIn(f, [[0, g]]);
  }
  /**
   * Composes polynomials in their principal generator, leaving other generators fixed.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The composition in the main variable.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_compose`
   */
  dmpCompose(f: P, g: P): P {
    return this.composeIn(f, [[0, g]]);
  }
  /**
   * Decomposes the polynomial into a composition of simpler polynomials.
   *
   * @param f - Polynomial to operate on.
   * @returns The components in composition order.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_decompose`
   */
  dupDecompose(f: P): P[] {
    return this.toPoly(f).decompose().map((p) => this.fromPoly(p));
  }
  /**
   * Counts sign changes between successive nonzero coefficients.
   *
   * @param f - Polynomial to operate on.
   * @returns The variation count.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_sign_variations`
   */
  dupSignVariations(f: P): number {
    const K = this.domain;
    let prev: boolean | undefined;
    let k = 0;
    const cs = f.listterms().sort((a, b) => first(b[0]) - first(a[0]));
    for (const [, c] of cs) {
      const neg0 = groundIsNegative(K, c);
      if (prev !== undefined && prev !== neg0) k++;
      prev = neg0;
    }
    return k;
  }
  /**
   * Clears coefficient denominators and optionally converts to the associated ring of integers.
   *
   * @param f - Polynomial to operate on.
   * @param convert - Convert the resulting coefficients to the associated ring.
   * @returns The common denominator and scaled polynomial.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_clear_denoms`
   */
  dupClearDenoms(f: P, convert = false): [Expr, P] {
    const K = this.domain;
    if (!(K instanceof RationalField)) return [K.one, f];
    const common = f.listterms().reduce((l, [, c]) => groundLcm(ZZ, l, groundDenom(c)), ZZ.one);
    const g = groundEq(common, K.one) ? f : f.mulGround(common);
    return [common, convert ? this.moveTo(g, this.withDomain(ZZ)) : g];
  }
  /**
   * Multiplies the polynomial by the least common multiple of its coefficient denominators.
   *
   * @param f - Polynomial to operate on.
   * @param convert - Convert the resulting coefficients to the associated ring.
   * @returns The common denominator and scaled polynomial.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_clear_denoms`
   */
  dmpClearDenoms(f: P, convert = false): [Expr, P] {
    return this.dupClearDenoms(f, convert);
  }
  /**
   * Computes the multiplicative inverse of the polynomial modulo `x**n`.
   *
   * @param f - Polynomial to operate on.
   * @param n - Truncation order of the inverse series.
   * @returns The truncated reciprocal.
   * @throws PolynomialError when the constant coefficient is not a unit.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_revert`
   */
  dupRevert(f: P, n: IntLike): P {
    const K = this.domain;
    const N = intArg(n);
    const tc = this.groundOf(this.coeffIn(f, 0, 0));
    if (!groundIsUnit(K, tc)) throw new PolynomialError(`${str(tc)} is not a unit in ${K.toString()}`);
    let g = this.groundNew(K.isField ? K.quo(K.one, tc) : tc);
    let h = this.fromTerms([[this.unit(0, 2), K.one]]);
    const steps = Math.ceil(Math.log2(N));
    for (let i = 1; i <= steps; i++) {
      g = this.dupRem(g.mulGround(Rational.of(2)).sub(f.mul(g.mul(g))), h);
      h = h.mul(h);
    }
    return g;
  }

  // ---- sqfreetools, factortools and euclidtools -----------------------------

  /** f as a Poly over the generators and domain of the ring. */
  protected toPoly(f: P): Poly {
    return Poly.from(f.asExpr(), this.symbols, { domain: this.domain });
  }
  /** A Poly over the generators of the ring as an element. */
  protected fromPoly(p: Poly): P {
    return this.fromTerms(p.terms());
  }
  /** An expression polynomial in the generators of the ring as an element. */
  protected fromExprPoly(e: Expr): P {
    return this.fromPoly(Poly.from(e, this.symbols, { domain: this.domain }));
  }

  /** The leading coefficient in the lexicographic order (SymPy dmp_ground_LC). */
  protected groundLC(f: P): Expr {
    let best: readonly [Monom, Expr] | undefined;
    for (const t of f.listterms()) if (best === undefined || lexCmp(t[0], best[0]) > 0) best = t;
    return best === undefined ? this.domain.zero : best[1];
  }

  /** The gcd normalized as SymPy's (monic over a field, positive leading coefficient over ZZ). */
  private gcdOf(f: P, g: P): P {
    const K = this.domain;
    if (K.isField && K.isExact && K !== QQ && K !== EX && String(K) !== 'EXRAW') {
      const h = new FieldPoly(K,this.ngens,f.listterms()).gcd(new FieldPoly(K,this.ngens,g.listterms()));
      return this.fromTerms(h.terms.map(([m,c]) => [m,K.toSympy(c)]));
    }
    // mgcd normalizes the leading coefficient to be positive
    const h = this.fromExprPoly(mgcd(f.asExpr(), g.asExpr(), this.symbols));
    return K.isField ? h.mulGround(K.quo(K.one, this.groundLC(h))) : h;
  }

  /**
   * Factors the greatest common divisor out of both inputs.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The GCD and both cofactors.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_inner_gcd`
   */
  dmpInnerGcd(f: P, g: P): [P, P, P] {
    if (f.isZero && g.isZero) return [this.zero, this.zero, this.zero];
    const h = this.gcdOf(f, g);
    return [h, this.exquoBy(f, h), this.exquoBy(g, h)];
  }
  /** f/h for a divisor h of f (a gcd or a content). */
  private exquoBy(f: P, h: P): P {
    return this.divIn(f, h, 0)[0];
  }
  /**
   * Factors the greatest common divisor out of both inputs.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The GCD and both cofactors.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_inner_gcd`
   */
  dupInnerGcd(f: P, g: P): [P, P, P] {
    return this.dmpInnerGcd(f, g);
  }
  /**
   * Finds the greatest polynomial divisor common to both inputs.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The GCD.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_gcd`
   */
  dmpGcd(f: P, g: P): P {
    return this.dmpInnerGcd(f, g)[0];
  }
  /**
   * Finds the greatest polynomial divisor common to both inputs.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The GCD.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_gcd`
   */
  dupGcd(f: P, g: P): P {
    return this.dmpGcd(f, g);
  }
  /** f*g/gcd(f, g), zero when f or g is zero. */
  private lcmPart(f: P, g: P): P {
    return f.isZero || g.isZero ? this.zero : this.exquoBy(f.mul(g), this.dmpGcd(f, g));
  }
  /**
   * Computes the polynomial LCM over a ring using the LCM of the contents and a positive leading
   * coefficient.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The normalized LCM.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_rr_lcm`
   */
  dupRrLcm(f: P, g: P): P {
    const K = this.domain;
    const [fc, F] = this.dupPrimitive(f);
    const [gc, G] = this.dupPrimitive(g);
    const h = this.lcmPart(F, G);
    return h.mulGround(K.mul(groundLcm(K, fc, gc), canonicalUnit(K, this.groundLC(h))));
  }
  /**
   * Computes the least common multiple over a coefficient field.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The monic LCM.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_ff_lcm`
   */
  dupFfLcm(f: P, g: P): P {
    return this.dupMonic(this.lcmPart(f, g));
  }
  /**
   * Finds the least polynomial multiple common to both inputs.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The LCM.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_lcm`
   */
  dupLcm(f: P, g: P): P {
    return this.domain.isField ? this.dupFfLcm(f, g) : this.dupRrLcm(f, g);
  }
  /**
   * Computes the polynomial LCM over a ring with the LCM of the ground contents.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The normalized LCM.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_rr_lcm`
   */
  dmpRrLcm(f: P, g: P): P {
    const K = this.domain;
    const [fc, F] = this.dmpGroundPrimitive(f);
    const [gc, G] = this.dmpGroundPrimitive(g);
    return this.lcmPart(F, G).mulGround(groundLcm(K, fc, gc));
  }
  /**
   * Computes the LCM over a field with ground leading coefficient one.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The ground-monic LCM.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_ff_lcm`
   */
  dmpFfLcm(f: P, g: P): P {
    return this.dmpGroundMonic(this.lcmPart(f, g));
  }
  /**
   * Computes the LCM, making it monic over a field and preserving the LCM of contents over a ring.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The normalized LCM.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_lcm`
   */
  dmpLcm(f: P, g: P): P {
    if (this.ngens === 1) return this.dupLcm(f, g);
    return this.domain.isField ? this.dmpFfLcm(f, g) : this.dmpRrLcm(f, g);
  }
  /** The content in x_j: the gcd of the coefficients of the powers of x_j (SymPy dmp_content). */
  private contentIn(f: P, j: number): P {
    let c = this.zero;
    for (let k = this.degIn(f, j); k >= 0; k--) {
      const a = this.coeffIn(f, j, k);
      if (!a.isZero) c = c.isZero ? a : this.dmpGcd(c, a);
    }
    return c;
  }

  /**
   * Tests whether every irreducible factor occurs at most once.
   *
   * @param f - Polynomial to operate on.
   * @returns True for a square-free polynomial.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_sqf_p`
   */
  dupSqfP(f: P): boolean {
    return this.dmpSqfP(f);
  }
  /**
   * Translates the polynomial until its norm over the ground field is square-free.
   *
   * @param f - Polynomial to operate on.
   * @returns The shift, translated polynomial, and norm.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_sqf_norm`
   */
  dmpSqfNorm(f: P): [number[], P, P] {
    const K = this.domain;
    const dense = dmpFromDict(new Map(f.listterms().map(([m, c]) => [m, K.convert(c)])), this.ngens - 1, K);
    const [shift, g, r] = dmpSqfNorm(dense, this.ngens - 1, K);
    const ground = this.withDomain(K.dom);
    return [shift, this.fromTerms([...dmpToDict(g, this.ngens - 1)].map(([m, c]) => [m, K.toSympy(c)])), ground.fromTerms([...dmpToDict(r, this.ngens - 1)].map(([m, c]) => [m, K.dom.toSympy(c)]))];
  }

  /**
   * Test whether the polynomial is square-free.
   *
   * @param f - Polynomial to operate on.
   * @returns Whether every irreducible factor occurs at most once.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_sqf_p`
   */
  dmpSqfP(f: P): boolean {
    if (f.isZero) return true;
    if (this.domain instanceof FiniteField && this.ngens === 1) return this.toPoly(f).isSqf;
    for (let i = 0; i < this.ngens; i++) {
      const fp = this.diffIn(f, 1, i);
      if (fp.isZero) continue;
      if (this.degIn(this.dmpGcd(f, fp), i) > 0) return false;
    }
    return true;
  }
  /**
   * Removes repeated irreducible factors from the polynomial.
   *
   * @param f - Polynomial to operate on.
   * @returns The square-free part.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_sqf_part`
   */
  dupSqfPart(f: P): P {
    return this.dmpSqfPart(f);
  }
  /**
   * Removes repeated irreducible factors from the polynomial.
   *
   * @param f0 - Polynomial in this ring.
   * @returns The square-free part.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_sqf_part`
   */
  dmpSqfPart(f0: P): P {
    const K = this.domain;
    if (f0.isZero) return f0;
    if (K instanceof FiniteField && this.ngens === 1) return this.fromPoly(this.toPoly(f0).sqfPart());
    const f = groundIsNegative(K, this.groundLC(f0)) ? f0.neg() : f0;
    let gcd = f;
    for (let i = 0; i < this.ngens; i++) gcd = this.dmpGcd(gcd, this.diffIn(f, 1, i));
    const sqf = this.divIn(f, gcd, 0)[0];
    return K.isField ? this.dmpGroundMonic(sqf) : this.dmpGroundPrimitive(sqf)[1];
  }

  /** Yun's square-free decomposition of a polynomial in x_j, x_{j+1}, ... (SymPy dmp_sqf_list). */
  private sqfListIn(f0: P, j: number, all: boolean): [Expr, [P, number][]] {
    const K = this.domain;
    let coeff: Expr;
    let f = f0;
    if (K.isField) {
      coeff = this.groundLC(f);
      f = this.dmpGroundMonic(f);
    } else {
      [coeff, f] = this.dmpGroundPrimitive(f);
      if (groundIsNegative(K, this.groundLC(f))) {
        f = f.neg();
        coeff = K.neg(coeff);
      }
    }
    const deg = this.degIn(f, j);
    if (f.isZero || (j === this.ngens - 1 && deg <= 0)) return [coeff, []];
    let content = this.one;
    if (j < this.ngens - 1) {
      content = this.contentIn(f, j);
      f = this.exquoBy(f, content);
    }
    const result = new Map<number, P>();
    if (deg !== 0) {
      let [g, p, q] = this.dmpInnerGcd(f, this.diffIn(f, 1, j));
      for (let i = 1; ; i++) {
        const h = q.sub(this.diffIn(p, 1, j));
        if (h.isZero) {
          result.set(i, p);
          break;
        }
        [g, p, q] = this.dmpInnerGcd(p, h);
        if (all || this.degIn(g, j) > 0) result.set(i, g);
      }
    }
    if (j < this.ngens - 1) {
      const [cc, rc] = this.sqfListIn(content, j + 1, all);
      coeff = K.mul(coeff, cc);
      for (const [fac, i] of rc) result.set(i, result.get(i)?.mul(fac) ?? fac);
    }
    return [coeff, [...result].sort((a, b) => a[0] - b[0]).map(([i, p]) => [p, i] as [P, number])];
  }
  /**
   * Groups polynomial factors according to multiplicity.
   *
   * @param f - Polynomial to operate on.
   * @param all - Include factors of missing multiplicities.
   * @returns The coefficient and square-free factor–multiplicity pairs.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_sqf_list`
   */
  dupSqfList(f: P, all = false): [Expr, [P, number][]] {
    return this.dmpSqfList(f, all);
  }
  /**
   * Separates the polynomial into square-free factors by multiplicity.
   *
   * @param f - Polynomial to operate on.
   * @param all - Include factors of missing multiplicities.
   * @returns The coefficient and factor–multiplicity pairs.
   * @throws NotImplementedError when the polynomial is multivariate over a finite field.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_sqf_list`
   */
  dmpSqfList(f: P, all = false): [Expr, [P, number][]] {
    if (this.domain instanceof FiniteField) {
      if (this.ngens > 1) throw new NotImplementedError('multivariate square-free decomposition in finite fields');
      const [c, factors] = this.toPoly(f).sqfListAll(all);
      return [c, factors.map(([p, k]) => [this.fromPoly(p), k])];
    }
    return this.sqfListIn(f, 0, all);
  }
  /**
   * Decomposes the polynomial into square-free factors with the coefficient included in the first factor.
   *
   * @param f - Polynomial to operate on.
   * @param all - Include factors of missing multiplicities.
   * @returns The factor–multiplicity pairs.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_sqf_list_include`
   */
  dupSqfListInclude(f: P, all = false): [P, number][] {
    const [c, fs] = this.sqfListIn(f, 0, all);
    const head = fs[0];
    if (head?.[1] === 1) return [[head[0].mulGround(c), 1], ...fs.slice(1)];
    return [[this.groundNew(c), 1], ...fs];
  }
  /**
   * Decomposes the polynomial into square-free factors with the coefficient included in the first factor.
   *
   * @param f - Polynomial to operate on.
   * @param all - Include factors of missing multiplicities.
   * @returns The factor–multiplicity pairs.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_sqf_list_include`
   */
  dmpSqfListInclude(f: P, all = false): [P, number][] {
    return this.dupSqfListInclude(f, all);
  }
  /**
   * Computes the greatest factorial factorization of the polynomial.
   *
   * @param f0 - Polynomial in this ring.
   * @returns The factors and their factorial lengths.
   * @throws RangeError when the polynomial is zero.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_gff_list`
   */
  dupGffList(f0: P): [P, number][] {
    const K = this.domain;
    if (f0.isZero) throw new RangeError("greatest factorial factorization doesn't exist for a zero polynomial");
    const f = this.dupMonic(f0);
    if (this.degIn(f, 0) <= 0) return [];
    let g = this.dmpGcd(f, this.dupShift(f, K.one));
    const H = this.dupGffList(g).map(([h, k]) => {
      g = g.mul(this.dupShift(h, K.neg(Rational.of(k))));
      return [h, k + 1] as [P, number];
    });
    const r = this.divIn(f, g, 0)[0];
    return this.degIn(r, 0) <= 0 ? H : [[r, 1], ...H];
  }
  /**
   * Computes the greatest factorial factorization of the polynomial.
   *
   * @param f - Polynomial to operate on.
   * @returns The factors and their factorial lengths.
   * @throws MultivariatePolynomialError when the operation requires a univariate polynomial.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_gff_list`
   */
  dmpGffList(f: P): [P, number][] {
    if (this.ngens > 1) throw new MultivariatePolynomialError('greatest factorial factorization of a multivariate polynomial');
    return this.dupGffList(f);
  }

  /**
   * Factors the polynomial and separates its content.
   *
   * @param f - Polynomial to operate on.
   * @returns The content and factor–multiplicity pairs.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_factor_list`
   */
  dmpFactorList(f: P): [Expr, [P, number][]] {
    if (this.domain instanceof GaussianIntegerRing) {
      const K = this.domain;
      const [c, factors] = Poly.from(f.asExpr(), this.symbols, { domain: QQ_I }).factorList();
      let coefficient = c;
      const result: [P, number][] = [];
      for (const [p, multiplicity] of factors) {
        const terms = p.terms().map(([m, a]) => [m, QQ_I.convert(a)] as const);
        const denominator = terms.reduce((d, [, a]) => ilcm(d, ilcm(a.re.denominator, a.im.denominator)), 1n);
        const integral = terms.map(([m, a]) => [m, K.convert(a.mul(denominator))] as const);
        const content = integral.reduce((g, [, a]) => K.gcd(g, a), K.convert(0));
        coefficient = mul(coefficient, pow(mul(K.toSympy(content), Rational.of(1, denominator)), multiplicity));
        result.push([this.fromTerms(integral.map(([m, a]) => [m, K.toSympy(a.divmod(content)[0])])), multiplicity]);
      }
      return [K.fromSympy(cancel(coefficient)), sortExtensionFactors(result, K, this.ngens - 1)];
    }
    if (this.domain instanceof RealField) {
      const K = this.domain;
      const [content, factors] = this.toPoly(f).toExact().factorList();
      let coefficient = content;
      const result = factors.map(([p, multiplicity]): [P, number] => {
        const norm = p.maxNorm();
        coefficient = mul(coefficient, pow(norm, multiplicity));
        return [this.fromPoly(p.mulGround(pow(norm, -1))), multiplicity];
      });
      return [K.fromSympy(coefficient), result];
    }
    const [c, fs] = this.toPoly(f).factorList();
    const result = fs.map(([p, k]): [P, number] => [this.fromPoly(p), k]);
    const K = this.domain;
    return [groundConvert(K, c), K instanceof AlgebraicField || K instanceof GaussianRationalField ? sortExtensionFactors(result, K, this.ngens - 1) : result];
  }
  /**
   * Decomposes the polynomial into irreducible factors.
   *
   * @param f - Polynomial to operate on.
   * @returns The coefficient and factor–multiplicity pairs.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_factor_list`
   */
  dupFactorList(f: P): [Expr, [P, number][]] {
    return this.dmpFactorList(f);
  }
  /**
   * Factors the polynomial over the integers.
   *
   * @param f - Polynomial to operate on.
   * @returns The content and integer factors with multiplicities.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_zz_factor`
   */
  dupZzFactor(f: P): [Expr, [P, number][]] {
    return this.dmpFactorList(f);
  }
  /**
   * Factors the polynomial over the integers.
   *
   * @param f - Polynomial to operate on.
   * @returns The content and integer factors with multiplicities.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_zz_factor`
   */
  dmpZzFactor(f: P): [Expr, [P, number][]] {
    return this.dmpFactorList(f);
  }
  /**
   * Factors the polynomial over its coefficient domain.
   *
   * @param f - Polynomial to operate on.
   * @returns The coefficient and factor–multiplicity pairs.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_ext_factor`
   */
  dupExtFactor(f: P): [Expr, [P, number][]] {
    return this.dmpFactorList(f);
  }
  /**
   * Factors the polynomial over its coefficient domain.
   *
   * @param f - Polynomial to operate on.
   * @returns The coefficient and factor–multiplicity pairs.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_ext_factor`
   */
  dmpExtFactor(f: P): [Expr, [P, number][]] {
    return this.dmpFactorList(f);
  }
  /**
   * Factors the polynomial over its coefficient domain.
   *
   * @param f - Polynomial to operate on.
   * @returns The coefficient and factor–multiplicity pairs.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_qq_i_factor`
   */
  dupQqIFactor(f: P): [Expr, [P, number][]] {
    return this.dmpFactorList(f);
  }
  /**
   * Factors the polynomial over its coefficient domain.
   *
   * @param f - Polynomial to operate on.
   * @returns The coefficient and factor–multiplicity pairs.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_qq_i_factor`
   */
  dmpQqIFactor(f: P): [Expr, [P, number][]] {
    return this.dmpFactorList(f);
  }
  /**
   * Factors the polynomial over its coefficient domain.
   *
   * @param f - Polynomial to operate on.
   * @returns The coefficient and factor–multiplicity pairs.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_zz_i_factor`
   */
  dupZzIFactor(f: P): [Expr, [P, number][]] {
    return this.dmpFactorList(f);
  }
  /**
   * Factors the polynomial over its coefficient domain.
   *
   * @param f - Polynomial to operate on.
   * @returns The coefficient and factor–multiplicity pairs.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_zz_i_factor`
   */
  dmpZzIFactor(f: P): [Expr, [P, number][]] {
    return this.dmpFactorList(f);
  }
  /**
   * Factors a square-free polynomial over the integers.
   *
   * @param f - Polynomial to operate on.
   * @returns The content and irreducible factors.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_zz_factor_sqf`
   */
  dupZzFactorSqf(f: P): [Expr, P[]] {
    const [c, factors] = this.dmpFactorList(f);
    return [c, factors.map(([p]) => p)];
  }
  /**
   * Factors the polynomial and folds its content into the factor list.
   *
   * @param f - Polynomial to operate on.
   * @returns The factor–multiplicity pairs.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_factor_list_include`
   */
  dupFactorListInclude(f: P): [P, number][] {
    const [c, factors] = this.dmpFactorList(f);
    const head = factors[0];
    if (head === undefined) return [[this.groundNew(c), 1]];
    return [[head[0].mulGround(c), head[1]], ...factors.slice(1)];
  }
  /**
   * Factors the multivariate polynomial with its content included in the list.
   *
   * @param f - Polynomial to operate on.
   * @returns The factor–multiplicity pairs.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_factor_list_include`
   */
  dmpFactorListInclude(f: P): [P, number][] {
    return this.dupFactorListInclude(f);
  }
  /**
   * Constructs the integer polynomial whose roots are the primitive nth roots of unity.
   *
   * @param n - Index of the cyclotomic polynomial.
   * @returns The nth cyclotomic polynomial.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_zz_cyclotomic_poly`
   */
  dupZzCyclotomicPoly(n: number): P {
    const cs = cyclotomicCoeffs(n);
    return this.fromTerms(cs.map((c, i) => [this.unit(0, cs.length - 1 - i), Rational.of(c)]));
  }
  /**
   * Factors a binomial of the form `x**n - 1` or `x**n + 1` into cyclotomic polynomials.
   *
   * @param f - Polynomial to operate on.
   * @returns The matching value, or `NoMatch` when the requested form is unavailable.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_zz_cyclotomic_factor`
   */
  dupZzCyclotomicFactor(f: P): P[] | NoMatchResult {
    const terms = f.listterms();
    if (terms.length !== 2 || !groundEq(this.groundLC(f), this.domain.one)) return NoMatch;
    const constant = this.groundOf(this.coeffIn(f, 0, 0));
    if (!(groundEq(constant, this.domain.one) || groundEq(constant, this.domain.neg(this.domain.one)))) return NoMatch;
    const n = this.degIn(f, 0);
    const positive = groundEq(constant, this.domain.one);
    return divisors(positive ? 2 * n : n).filter(d => !positive || BigInt(n) % d !== 0n).map(d => this.dupZzCyclotomicPoly(Number(d)));
  }
  /**
   * Tests whether a univariate polynomial is irreducible over its coefficient domain.
   *
   * @param f - Polynomial to operate on.
   * @returns Whether the polynomial is irreducible over its coefficient domain.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_irreducible_p`
   */
  dupIrreducibleP(f: P): boolean {
    return this.dmpIrreducibleP(f);
  }
  /**
   * Tests whether a univariate polynomial is irreducible over the integers.
   *
   * @param f - Polynomial to operate on.
   * @returns The truth value, including `unknown` if undecidable.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_zz_irreducible_p`
   */
  dupZzIrreducibleP(f: P): Truth {
    const coeffs = this.toPoly(f).allCoeffs().map(c => rat(c).p);
    const content = coeffs.slice(1).reduce((a, b) => igcd(a, b), 0n);
    if (content !== 0n) {
      for (const p of factorint(content).keys()) {
        if (first(coeffs) % p !== 0n && last(coeffs) % (p * p) !== 0n) return true;
      }
    }
    return 'unknown';
  }
  /**
   * Tests whether the polynomial is irreducible.
   *
   * @param f - Polynomial to operate on.
   * @returns Whether the polynomial is irreducible over its coefficient domain.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_irreducible_p`
   */
  dmpIrreducibleP(f: P): boolean {
    const [, fs] = this.dmpFactorList(f);
    return fs.length === 1 && at(first(fs), 1) === 1;
  }
  /**
   * Bounds the coefficients of integer polynomial factors using the Knuth–Cohen bound.
   *
   * @param f - Polynomial to operate on.
   * @returns The coefficient bound.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_zz_mignotte_bound`
   */
  dupZzMignotteBound(f: P): Expr {
    const d = this.degIn(f, 0);
    const delta = Math.ceil(d / 2);
    const delta2 = Math.ceil(delta / 2);
    const cs = f.listterms().map(([, c]) => rat(c).p);
    const eucl = iroot(cs.reduce((s, c) => s + c * c, 0n), 2n);
    const t1 = binomialInt(delta - 1, delta2);
    const t2 = binomialInt(delta - 1, delta2 - 1);
    const lc = rat(this.groundLC(f)).p;
    const bound = t1 * eucl + t2 * (lc < 0n ? -lc : lc) + rat(this.dupMaxNorm(f)).p;
    return Rational.of(-floorDiv(-bound, 2n) * 2n);
  }
  /**
   * Tests whether the polynomial is cyclotomic.
   *
   * @param f - Polynomial to operate on.
   * @param irreducible - Whether the polynomial is already known to be irreducible.
   * @returns Whether the input is a cyclotomic polynomial.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_cyclotomic_p`
   */
  dupCyclotomicP(f: P, irreducible = false): boolean {
    const K = this.domain;
    if (!(isZZ(K) || K instanceof RationalField)) return false;
    if (f.listterms().some(([, c]) => !rat(c).isInteger)) return false;
    const lc = rat(this.groundLC(f));
    const tc = rat(this.groundOf(this.coeffIn(f, 0, 0)));
    if (!lc.isOne || !(tc.isOne || tc.p === -1n)) return false;
    if (!irreducible) {
      const [c, fs] = this.dmpFactorList(f);
      if (!groundEq(c, K.one) || fs.length !== 1 || at(first(fs), 1) !== 1) return false;
    }
    const n = this.degIn(f, 0);
    const x = at(this.gens, 0);
    // f(x) = g(x**2) + x*h(x**2) for odd n, h(x**2) + x*g(x**2) for even n; F = g**2 - x*h**2
    let g = this.zero;
    let h = this.zero;
    for (const [m, c] of f.listterms()) {
      const e = first(m);
      const t = x.pow(Math.floor(e / 2)).mulGround(c);
      if ((n - e) % 2 === 0) g = g.add(t);
      else h = h.add(t);
    }
    let F = g.mul(g).sub(x.mul(h.mul(h)));
    if (groundIsNegative(K, this.groundLC(F))) F = F.neg();
    if (F.equals(f)) return true;
    let G = this.dupMirror(f);
    if (groundIsNegative(K, this.groundLC(G))) G = G.neg();
    if (F.equals(G) && this.dupCyclotomicP(G)) return true;
    const S0 = this.dupSqfPart(F);
    return S0.mul(S0).equals(F) && this.dupCyclotomicP(S0);
  }

  /**
   * Eliminates the main variable by taking the resultant.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns A polynomial in the remaining variables or a ground element.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_resultant`
   */
  dmpResultant(f: P, g: P): P | Expr {
    return this.dropIn(this.fromExprPoly(resultant(f.asExpr(), g.asExpr(), this.gen0())), 0);
  }
  /**
   * Eliminates the polynomial variable by taking the resultant of the inputs.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The resultant.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_resultant`
   */
  dupResultant(f: P, g: P): Expr {
    return this.groundOf(this.fromExprPoly(resultant(f.asExpr(), g.asExpr(), this.gen0())));
  }
  /**
   * Computes the discriminant with respect to the principal generator.
   *
   * @param f - Polynomial to operate on.
   * @returns The discriminant in `x_0`.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_discriminant`
   */
  dmpDiscriminant(f: P): P | Expr {
    if (this.degIn(f, 0) <= 0) return this.dropIn(this.zero, 0);
    return this.dropIn(this.fromExprPoly(discriminant(f.asExpr(), this.gen0())), 0);
  }
  /**
   * Computes the discriminant of the polynomial.
   *
   * @param f - Polynomial to operate on.
   * @returns The discriminant value.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_discriminant`
   */
  dupDiscriminant(f: P): Expr {
    if (this.degIn(f, 0) <= 0) return this.domain.zero;
    return this.groundOf(this.fromExprPoly(discriminant(f.asExpr(), this.gen0())));
  }
  private gen0(): Sym {
    const x = first(this.symbols);
    if (!(x instanceof Sym)) throw new PolynomialError('the first generator must be a symbol');
    return x;
  }
  /**
   * Computes Bézout coefficients satisfying `s*f + t*g = h` for the GCD `h`.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The triple `[s, t, h]`.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_gcdex`
   */
  dupGcdex(f: P, g: P): [P, P, P] {
    const [s, t, h] = this.toPoly(f).gcdex(this.toPoly(g));
    return [this.fromPoly(s), this.fromPoly(t), this.fromPoly(h)];
  }
  /**
   * Finds a coefficient `s` satisfying `s*f = h` modulo `g` for the GCD `h`.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The pair `[s, h]`.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_half_gcdex`
   */
  dupHalfGcdex(f: P, g: P): [P, P] {
    const [s, , h] = this.dupGcdex(f, g);
    return [s, h];
  }
  /**
   * Inverts the polynomial in the quotient ring modulo `g`.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The modular inverse.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_invert`
   */
  dupInvert(f: P, g: P): P {
    return this.fromPoly(this.toPoly(f).invert(this.toPoly(g)));
  }
  /**
   * Builds the Sturm sequence for the polynomial.
   *
   * @param f - Polynomial to operate on.
   * @returns The ordered Sturm polynomials.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_sturm`
   */
  dupSturm(f: P): P[] {
    return this.toPoly(f).sturm().map((p) => this.fromPoly(p));
  }

  // ---- euclidtools: subresultants, resultants, contents, gcds and cancel ----

  /** An element without x_0 as an element of R[1:] (the ring without the first generator). */
  private toTail(R1: IPolys<P>, f: P): P {
    return R1.fromTerms(f.listterms().map(([m, c]) => [m.slice(1), c] as const));
  }

  /**
   * The subresultant PRS in x_0 and the scalar subresultants, the latter as
   * elements without x_0 (SymPy dmp_inner_subresultants).
   */
  private innerSubresultants(f0: P, g0: P): [P[], P[]] {
    const K = this.domain;
    let [f, g] = [f0, g0];
    let n = this.degIn(f, 0);
    let m = this.degIn(g, 0);
    if (n < m) [f, g, n, m] = [g, f, m, n];
    if (f.isZero) return [[], []];
    if (g.isZero) return [[f], [this.one]];
    const R = [f, g];
    let d = n - m;
    // b = (-1)**(d + 1)
    let h = this.dupPrem(f, g).mulGround(d % 2 ? K.one : K.neg(K.one));
    let lc = this.lcIn(g, 0);
    let c = lc.pow(d);
    // the conventional first scalar subdeterminant is 1
    const S = [this.one, c];
    c = c.neg();
    while (!h.isZero) {
      const k = this.degIn(h, 0);
      R.push(h);
      [f, g, d, m] = [g, h, m - k, k];
      h = this.exquoBy(this.dupPrem(f, g), lc.neg().mul(c.pow(d)));
      lc = this.lcIn(g, 0);
      // d > 1 is the abnormal case
      c = d > 1 ? this.exquoBy(lc.neg().pow(d), c.pow(d - 1)) : lc.neg();
      S.push(c.neg());
    }
    return [R, S];
  }
  /**
   * Computes the subresultant polynomial remainder sequence and its scalar subresultants.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The polynomial and scalar sequences.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_inner_subresultants`
   */
  dupInnerSubresultants(f: P, g: P): [P[], Expr[]] {
    const [R, S] = this.innerSubresultants(f, g);
    return [R, S.map((s) => this.groundOf(s))];
  }
  /**
   * Computes polynomial and scalar subresultants with respect to the principal generator.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The remainder sequence and scalar subresultants.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_inner_subresultants`
   */
  dmpInnerSubresultants(f: P, g: P): [P[], (P | Expr)[]] {
    const [R, S] = this.innerSubresultants(f, g);
    return [R, S.map((s) => this.dropIn(s, 0))];
  }
  /**
   * Computes the polynomial remainder sequence formed by successive subresultants.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The subresultant sequence.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_subresultants`
   */
  dupSubresultants(f: P, g: P): P[] {
    return this.innerSubresultants(f, g)[0];
  }
  /**
   * Computes successive subresultants in the principal generator.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The polynomial remainder sequence.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_subresultants`
   */
  dmpSubresultants(f: P, g: P): P[] {
    return this.innerSubresultants(f, g)[0];
  }
  /** The resultant and the PRS, the resultant as an element without x_0. */
  private prsResultant(f: P, g: P): [P, P[]] {
    if (f.isZero || g.isZero) return [this.zero, []];
    const [R, S] = this.innerSubresultants(f, g);
    return [this.degIn(last(R), 0) > 0 ? this.zero : last(S), R];
  }
  /**
   * Obtains the resultant from the subresultant remainder sequence.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The resultant and the sequence.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_prs_resultant`
   */
  dupPrsResultant(f: P, g: P): [Expr, P[]] {
    const [r, R] = this.prsResultant(f, g);
    return [this.groundOf(r), R];
  }
  /**
   * Eliminates the main variable using the subresultant remainder sequence.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The resultant and the sequence.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_prs_resultant`
   */
  dmpPrsResultant(f: P, g: P): [P | Expr, P[]] {
    const [r, R] = this.prsResultant(f, g);
    return [this.dropIn(r, 0), R];
  }
  /** The resultant in x_0 as an element without x_0 (zero when f or g is zero). */
  private collinsResultant(f: P, g: P): P {
    if (f.isZero || g.isZero) return this.zero;
    return this.fromExprPoly(resultant(f.asExpr(), g.asExpr(), this.gen0()));
  }
  /**
   * Computes the resultant in the main variable modulo a prime, using symmetric representatives for the
   * coefficients.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @param p - Prime modulus for computing the resultant.
   * @returns The resultant in the remaining generators, with coefficients reduced modulo the prime.
   * @throws DomainError when the coefficient domain is not the integers.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_zz_modular_resultant`
   */
  dmpZzModularResultant(f: P, g: P, p: IntLike): P | Expr {
    if (!isZZ(this.domain)) throw new DomainError(`modular resultants need ZZ, got ${this.domain.toString()}`);
    return this.dropIn(this.dupTrunc(this.collinsResultant(f, g), p), 0);
  }
  /**
   * Computes the resultant in the main variable over the integers.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The integer-domain resultant.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_zz_collins_resultant`
   */
  dmpZzCollinsResultant(f: P, g: P): P | Expr {
    return this.dropIn(this.collinsResultant(f, g), 0);
  }
  /**
   * Computes the resultant in the main variable over the rationals.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The rational-domain resultant.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_qq_collins_resultant`
   */
  dmpQqCollinsResultant(f: P, g: P): P | Expr {
    return this.dropIn(this.collinsResultant(f, g), 0);
  }

  /**
   * The content in x_0 as an element without x_0, with a nonnegative ground
   * leading coefficient (SymPy dmp_content); like SymPy, a polynomial of
   * degree 0 in x_0 is its own content up to the sign.
   */
  private contentOf(f: P): P {
    if (f.isZero) return f;
    const n = this.degIn(f, 0);
    let c = this.coeffIn(f, 0, n);
    for (let k = n - 1; k >= 0; k--) c = this.dmpGcd(c, this.coeffIn(f, 0, k));
    return groundIsNegative(this.domain, this.groundLC(c)) ? c.neg() : c;
  }
  /** The content in x_0 and the primitive part (SymPy dmp_primitive). */
  private primitiveOf(f: P): [P, P] {
    const c = this.contentOf(f);
    if (f.isZero || c.equals(this.one)) return [c, f];
    return [c, this.exquoBy(f, c)];
  }
  /**
   * Extracts the content in the principal generator, using ground content in the univariate case.
   *
   * @param f - Polynomial to operate on.
   * @returns The content in x_0, an element of R[1:].
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_content`
   */
  dmpContent(f: P): P | Expr {
    if (this.ngens === 1) return this.dupContent(f);
    return this.dropIn(this.contentOf(f), 0);
  }
  /**
   * Extracts the content in the main variable as a polynomial in the remaining generators.
   *
   * @param f - Polynomial to operate on.
   * @returns The content and primitive part.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_primitive`
   */
  dmpPrimitive(f: P): [P | Expr, P] {
    if (this.ngens === 1) return this.dupPrimitive(f);
    const [c, p] = this.primitiveOf(f);
    return [this.dropIn(c, 0), p];
  }

  /**
   * The gcd and the cofactors from the subresultant PRS (SymPy dmp_rr_prs_gcd
   * and dmp_ff_prs_gcd): the gcd of the contents in x_0 times the primitive
   * part of the last subresultant, with a positive leading coefficient over a
   * ring (field false) or monic over a field.
   */
  private prsGcd(f: P, g: P, field: boolean): [P, P, P] {
    // the trivial gcds of SymPy have the normalization of dmpInnerGcd
    if (f.isZero || g.isZero) return this.dmpInnerGcd(f, g);
    const K = this.domain;
    const R1 = this.dropRing(0);
    let h: P;
    if (!(R1 instanceof IPolys)) {
      if (field) h = this.dupMonic(last(this.dupSubresultants(f, g)));
      else {
        const [fc, F] = this.dupPrimitive(f);
        const [gc, G] = this.dupPrimitive(g);
        h = this.dupPrimitive(last(this.dupSubresultants(F, G)))[1];
        h = h.mulGround(K.mul(groundGcd(K, fc, gc), canonicalUnit(K, this.groundLC(h))));
      }
    } else {
      const [fc, F] = this.primitiveOf(f);
      const [gc, G] = this.primitiveOf(g);
      const c = this.embed(R1.prsGcd(this.toTail(R1, fc), this.toTail(R1, gc), field)[0]);
      h = this.primitiveOf(last(this.dmpSubresultants(F, G)))[1].mul(c);
      if (field) h = this.dmpGroundMonic(h);
      else if (groundIsNegative(K, this.groundLC(h))) h = h.neg();
    }
    return [h, this.exquoBy(f, h), this.exquoBy(g, h)];
  }
  /**
   * Uses subresultant remainders to find the GCD over a coefficient ring.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The GCD and both cofactors.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_rr_prs_gcd`
   */
  dupRrPrsGcd(f: P, g: P): [P, P, P] {
    return this.prsGcd(f, g, false);
  }
  /**
   * Uses subresultant remainders to find the GCD over a coefficient field.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The GCD and both cofactors.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_ff_prs_gcd`
   */
  dupFfPrsGcd(f: P, g: P): [P, P, P] {
    return this.prsGcd(f, g, true);
  }
  /**
   * Uses subresultant remainders to find the GCD over a coefficient ring.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The GCD and both cofactors.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_rr_prs_gcd`
   */
  dmpRrPrsGcd(f: P, g: P): [P, P, P] {
    return this.prsGcd(f, g, false);
  }
  /**
   * Uses subresultant remainders to find the GCD over a coefficient field.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The GCD and both cofactors.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_ff_prs_gcd`
   */
  dmpFfPrsGcd(f: P, g: P): [P, P, P] {
    return this.prsGcd(f, g, true);
  }
  /**
   * Computes an integer polynomial GCD and divides it out of each input.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The normalized GCD and both cofactors.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_zz_heu_gcd`
   */
  dupZzHeuGcd(f: P, g: P): [P, P, P] {
    return this.dmpInnerGcd(f, g);
  }
  /**
   * Computes the integer polynomial GCD by the heuristic GCD algorithm.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The GCD and both cofactors.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_zz_heu_gcd`
   */
  dmpZzHeuGcd(f: P, g: P): [P, P, P] {
    return this.dmpInnerGcd(f, g);
  }
  /**
   * Computes the monic rational polynomial GCD by the heuristic GCD algorithm.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The GCD and both cofactors.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_qq_heu_gcd`
   */
  dupQqHeuGcd(f: P, g: P): [P, P, P] {
    return this.dmpInnerGcd(f, g);
  }
  /**
   * Computes the monic rational polynomial GCD by the heuristic GCD algorithm.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @returns The GCD and both cofactors.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_qq_heu_gcd`
   */
  dmpQqHeuGcd(f: P, g: P): [P, P, P] {
    return this.dmpInnerGcd(f, g);
  }

  /**
   * Reduces the polynomial ratio to lowest terms, optionally separating its scalar factors.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @param include - Incorporate the scalar factors in the reduced numerator and denominator. If false, return the scalars separately.
   * @returns The reduced numerator and denominator.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_cancel`
   */
  dmpCancel(f: P, g: P, include?: true): [P, P];
  /**
   * Reduces the polynomial ratio to lowest terms, optionally separating its scalar factors.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @param include - Incorporate the scalar factors in the reduced numerator and denominator. If false, return the scalars separately.
   * @returns The scalar factors and reduced polynomial pair.
   * @see SymPy `sympy.polys.compatibility.IPolys.dmp_cancel`
   */
  dmpCancel(f: P, g: P, include: false): [Expr, Expr, P, P];
  dmpCancel(f: P, g: P, include = true): [P, P] | [Expr, Expr, P, P] {
    const K = this.domain;
    let cp = K.one;
    let cq = K.one;
    let p: P;
    let q: P;
    if (K.isField && hasAssocRing(K)) {
      const Z = this.withDomain(ZZ);
      const [cf, F] = this.dmpClearDenoms(f, true);
      const [cg, G] = this.dmpClearDenoms(g, true);
      const [, pz, qz] = Z.dmpInnerGcd(F, G);
      const c = groundGcd(ZZ, cf, cg);
      [cp, cq] = [groundExquo(ZZ, cg, c), groundExquo(ZZ, cf, c)];
      [p, q] = [Z.moveTo(pz, this), Z.moveTo(qz, this)];
    } else [, p, q] = this.dmpInnerGcd(f, g);
    const pNeg = groundIsNegative(K, this.groundLC(p));
    const qNeg = groundIsNegative(K, this.groundLC(q));
    if (pNeg !== qNeg) cp = K.neg(cp);
    if (pNeg) p = p.neg();
    if (qNeg) q = q.neg();
    if (!include) return [cp, cq, p, q];
    return [p.mulGround(cp), q.mulGround(cq)];
  }
  /**
   * Cancels common factors in the polynomial ratio.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @param include - Incorporate the scalar factors in the reduced numerator and denominator. If false, return the scalars separately.
   * @returns The reduced numerator and denominator.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_cancel`
   */
  dupCancel(f: P, g: P, include?: true): [P, P];
  /**
   * Cancels common factors in the polynomial ratio.
   *
   * @param f - Polynomial to operate on.
   * @param g - Second polynomial operand.
   * @param include - Incorporate the scalar factors in the reduced numerator and denominator. If false, return the scalars separately.
   * @returns The scalar factors and reduced polynomial pair.
   * @see SymPy `sympy.polys.compatibility.IPolys.dup_cancel`
   */
  dupCancel(f: P, g: P, include: false): [Expr, Expr, P, P];
  dupCancel(f: P, g: P, include = true): [P, P] | [Expr, Expr, P, P] {
    return include ? this.dmpCancel(f, g) : this.dmpCancel(f, g, false);
  }
}

/** The lexicographic comparison of exponent vectors. */
const lexCmp = (a: Monom, b: Monom): number => a.reduce((acc, e, i) => acc || e - at(b, i), 0);

/** f is an element of a polynomial ring (anything with a ring and term list). */
function isElement<P>(f: unknown): f is P {
  return typeof f === 'object' && f !== null && 'ring' in f && 'listterms' in f;
}

/** n*(n-1)*...*(n-m+1). */
function fallingDown(n: number, m: number): bigint {
  let r = 1n;
  for (let k = 0; k < m; k++) r *= BigInt(n - k);
  return r;
}

/** (n+1)*(n+2)*...*(n+m). */
function fallingFrom(n: number, m: number): bigint {
  let r = 1n;
  for (let k = 1; k <= m; k++) r *= BigInt(n + k);
  return r;
}

/** binomial(n, k) for small integers k <= n or k = n + 1 (zero). */
function binomialInt(n: number, k: number): bigint {
  let r = 1n;
  for (let i = 0; i < k; i++) r = (r * BigInt(n - i)) / BigInt(i + 1);
  return r;
}


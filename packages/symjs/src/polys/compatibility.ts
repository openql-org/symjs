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

import { ExactQuotientFailed, PolynomialError } from '../core/errors';
import { at, first } from '../core/guard';
import type { Expr, ExprLike } from '../core/nodes';
import { Float, Rational, S, Sym } from '../core/nodes';
import { gcd as igcd, iroot, lcm as ilcm } from '../core/numbers';
import { pow, splitCoeff, sympify } from '../core/ops';
import { asInt } from '../ntheory/intutil';
import type { IntLike } from '../ntheory/intutil';
import { PREC, floatString, precedence, str } from '../printing/str';
import { expand } from '../simplify/expand';
import { cancel, fraction } from '../simplify/rational';
import type { Domain } from './domains';
import { EX, FractionField, IntegerRing, PolynomialRing, QQ, RationalField, RealField, ZZ } from './domains';
import { mgcd } from './mpoly';
import { MultivariatePolynomialError } from './polyerrors';
import { Poly, discriminant, polyGcd, resultant } from './sympoly';

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

/** SymPy K.convert(a): a value as an element of K (CoercionFailed when it is not one). */
export function groundConvert(K: Domain, a: ExprLike): Expr {
  return K.fromSympy(sympify(a));
}

/** a == 0 in K. */
export const groundIsZero = (K: Domain, a: Expr): boolean => K.isZero(a) || (a instanceof Rational && a.isZero);

/** a == b for elements of K. */
export const groundEq = (a: Expr, b: Expr): boolean => a.key === b.key;

/** SymPy K.is_negative(a). */
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

/** SymPy K.quo(a, b): floor division in ZZ, the quotient in a field. */
export function groundQuo(K: Domain, a: Expr, b: Expr): Expr {
  if (groundIsZero(K, b)) throw new RangeError('division by zero');
  if (isZZ(K)) return Rational.of(floorDiv(rat(a).p, rat(b).p));
  if (K.isField) return K.quo(a, b);
  // a polynomial ring: the exact quotient when b divides a
  return groundExquo(K, a, b);
}

/** SymPy K.rem(a, b): the Python remainder in ZZ, zero in a field. */
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

/** SymPy K.exquo(a, b): the exact quotient (ExactQuotientFailed when b does not divide a). */
export function groundExquo(K: Domain, a: Expr, b: Expr): Expr {
  if (groundIsZero(K, b)) throw new RangeError('division by zero');
  if (isZZ(K)) {
    const x = rat(a).p;
    const y = rat(b).p;
    if (x % y !== 0n) throw new ExactQuotientFailed(`${str(b)} does not divide ${str(a)} in ZZ`);
    return Rational.of(x / y);
  }
  if (K.isField) return K.quo(a, b);
  try {
    return K.fromSympy(cancel(K.quo(a, b)));
  } catch {
    throw new ExactQuotientFailed(`${str(b)} does not divide ${str(a)} in ${K.toString()}`);
  }
}

/** SymPy K.abs(a). */
export const groundAbs = (K: Domain, a: Expr): Expr => (groundIsNegative(K, a) ? K.neg(a) : a);

/** SymPy K.gcd(a, b) (ZZ: nonnegative; QQ: gcd of numerators over lcm of denominators; other fields: one). */
export function groundGcd(K: Domain, a: Expr, b: Expr): Expr {
  if (isZZ(K)) return Rational.of(igcd(rat(a).p, rat(b).p));
  if (K instanceof RationalField) {
    const x = rat(a);
    const y = rat(b);
    return Rational.of(igcd(x.p, y.p), ilcm(x.q, y.q));
  }
  if (K instanceof PolynomialRing) return K.canon(polyGcd(a, b));
  return K.one;
}

/** SymPy K.lcm(a, b). */
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

/** SymPy K.numer(a) / K.denom(a) of a QQ element. */
export const groundDenom = (a: Expr): Expr => Rational.of(rat(a).q);

/** a**n in K. */
export const groundPow = (K: Domain, a: Expr, n: number): Expr => K.canon(pow(a, n));

/** SymPy K.get_ring(): the ring of integers of QQ (DomainError otherwise). */
export function groundRing(K: Domain): Domain {
  if (K instanceof RationalField) return ZZ;
  return K;
}

/** The domain has an associated ring (SymPy has_assoc_Ring). */
export const hasAssocRing = (K: Domain): boolean => K instanceof RationalField || K instanceof IntegerRing;

/** SymPy K.canonical_unit(a): -1 for a negative element, else 1. */
export const canonicalUnit = (K: Domain, a: Expr): Expr => (groundIsNegative(K, a) ? K.neg(K.one) : K.one);

/** SymPy K.is_unit(a). */
export function groundIsUnit(K: Domain, a: Expr): boolean {
  if (K.isField) return !groundIsZero(K, a);
  return groundEq(a, K.one) || groundEq(a, K.neg(K.one));
}

/** The printed form of an element of K (SymPy printer._print of a domain element). */
export function groundStr(K: Domain, a: Expr): string {
  if (K instanceof RealField && a instanceof Float) return floatString(a, true);
  if (K === EX) return `EX(${str(a)})`;
  return str(a);
}

/** The printing precedence of an element of K (SymPy precedence of a domain element). */
export function groundPrecedence(K: Domain, a: Expr): number {
  if (K === EX) return PREC.ATOM;
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
 * The compatibility methods of a polynomial ring (SymPy IPolys): `R.dup_*`
 * work on univariate polynomials, `R.dmp_*` on multivariate ones read as
 * polynomials in the first generator.
 */
export abstract class IPolys<P extends CompatElement<P>> {
  abstract readonly ngens: number;
  abstract readonly domain: Domain;
  abstract readonly symbols: readonly Expr[];
  abstract readonly gens: readonly P[];
  abstract get zero(): P;
  abstract get one(): P;
  /** The constant polynomial c. */
  abstract groundNew(c: ExprLike): P;
  /** A polynomial from its terms (zero coefficients are dropped, repeated monomials added). */
  abstract fromTerms(terms: Iterable<readonly [Monom, ExprLike]>): P;
  /** The ring with the generators start..end (SymPy R[start:end]); the domain when none remain. */
  abstract slice(start: number, end?: number): IPolys<P> | Domain;
  /** The ring over another domain (SymPy R.clone(domain=K)). */
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

  /** f + c*x**i (SymPy dup_add_term). */
  dupAddTerm(f: P, c: ExprLike, i: IntLike): P {
    return f.add(this.groundNew(c).mul(this.genPow(0, intArg(i))));
  }
  /** f + c*x_0**i with c a polynomial in the other generators (SymPy dmp_add_term). */
  dmpAddTerm(f: P, c: P | ExprLike, i: IntLike): P {
    return f.add(this.wrap(c).mul(this.genPow(0, intArg(i))));
  }
  /** f - c*x**i (SymPy dup_sub_term). */
  dupSubTerm(f: P, c: ExprLike, i: IntLike): P {
    return f.sub(this.groundNew(c).mul(this.genPow(0, intArg(i))));
  }
  /** f - c*x_0**i (SymPy dmp_sub_term). */
  dmpSubTerm(f: P, c: P | ExprLike, i: IntLike): P {
    return f.sub(this.wrap(c).mul(this.genPow(0, intArg(i))));
  }
  /** f*c*x**i (SymPy dup_mul_term). */
  dupMulTerm(f: P, c: ExprLike, i: IntLike): P {
    return f.mul(this.groundNew(c).mul(this.genPow(0, intArg(i))));
  }
  /** f*c*x_0**i (SymPy dmp_mul_term). */
  dmpMulTerm(f: P, c: P | ExprLike, i: IntLike): P {
    return f.mul(this.wrap(c).mul(this.genPow(0, intArg(i))));
  }
  /** f + c (SymPy dup_add_ground). */
  dupAddGround(f: P, c: ExprLike): P {
    return f.add(this.groundNew(c));
  }
  /** f + c (SymPy dmp_add_ground). */
  dmpAddGround(f: P, c: ExprLike): P {
    return f.add(this.groundNew(c));
  }
  /** f - c (SymPy dup_sub_ground). */
  dupSubGround(f: P, c: ExprLike): P {
    return f.sub(this.groundNew(c));
  }
  /** f - c (SymPy dmp_sub_ground). */
  dmpSubGround(f: P, c: ExprLike): P {
    return f.sub(this.groundNew(c));
  }
  /** c*f (SymPy dup_mul_ground). */
  dupMulGround(f: P, c: ExprLike): P {
    return f.mulGround(groundConvert(this.domain, c));
  }
  /** c*f (SymPy dmp_mul_ground). */
  dmpMulGround(f: P, c: ExprLike): P {
    return this.dupMulGround(f, c);
  }
  /** The quotients of the coefficients by c (SymPy dup_quo_ground: floor division in ZZ). */
  dupQuoGround(f: P, c: ExprLike): P {
    const K = this.domain;
    const d = groundConvert(K, c);
    return this.mapCoeffs(f, (a) => groundQuo(K, a, d));
  }
  /** The quotients of the coefficients by c (SymPy dmp_quo_ground). */
  dmpQuoGround(f: P, c: ExprLike): P {
    return this.dupQuoGround(f, c);
  }
  /** The exact quotients of the coefficients by c (SymPy dup_exquo_ground). */
  dupExquoGround(f: P, c: ExprLike): P {
    const K = this.domain;
    const d = groundConvert(K, c);
    return this.mapCoeffs(f, (a) => groundExquo(K, a, d));
  }
  /** The exact quotients of the coefficients by c (SymPy dmp_exquo_ground). */
  dmpExquoGround(f: P, c: ExprLike): P {
    return this.dupExquoGround(f, c);
  }
  /** f*x**n (SymPy dup_lshift). */
  dupLshift(f: P, n: IntLike): P {
    return f.mul(this.genPow(0, intArg(n)));
  }
  /** f/x**n with the terms of lower degree dropped (SymPy dup_rshift). */
  dupRshift(f: P, n: IntLike): P {
    const k = intArg(n);
    return this.fromTerms(f.listterms().filter(([m]) => first(m) >= k).map(([m, c]) => [[first(m) - k, ...m.slice(1)], c] as const));
  }
  /** The absolute values of the coefficients (SymPy dup_abs). */
  dupAbs(f: P): P {
    return this.mapCoeffs(f, (c) => groundAbs(this.domain, c));
  }
  /** The absolute values of the coefficients (SymPy dmp_abs). */
  dmpAbs(f: P): P {
    return this.dupAbs(f);
  }
  /** -f (SymPy dup_neg). */
  dupNeg(f: P): P {
    return f.neg();
  }
  /** -f (SymPy dmp_neg). */
  dmpNeg(f: P): P {
    return f.neg();
  }
  /** f + g (SymPy dup_add). */
  dupAdd(f: P, g: P): P {
    return f.add(g);
  }
  /** f + g (SymPy dmp_add). */
  dmpAdd(f: P, g: P): P {
    return f.add(g);
  }
  /** f - g (SymPy dup_sub). */
  dupSub(f: P, g: P): P {
    return f.sub(g);
  }
  /** f - g (SymPy dmp_sub). */
  dmpSub(f: P, g: P): P {
    return f.sub(g);
  }
  /** f + g*h (SymPy dup_add_mul). */
  dupAddMul(f: P, g: P, h: P): P {
    return f.add(g.mul(h));
  }
  /** f + g*h (SymPy dmp_add_mul). */
  dmpAddMul(f: P, g: P, h: P): P {
    return f.add(g.mul(h));
  }
  /** f - g*h (SymPy dup_sub_mul). */
  dupSubMul(f: P, g: P, h: P): P {
    return f.sub(g.mul(h));
  }
  /** f - g*h (SymPy dmp_sub_mul). */
  dmpSubMul(f: P, g: P, h: P): P {
    return f.sub(g.mul(h));
  }
  /** f*g (SymPy dup_mul). */
  dupMul(f: P, g: P): P {
    return f.mul(g);
  }
  /** f*g (SymPy dmp_mul). */
  dmpMul(f: P, g: P): P {
    return f.mul(g);
  }
  /** f**2 (SymPy dup_sqr). */
  dupSqr(f: P): P {
    return f.mul(f);
  }
  /** f**2 (SymPy dmp_sqr). */
  dmpSqr(f: P): P {
    return f.mul(f);
  }
  /** f**n (SymPy dup_pow). */
  dupPow(f: P, n: IntLike): P {
    return this.dmpPow(f, n);
  }
  /** f**n (SymPy dmp_pow). */
  dmpPow(f: P, n: IntLike): P {
    const k = intArg(n);
    if (k < 0) throw new RangeError("can't raise polynomial to a negative power");
    return k === 0 || f.isZero ? (k === 0 ? this.one : f) : f.pow(k);
  }
  /** The product of the polynomials (SymPy dup_expand). */
  dupExpand(polys: readonly P[]): P {
    return polys.reduce((a, b) => a.mul(b), this.one);
  }
  /** The product of the polynomials (SymPy dmp_expand). */
  dmpExpand(polys: readonly P[]): P {
    return this.dupExpand(polys);
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
  /** Pseudo-division (SymPy dup_pdiv). */
  dupPdiv(f: P, g: P): [P, P] {
    return this.pdivIn(f, g, true);
  }
  /** Pseudo-remainder (SymPy dup_prem). */
  dupPrem(f: P, g: P): P {
    return this.pdivIn(f, g, false)[1];
  }
  /** Pseudo-quotient (SymPy dup_pquo). */
  dupPquo(f: P, g: P): P {
    return this.pdivIn(f, g, true)[0];
  }
  /** Exact pseudo-quotient (SymPy dup_pexquo). */
  dupPexquo(f: P, g: P): P {
    const [q, r] = this.pdivIn(f, g, true);
    if (!r.isZero) throw new ExactQuotientFailed(`${str(g.asExpr())} does not divide ${str(f.asExpr())}`);
    return q;
  }
  /** Pseudo-division in x_0 (SymPy dmp_pdiv). */
  dmpPdiv(f: P, g: P): [P, P] {
    return this.dupPdiv(f, g);
  }
  /** Pseudo-remainder in x_0 (SymPy dmp_prem). */
  dmpPrem(f: P, g: P): P {
    return this.dupPrem(f, g);
  }
  /** Pseudo-quotient in x_0 (SymPy dmp_pquo). */
  dmpPquo(f: P, g: P): P {
    return this.dupPquo(f, g);
  }
  /** Exact pseudo-quotient in x_0 (SymPy dmp_pexquo). */
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
  /** Division with remainder over a ring (SymPy dup_rr_div). */
  dupRrDiv(f: P, g: P): [P, P] {
    return this.divIn(f, g, 0);
  }
  /** Division with remainder over a ring (SymPy dmp_rr_div). */
  dmpRrDiv(f: P, g: P): [P, P] {
    return this.divIn(f, g, 0);
  }
  /** Division with remainder over a field (SymPy dup_ff_div). */
  dupFfDiv(f: P, g: P): [P, P] {
    return this.divIn(f, g, 0);
  }
  /** Division with remainder over a field (SymPy dmp_ff_div). */
  dmpFfDiv(f: P, g: P): [P, P] {
    return this.divIn(f, g, 0);
  }
  /** Division with remainder (SymPy dup_div). */
  dupDiv(f: P, g: P): [P, P] {
    return this.divIn(f, g, 0);
  }
  /** The remainder (SymPy dup_rem). */
  dupRem(f: P, g: P): P {
    return this.divIn(f, g, 0)[1];
  }
  /** The quotient (SymPy dup_quo). */
  dupQuo(f: P, g: P): P {
    return this.divIn(f, g, 0)[0];
  }
  /** The exact quotient (SymPy dup_exquo). */
  dupExquo(f: P, g: P): P {
    const [q, r] = this.divIn(f, g, 0);
    if (!r.isZero) throw new ExactQuotientFailed(`${str(g.asExpr())} does not divide ${str(f.asExpr())}`);
    return q;
  }
  /** Division with remainder (SymPy dmp_div). */
  dmpDiv(f: P, g: P): [P, P] {
    return this.divIn(f, g, 0);
  }
  /** The remainder (SymPy dmp_rem). */
  dmpRem(f: P, g: P): P {
    return this.divIn(f, g, 0)[1];
  }
  /** The quotient (SymPy dmp_quo). */
  dmpQuo(f: P, g: P): P {
    return this.divIn(f, g, 0)[0];
  }
  /** The exact quotient (SymPy dmp_exquo). */
  dmpExquo(f: P, g: P): P {
    return this.dupExquo(f, g);
  }

  /** The largest absolute value of a coefficient (SymPy dup_max_norm). */
  dupMaxNorm(f: P): Expr {
    const K = this.domain;
    const cs = f.listterms().map(([, c]) => rat(groundAbs(K, c)));
    return cs.reduce((a, b) => (a.value >= b.value ? a : b), Rational.of(0));
  }
  /** The largest absolute value of a coefficient (SymPy dmp_max_norm). */
  dmpMaxNorm(f: P): Expr {
    return this.dupMaxNorm(f);
  }
  /** The sum of the absolute values of the coefficients (SymPy dup_l1_norm). */
  dupL1Norm(f: P): Expr {
    const K = this.domain;
    return f.listterms().reduce((s, [, c]) => K.add(s, groundAbs(K, c)), K.zero);
  }
  /** The sum of the absolute values of the coefficients (SymPy dmp_l1_norm). */
  dmpL1Norm(f: P): Expr {
    return this.dupL1Norm(f);
  }
  /** The sum of the squares of the coefficients (SymPy dup_l2_norm_squared). */
  dupL2NormSquared(f: P): Expr {
    const K = this.domain;
    return f.listterms().reduce((s, [, c]) => K.add(s, K.mul(c, c)), K.zero);
  }
  /** The sum of the squares of the coefficients (SymPy dmp_l2_norm_squared). */
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
  /** The m-th integral (SymPy dup_integrate). */
  dupIntegrate(f: P, m: IntLike): P {
    return this.integrateIn(f, intArg(m), 0);
  }
  /** The m-th integral in x_0 (SymPy dmp_integrate). */
  dmpIntegrate(f: P, m: IntLike): P {
    return this.integrateIn(f, intArg(m), 0);
  }
  /** The m-th integral in x_j (SymPy dmp_integrate_in). */
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
  /** The m-th derivative (SymPy dup_diff). */
  dupDiff(f: P, m: IntLike): P {
    return this.diffIn(f, intArg(m), 0);
  }
  /** The m-th derivative in x_0 (SymPy dmp_diff). */
  dmpDiff(f: P, m: IntLike): P {
    return this.diffIn(f, intArg(m), 0);
  }
  /** The m-th derivative in x_j (SymPy dmp_diff_in). */
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

  /** f(a) (SymPy dup_eval). */
  dupEval(f: P, a: ExprLike): Expr {
    return this.groundOf(this.evalIn(f, groundConvert(this.domain, a), 0));
  }
  /** f(a, x_1, ...) in R[1:] (SymPy dmp_eval). */
  dmpEval(f: P, a: ExprLike): P | Expr {
    return this.dropIn(this.evalIn(f, groundConvert(this.domain, a), 0), 0);
  }
  /** f with x_j = a in the ring without x_j (SymPy dmp_eval_in). */
  dmpEvalIn(f: P, a: ExprLike, j: IntLike): P | Expr {
    const k = this.checkLevel(j);
    return this.dropIn(this.evalIn(f, groundConvert(this.domain, a), k), k);
  }
  /** The m-th derivative in x_j at x_j = a (SymPy dmp_diff_eval_in). */
  dmpDiffEvalIn(f: P, m: IntLike, a: ExprLike, j: IntLike): P | Expr {
    const k = this.checkLevel(j);
    return this.dropIn(this.evalIn(this.diffIn(f, intArg(m), k), groundConvert(this.domain, a), k), k);
  }
  /** f with its last generators set to the values A (SymPy dmp_eval_tail). */
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

  /** The coefficients reduced modulo p into the symmetric range in ZZ (SymPy dup_trunc). */
  dupTrunc(f: P, p: ExprLike): P {
    const K = this.domain;
    const q = groundConvert(K, p);
    return this.mapCoeffs(f, (c) => {
      const r = groundRem(K, c, q);
      return isZZ(K) && rat(r).p > floorDiv(rat(q).p, 2n) ? K.sub(r, q) : r;
    });
  }
  /** The coefficients of x_0 reduced modulo the polynomial g of R[1:] (SymPy dmp_trunc). */
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
  /** The ground coefficients reduced modulo p (SymPy dmp_ground_trunc). */
  dmpGroundTrunc(f: P, p: ExprLike): P {
    return this.dupTrunc(f, p);
  }
  /** f divided by its leading coefficient (SymPy dup_monic). */
  dupMonic(f: P): P {
    if (f.isZero) return f;
    const lc = f.LC;
    return groundEq(lc, this.domain.one) ? f : this.dupExquoGround(f, lc);
  }
  /** f divided by its ground leading coefficient (SymPy dmp_ground_monic). */
  dmpGroundMonic(f: P): P {
    return this.dupMonic(f);
  }
  /** The gcd of the coefficients (SymPy dup_content). */
  dupContent(f: P): Expr {
    const K = this.domain;
    return f.listterms().reduce((g, [, c]) => groundGcd(K, g, c), K.zero);
  }
  /** The gcd of the ground coefficients (SymPy dmp_ground_content). */
  dmpGroundContent(f: P): Expr {
    return this.dupContent(f);
  }
  /** The content and the primitive part (SymPy dup_primitive). */
  dupPrimitive(f: P): [Expr, P] {
    const K = this.domain;
    const cont = this.dupContent(f);
    if (f.isZero || groundEq(cont, K.one)) return [cont, f];
    return [cont, this.dupQuoGround(f, cont)];
  }
  /** The ground content and the primitive part (SymPy dmp_ground_primitive). */
  dmpGroundPrimitive(f: P): [Expr, P] {
    return this.dupPrimitive(f);
  }
  /** The common content of f and g and their quotients by it (SymPy dup_extract). */
  dupExtract(f: P, g: P): [Expr, P, P] {
    const K = this.domain;
    const c = groundGcd(K, this.dupContent(f), this.dupContent(g));
    if (groundEq(c, K.one)) return [c, f, g];
    return [c, this.dupQuoGround(f, c), this.dupQuoGround(g, c)];
  }
  /** The common ground content of f and g and their quotients by it (SymPy dmp_ground_extract). */
  dmpGroundExtract(f: P, g: P): [Expr, P, P] {
    return this.dupExtract(f, g);
  }

  /** The real and imaginary parts of f(x + I*y) in the first two generators (SymPy dup_real_imag). */
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
  /** f(-x) (SymPy dup_mirror). */
  dupMirror(f: P): P {
    return this.mapCoeffs(f, (c, m) => (first(m) % 2 ? this.domain.neg(c) : c));
  }
  /** f(a*x) (SymPy dup_scale). */
  dupScale(f: P, a: ExprLike): P {
    const K = this.domain;
    const b = groundConvert(K, a);
    return this.mapCoeffs(f, (c, m) => K.mul(c, groundPow(K, b, first(m))));
  }
  /** f(x + a) (SymPy dup_shift). */
  dupShift(f: P, a: ExprLike): P {
    return this.composeIn(f, [[0, at(this.gens, 0).add(this.groundNew(a))]]);
  }
  /** f(x_0 + a_0, x_1 + a_1, ...) (SymPy dmp_shift). */
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
  /** q**n * f(p/q) with n the degree of f (SymPy dup_transform). */
  dupTransform(f: P, p: P, q: P): P {
    if (f.isZero) return f;
    const n = this.degIn(f, 0);
    let out = this.zero;
    for (const [m, c] of f.listterms()) out = out.add(p.pow(first(m)).mul(q.pow(n - first(m))).mulGround(c));
    return out;
  }
  /** f(g) (SymPy dup_compose). */
  dupCompose(f: P, g: P): P {
    return this.composeIn(f, [[0, g]]);
  }
  /** f(g, x_1, ...) (SymPy dmp_compose). */
  dmpCompose(f: P, g: P): P {
    return this.composeIn(f, [[0, g]]);
  }
  /** A functional decomposition f = f_1(f_2(...)) (SymPy dup_decompose). */
  dupDecompose(f: P): P[] {
    return this.toPoly(f).decompose().map((p) => this.fromPoly(p));
  }
  /** The number of sign changes of the coefficients (SymPy dup_sign_variations). */
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
  /** The lcm of the denominators and f multiplied by it, over its ring of integers when convert is true (SymPy dup_clear_denoms). */
  dupClearDenoms(f: P, convert = false): [Expr, P] {
    const K = this.domain;
    if (!(K instanceof RationalField)) return [K.one, f];
    const common = f.listterms().reduce((l, [, c]) => groundLcm(ZZ, l, groundDenom(c)), ZZ.one);
    const g = groundEq(common, K.one) ? f : f.mulGround(common);
    return [common, convert ? this.moveTo(g, this.withDomain(ZZ)) : g];
  }
  /** The lcm of the denominators and f multiplied by it (SymPy dmp_clear_denoms). */
  dmpClearDenoms(f: P, convert = false): [Expr, P] {
    return this.dupClearDenoms(f, convert);
  }
  /** The power series reversion of f modulo x**n (SymPy dup_revert). */
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
    return Poly.from(f.asExpr(), this.symbols, { domain: this.domain.toString() });
  }
  /** A Poly over the generators of the ring as an element. */
  protected fromPoly(p: Poly): P {
    return this.fromTerms(p.terms());
  }
  /** An expression polynomial in the generators of the ring as an element. */
  protected fromExprPoly(e: Expr): P {
    return this.fromPoly(Poly.from(e, this.symbols, { domain: this.domain.toString() }));
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
    // mgcd normalizes the leading coefficient to be positive
    const h = this.fromExprPoly(mgcd(f.asExpr(), g.asExpr(), this.symbols));
    return K.isField ? h.mulGround(K.quo(K.one, this.groundLC(h))) : h;
  }

  /** The gcd and the cofactors (SymPy dmp_inner_gcd). */
  dmpInnerGcd(f: P, g: P): [P, P, P] {
    if (f.isZero && g.isZero) return [this.zero, this.zero, this.zero];
    const h = this.gcdOf(f, g);
    return [h, this.exquoBy(f, h), this.exquoBy(g, h)];
  }
  /** f/h for a divisor h of f (a gcd or a content). */
  private exquoBy(f: P, h: P): P {
    return this.divIn(f, h, 0)[0];
  }
  /** The gcd and the cofactors (SymPy dup_inner_gcd). */
  dupInnerGcd(f: P, g: P): [P, P, P] {
    return this.dmpInnerGcd(f, g);
  }
  /** The gcd (SymPy dmp_gcd). */
  dmpGcd(f: P, g: P): P {
    return this.dmpInnerGcd(f, g)[0];
  }
  /** The gcd (SymPy dup_gcd). */
  dupGcd(f: P, g: P): P {
    return this.dmpGcd(f, g);
  }
  /** The lcm (SymPy dmp_lcm): monic over a field, with the lcm of the contents over a ring. */
  dmpLcm(f: P, g: P): P {
    const K = this.domain;
    if (f.isZero || g.isZero) return this.zero;
    if (K.isField) {
      const h = this.exquoBy(f.mul(g), this.dmpGcd(f, g));
      return h.mulGround(K.quo(K.one, this.groundLC(h)));
    }
    const [fc, f1] = this.dmpGroundPrimitive(f);
    const [gc, g1] = this.dmpGroundPrimitive(g);
    return this.exquoBy(f1.mul(g1), this.dmpGcd(f1, g1)).mulGround(groundLcm(K, fc, gc));
  }
  /** The lcm (SymPy dup_lcm). */
  dupLcm(f: P, g: P): P {
    return this.dmpLcm(f, g);
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

  /** f is square-free (SymPy dup_sqf_p). */
  dupSqfP(f: P): boolean {
    return this.dmpSqfP(f);
  }
  /** f is square-free (SymPy dmp_sqf_p). */
  dmpSqfP(f: P): boolean {
    if (f.isZero) return true;
    for (let i = 0; i < this.ngens; i++) {
      const fp = this.diffIn(f, 1, i);
      if (fp.isZero) continue;
      if (this.degIn(this.dmpGcd(f, fp), i) > 0) return false;
    }
    return true;
  }
  /** The square-free part (SymPy dup_sqf_part). */
  dupSqfPart(f: P): P {
    return this.dmpSqfPart(f);
  }
  /** The square-free part (SymPy dmp_sqf_part). */
  dmpSqfPart(f0: P): P {
    const K = this.domain;
    if (f0.isZero) return f0;
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
  /** The square-free decomposition (coefficient, [(factor, multiplicity)]) (SymPy dup_sqf_list). */
  dupSqfList(f: P, all = false): [Expr, [P, number][]] {
    return this.sqfListIn(f, 0, all);
  }
  /** The square-free decomposition (SymPy dmp_sqf_list). */
  dmpSqfList(f: P, all = false): [Expr, [P, number][]] {
    return this.sqfListIn(f, 0, all);
  }
  /** The square-free decomposition with the coefficient in the first factor (SymPy dup_sqf_list_include). */
  dupSqfListInclude(f: P, all = false): [P, number][] {
    const [c, fs] = this.sqfListIn(f, 0, all);
    const head = fs[0];
    if (head?.[1] === 1) return [[head[0].mulGround(c), 1], ...fs.slice(1)];
    return [[this.groundNew(c), 1], ...fs];
  }
  /** The square-free decomposition with the coefficient in the first factor (SymPy dmp_sqf_list_include). */
  dmpSqfListInclude(f: P, all = false): [P, number][] {
    return this.dupSqfListInclude(f, all);
  }
  /** The greatest factorial factorization (SymPy dup_gff_list). */
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
  /** The greatest factorial factorization (SymPy dmp_gff_list). */
  dmpGffList(f: P): [P, number][] {
    if (this.ngens > 1) throw new MultivariatePolynomialError('greatest factorial factorization of a multivariate polynomial');
    return this.dupGffList(f);
  }

  /** The factorization (content, [(factor, multiplicity)]) (SymPy dmp_factor_list). */
  dmpFactorList(f: P): [Expr, [P, number][]] {
    const [c, fs] = this.toPoly(f).factorList();
    return [groundConvert(this.domain, c), fs.map(([p, k]) => [this.fromPoly(p), k] as [P, number])];
  }
  /** The factorization (SymPy dup_factor_list). */
  dupFactorList(f: P): [Expr, [P, number][]] {
    return this.dmpFactorList(f);
  }
  /** The factorization over ZZ (SymPy dup_zz_factor). */
  dupZzFactor(f: P): [Expr, [P, number][]] {
    return this.dmpFactorList(f);
  }
  /** The factorization over ZZ (SymPy dmp_zz_factor). */
  dmpZzFactor(f: P): [Expr, [P, number][]] {
    return this.dmpFactorList(f);
  }
  /** f is irreducible (SymPy dmp_irreducible_p). */
  dmpIrreducibleP(f: P): boolean {
    const [, fs] = this.dmpFactorList(f);
    return fs.length === 1 && at(first(fs), 1) === 1;
  }
  /** The Knuth-Cohen variant of the Mignotte bound (SymPy dup_zz_mignotte_bound). */
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
  /** f is a cyclotomic polynomial (SymPy dup_cyclotomic_p). */
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

  /** The resultant in x_0 (SymPy dmp_resultant): a polynomial of R[1:], or a ground element for a univariate ring. */
  dmpResultant(f: P, g: P): P | Expr {
    return this.dropIn(this.fromExprPoly(resultant(f.asExpr(), g.asExpr(), this.gen0())), 0);
  }
  /** The resultant (SymPy dup_resultant). */
  dupResultant(f: P, g: P): Expr {
    return this.groundOf(this.fromExprPoly(resultant(f.asExpr(), g.asExpr(), this.gen0())));
  }
  /** The discriminant in x_0 (SymPy dmp_discriminant). */
  dmpDiscriminant(f: P): P | Expr {
    return this.dropIn(this.fromExprPoly(discriminant(f.asExpr(), this.gen0())), 0);
  }
  /** The discriminant (SymPy dup_discriminant). */
  dupDiscriminant(f: P): Expr {
    return this.groundOf(this.fromExprPoly(discriminant(f.asExpr(), this.gen0())));
  }
  private gen0(): Sym {
    const x = first(this.symbols);
    if (!(x instanceof Sym)) throw new PolynomialError('the first generator must be a symbol');
    return x;
  }
  /** The extended Euclidean algorithm (s, t, h) with s*f + t*g = h (SymPy dup_gcdex). */
  dupGcdex(f: P, g: P): [P, P, P] {
    const [s, t, h] = this.toPoly(f).gcdex(this.toPoly(g));
    return [this.fromPoly(s), this.fromPoly(t), this.fromPoly(h)];
  }
  /** The half extended Euclidean algorithm (s, h) with s*f = h mod g (SymPy dup_half_gcdex). */
  dupHalfGcdex(f: P, g: P): [P, P] {
    const [s, , h] = this.dupGcdex(f, g);
    return [s, h];
  }
  /** The inverse of f modulo g (SymPy dup_invert). */
  dupInvert(f: P, g: P): P {
    return this.fromPoly(this.toPoly(f).invert(this.toPoly(g)));
  }
  /** The Sturm sequence (SymPy dup_sturm). */
  dupSturm(f: P): P[] {
    return this.toPoly(f).sturm().map((p) => this.fromPoly(p));
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


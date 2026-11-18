// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (polys/domains/*.py, polys/polyclasses.py: DMP,
// DMF; polys/euclidtools.py: gcd, lcm and cancel of dense univariate
// polynomials), Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause
// License (see LICENSE).

/**
 * @file Ground domains (SymPy ZZ, QQ, RR, ZZ[a, ...], QQ(a, ...)) and the
 * univariate "old" polynomial rings over them with their fraction fields
 * (SymPy `K.old_poly_ring(x)`, `GlobalPolynomialRing`, DMP and DMF), as the
 * holonomic module uses them. Domain elements are expressions in a
 * canonical form: rationals, floats or (for polynomial rings and fraction
 * fields of symbols) expanded or cancelled expressions.
 */

import { ExactQuotientFailed, NotImplementedError } from '../core/errors';
import { at, defined, expectType, first } from '../core/guard';
import type { ExprLike } from '../core/nodes';
import { Add, Expr, Float, Mul, Pow, Rational, S, Sym } from '../core/nodes';
import { add, mul, neg, pow, sympify } from '../core/ops';
import { freeSymbols } from '../core/traverse';
import { gcd as igcd, lcm as ilcm } from '../core/numbers';
import { limitDenominator } from '../core/numberutils';
import { NoMatch, isNoMatch, type NoMatchResult } from '../core/truth';
import { sqrtrem } from '../ntheory/intutil';
import { isqrt, div as mpfDiv, fromRational as mpfFromRational, toRational as mpfToRational } from '../numeric/mpf';
import { evalfPrec } from '../numeric/evalf';
import { str } from '../printing/str';
import { expand, expandMul } from '../simplify/expand';
import { cancel, fraction, together } from '../simplify/rational';
import { polyCoefficients } from './poly';
import { RealElement, ComplexElement, MPContext } from './domains/mpelements';
import { PythonMPQ } from './domains/pythonrational';
import { GeneratorsError, UnificationFailed } from './polyerrors';
import type { FreeModule } from './agca/modules';
import type { ModuleImplementedIdeal } from './agca/ideals';
import type { PolynomialRingBase } from './domains/oldpolynomialring';
import type { QuotientRing } from './domains/quotientring';
import type { IntLike } from '../ntheory/intutil';

/** A value cannot be converted to an element of a domain (SymPy CoercionFailed). */
export class CoercionFailed extends TypeError {}

type Ground = 'ZZ' | 'QQ' | 'RR' | 'EX';


/** RR.to_rational: the float as a rational with a bounded denominator (mpmath max_denom at 53 bits). */
const RR_MAX_DENOM = 45035996273704n;
function floatToRational(f: Float): Rational {
  const [p, q] = mpfToRational(f.mpf);
  const r = Rational.of(p, q);
  if (q <= RR_MAX_DENOM) return r;
  // SymPy to_rational keeps the exact value when a bound of the approximation is 0 (a tiny float)
  const [p0, q0, p1, q1] = convergents(p, q, RR_MAX_DENOM);
  return p1 === 0n || p0 + ((RR_MAX_DENOM - q0) / q1) * p1 === 0n ? r : limitDenominator(r, RR_MAX_DENOM);
}

/** The last two continued fraction convergents p0/q0, p1/q1 of p/q with denominators at most maxDen. */
function convergents(p: bigint, q: bigint, maxDen: bigint): [bigint, bigint, bigint, bigint] {
  let [p0, q0, p1, q1, n, d] = [0n, 1n, 1n, 0n, p, q];
  for (;;) {
    const a = n / d - (n < 0n && n % d !== 0n ? 1n : 0n);
    const q2 = q0 + a * q1;
    if (q2 > maxDen) return [p0, q0, p1, q1];
    [p0, q0, p1, q1, n, d] = [p1, q1, p0 + a * p1, q2, d, n - a * d];
  }
}

/**
 * A SymPy ground value (a JavaScript number or bigint, a PythonMPQ or a
 * rational/float expression) as an expression; other values are returned
 * unchanged for the caller to reject.
 */
export function groundToSympy(a: unknown): unknown {
  if (typeof a === 'bigint') return Rational.of(a);
  if (a instanceof DMP || a instanceof DMF) return a.toSympy();
  if (isPolynomialElement(a)) return a.asExpr();
  if (typeof a === 'number') return Number.isInteger(a) ? Rational.of(BigInt(a)) : sympify(a);
  if (a instanceof RealElement || a instanceof ComplexElement) return a.toSympy();
  if (a instanceof PythonMPQ) return Rational.of(a.numerator, a.denominator);
  return a;
}

/** A sparse polynomial or rational function (SymPy PolyElement, FracElement): an element of its ring or field. */
function isPolynomialElement(a: unknown): a is { asExpr(): Expr } {
  return typeof a === 'object' && a !== null && ('ring' in a || 'field' in a) && 'asExpr' in a && typeof a.asExpr === 'function';
}

/** A rational ground value as [p, q] (numbers, bigints, PythonMPQ, Rational, finite Float); undefined otherwise. */
export function groundRational(a: unknown): [bigint, bigint] | undefined {
  const e = groundToSympy(a);
  if (e instanceof Rational) return [e.p, e.q];
  if (e instanceof Float) return mpfToRational(e.mpf);
  return undefined;
}

/** The sign of a rational ground value (numbers, bigints, PythonMPQ, Rational, Float); undefined for other values. */
function groundSign(a: unknown): number | undefined {
  const r = groundRational(a);
  return r === undefined ? undefined : r[0] === 0n ? 0 : r[0] < 0n ? -1 : 1;
}

/** Python floor division and modulo of bigints. */
function floorDivmod(a: bigint, b: bigint): [bigint, bigint] {
  if (b === 0n) throw new RangeError('integer division or modulo by zero');
  let q = a / b;
  if (a % b !== 0n && a < 0n !== b < 0n) q -= 1n;
  return [q, a - q * b];
}

/** A domain element object with arithmetic methods (PythonMPQ, Gaussian elements, ModularInteger, ANP, Expression). */
export interface DomainElement {
  add(o: unknown): unknown;
  sub(o: unknown): unknown;
  mul(o: unknown): unknown;
  div(o: unknown): unknown;
  neg(): unknown;
  equals(o: unknown): boolean;
  readonly isZero: boolean;
}
/** Is x a domain element object (not an expression)? @internal */
export const isDomainElement = (x: unknown): x is DomainElement => typeof x === 'object' && x !== null && !(x instanceof Expr) && typeof (x as { mul?: unknown }).mul === 'function';

/**
 * a op b for elements of K of any representation (SymPy's operators on
 * domain elements): integers as bigints, element objects by their methods,
 * expressions by K's canonical arithmetic. @internal
 */
export function domainArith(K: Domain, op: 'add' | 'sub' | 'mul' | 'quo', aIn: unknown, bIn: unknown): unknown {
  const [a, b] = [K.convert(aIn), K.convert(bIn)];
  if (typeof a === 'bigint' && typeof b === 'bigint') return op === 'add' ? a + b : op === 'sub' ? a - b : op === 'mul' ? a * b : floorDivmod(a, b)[0];
  if (isDomainElement(a)) return op === 'quo' ? a.div(b) : a[op](b);
  const [x, y] = [K.toSympy(a), K.toSympy(b)];
  return K.convert(op === 'add' ? K.add(x, y) : op === 'sub' ? K.sub(x, y) : op === 'mul' ? K.mul(x, y) : K.quo(x, y));
}

/** -a for an element of K of any representation. @internal */
export function domainNeg(K: Domain, a: unknown): unknown {
  return domainArith(K, 'sub', 0, a);
}

/** Hooks set by the modules of the domains that depend on heavier machinery (algebraic fields). @internal */
export const domainHooks: {
  algebraicField?: (K: Domain, exts: readonly ExprLike[]) => Domain;
  polynomialRing?: (K: Domain, gens: readonly Sym[]) => PolynomialRingBase;
  freeModule?: (K: Domain, rank: IntLike) => FreeModule;
  ideal?: (K: Domain, gens: readonly ExprLike[]) => ModuleImplementedIdeal;
  quotientRing?: (K: Domain, ideal: ModuleImplementedIdeal | readonly ExprLike[]) => QuotientRing;
  compositeRing?: (K: Domain, gens: readonly Sym[]) => Domain;
  compositeField?: (K: Domain, gens: readonly Sym[]) => Domain;
  complexField?: (prec: number) => Domain;
} = {};

/** Values that are not coefficients of any domain (SymPy _not_a_coeff: nan, oo, -oo and zoo). */
function notACoefficient(a: unknown): boolean {
  if (typeof a === 'number') return !Number.isFinite(a);
  return a === S.NaN || a === S.Infinity || a === S.NegativeInfinity || a === S.ComplexInfinity;
}

/** The kinds of domains that SymPy unify distinguishes. @internal */
export type UnificationKind = 'ZZ' | 'QQ' | 'RR' | 'CC' | 'ALG' | 'ZZ_I' | 'QQ_I' | 'EX' | 'EXRAW' | 'other';

const isSym = (e: unknown): e is Sym => e instanceof Sym;

/** The generators of both lists, the common ones in a consistent order (SymPy _unify_gens). @internal */
export function unifyGens(fIn: readonly Expr[], gIn: readonly Expr[]): Expr[] {
  let [f, g] = [[...fIn], [...gIn]];
  if (f.length === g.length && f.every((a, i) => a.key === at(g, i).key)) return f;
  const has = (list: readonly Expr[], e: Expr): boolean => list.some((a) => a.key === e.key);
  const common = f.filter((a) => has(g, a));
  let k = 0;
  g = g.map((a) => (has(common, a) ? at(common, k++) : a));
  const gens: Expr[] = [];
  for (const c of common) {
    const i = f.findIndex((a) => a.key === c.key);
    gens.push(...f.slice(0, i));
    f = f.slice(i + 1);
    const j = g.findIndex((a) => a.key === c.key);
    gens.push(...g.slice(0, j));
    g = g.slice(j + 1);
    gens.push(c);
  }
  return [...gens, ...f, ...g];
}

/** Is e a generator, or (in a field) the reciprocal of one (x in QQ(1/x))? */
const isGenerator = (e: Expr, gens: readonly Expr[], ring: boolean): boolean => gens.some((g) => g.key === e.key) || (!ring && gens.some((g) => g.key === pow(e, -1).key));

/**
 * e is built from the generators, numbers of the ground domain, +, * and
 * integer powers (nonnegative ones only for a ring); over EX any
 * subexpression free of the generators is a coefficient.
 */
function isRationalIn(e: Expr, gens: readonly Sym[], ground: Ground, ring: boolean): boolean {
  if (e instanceof Rational) return ground !== 'ZZ' || e.isInteger || !ring;
  if (e instanceof Float) return ground === 'RR';
  if (isGenerator(e, gens, ring)) return true;
  if (ground === 'EX' && !gens.some((g) => [...freeSymbols(g)].some((s) => freeSymbols(e).has(s)))) return true;
  if (e instanceof Add || e instanceof Mul) return e.args.every((a) => isRationalIn(a, gens, ground, ring));
  if (e instanceof Pow) {
    const k = e.exp;
    return k instanceof Rational && k.isInteger && (!ring || k.p >= 0n) && isRationalIn(e.base, gens, ground, ring);
  }
  return false;
}

/**
 * A ground domain (SymPy Domain): ZZ, QQ, RR, a polynomial ring K[a, ...] or a
 * fraction field K(a, ...) of symbols. Elements are expressions in canonical
 * form, so equal elements have equal keys.
 */
export abstract class Domain {
  /** The numeric ground domain under the symbols. */
  abstract readonly ground: Ground;
  /** The symbols of a polynomial ring or fraction field (empty for ZZ, QQ, RR). */
  readonly symbols: readonly Sym[] = [];
  abstract readonly isField: boolean;
  readonly zero: Expr = S.Zero;
  readonly one: Expr = S.One;
  abstract toString(): string;
  /** The canonical form of a value known to belong to the domain. */
  abstract canon(e: Expr): Expr;
  /** Convert an expression to an element (SymPy from_sympy); throws CoercionFailed. */
  abstract fromSympy(e: ExprLike): Expr;
  /** The element as an expression (SymPy to_sympy); ground numbers (bigint, PythonMPQ) become rationals. */
  toSympy(a: unknown): Expr {
    const e = groundToSympy(a);
    if (e instanceof Expr) return e;
    throw new CoercionFailed(`${String(a)} is not an element of ${this.toString()}`);
  }
  /** SymPy K(a) or K(p, q): an element of the domain (SymPy Domain.new / __call__). */
  new(...args: unknown[]): unknown {
    return this.convert(first(args));
  }
  /**
   * Convert a value to an element of the domain (SymPy convert): an
   * expression, a number, or an element of the domain `base`. ZZ elements
   * are bigints and QQ elements PythonMPQ (SymPy's ground types); the
   * other domains keep expressions.
   */
  convert(a: unknown, base?: Domain): unknown {
    const e = base !== undefined && !base.equals(this) ? base.toSympy(a) : groundToSympy(a);
    if (!(e instanceof Expr)) throw new CoercionFailed(`cannot convert ${String(a)} to ${this.toString()}`);
    return this.fromSympy(e);
  }
  /** Is a a unit, an invertible element (SymPy is_unit)? */
  isUnit(a: unknown): boolean {
    if (this.isField) return !this.isZero(this.convert(a));
    throw new NotImplementedError(`isUnit is not implemented for ${this.toString()}`);
  }
  /** The unit u for which u*a is the canonical associate of a (SymPy canonical_unit). */
  canonicalUnit(a: unknown): unknown {
    return this.convert(this.isNegative(this.convert(a)) ? -1 : 1);
  }
  /** The square root of a when it is a square in the domain (SymPy exsqrt), NoMatch otherwise. */
  exsqrt(_a: unknown): unknown {
    throw new NotImplementedError(`exsqrt is not implemented for ${this.toString()}`);
  }
  /** Is a a square in the domain (SymPy is_square)? */
  isSquare(a: unknown): boolean {
    return !isNoMatch(this.exsqrt(a));
  }
  /** Convert an element of the domain `base` to an element of this domain (SymPy convert_from); throws CoercionFailed. */
  convertFrom(a: unknown, base: Domain): unknown {
    return this.convert(a, base);
  }
  /** The element of a polynomial ring K0 as an element of this domain (SymPy from_PolynomialRing), NoMatch when it is not one. */
  fromPolynomialRing(a: unknown, K0: Domain): unknown {
    return this.convertOrNoMatch(a, K0);
  }
  /** The element of a fraction field K0 as an element of this domain (SymPy from_FractionField), NoMatch when it is not one. */
  fromFractionField(a: unknown, K0: Domain): unknown {
    return this.convertOrNoMatch(a, K0);
  }
  private convertOrNoMatch(a: unknown, K0: Domain): unknown {
    try { return this.convert(a, K0); }
    catch (error) { if (error instanceof CoercionFailed) return NoMatch; throw error; }
  }
  /** Is a an element of the domain's type (SymPy of_type)? */
  ofType(a: unknown): boolean {
    return a instanceof Expr;
  }
  /** The number of generators of a polynomial ring or fraction field (SymPy ngens). */
  get ngens(): number {
    return this.symbols.length;
  }
  /** The ground domain of a polynomial ring or fraction field, the domain itself otherwise (SymPy dom). */
  get dom(): Domain {
    return GROUNDS[this.ground];
  }
  /** The ring of a field (SymPy get_ring): QQ -> ZZ, K(x) -> K[x]; a ring is its own ring. */
  getRing(): Domain {
    return this;
  }
  /** Whether this domain provides an associated field (SymPy has_assoc_Field). */
  get hasAssocField(): boolean {
    try { this.getField(); return true; }
    catch (error) { if (error instanceof NotImplementedError) return false; throw error; }
  }
  /** Whether this domain has an associated ring of which it is the field (SymPy has_assoc_Ring). */
  get hasAssocRing(): boolean {
    return false;
  }
  /** a > 0 (SymPy is_positive of a ground element). */
  isPositive(a: unknown): boolean {
    return (groundSign(a) ?? 0) > 0;
  }
  /** a >= 0 (SymPy is_nonnegative). */
  isNonnegative(a: unknown): boolean {
    return (groundSign(a) ?? -1) >= 0;
  }
  /** a <= 0 (SymPy is_nonpositive). */
  isNonpositive(a: unknown): boolean {
    return (groundSign(a) ?? 1) <= 0;
  }
  /** The greatest common divisor of two elements (SymPy gcd). */
  gcd(_a: unknown, _b: unknown): unknown {
    throw new NotImplementedError(`gcd is not implemented for ${this.toString()}`);
  }
  /** The least common multiple of two elements (SymPy lcm). */
  lcm(_a: unknown, _b: unknown): unknown {
    throw new NotImplementedError(`lcm is not implemented for ${this.toString()}`);
  }
  /** [quotient, remainder] of two elements (SymPy div). */
  div(_a: unknown, _b: unknown): [unknown, unknown] {
    throw new NotImplementedError(`div is not implemented for ${this.toString()}`);
  }
  /** The exact quotient of two elements (SymPy exquo); throws ExactQuotientFailed. */
  exquo(_a: unknown, _b: unknown): unknown {
    throw new NotImplementedError(`exquo is not implemented for ${this.toString()}`);
  }
  /** The remainder of two elements (SymPy rem). */
  rem(_a: unknown, _b: unknown): unknown {
    throw new NotImplementedError(`rem is not implemented for ${this.toString()}`);
  }
  /** The terms {monomial: coefficient} of a polynomial-ring element (SymPy PolyElement.to_dict). */
  toDict(a: unknown): Map<number[], unknown> {
    throw new NotImplementedError(`${String(a)} is not a polynomial-ring element of ${this.toString()}`);
  }
  /** The algebraic number field QQ<a, ...> over this domain (SymPy algebraic_field). */
  algebraicField(...exts: ExprLike[]): Domain {
    return defined(domainHooks.algebraicField, 'algebraic field module')(this, exts);
  }
  add(a: Expr, b: Expr): Expr {
    return this.canon(add(a, b));
  }
  sub(a: Expr, b: Expr): Expr {
    return this.canon(add(a, neg(b)));
  }
  mul(a: Expr, b: Expr): Expr {
    return this.canon(mul(a, b));
  }
  neg(a: Expr): Expr {
    return this.canon(neg(a));
  }
  /** a/b in the fraction field of the domain. */
  quo(a: Expr, b: Expr): Expr {
    return this.getField().canon(mul(a, pow(b, -1)));
  }
  isZero(a: unknown): boolean {
    return groundSign(a) === 0;
  }
  isOne(a: unknown): boolean {
    const e = groundToSympy(a);
    return e instanceof Rational && e.isOne;
  }
  /** a < 0 for a number (SymPy is_negative of the leading ground coefficient). */
  isNegative(a: unknown): boolean {
    return (groundSign(a) ?? 0) < 0;
  }
  equals(o: Domain): boolean {
    return this.toString() === o.toString();
  }
  /** The fraction field (SymPy get_field). */
  abstract getField(): Domain;
  /** SymPy K[gens] (K.poly_ring): the polynomial ring in gens over this domain. */
  polyRing(...gens: Sym[]): Domain {
    if (isGroundDomain(this) || this instanceof PolynomialRing) return new PolynomialRing(this, gens);
    return defined(domainHooks.compositeRing, 'composite domains')(this, gens);
  }
  /** SymPy K.frac_field(*gens): the field of rational functions in gens over this domain. */
  fracField(...gens: Sym[]): Domain {
    if (isGroundDomain(this) || this instanceof SymbolicDomain) return new FractionField(this, gens);
    return defined(domainHooks.compositeField, 'composite domains')(this, gens);
  }
  /** SymPy K.inject(*symbols): the polynomial ring over this domain, or this composite domain with more generators. */
  inject(...symbols: Sym[]): Domain {
    return this.polyRing(...symbols);
  }
  /** SymPy K.drop(*symbols): a simple domain has no generators to drop. */
  drop(..._symbols: Expr[]): Domain {
    return this;
  }
  /** SymPy `a in K`: whether a converts to an element of the domain. */
  contains(a: unknown): boolean {
    if (notACoefficient(a)) return false;
    try { this.convert(a); return true; }
    catch (error) { if (error instanceof CoercionFailed) return false; throw error; }
  }
  /** Whether the elements are exact (SymPy is_Exact): false for the floating-point domains. */
  get isExact(): boolean {
    return true;
  }
  /** The exact domain closest to this one (SymPy get_exact). */
  getExact(): Domain {
    return this;
  }
  /** Whether the domain has characteristic zero (SymPy has_CharacteristicZero). */
  get hasCharacteristicZero(): boolean {
    return false;
  }
  /** The characteristic of the domain (SymPy characteristic): 0 for a domain of characteristic zero. */
  characteristic(): bigint {
    if (this.hasCharacteristicZero) return 0n;
    throw new NotImplementedError('characteristic()');
  }
  /** SymPy K.old_poly_ring(x): the univariate polynomial ring over this domain. */
  oldPolyRing(gen: Sym): GlobalPolynomialRing;
  oldPolyRing(...gens: Sym[]): GlobalPolynomialRing | PolynomialRingBase;
  oldPolyRing(...gens: Sym[]): GlobalPolynomialRing | PolynomialRingBase {
    if (gens.length === 0) throw new NotImplementedError('oldPolyRing requires generators');
    return gens.length === 1 ? new GlobalPolynomialRing(this, first(gens)) : defined(domainHooks.polynomialRing, 'polynomial ring module')(this, gens);
  }
  /** A finite free module over this ring (SymPy free_module). */
  freeModule(rank: IntLike): FreeModule {
    return defined(domainHooks.freeModule, 'AGCA modules')(this, rank);
  }
  /** The ideal generated by the given elements. */
  ideal(...gens: ExprLike[]): ModuleImplementedIdeal {
    return defined(domainHooks.ideal, 'AGCA ideals')(this, gens);
  }
  /** The quotient by an ideal or its generators. */
  quotientRing(ideal: ModuleImplementedIdeal | readonly ExprLike[]): QuotientRing {
    return defined(domainHooks.quotientRing, 'quotient rings')(this, ideal);
  }
  /** The kind of the domain in the unification rules of SymPy unify. @internal */
  protected get unificationKind(): UnificationKind {
    return 'other';
  }
  /** The precision in bits of a floating-point domain (RR, CC). @internal */
  protected get floatPrecision(): number {
    return 53;
  }
  /** The extensions an algebraic field was made from (SymPy orig_ext). @internal */
  protected get algebraicExtensions(): readonly Expr[] {
    return [];
  }
  /** The coefficient domain and generators of a composite domain (K[x], K(x)); false for a simple domain. @internal */
  protected get compositeParts(): readonly [Domain, readonly Sym[]] | false {
    return false;
  }
  /** The composite domain of the same kind over K in the generators. @internal */
  protected recompose(_K: Domain, _gens: readonly Sym[]): Domain {
    throw new NotImplementedError(`${this.toString()} is not a composite domain`);
  }
  /** Whether elements are represented modulo a finite extension's defining polynomial. */
  get isFiniteExtension(): boolean { return false; }

  /** The smallest domain containing this one and K1 (SymPy unify). */
  unify(K1In: Domain): Domain {
    let [K0, K1]: [Domain, Domain] = [this, K1In];
    if (K0.equals(K1)) return K0;
    if (!(K0.hasCharacteristicZero && K1.hasCharacteristicZero)) {
      if (K0.characteristic() !== K1.characteristic()) throw new UnificationFailed(`Cannot unify ${K0.toString()} with ${K1.toString()}`);
      return K0.unifyComposite(K1);
    }
    for (const kind of ['EXRAW', 'EX'] as const) {
      if (K0.unificationKind === kind) return K0;
      if (K1.unificationKind === kind) return K1;
    }
    if (K1.isFiniteExtension) return K1.unify(K0);
    if (K0.compositeParts !== false || K1.compositeParts !== false) return K0.unifyComposite(K1);
    const kind = (K: Domain): UnificationKind => K.unificationKind;
    if (kind(K1) === 'CC') [K0, K1] = [K1, K0];
    if (kind(K0) === 'CC') {
      if ((kind(K1) === 'CC' || kind(K1) === 'RR') && K1.floatPrecision > K0.floatPrecision) return kind(K1) === 'CC' ? K1 : defined(domainHooks.complexField, 'complex field')(K1.floatPrecision);
      return K0;
    }
    if (kind(K1) === 'RR') [K0, K1] = [K1, K0];
    if (kind(K0) === 'RR') {
      if (kind(K1) === 'RR') return K1.floatPrecision > K0.floatPrecision ? K1 : K0;
      if (kind(K1) === 'ZZ_I' || kind(K1) === 'QQ_I') return defined(domainHooks.complexField, 'complex field')(K0.floatPrecision);
      return K0;
    }
    if (kind(K1) === 'ALG') [K0, K1] = [K1, K0];
    if (kind(K0) === 'ALG') {
      if (kind(K1) === 'ZZ_I') K1 = K1.getField();
      if (kind(K1) === 'QQ_I') K1 = QQ.algebraicField(S.I);
      return kind(K1) === 'ALG' ? QQ.algebraicField(...unifyGens(K0.algebraicExtensions, K1.algebraicExtensions)) : K0;
    }
    for (const k of ['QQ_I', 'ZZ_I'] as const) {
      if (kind(K0) === k) return k === 'ZZ_I' && kind(K1) === 'QQ' ? K0.getField() : K0;
      if (kind(K1) === k) return k === 'ZZ_I' && kind(K0) === 'QQ' ? K1.getField() : K1;
    }
    for (const k of ['QQ', 'ZZ'] as const) {
      if (kind(K0) === k) return K0;
      if (kind(K1) === k) return K1;
    }
    return EX;
  }
  /** Unify two domains of which at least one is composite (SymPy unify_composite). */
  private unifyComposite(K1: Domain): Domain {
    const [p0, p1] = [this.compositeParts, K1.compositeParts];
    const [g0, s0] = p0 === false ? [this, []] : p0;
    const [g1, s1] = p1 === false ? [K1, []] : p1;
    let domain = g0.unify(g1);
    const symbols = unifyGens(s0, s1);
    // ZZ[x].unify(QQ.frac_field(x)) is ZZ.frac_field(x)
    const mixed = p0 !== false && p1 !== false && this.isField !== K1.isField;
    if (mixed && (!g0.isField || !g1.isField) && domain.isField && domain.hasAssocRing) domain = domain.getRing();
    const cls = p0 !== false && (p1 === false || this.isField || !K1.isField) ? this : K1;
    return cls.recompose(domain, symbols.map((g) => expectType(g, isSym, 'generator')));
  }
  /** The unified domain, failing when a composite domain has one of the symbols as a generator (SymPy unify_with_symbols). */
  unifyWithSymbols(K1: Domain, symbols: readonly Expr[]): Domain {
    const shares = (K: Domain): boolean => {
      const parts = K.compositeParts;
      return parts !== false && parts[1].some((g) => symbols.some((s) => s.key === g.key));
    };
    if (shares(this) || shares(K1)) throw new UnificationFailed(`Cannot unify ${this.toString()} with ${K1.toString()}, given (${symbols.map((s) => str(s)).join(', ')}) generators`);
    return this.unify(K1);
  }
}

/** SymPy ZZ: the integers (SymPy IntegerRing). */
export class IntegerRing extends Domain {
  readonly ground = 'ZZ' as const;
  readonly isField = false;
  toString(): string {
    return 'ZZ';
  }
  protected override get unificationKind(): UnificationKind {
    return 'ZZ';
  }
  override get hasAssocRing(): boolean {
    return true;
  }
  override get hasCharacteristicZero(): boolean {
    return true;
  }
  canon(e: Expr): Expr {
    return e;
  }
  fromSympy(eIn: ExprLike): Expr {
    const e = sympify(eIn);
    if (e instanceof Rational && e.isInteger) return e;
    if (e instanceof Float) {
      const r = floatToRational(e);
      if (r.isInteger) return r;
    }
    throw new CoercionFailed(`expected an integer, got ${str(e)}`);
  }
  getField(): Domain {
    return QQ;
  }
  /** An integer element as a bigint (SymPy ZZ.convert); throws CoercionFailed. */
  override convert(a: unknown, base?: Domain): bigint {
    const r = groundRational(base !== undefined && !base.equals(this) ? base.toSympy(a) : a);
    if (r !== undefined && r[0] % r[1] === 0n) return r[0] / r[1];
    throw new CoercionFailed(`expected an integer, got ${String(a)}`);
  }
  override ofType(a: unknown): boolean {
    return typeof a === 'bigint';
  }
  override gcd(a: unknown, b: unknown): bigint {
    return igcd(this.convert(a), this.convert(b));
  }
  override lcm(a: unknown, b: unknown): bigint {
    return ilcm(this.convert(a), this.convert(b));
  }
  /** Python divmod (the quotient rounds toward -infinity). */
  override div(a: unknown, b: unknown): [bigint, bigint] {
    return floorDivmod(this.convert(a), this.convert(b));
  }
  override exquo(a: unknown, b: unknown): bigint {
    const [q, r] = floorDivmod(this.convert(a), this.convert(b));
    if (r !== 0n) throw new ExactQuotientFailed(`${String(a)} does not divide ${String(b)} in ZZ`);
    return q;
  }
  override rem(a: unknown, b: unknown): bigint {
    return floorDivmod(this.convert(a), this.convert(b))[1];
  }
  /** 1 and -1 are the units of ZZ. */
  override isUnit(a: unknown): boolean {
    const n = this.convert(a);
    return n === 1n || n === -1n;
  }
  /** The nonnegative square root of a square (SymPy ZZ.exsqrt), NoMatch otherwise. */
  override exsqrt(aIn: unknown): bigint | NoMatchResult {
    const a = this.convert(aIn);
    if (a < 0n) return NoMatch;
    const [root, rem] = sqrtrem(a);
    return rem === 0n ? root : NoMatch;
  }
  /** floor(log(a, b)) computed in floating point like SymPy's math.log (SymPy ZZ.log). */
  log(a: unknown, b: unknown): bigint {
    return BigInt(Math.trunc(Math.log(Number(this.convert(a))) / Math.log(Number(this.convert(b)))));
  }
}

/** SymPy QQ: the rationals. */
export class RationalField extends Domain {
  readonly ground = 'QQ' as const;
  readonly isField = true;
  toString(): string {
    return 'QQ';
  }
  protected override get unificationKind(): UnificationKind {
    return 'QQ';
  }
  override get hasAssocRing(): boolean {
    return true;
  }
  override get hasCharacteristicZero(): boolean {
    return true;
  }
  canon(e: Expr): Expr {
    return e;
  }
  fromSympy(eIn: ExprLike): Expr {
    const e = sympify(eIn);
    if (e instanceof Rational) return e;
    if (e instanceof Float) return floatToRational(e);
    throw new CoercionFailed(`expected a rational number, got ${str(e)}`);
  }
  getField(): Domain {
    return this;
  }
  override getRing(): Domain {
    return ZZ;
  }
  /** SymPy QQ(p, q): the PythonMPQ p/q. */
  override new(...args: unknown[]): PythonMPQ {
    const [p, q] = [this.convert(first(args)), args.length > 1 ? this.convert(args[1]) : new PythonMPQ(1n)];
    return p.div(q);
  }
  /** A rational element as a PythonMPQ (SymPy QQ.convert); throws CoercionFailed. */
  override convert(a: unknown, base?: Domain): PythonMPQ {
    const r = groundRational(base !== undefined && !base.equals(this) ? base.toSympy(a) : a);
    if (r === undefined) throw new CoercionFailed(`expected a rational number, got ${String(a)}`);
    return new PythonMPQ(r[0], r[1]);
  }
  override ofType(a: unknown): boolean {
    return a instanceof PythonMPQ;
  }
  /** gcd of the numerators over the lcm of the denominators (SymPy Field.gcd). */
  override gcd(a: unknown, b: unknown): PythonMPQ {
    const [x, y] = [this.convert(a), this.convert(b)];
    return new PythonMPQ(igcd(x.numerator, y.numerator), ilcm(x.denominator, y.denominator));
  }
  /** lcm of the numerators over the gcd of the denominators (SymPy Field.lcm). */
  override lcm(a: unknown, b: unknown): PythonMPQ {
    const [x, y] = [this.convert(a), this.convert(b)];
    return new PythonMPQ(ilcm(x.numerator, y.numerator), igcd(x.denominator, y.denominator));
  }
  override div(a: unknown, b: unknown): [PythonMPQ, PythonMPQ] {
    return [this.exquo(a, b), new PythonMPQ(0n)];
  }
  override exquo(a: unknown, b: unknown): PythonMPQ {
    return this.convert(a).div(this.convert(b));
  }
  override rem(_a: unknown, _b: unknown): PythonMPQ {
    return new PythonMPQ(0n);
  }
  /** The nonnegative square root of a square (SymPy QQ.exsqrt), NoMatch otherwise. */
  override exsqrt(aIn: unknown): PythonMPQ | NoMatchResult {
    const a = this.convert(aIn);
    const [p, q] = [ZZ.exsqrt(a.numerator), ZZ.exsqrt(a.denominator)];
    return isNoMatch(p) || isNoMatch(q) ? NoMatch : new PythonMPQ(p, q);
  }
}

/** SymPy RR: floating-point numbers with 53 bits. */
export class RealField extends Domain {
  readonly context: MPContext;
  constructor(prec = 53) {
    super();
    this.context = new MPContext(prec, { real: true, parent: this });
  }
  get precision(): number { return this.context.prec; }
  get dps(): number { return this.context.dps; }
  dtype(value: unknown = 0): RealElement { return this.context.mpf(value); }
  readonly ground = 'RR' as const;
  readonly isField = true;
  toString(): string {
    return this.precision === 53 ? 'RR' : `RR_${this.precision}`;
  }
  override equals(other: Domain): boolean { return other instanceof RealField && other.precision === this.precision; }
  override get isExact(): boolean { return false; }
  /** The exact counterpart QQ (SymPy get_exact). */
  override getExact(): Domain { return QQ; }
  override get hasCharacteristicZero(): boolean { return true; }
  protected override get unificationKind(): UnificationKind { return 'RR'; }
  protected override get floatPrecision(): number { return this.precision; }
  /** The nonnegative square root of a >= 0 (SymPy RR.exsqrt), NoMatch for a < 0. */
  override exsqrt(aIn: unknown): Expr | NoMatchResult {
    const a = this.convert(aIn);
    return a instanceof Float && a.isNegative ? NoMatch : this.fromSympy(pow(this.toSympy(a), S.Half));
  }
  canon(e: Expr): Expr {
    return e instanceof Rational ? new Float(mpfFromRational(e.p, e.q, this.precision), this.precision) : e;
  }
  override quo(a: Expr, b: Expr): Expr {
    const [fa, fb] = [this.canon(a), this.canon(b)];
    return new Float(mpfDiv(expectType(fa, isFloat, 'RR element').mpf, expectType(fb, isFloat, 'RR element').mpf, this.precision), this.precision);
  }
  fromSympy(eIn: ExprLike): Expr {
    const e = sympify(eIn);
    if (e instanceof Float) return e.prec === this.precision ? e : new Float(e.mpf, this.precision);
    if (e instanceof Rational) return evalfPrec(e, this.precision);
    if (freeSymbols(e).size === 0) {
      const v = evalfPrec(e, this.precision);
      if (v instanceof Float) return v;
    }
    throw new CoercionFailed(`expected a real number, got ${str(e)}`);
  }
  getField(): Domain {
    return this;
  }
}

/** An element of EX (SymPy ExpressionDomain.Expression): a simplified expression, printed `EX(sqrt(2))`. */
export class Expression {
  readonly ex: Expr;
  constructor(ex: ExprLike) {
    this.ex = EX.canon(sympify(ex));
  }
  private static of(o: unknown): Expr {
    return o instanceof Expression ? o.ex : EX.toSympy(o);
  }
  get isZero(): boolean {
    return this.ex instanceof Rational && this.ex.isZero;
  }
  add(o: unknown): Expression {
    return new Expression(add(this.ex, Expression.of(o)));
  }
  sub(o: unknown): Expression {
    return new Expression(add(this.ex, neg(Expression.of(o))));
  }
  mul(o: unknown): Expression {
    return new Expression(mul(this.ex, Expression.of(o)));
  }
  div(o: unknown): Expression {
    return new Expression(mul(this.ex, pow(Expression.of(o), -1)));
  }
  neg(): Expression {
    return new Expression(neg(this.ex));
  }
  pow(n: ExprLike): Expression {
    return new Expression(pow(this.ex, n));
  }
  equals(o: unknown): boolean {
    return this.ex.key === Expression.of(o).key;
  }
  /** SymPy str and repr: `EX(sqrt(2))`. */
  toString(): string {
    return `EX(${str(this.ex)})`;
  }
  repr(): string {
    return this.toString();
  }
}

/**
 * SymPy EX: arbitrary expressions (for algebraic or symbolic coefficients
 * such as sqrt(2)*I). Elements are canonicalized as SymPy does
 * (cancel, then expand), so a zero is recognized when it cancels.
 */
export class ExpressionDomain extends Domain {
  readonly ground = 'EX' as const;
  readonly isField = true;
  toString(): string {
    return 'EX';
  }
  protected override get unificationKind(): UnificationKind {
    return 'EX';
  }
  override get hasCharacteristicZero(): boolean {
    return true;
  }
  canon(e: Expr): Expr {
    return e instanceof Rational ? e : expand(cancel(e));
  }
  fromSympy(eIn: ExprLike): Expr {
    return this.canon(sympify(eIn));
  }
  getField(): Domain {
    return this;
  }
  override toSympy(a: unknown): Expr {
    return a instanceof Expression ? a.ex : super.toSympy(a);
  }
  /** An element (SymPy EX.convert): the expression wrapped as an Expression; nan and the infinities are not elements. */
  override convert(a: unknown, base?: Domain): Expression {
    if (notACoefficient(a)) throw new CoercionFailed(`${String(a)} is not in any domain`);
    return new Expression(a instanceof Expression ? a.ex : (base ?? this).toSympy(a));
  }
  override ofType(a: unknown): boolean {
    return a instanceof Expression;
  }
  override isZero(a: unknown): boolean {
    return a instanceof Expression ? a.isZero : super.isZero(a);
  }
}

/**
 * Shared parts of K[a, ...] and K(a, ...) over a numeric ground domain or
 * over such a domain with generators (ZZ[z][x]). Elements are expressions in
 * all generators: `symbols` lists those of the coefficient domain first, and
 * `gens` the generators added by this domain.
 */
abstract class SymbolicDomain extends Domain {
  readonly ground: Ground;
  override readonly symbols: readonly Sym[];
  /** The coefficient domain (SymPy domain). */
  readonly domain: Domain;
  /** The generators over the coefficient domain (SymPy symbols). */
  readonly gens: readonly Sym[];
  constructor(coefficients: Ground | Domain, gens: readonly Sym[]) {
    super();
    this.domain = typeof coefficients === 'string' ? GROUNDS[coefficients] : coefficients;
    this.ground = this.domain.ground;
    this.gens = gens;
    this.symbols = [...this.domain.symbols, ...gens];
  }
  protected abstract readonly ring: boolean;
  protected get bracket(): [string, string] {
    return this.ring ? ['[', ']'] : ['(', ')'];
  }
  toString(): string {
    const [l, r] = this.bracket;
    return `${this.domain.toString()}${l}${this.gens.map((s) => str(s)).join(',')}${r}`;
  }
  /** The same kind of domain over another coefficient domain (SymPy set_domain). */
  abstract setDomain(K: Domain): Domain;
  override get isExact(): boolean {
    return this.domain.isExact;
  }
  override getExact(): Domain {
    return this.setDomain(this.domain.getExact());
  }
  override get hasCharacteristicZero(): boolean {
    return this.domain.hasCharacteristicZero;
  }
  override characteristic(): bigint {
    return this.domain.characteristic();
  }
  override inject(...symbols: Sym[]): Domain {
    if (symbols.some((s) => this.symbols.some((t) => t.key === s.key))) throw new GeneratorsError(`common generators in (${this.gens.map((g) => str(g)).join(', ')}) and (${symbols.map((g) => str(g)).join(', ')})`);
    return this.recompose(this.domain, [...this.gens, ...symbols]);
  }
  override drop(...symbols: Expr[]): Domain {
    const gens = this.gens.filter((g) => !symbols.some((s) => s.key === g.key));
    const K = this.domain.drop(...symbols);
    return gens.length ? this.recompose(K, gens) : K;
  }
  protected override get compositeParts(): readonly [Domain, readonly Sym[]] {
    return [this.domain, this.gens];
  }
  /** The same kind of domain with other generators over K. */
  protected abstract override recompose(K: Domain, gens: readonly Sym[]): Domain;
  override get hasAssocRing(): boolean {
    return true;
  }
  fromSympy(eIn: ExprLike): Expr {
    const e = this.groundCoefficients(sympify(eIn));
    if (!isRationalIn(e, this.symbols, this.ground, this.ring)) throw new CoercionFailed(`cannot convert ${str(e)} to ${this.toString()}`);
    return this.canon(e);
  }
  /** e with its numbers converted to elements of the ground domain where they are (3.0 in ZZ, sqrt(7) in RR). */
  private groundCoefficients(e: Expr): Expr {
    if (e instanceof Rational || e instanceof Sym) return e;
    if (freeSymbols(e).size === 0) return GROUNDS[this.ground].contains(e) ? GROUNDS[this.ground].fromSympy(e) : e;
    if (e instanceof Add) return add(...e.args.map((a) => this.groundCoefficients(a)));
    if (e instanceof Mul) return mul(...e.args.map((a) => this.groundCoefficients(a)));
    if (e instanceof Pow) return pow(this.groundCoefficients(e.base), e.exp);
    return e;
  }
  override isZero(a: Expr): boolean {
    return a instanceof Rational && a.isZero;
  }
}

const isTermMap = (x: unknown): x is ReadonlyMap<unknown, unknown> => x instanceof Map;

/** SymPy K[a, ...]: polynomials in symbols (elements are expanded). */
export class PolynomialRing extends SymbolicDomain {
  readonly isField = false;
  protected readonly ring = true;
  canon(e: Expr): Expr {
    return expandMul(e);
  }
  /** SymPy K[x](a): an element from an expression, a number or a dict {monomial: coefficient}. */
  override new(...args: unknown[]): unknown {
    return this.convert(first(args));
  }
  /** The element as an expression; a dict {monomial: coefficient} (SymPy's PolyElement is a dict) is summed. */
  override toSympy(a: unknown): Expr {
    if (!isTermMap(a)) return super.toSympy(a);
    const terms = [...a].map(([m, c]) => {
      const monom: unknown[] = Array.isArray(m) ? m : [m];
      return mul(this.dom.toSympy(c), ...monom.map((k, i) => pow(at(this.symbols, i), Number(k))));
    });
    return this.canon(add(...terms));
  }
  override convert(a: unknown, base?: Domain): unknown {
    return isTermMap(a) ? this.toSympy(a) : super.convert(a, base);
  }
  /** The terms {monomial: coefficient} of an element; coefficients are elements of the ground domain. */
  override toDict(aIn: unknown): Map<number[], unknown> {
    const a = this.canon(this.toSympy(aIn));
    const out = new Map<string, [number[], Expr]>();
    for (const t of a instanceof Add ? a.args : [a]) {
      const monom = this.symbols.map(() => 0);
      const rest: Expr[] = [];
      for (const f of t instanceof Mul ? t.args : [t]) {
        const [b, k] = f instanceof Pow && f.exp instanceof Rational ? [f.base, Number(f.exp.p)] : [f, 1];
        const i = this.symbols.findIndex((s) => s.key === b.key);
        if (i >= 0) monom[i] = at(monom, i) + k;
        else rest.push(f);
      }
      // the canonical (expanded) element has one term per monomial
      out.set(monom.join(','), [monom, mul(...rest)]);
    }
    return new Map([...out.values()].filter(([, c]) => !(c instanceof Rational && c.isZero)).map(([m, c]) => [m, this.dom.convert(c)]));
  }
  getField(): Domain {
    return this.domain.fracField(...this.gens);
  }
  setDomain(K: Domain): Domain {
    return K.polyRing(...this.gens);
  }
  /** The units are the units of the ground domain (SymPy PolynomialRing.is_unit). */
  override isUnit(a: unknown): boolean {
    const e = this.toSympy(this.convert(a));
    const free = [...freeSymbols(e)];
    return !this.symbols.some((s) => free.some((f) => f.key === s.key)) && GROUNDS[this.ground].isUnit(e);
  }
  /** The canonical unit of the leading coefficient (SymPy PolynomialRing.canonical_unit). */
  override canonicalUnit(a: unknown): unknown {
    const terms = [...this.toDict(this.convert(a))];
    if (!terms.length) return this.convert(1);
    // lex order with the generators of this ring before those of its coefficient domain
    const rank = this.lexRank();
    const key = (m: readonly number[]): number[] => rank.map((i) => at(m, i));
    // distinct monomials differ at some position
    const compare = (u: readonly number[], v: readonly number[]): number => {
      const i = u.findIndex((k, j) => k !== at(v, j));
      return at(u, i) - at(v, i);
    };
    const [, lc] = terms.reduce((best, t) => (compare(key(t[0]), key(best[0])) > 0 ? t : best));
    return this.convert(GROUNDS[this.ground].canonicalUnit(lc));
  }
  /** The positions of the symbols in lex significance: this ring's generators, then the coefficient domain's. */
  private lexRank(): number[] {
    const inner = this.domain instanceof PolynomialRing ? this.domain.lexRank() : [];
    return [...this.gens.map((_, i) => inner.length + i), ...inner];
  }
  protected recompose(K: Domain, gens: readonly Sym[]): Domain {
    return K.polyRing(...gens);
  }
}

/** SymPy K(a, ...): rational functions of symbols (elements are cancelled). */
export class FractionField extends SymbolicDomain {
  readonly isField = true;
  protected readonly ring = false;
  canon(e: Expr): Expr {
    return e instanceof Rational || e instanceof Float || e instanceof Sym ? e : cancel(e);
  }
  getField(): Domain {
    return this;
  }
  override getRing(): Domain {
    return this.domain.polyRing(...this.gens);
  }
  setDomain(K: Domain): Domain {
    return K.fracField(...this.gens);
  }
  protected recompose(K: Domain, gens: readonly Sym[]): Domain {
    return K.fracField(...gens);
  }
}

/** SymPy ZZ. */
export const ZZ: IntegerRing = new IntegerRing();
/** SymPy QQ. */
export const QQ: RationalField = new RationalField();
/** SymPy RR (53-bit floats). */
export const RR: Domain = new RealField();
/** SymPy EX (expressions). */
export const EX: ExpressionDomain = new ExpressionDomain();

const GROUNDS: Record<Ground, Domain> = { ZZ, QQ, RR, EX };

/** Is K one of the numeric ground domains ZZ, QQ, RR (53 bits) and EX? */
function isGroundDomain(K: Domain): boolean {
  return K.equals(GROUNDS[K.ground]);
}

// ---------------------------------------------------------------------------
// dense univariate polynomials (SymPy DMP) and fractions of them (DMF)
// ---------------------------------------------------------------------------

type Rep = readonly Expr[];

function strip(dom: Domain, rep: Rep): Expr[] {
  let i = 0;
  while (i < rep.length && dom.isZero(at(rep, i))) i++;
  return rep.slice(i);
}

function repAdd(dom: Domain, f: Rep, g: Rep): Expr[] {
  const n = Math.max(f.length, g.length);
  const pad = (h: Rep): Expr[] => [...Array.from({ length: n - h.length }, () => dom.zero), ...h];
  const [F, G] = [pad(f), pad(g)];
  return strip(
    dom,
    F.map((c, i) => dom.add(c, at(G, i))),
  );
}

const repNeg = (dom: Domain, f: Rep): Expr[] => f.map((c) => dom.neg(c));

function repMul(dom: Domain, f: Rep, g: Rep): Expr[] {
  if (!f.length || !g.length) return [];
  const out: Expr[] = Array.from({ length: f.length + g.length - 1 }, () => dom.zero);
  for (const [i, a] of f.entries()) {
    if (dom.isZero(a)) continue;
    for (const [j, b] of g.entries()) out[i + j] = dom.add(at(out, i + j), dom.mul(a, b));
  }
  return strip(dom, out);
}

const repMulGround = (dom: Domain, f: Rep, c: Expr): Expr[] => strip(dom, f.map((a) => dom.mul(a, c)));

/** Division with remainder over a field. */
function repDivmod(dom: Domain, f: Rep, g: Rep): [Expr[], Expr[]] {
  if (!g.length) throw new RangeError('polynomial division by zero');
  const dg = g.length - 1;
  if (f.length - 1 < dg) return [[], [...f]];
  const r = [...f];
  const q: Expr[] = [];
  const lc = first(g);
  for (let i = 0; i <= f.length - 1 - dg; i++) {
    const c = dom.quo(at(r, i), lc);
    q.push(c);
    for (let j = 1; j <= dg; j++) r[i + j] = dom.sub(at(r, i + j), dom.mul(c, at(g, j)));
  }
  return [strip(dom, q), strip(dom, r.slice(f.length - dg))];
}

function repMonic(dom: Domain, f: Rep): Expr[] {
  return f.map((c) => dom.quo(c, first(f)));
}

/** Monic gcd over a field by Euclid's algorithm. */
function repGcdField(dom: Domain, f: Rep, g: Rep): Expr[] {
  let [a, b] = [[...f], [...g]];
  while (b.length) [a, b] = [b, repDivmod(dom, a, b)[1]];
  return repMonic(dom, a);
}

const isRat = (e: unknown): e is Rational => e instanceof Rational;
const isFloat = (e: unknown): e is Float => e instanceof Float;
const rat = (e: Expr): Rational => expectType(e, isRat, 'rational coefficient');

const toExactRep = (f: Rep): Expr[] => f.map((c) => (c instanceof Float ? floatToRational(c) : c));
const toFloatRep = (f: Rep): Expr[] => f.map((c) => RR.canon(c));

// ---- integer polynomials (bigint coefficients, highest degree first) ----

type IP = bigint[];
const ipStrip = (f: readonly bigint[]): IP => {
  let i = 0;
  while (i < f.length && f[i] === 0n) i++;
  return f.slice(i);
};
const ipContent = (f: readonly bigint[]): bigint => f.reduce((g, c) => igcd(g, c), 0n);
/** f/content with a positive leading coefficient. */
function ipPrimitive(f: readonly bigint[]): IP {
  if (!f.length) return [];
  const c = ipContent(f) * BigInt(Math.sign(Number(at(f, 0))));
  return f.map((x) => x / c);
}

/** f/g over ZZ, undefined when g does not divide f exactly. */
function ipExquo(f: readonly bigint[], g: readonly bigint[]): IP | undefined {
  const dg = g.length - 1;
  if (f.length - 1 < dg) return f.length ? undefined : [];
  const r = [...f];
  const q: bigint[] = [];
  const lc = at(g, 0);
  for (let i = 0; i <= f.length - 1 - dg; i++) {
    const ri = at(r, i);
    if (ri % lc !== 0n) return undefined;
    const c = ri / lc;
    q.push(c);
    if (c !== 0n) for (let j = 1; j <= dg; j++) r[i + j] = at(r, i + j) - c * at(g, j);
  }
  return r.slice(f.length - dg).every((c) => c === 0n) ? ipStrip(q) : undefined;
}

/** The heuristic gcd tries before the Euclidean algorithm (SymPy HEU_GCD_MAX). @internal */
export const gcdSettings = { heuristicTries: 6 };

const ipEval = (f: readonly bigint[], x: bigint): bigint => f.reduce((acc, c) => acc * x + c, 0n);
const babs = (a: bigint): bigint => (a < 0n ? -a : a);
const ipNorm = (f: readonly bigint[]): bigint => f.reduce((m, c) => (babs(c) > m ? babs(c) : m), 0n);

/** The polynomial with the balanced base-x digits of h, made primitive (SymPy _dup_zz_gcd_interpolate). */
function ipInterpolate(hIn: bigint, x: bigint): IP {
  const f: bigint[] = [];
  let h = hIn;
  while (h) {
    // h % x is in (-x, x); take the digit in (-x/2, x/2]
    let g = ((h % x) + x) % x;
    if (g > x / 2n) g -= x;
    f.unshift(g);
    h = (h - g) / x;
  }
  return ipPrimitive(f);
}

/**
 * The gcd of two primitive integer polynomials with positive leading
 * coefficients and degrees >= 1: the heuristic gcd (SymPy
 * dup_zz_heu_gcd), then the primitive Euclidean algorithm.
 */
function ipGcdPrimitive(f: IP, g: IP): IP {
  const [fn, gn] = [ipNorm(f), ipNorm(g)];
  const B = 2n * (fn < gn ? fn : gn) + 29n;
  const s = 99n * isqrt(B);
  const [a1, a2] = [fn / at(f, 0), gn / at(g, 0)];
  const alt = 2n * (a1 < a2 ? a1 : a2) + 4n;
  let x = B < s ? B : s;
  if (alt > x) x = alt;
  for (let i = 0; i < gcdSettings.heuristicTries; i++) {
    const [ff, gg] = [ipEval(f, x), ipEval(g, x)];
    // f(x), g(x) are nonzero for the large x
    const hh = igcd(ff, gg);
    const h = ipInterpolate(hh, x);
    if (ipExquo(f, h) && ipExquo(g, h)) return h;
    for (const [u, v, w] of [[f, g, ff], [g, f, gg]] as const) {
      const q = ipExquo(u, ipInterpolate(w / hh, x));
      if (q && ipExquo(v, q)) return ipPrimitive(q);
    }
    x = (73794n * x * isqrt(isqrt(x))) / 27011n;
  }
  let [u, v] = f.length >= g.length ? [f, g] : [g, f];
  while (v.length) {
    let r = [...u];
    const lc = at(v, 0);
    // pseudo-remainder: r*lc - c*x**k*v until deg r < deg v
    while (r.length >= v.length) {
      const c = at(r, 0);
      r = ipStrip(r.map((t, i) => t * lc - (i < v.length ? c * at(v, i) : 0n)).slice(1));
    }
    [u, v] = [v, ipPrimitive(r)];
  }
  return u;
}

/** The primitive gcd of two primitive integer polynomials (one of them nonzero). */
function ipGcd(f: IP, g: IP): IP {
  if (!f.length || !g.length) return f.length ? f : g;
  return f.length === 1 || g.length === 1 ? [1n] : ipGcdPrimitive(f, g);
}

/** A rational polynomial as (content, primitive integer polynomial with a positive leading coefficient). */
function toIP(f: Rep): [Rational, IP] {
  if (!f.length) return [Rational.of(0n), []];
  let den = 1n;
  for (const c of f) den = ilcm(den, rat(c).q);
  const ints = f.map((c) => rat(c).p * (den / rat(c).q));
  const g = ipContent(ints) * (at(ints, 0) < 0n ? -1n : 1n);
  return [Rational.of(g, den), ints.map((c) => c / g)];
}
const fromIP = (c: Rational, f: readonly bigint[]): Expr[] => f.map((t) => Rational.of(t * c.p, c.q));

/** SymPy dup_gcd: monic over a field, with the content gcd and a positive leading coefficient over ZZ. */
function repGcd(dom: Domain, f: Rep, g: Rep): Expr[] {
  if (dom === RR) return toFloatRep(repGcd(QQ, toExactRep(f), toExactRep(g)));
  if (dom === QQ || dom === ZZ) {
    if (!f.length && !g.length) return [];
    const [cf, F] = toIP(f);
    const [cg, G] = toIP(g);
    const h = ipGcd(F, G);
    if (dom === QQ) return fromIP(Rational.of(1n, at(h, 0)), h);
    const c = !f.length ? cg.p : !g.length ? cf.p : igcd(cf.p, cg.p);
    return fromIP(Rational.of(c), h);
  }
  if (dom.isField) return repGcdField(dom, f, g);
  return repGcdField(dom.getField(), f, g).map((c) => dom.canon(c));
}

/** SymPy dup_lcm: monic over a field, with the content lcm and a positive leading coefficient over ZZ. */
function repLcm(dom: Domain, f: Rep, g: Rep): Expr[] {
  if (!f.length || !g.length) return [];
  if (dom === RR) return toFloatRep(repLcm(QQ, toExactRep(f), toExactRep(g)));
  if (dom === QQ || dom === ZZ) {
    const [cf, F] = toIP(f);
    const [cg, G] = toIP(g);
    const h = ipGcd(F, G);
    const m = ipPrimitive(repMulInt(F, defined(ipExquo(G, h), 'gcd cofactor')));
    if (dom === QQ) return fromIP(Rational.of(1n, at(m, 0)), m);
    return fromIP(Rational.of(ilcm(cf.p, cg.p)), m);
  }
  const field = dom.getField();
  const h = repDivmod(field, repMul(field, f, g), repGcd(field, f, g))[0];
  return repMonic(field, h).map((c) => dom.canon(c));
}

/** f*g for nonzero integer polynomials. */
function repMulInt(f: readonly bigint[], g: readonly bigint[]): IP {
  const out: bigint[] = Array.from({ length: f.length + g.length - 1 }, () => 0n);
  for (const [i, a] of f.entries()) for (const [j, b] of g.entries()) out[i + j] = at(out, i + j) + a * b;
  return out;
}

/** The exact quotient f/g; throws ExactQuotientFailed when g does not divide f in the ring. */
function repExquo(dom: Domain, f: Rep, g: Rep): Expr[] {
  if (dom === QQ || dom === ZZ) {
    if (!g.length) throw new RangeError('polynomial division by zero');
    const [cf, F] = toIP(f);
    const [cg, G] = toIP(g);
    const q = ipExquo(F, G);
    const c = Rational.of(cf.p * cg.q, cf.q * cg.p);
    if (!q || (dom === ZZ && !q.every((t) => (t * c.p) % c.q === 0n))) throw new ExactQuotientFailed('the polynomial does not divide exactly');
    return fromIP(c, q);
  }
  const field = dom === RR ? RR : dom.getField();
  const [q, r] = repDivmod(field, f, g);
  if (r.length && dom !== RR) throw new ExactQuotientFailed(`${str(repToExpr(f, S.One))} does not divide exactly`);
  return q.map((c) => dom.canon(c));
}

function repToExpr(f: Rep, x: Expr): Expr {
  const n = f.length - 1;
  return add(...f.map((c, i) => mul(c, pow(x, n - i))));
}

/** SymPy GlobalPolynomialRing (K.old_poly_ring(x)): univariate polynomials over a ground domain. */
export class GlobalPolynomialRing {
  constructor(
    readonly dom: Domain,
    readonly gen: Sym,
  ) {}
  /** The generators (SymPy gens). */
  get gens(): Sym[] {
    return [this.gen];
  }
  get zero(): DMP {
    return new DMP([], this);
  }
  get one(): DMP {
    return new DMP([this.dom.one], this);
  }
  toString(): string {
    return `${this.dom.toString()}[${str(this.gen)}]`;
  }
  equals(o: GlobalPolynomialRing): boolean {
    return this.dom.equals(o.dom) && this.gen.key === o.gen.key;
  }
  /** The polynomial with these coefficients (highest degree first; SymPy R(list)). */
  fromList(rep: readonly ExprLike[]): DMP {
    return new DMP(
      rep.map((c) => this.dom.fromSympy(c)),
      this,
    );
  }
  /** Convert a polynomial expression (SymPy from_sympy); throws CoercionFailed. */
  fromSympy(eIn: ExprLike): DMP {
    const e = sympify(eIn);
    const cs = polyCoefficients(e, this.gen);
    if (!cs) throw new CoercionFailed(`${str(e)} is not a polynomial in ${str(this.gen)}`);
    const deg = Math.max(-1, ...cs.keys());
    const rep: Expr[] = [];
    for (let k = deg; k >= 0; k--) rep.push(this.dom.fromSympy(cs.get(k) ?? S.Zero));
    return new DMP(rep, this);
  }
  toSympy(p: DMP): Expr {
    return repToExpr(p.rep.map((c) => this.dom.toSympy(c)), this.gen);
  }
  /** The fraction field (SymPy get_field). */
  getField(): OldFractionField {
    return new OldFractionField(this);
  }
  /** Free modules use the multivariate polynomial presentation of this ring. */
  freeModule(rank: IntLike): FreeModule {
    return defined(domainHooks.polynomialRing, 'polynomial ring module')(this.dom, this.gens).freeModule(rank);
  }
  ideal(...gens: ExprLike[]): ModuleImplementedIdeal {
    return defined(domainHooks.polynomialRing, 'polynomial ring module')(this.dom, this.gens).ideal(...gens);
  }
  quotientRing(ideal: ModuleImplementedIdeal | readonly ExprLike[]): QuotientRing {
    return defined(domainHooks.polynomialRing, 'polynomial ring module')(this.dom, this.gens).quotientRing(ideal);
  }
}

/** A dense univariate polynomial over a ground domain (SymPy DMP); the coefficients are listed from the highest degree. */
export class DMP {
  readonly rep: readonly Expr[];
  constructor(
    rep: readonly Expr[],
    readonly ring: GlobalPolynomialRing,
  ) {
    this.rep = strip(ring.dom, rep);
  }
  get dom(): Domain {
    return this.ring.dom;
  }
  private per(rep: readonly Expr[]): DMP {
    return new DMP(rep, this.ring);
  }
  private repOf(o: DMP | ExprLike): Rep {
    return o instanceof DMP ? o.rep : this.ring.fromSympy(o).rep;
  }
  /** The coefficients from the highest degree (SymPy to_list). */
  toList(): Expr[] {
    return [...this.rep];
  }
  /** All coefficients ([0] for the zero polynomial; SymPy all_coeffs). */
  allCoeffs(): Expr[] {
    return this.rep.length ? [...this.rep] : [this.dom.zero];
  }
  get isZero(): boolean {
    return this.rep.length === 0;
  }
  /** The degree (-Infinity for the zero polynomial). */
  degree(): number {
    return this.rep.length ? this.rep.length - 1 : -Infinity;
  }
  /** The leading coefficient. */
  LC(): Expr {
    return this.rep[0] ?? this.dom.zero;
  }
  add(o: DMP | ExprLike): DMP {
    return this.per(repAdd(this.dom, this.rep, this.repOf(o)));
  }
  sub(o: DMP | ExprLike): DMP {
    return this.per(repAdd(this.dom, this.rep, repNeg(this.dom, this.repOf(o))));
  }
  mul(o: DMP | ExprLike): DMP {
    return this.per(repMul(this.dom, this.rep, this.repOf(o)));
  }
  neg(): DMP {
    return this.per(repNeg(this.dom, this.rep));
  }
  mulGround(c: ExprLike): DMP {
    return this.per(repMulGround(this.dom, this.rep, this.dom.fromSympy(c)));
  }
  /** The derivative (SymPy DMP.diff). */
  diff(): DMP {
    const n = this.rep.length - 1;
    return this.per(this.rep.slice(0, -1).map((c, i) => this.dom.mul(c, Rational.of(BigInt(n - i)))));
  }
  /** p(x + a) (SymPy shift). */
  shift(a: ExprLike): DMP {
    const lin = this.per([this.dom.one, this.dom.fromSympy(a)]);
    let r = this.ring.zero;
    for (const c of this.rep) r = r.mul(lin).add(this.per([c]));
    return r;
  }
  /** SymPy gcd (monic over a field). */
  gcd(o: DMP): DMP {
    return this.per(repGcd(this.dom, this.rep, o.rep));
  }
  /** SymPy lcm (monic over a field). */
  lcm(o: DMP): DMP {
    return this.per(repLcm(this.dom, this.rep, o.rep));
  }
  /** The exact quotient (SymPy exquo); throws ExactQuotientFailed. */
  exquo(o: DMP): DMP {
    return this.per(repExquo(this.dom, this.rep, o.rep));
  }
  equals(o: DMP | ExprLike): boolean {
    let r: Rep;
    try {
      r = this.repOf(o);
    } catch {
      return false;
    }
    return r.length === this.rep.length && r.every((c, i) => c.key === at(this.rep, i).key);
  }
  toSympy(): Expr {
    return this.ring.toSympy(this);
  }
  toString(): string {
    return `DMP(${str(this.toSympy())}, ${this.dom.toString()})`;
  }
}

/** SymPy FractionField of an old polynomial ring (K(x)): fractions of DMPs. */
export class OldFractionField {
  constructor(readonly ring: GlobalPolynomialRing) {}
  get dom(): Domain {
    return this.ring.dom;
  }
  get zero(): DMF {
    return this.frac(this.ring.zero, this.ring.one);
  }
  get one(): DMF {
    return this.frac(this.ring.one, this.ring.one);
  }
  toString(): string {
    return `${this.dom.toString()}(${str(this.ring.gen)})`;
  }
  /** The fraction p/1 of a polynomial or coefficient list (SymPy K.new). */
  new(p: DMP | readonly Expr[]): DMF {
    return this.frac(p instanceof DMP ? p : new DMP(p, this.ring), this.ring.one);
  }
  /**
   * The fraction num/den with common factors cancelled (SymPy dmp_cancel): over QQ the
   * denominators are cleared and the gcd is taken over ZZ, over RR over the exact rationals of the
   * coefficients; the denominator gets a positive leading coefficient.
   */
  frac(num: DMP, den: DMP): DMF {
    if (den.isZero) throw new RangeError('division by zero in a fraction field');
    if (num.isZero) return new DMF(num, this.ring.one, this);
    const dom = this.dom;
    let [p, q]: [Rep, Rep] = [num.rep, den.rep];
    if (dom === RR) {
      const [f, g] = [strip(QQ, toExactRep(p)), strip(QQ, toExactRep(q))];
      const h = repGcd(QQ, f, g);
      [p, q] = [toFloatRep(repExquo(QQ, f, h)), toFloatRep(repExquo(QQ, g, h))];
    } else if (dom === QQ) {
      const denominator = (f: Rep): bigint => f.reduce((m, c) => ilcm(m, rat(c).q), 1n);
      const [cq, cp] = [denominator(p), denominator(q)];
      const [f, g] = [repMulGround(QQ, p, Rational.of(cq)), repMulGround(QQ, q, Rational.of(cp))];
      const h = repGcd(ZZ, f, g);
      const c = igcd(cp, cq);
      [p, q] = [repMulGround(QQ, repExquo(ZZ, f, h), Rational.of(cp / c)), repMulGround(QQ, repExquo(ZZ, g, h), Rational.of(cq / c))];
    } else {
      const h = repGcd(dom, p, q);
      [p, q] = [repExquo(dom, p, h), repExquo(dom, q, h)];
    }
    if (dom.isNegative(first(q))) [p, q] = [repNeg(dom, p), repNeg(dom, q)];
    return new DMF(new DMP(p, this.ring), new DMP(q, this.ring), this);
  }
  /** Convert a rational function of the generator (SymPy from_sympy); throws CoercionFailed. */
  fromSympy(eIn: ExprLike): DMF {
    const e = sympify(eIn);
    const [n, d] = fraction(together(e));
    return this.frac(this.ring.fromSympy(n), this.ring.fromSympy(d));
  }
  toSympy(f: DMF): Expr {
    return mul(this.ring.toSympy(f.num), pow(this.ring.toSympy(f.den), -1));
  }
}

/** A fraction of univariate polynomials (SymPy DMF), kept with common factors cancelled. */
export class DMF {
  constructor(
    readonly num: DMP,
    readonly den: DMP,
    readonly field: OldFractionField,
  ) {}
  private of(o: DMF | DMP | ExprLike): DMF {
    if (o instanceof DMF) return o;
    if (o instanceof DMP) return this.field.new(o);
    return this.field.fromSympy(o);
  }
  numer(): DMP {
    return this.num;
  }
  denom(): DMP {
    return this.den;
  }
  get isZero(): boolean {
    return this.num.isZero;
  }
  add(oIn: DMF | DMP | ExprLike): DMF {
    const o = this.of(oIn);
    if (this.den.equals(o.den)) return this.field.frac(this.num.add(o.num), this.den);
    return this.field.frac(this.num.mul(o.den).add(o.num.mul(this.den)), this.den.mul(o.den));
  }
  sub(o: DMF | DMP | ExprLike): DMF {
    return this.add(this.of(o).neg());
  }
  mul(oIn: DMF | DMP | ExprLike): DMF {
    const o = this.of(oIn);
    return this.field.frac(this.num.mul(o.num), this.den.mul(o.den));
  }
  div(oIn: DMF | DMP | ExprLike): DMF {
    const o = this.of(oIn);
    return this.field.frac(this.num.mul(o.den), this.den.mul(o.num));
  }
  neg(): DMF {
    return new DMF(this.num.neg(), this.den, this.field);
  }
  /** The derivative (p/q)' = (p'q - pq')/q**2 (SymPy DMFdiff of the holonomic module). */
  diff(): DMF {
    return this.field.frac(this.den.mul(this.num.diff()).sub(this.num.mul(this.den.diff())), this.den.mul(this.den));
  }
  equals(oIn: DMF | DMP | ExprLike): boolean {
    const o = this.of(oIn);
    return this.num.equals(o.num) && this.den.equals(o.den);
  }
  toSympy(): Expr {
    return this.field.toSympy(this);
  }
  toString(): string {
    return `DMF(${str(this.toSympy())}, ${this.field.dom.toString()})`;
  }
}

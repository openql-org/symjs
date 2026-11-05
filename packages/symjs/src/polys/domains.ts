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
import type { Expr, ExprLike } from '../core/nodes';
import { Add, Float, Mul, Pow, Rational, S, Sym } from '../core/nodes';
import { add, mul, neg, pow, sympify } from '../core/ops';
import { freeSymbols } from '../core/traverse';
import { gcd as igcd, lcm as ilcm } from '../core/numbers';
import { limitDenominator } from '../core/numberutils';
import { isqrt, div as mpfDiv, fromRational as mpfFromRational, toRational as mpfToRational } from '../numeric/mpf';
import { evalf } from '../numeric/evalf';
import { str } from '../printing/str';
import { expand, expandMul } from '../simplify/expand';
import { cancel, fraction, together } from '../simplify/rational';
import { polyCoefficients } from './poly';

/** A value cannot be converted to an element of a domain (SymPy CoercionFailed). */
export class CoercionFailed extends TypeError {}

type Ground = 'ZZ' | 'QQ' | 'RR' | 'EX';

const GROUND_RANK: Record<Ground, number> = { ZZ: 0, QQ: 1, RR: 2, EX: 3 };

/** RR.to_rational: the float as a rational with a bounded denominator (mpmath max_denom at 53 bits). */
const RR_MAX_DENOM = 45035996273704n;
function floatToRational(f: Float): Rational {
  const [p, q] = mpfToRational(f.mpf);
  return limitDenominator(Rational.of(p, q), RR_MAX_DENOM);
}

/** e is built from the generators, numbers of the ground domain, +, * and integer powers (nonnegative ones only for a ring). */
function isRationalIn(e: Expr, gens: readonly Sym[], ground: Ground, ring: boolean): boolean {
  if (e instanceof Rational) return ground !== 'ZZ' || e.isInteger || !ring;
  if (e instanceof Float) return ground === 'RR';
  if (e instanceof Sym) return gens.some((g) => g.key === e.key);
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
  /** The element as an expression (SymPy to_sympy). */
  toSympy(a: Expr): Expr {
    return a;
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
  isZero(a: Expr): boolean {
    return (a instanceof Rational || a instanceof Float) && a.isZero;
  }
  isOne(a: Expr): boolean {
    return a instanceof Rational && a.isOne;
  }
  /** a < 0 for a number (SymPy is_negative of the leading ground coefficient). */
  isNegative(a: Expr): boolean {
    return (a instanceof Rational && a.p < 0n) || (a instanceof Float && a.mpf.man < 0n);
  }
  equals(o: Domain): boolean {
    return this.toString() === o.toString();
  }
  /** The fraction field (SymPy get_field). */
  abstract getField(): Domain;
  /** SymPy K[gens] (K.poly_ring). */
  polyRing(...gens: Sym[]): Domain {
    return new PolynomialRing(this.ground, [...this.symbols, ...gens]);
  }
  /** SymPy K.frac_field(*gens). */
  fracField(...gens: Sym[]): Domain {
    return new FractionField(this.ground, [...this.symbols, ...gens]);
  }
  /** SymPy K.old_poly_ring(x): the univariate polynomial ring over this domain. */
  oldPolyRing(...gens: Sym[]): GlobalPolynomialRing {
    if (gens.length !== 1) throw new NotImplementedError('oldPolyRing: only univariate rings are supported');
    return new GlobalPolynomialRing(this, first(gens));
  }
  /** The smallest domain containing this one and o (SymPy unify). */
  unify(o: Domain): Domain {
    if (this.equals(o)) return this;
    if (this === EX || o === EX) return EX;
    const ground: Ground = GROUND_RANK[this.ground] >= GROUND_RANK[o.ground] ? this.ground : o.ground;
    const symbols = [...this.symbols];
    for (const s of o.symbols) if (!symbols.some((t) => t.key === s.key)) symbols.push(s);
    if (symbols.length === 0) return GROUNDS[ground];
    const frac = this instanceof FractionField || o instanceof FractionField;
    return frac ? new FractionField(ground, symbols) : new PolynomialRing(ground, symbols);
  }
}

/** SymPy ZZ: the integers (SymPy IntegerRing). */
export class IntegerRing extends Domain {
  readonly ground = 'ZZ' as const;
  readonly isField = false;
  toString(): string {
    return 'ZZ';
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
}

/** SymPy QQ: the rationals. */
export class RationalField extends Domain {
  readonly ground = 'QQ' as const;
  readonly isField = true;
  toString(): string {
    return 'QQ';
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
}

/** SymPy RR: floating-point numbers with 53 bits. */
export class RealField extends Domain {
  readonly ground = 'RR' as const;
  readonly isField = true;
  toString(): string {
    return 'RR';
  }
  canon(e: Expr): Expr {
    return e instanceof Rational ? new Float(mpfFromRational(e.p, e.q, 53)) : e;
  }
  override quo(a: Expr, b: Expr): Expr {
    const [fa, fb] = [this.canon(a), this.canon(b)];
    return new Float(mpfDiv(expectType(fa, isFloat, 'RR element').mpf, expectType(fb, isFloat, 'RR element').mpf, 53));
  }
  fromSympy(eIn: ExprLike): Expr {
    const e = sympify(eIn);
    if (e instanceof Float) return e.prec === 53 ? e : new Float(e.mpf, 53);
    if (e instanceof Rational) return evalf(e);
    if (freeSymbols(e).size === 0) {
      const v = evalf(e);
      if (v instanceof Float) return v;
    }
    throw new CoercionFailed(`expected a real number, got ${str(e)}`);
  }
  getField(): Domain {
    return this;
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
  canon(e: Expr): Expr {
    return e instanceof Rational ? e : expand(cancel(e));
  }
  fromSympy(eIn: ExprLike): Expr {
    return this.canon(sympify(eIn));
  }
  getField(): Domain {
    return this;
  }
}

/** Shared parts of K[a, ...] and K(a, ...). */
abstract class SymbolicDomain extends Domain {
  constructor(
    readonly ground: Ground,
    readonly symbols: readonly Sym[],
  ) {
    super();
  }
  protected abstract readonly ring: boolean;
  protected get bracket(): [string, string] {
    return this.ring ? ['[', ']'] : ['(', ')'];
  }
  toString(): string {
    const [l, r] = this.bracket;
    return `${this.ground}${l}${this.symbols.map((s) => str(s)).join(',')}${r}`;
  }
  fromSympy(eIn: ExprLike): Expr {
    const e = sympify(eIn);
    if (!isRationalIn(e, this.symbols, this.ground, this.ring)) throw new CoercionFailed(`cannot convert ${str(e)} to ${this.toString()}`);
    return this.canon(e);
  }
  override isZero(a: Expr): boolean {
    return a instanceof Rational && a.isZero;
  }
}

/** SymPy K[a, ...]: polynomials in symbols (elements are expanded). */
export class PolynomialRing extends SymbolicDomain {
  readonly isField = false;
  protected readonly ring = true;
  canon(e: Expr): Expr {
    return expandMul(e);
  }
  getField(): Domain {
    return new FractionField(this.ground, this.symbols);
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
}

/** SymPy ZZ. */
export const ZZ: Domain = new IntegerRing();
/** SymPy QQ. */
export const QQ: Domain = new RationalField();
/** SymPy RR (53-bit floats). */
export const RR: Domain = new RealField();
/** SymPy EX (expressions). */
export const EX: Domain = new ExpressionDomain();

const GROUNDS: Record<Ground, Domain> = { ZZ, QQ, RR, EX };

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
  /** The fraction num/den with common factors cancelled (SymPy dmp_cancel). */
  frac(num: DMP, den: DMP): DMF {
    if (den.isZero) throw new RangeError('division by zero in a fraction field');
    if (num.isZero) return new DMF(num, this.ring.one, this);
    const dom = this.dom;
    if (dom === RR) {
      const exact = new OldFractionField(new GlobalPolynomialRing(QQ, this.ring.gen));
      const r = exact.frac(new DMP(toExactRep(num.rep), exact.ring), new DMP(toExactRep(den.rep), exact.ring));
      return new DMF(new DMP(toFloatRep(r.num.rep), this.ring), new DMP(toFloatRep(r.den.rep), this.ring), this);
    }
    const g = num.gcd(den);
    let [p, q] = [num.exquo(g), den.exquo(g)];
    if (dom.isField) {
      const lc = q.LC();
      if (!dom.isOne(lc)) [p, q] = [new DMP(p.rep.map((c) => dom.quo(c, lc)), this.ring), new DMP(q.rep.map((c) => dom.quo(c, lc)), this.ring)];
    } else if (dom.isNegative(q.LC())) [p, q] = [p.neg(), q.neg()];
    return new DMF(p, q, this);
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

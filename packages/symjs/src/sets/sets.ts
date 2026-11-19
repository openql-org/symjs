// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Parts ported from SymPy (sympy/sets/sets.py, fancysets.py, conditionset.py, powerset.py and
// sympy/sets/handlers/), Copyright (c) SymPy Development Team, BSD-3-Clause.

/**
 * @file Sets (SymPy sets): Interval, FiniteSet, Range, ImageSet,
 * ConditionSet, ProductSet, PowerSet, DisjointUnion, Union, Intersection,
 * Complement, SymmetricDifference, EmptySet, UniversalSet and the standard
 * sets Reals, Rationals, Integers, Naturals, Naturals0 and Complexes. Set
 * operations simplify for real intervals, finite sets with comparable
 * elements, numeric ranges and linear image sets.
 */

import { NotImplementedError } from '../core/errors';
import type { Truth } from '../core/truth';
import type { ExprLike } from '../core/nodes';
import { Add, BoolAtom, Constant, Expr, ExtensionExpr, Float, Fn, Dummy, Mul, Piecewise, Pow, Rational, Rel, S, Special, Sym, WildFunction, impl } from '../core/nodes';
import type { UndefinedFunction } from '../core/undef';
import { isNoMatch, truthAnd } from '../core/truth';
import { add, div, mul, neg, pow, sympify } from '../core/ops';
import { Eq, Ge, Gt, Le, Lt } from '../core/logic';
import { and, not, or } from '../core/boolalg';
import { compareKeys, sortKey } from '../printing/sortkey';
import { at, cast, expectType, first, getOrThrow } from '../core/guard';
import { Max, Min } from '../functions/special/special';
import { isIntegerQ, isNegative, isNonNegative, isPositive, isReal, isZero } from '../core/assumptions';
import { polyCoefficients, rootsDict } from '../polys/poly';
import { fn } from '../functions/elementary/elementary';
import { couldExtractMinusSign } from '../core/ops';
import { callableClass } from '../core/callable';
import { TupleNode } from '../core/containers';
import { LambdaNode } from '../core/lambda';
import { Mod } from '../functions/mod';
import { xreplace } from '../core/traverse';
import { gcdext } from '../ntheory/intutil';
import { gcd } from '../core/numbers';
import { registerRewrite } from '../simplify/rewrite';
import { BasicNode } from '../core/basic';
import { DefinedFunctionCall } from '../core/defun';
import { integerNthroot } from '../core/numberutils';
import { divisors } from '../ntheory/factor';
import { asCoeffAdd, asCoeffMul, asNumerDenom } from '../core/methods';
import { asBoolean, binarySymbols } from '../logic/boolalg';
import { toMpf } from '../core/num';
import { setArgsOrdered } from '../printing/sets';
import { ordered } from '../core/match';
import { iproduct, roundrobin } from '../utilities/iterables';
import { floatToString, precToDps } from '../numeric/mpf';

/** Base class of all sets. */
export abstract class SetExpr extends Expr {
  readonly kind = 'Set' as const;
  /** SymPy's +, - and * on sets denote union, difference and Cartesian product. */
  override add(other: ExprLike): SetExpr { return union(this, cast(sympify(other), SetExpr)); }
  override sub(other: ExprLike): SetExpr { return complement(this, cast(sympify(other), SetExpr)); }
  override mul(other: ExprLike): SetExpr { return productSet(this, cast(sympify(other), SetExpr)); }
  override pow(exponent: ExprLike): SetExpr {
    const n = sympify(exponent);
    if (!(n instanceof Rational && n.isInteger && !n.isNegative)) throw new RangeError('Cartesian powers require a nonnegative integer');
    return productSet(...Array.from({ length: Number(n.p) }, () => this));
  }
  /** Definite membership, as required by the in operator. */
  hasElement(x: Expr): boolean {
    const result = contains(this, x);
    if (result instanceof BoolAtom) return result.value;
    throw new TypeError('cannot determine symbolic set membership');
  }
  abstract get className(): string;
  /** Set order is inclusion, with strict order excluding equality. */
  le(other: SetExpr): Truth { return isSubset(this, other) ?? 'unknown'; }
  ge(other: SetExpr): Truth { return isSubset(other, this) ?? 'unknown'; }
  lt(other: SetExpr): Truth { return this.key === other.key ? false : this.le(other); }
  gt(other: SetExpr): Truth { return this.key === other.key ? false : this.ge(other); }
  /** Whether this set has finitely many elements. */
  get isFiniteSet(): Truth { return 'unknown'; }
  get isEmpty(): boolean {
    return false;
  }
  get isEmptyQ(): Truth { return this.isEmpty; }
  get isIterable(): boolean { return false; }

  /** Topological boundary in the real line. */
  get boundary(): SetExpr { throw new NotImplementedError(`boundary of ${this.className}`); }
  get closure(): SetExpr { return union(this, this.boundary); }
  get interior(): SetExpr { return complement(this, this.boundary); }
  get isClosed(): Truth { return isSubset(this.boundary, this) ?? 'unknown'; }
  get isOpen(): Truth { return isSubset(intersection(this, this.boundary), EmptySet) ?? 'unknown'; }
  /** Lebesgue measure. */
  get measure(): Expr { throw new NotImplementedError(`measure of ${this.className}`); }
  /** A set of the same class with new arguments (the sets of this module are rebuilt by rebuildSet). */
  withArgs(_args: readonly Expr[]): Expr {
    return this;
  }
  /** SymPy Set._contains for the set classes that define it: true, false or 'unknown'. */
  elementOf(_x: Expr): Truth {
    return 'unknown';
  }
  /** SymPy intersection_sets of this class: its intersection with another set, or undefined without a rule. */
  intersectSelf(_other: SetExpr): SetExpr | undefined {
    return undefined;
  }
  /** SymPy union_sets of this class: its union with another set, or undefined when the two do not combine. */
  unionSelf(_other: SetExpr): SetExpr | undefined {
    return undefined;
  }
}

const isNegOo = (e: Expr) => e instanceof Special && e.name === '-oo';
const isOo = (e: Expr) => e instanceof Special && e.name === 'oo';
const isInf = (e: Expr) => isOo(e) || isNegOo(e);

/** Real value for ordering, or undefined when it cannot be decided. */
export function realValue(e: Expr): number | undefined {
  if (isOo(e)) return Infinity;
  if (isNegOo(e)) return -Infinity;
  if (e instanceof Rational || e instanceof Float) return e.value;
  if (e.freeSymbols().size) return undefined;
  try {
    const v = impl.toComplex(e);
    return Math.abs(v.im) > 1e-12 * Math.max(1, Math.abs(v.re)) ? undefined : v.re;
  } catch {
    // a number without a machine evaluation (an indexed root) is evaluated in arbitrary precision
    try {
      const v = impl.evalf(e, 15);
      return v instanceof Float || v instanceof Rational ? v.value : undefined;
    } catch {
      return undefined;
    }
  }
}

/** Compare two real numbers: -1, 0, 1, or undefined when unknown. */
export function cmpReal(a: Expr, b: Expr): number | undefined {
  if (a.key === b.key) return 0;
  if (a instanceof Rational && b instanceof Rational) {
    const d = a.p * b.q - b.p * a.q;
    // equal rationals have equal keys
    return d < 0n ? -1 : 1;
  }
  const x = realValue(a);
  const y = realValue(b);
  if (x === undefined || y === undefined) return undefined;
  const near = x === y || (Number.isFinite(x) && Number.isFinite(y) && Math.abs(x - y) <= 1e-10 * Math.max(1, Math.abs(x), Math.abs(y)));
  if (!near) return x < y ? -1 : 1;
  // equal within rounding (or both too large for a double): the floor and ceiling of the exact
  // difference d decide its sign, else it is not known
  // An odd power is injective on the reals. Expand a small radical's power
  // before asking floor/ceiling to separate algebraically equal expressions.
  const radical = [a, b].find((v) => v instanceof Pow && v.exp instanceof Rational && v.exp.q > 1n && v.exp.q <= 5n && v.exp.q % 2n === 1n);
  if (radical instanceof Pow && radical.exp instanceof Rational && isReal(a) === true && isReal(b) === true &&
      pow(a, radical.exp.q).expand().key === pow(b, radical.exp.q).expand().key) return 0;
  const d = add(a, mul(-1, b));
  const lo = fn('floor', [d]);
  const hi = fn('ceiling', [d]);
  if (lo instanceof Rational && hi instanceof Rational) return lo.p < 0n ? -1 : hi.p > 0n ? 1 : 0;
  return undefined;
}

// ---------------------------------------------------------------------------
// Standard sets
// ---------------------------------------------------------------------------

class NamedSet extends SetExpr {
  override get isFiniteSet(): boolean { return this.name === 'EmptySet'; }
  override get isIterable(): boolean { return ['EmptySet', 'Integers', 'Naturals', 'Naturals0', 'Rationals'].includes(this.name); }
  *elements(): Generator<Expr> {
    if (this === EmptySet) return;
    if (!this.isIterable) throw new TypeError(`${this.name} is not iterable`);
    if (this === Rationals) {
      yield S.Zero;
      yield S.One;
      yield S.NegOne;
      for (let d = 2n; ; d++) {
        for (let n = 1n; n < d; n++) {
          if (gcd(n, d) !== 1n) continue;
          yield Rational.of(n, d);
          yield Rational.of(d, n);
          yield Rational.of(-n, d);
          yield Rational.of(-d, n);
        }
      }
    }
    for (let i = this === Naturals ? 1n : 0n; ; i++) {
      yield Rational.of(i);
      if (this === Integers && i) yield Rational.of(-i);
    }
  }
  override get boundary(): SetExpr {
    if (this.name === 'Reals' || this.name === 'EmptySet' || this.name === 'UniversalSet') return EmptySet;
    if (this.name === 'Rationals') return Reals;
    if (['Integers', 'Naturals', 'Naturals0'].includes(this.name)) return this;
    throw new NotImplementedError(`boundary of ${this.name}`);
  }
  override get measure(): Expr {
    if (this.name === 'Reals') return S.Infinity;
    if (['EmptySet', 'Integers', 'Naturals', 'Naturals0', 'Rationals'].includes(this.name)) return S.Zero;
    throw new NotImplementedError(`measure of ${this.name}`);
  }
  readonly args: readonly Expr[] = [];
  constructor(readonly name: 'Reals' | 'Rationals' | 'Integers' | 'Naturals' | 'Naturals0' | 'Complexes' | 'EmptySet' | 'UniversalSet') {
    super();
  }
  get className(): string {
    return this.name;
  }
  get isEmpty(): boolean {
    return this.name === 'EmptySet';
  }
  /** Openness in the usual real or complex topology (decided for every named set). */
  override get isOpen(): boolean {
    return ['Reals', 'Complexes', 'EmptySet', 'UniversalSet'].includes(this.name);
  }
  protected computeKey(): string {
    return `%${this.name}`;
  }
  printStr(): string {
    return this.name;
  }
}

export const EmptySet = new NamedSet('EmptySet');
export const Reals = new NamedSet('Reals');
export const Rationals = new NamedSet('Rationals');
export const Integers = new NamedSet('Integers');
export const Naturals = new NamedSet('Naturals');
export const Naturals0 = new NamedSet('Naturals0');
export const Complexes = new NamedSet('Complexes');
export const UniversalSet = new NamedSet('UniversalSet');

/** Dispatch iteration to the domain, including the infinite standard number sets. */
function elements(s: SetExpr): Iterable<Expr> {
  if (s instanceof NamedSet) return s.elements();
  if (s instanceof Range || s instanceof FiniteSet || s instanceof ImageSet || s instanceof ProductSetNode || s instanceof SetOp) return s;
  throw new TypeError(`${s.className} is not iterable`);
}

/** The allowed argument counts of an undefined or wildcard function. */
export function nargs(f: UndefinedFunction | WildFunction): SetExpr {
  const arities = f instanceof WildFunction ? f.nargs : f.arity;
  return arities === undefined || isNoMatch(arities) ? Naturals0 : finiteSet(...arities);
}

// ---------------------------------------------------------------------------
// Interval
// ---------------------------------------------------------------------------

export class Interval extends SetExpr {
  override get isFiniteSet(): Truth {
    const order = cmpReal(this.start, this.end);
    return order === undefined ? 'unknown' : order >= 0;
  }
  override get isEmptyQ(): Truth {
    if (isOo(this.end) && isReal(this.start) === true || isNegOo(this.start) && isReal(this.end) === true) return false;
    const width = add(this.end, neg(this.start));
    if (isPositive(width) === true || !this.leftOpen && !this.rightOpen && isNonNegative(width) === true) return false;
    return 'unknown';
  }
  get isLeftUnbounded(): boolean { return isNegOo(this.start); }
  get isRightUnbounded(): boolean { return isOo(this.end); }
  override get boundary(): SetExpr { return finiteSet(...[this.start, this.end].filter((e) => !isInf(e))); }
  override get measure(): Expr { return add(this.end, neg(this.start)); }
  readonly args: readonly Expr[];
  /** SymPy `Interval(a, b, left_open, right_open)` (EmptySet or a point when degenerate). */
  static of(a: ExprLike, b: ExprLike, leftOpen = false, rightOpen = false): SetExpr {
    return interval(a, b, leftOpen, rightOpen);
  }
  /** The numeric endpoints at the requested binary precision (SymPy to_mpi). */
  toMpi(precision = 53): readonly [Expr, Expr] {
    if (!Number.isSafeInteger(precision) || precision < 1) throw new RangeError('Expected positive precision');
    const endpoint = (x: Expr): Expr => {
      if (isInf(x)) return x;
      const n = x instanceof Rational || x instanceof Float ? x : x.evalf(precToDps(precision) + 2);
      if (!(n instanceof Float || n instanceof Rational)) throw new TypeError('Expected a numeric interval endpoint');
      return new Float(toMpf(n, precision), precision);
    };
    return [endpoint(this.start), endpoint(this.end)];
  }
  /** SymPy `Interval.open(a, b)`. */
  static open(a: ExprLike, b: ExprLike): SetExpr {
    return interval(a, b, true, true);
  }
  /** SymPy `Interval.Lopen(a, b)`: open on the left. */
  static Lopen(a: ExprLike, b: ExprLike): SetExpr {
    return interval(a, b, true, false);
  }
  /** SymPy `Interval.Ropen(a, b)`: open on the right. */
  static Ropen(a: ExprLike, b: ExprLike): SetExpr {
    return interval(a, b, false, true);
  }
  /** @internal use Interval.of() */
  constructor(
    readonly start: Expr,
    readonly end: Expr,
    readonly leftOpen: boolean,
    readonly rightOpen: boolean,
  ) {
    super();
    this.args = [start, end, leftOpen ? S.true : S.false, rightOpen ? S.true : S.false];
  }
  get className(): string {
    return 'Interval';
  }
  protected computeKey(): string {
    return `Interval(${this.start.key},${this.end.key},${this.leftOpen},${this.rightOpen})`;
  }
  printStr(p: (e: Expr) => string): string {
    const a = this.start;
    const b = this.end;
    const l = this.leftOpen;
    const r = this.rightOpen;
    let m: string;
    if (isInf(a) && isInf(b)) m = '';
    else if (isInf(a) && !r) m = '';
    else if (isInf(b) && !l) m = '';
    else if (!l && !r) m = '';
    else if (l && r) m = '.open';
    else if (l) m = '.Lopen';
    else m = '.Ropen';
    const endpoint = (e: Expr): string => e instanceof Float ? floatToString(e.mpf, e.prec, false) : p(e);
    return `Interval${m}(${endpoint(a)}, ${endpoint(b)})`;
  }
}

/** Interval(a, b) with open ends; empty or degenerate intervals simplify. */
export function interval(aIn: ExprLike, bIn: ExprLike, leftOpenIn = false, rightOpenIn = false): SetExpr {
  let leftOpen = leftOpenIn;
  let rightOpen = rightOpenIn;
  const a = sympify(aIn);
  const b = sympify(bIn);
  if (isReal(a) === false || isReal(b) === false || isReal(add(b, neg(a))) === false) throw new RangeError('Interval endpoints must be extended real');
  if (typeof leftOpen !== 'boolean' || typeof rightOpen !== 'boolean') throw new NotImplementedError('Interval openness must be a boolean');
  if (isOo(a) || isNegOo(b)) return EmptySet;
  const c = cmpReal(a, b);
  if (c === 1 || c === undefined && isPositive(add(a, neg(b))) === true) return EmptySet;
  if (c === 0) {
    if (leftOpen || rightOpen) return EmptySet;
    return finiteSet(a);
  }
  if (isNegOo(a)) leftOpen = true;
  if (isOo(b)) rightOpen = true;
  if (isNegOo(a) && isOo(b)) return Reals;
  return new Interval(a, b, leftOpen, rightOpen);
}

export const openInterval = (a: ExprLike, b: ExprLike): SetExpr => interval(a, b, true, true);
export const Lopen = (a: ExprLike, b: ExprLike): SetExpr => interval(a, b, true, false);
export const Ropen = (a: ExprLike, b: ExprLike): SetExpr => interval(a, b, false, true);

// ---------------------------------------------------------------------------
// FiniteSet
// ---------------------------------------------------------------------------

export class FiniteSet extends SetExpr {
  override get isFiniteSet(): boolean { return true; }
  override get isIterable(): boolean { return true; }
  override get boundary(): SetExpr { return this; }
  override get measure(): Expr { return S.Zero; }
  readonly args: readonly Expr[];
  /** SymPy `FiniteSet(*elements)` (EmptySet when empty, duplicates removed). */
  static of(...xs: ExprLike[]): SetExpr {
    return finiteSet(...xs);
  }
  /** @internal use FiniteSet.of() */
  constructor(elems: readonly Expr[]) {
    super();
    this.args = [...elems].sort((x, y) => compareKeys(sortKey(x), sortKey(y)));
  }
  get className(): string {
    return 'FiniteSet';
  }
  protected computeKey(): string {
    return `{${this.args.map((a) => a.key).join(',')}}`;
  }
  /** SymPy StrPrinter._print_FiniteSet: {a, b}, or FiniteSet(a, b) when an element contains a FiniteSet. */
  printStr(p: (e: Expr) => string): string {
    const items = this.args.map(p).join(', ');
    return this.args.some(hasFiniteSet) ? `FiniteSet(${items})` : `{${items}}`;
  }
  [Symbol.iterator](): Iterator<Expr> { return this.args[Symbol.iterator](); }
  /** SymPy FiniteSet._eval_rewrite_as_PowerSet: all subsets of the largest member. */
  rewriteAsPowerSet(): SetExpr {
    if (!this.args.includes(EmptySet)) return this;
    const members = this.args.filter((a) => a instanceof FiniteSet);
    const largest = members.sort((a, b) => b.args.length - a.args.length)[0] ?? EmptySet;
    if (BigInt(this.args.length) !== 2n ** BigInt(largest.args.length)) return this;
    return powerset(largest).key === this.key ? PowerSet(largest) : this;
  }
  /** SymPy FiniteSet._eval_powerset: the FiniteSet of all subsets. */
  powerset(): SetExpr {
    let subsets: Expr[][] = [[]];
    for (const x of this.args) subsets = [...subsets, ...subsets.map((t) => [...t, x])];
    return finiteSet(...subsets.map((t) => finiteSet(...t)));
  }
}

const hasFiniteSet = (e: Expr): boolean => e instanceof FiniteSet || e.args.some(hasFiniteSet);

export function finiteSet(...xs: ExprLike[]): SetExpr {
  const m = new Map<string, Expr>();
  for (const x of xs.map(sympify)) m.set(x.key, x);
  return m.size ? new FiniteSet([...m.values()]) : EmptySet;
}

// ---------------------------------------------------------------------------
// Range
// ---------------------------------------------------------------------------

const INVALID_SYMBOLIC = 'Invalid method for symbolic Range';
const hasSymbol = (e: Expr): boolean => e.freeSymbols().size > 0;
const integerOrInf = (e: Expr): boolean => isInf(e) || isIntegerQ(e) === true;
/**
 * The sign of an infinite count (stop - start)/step: oo or -oo, or oo plus finite (integer)
 * terms as SymPy's oo - i; undefined when the count is not known to be infinite.
 */
function infSign(e: Expr): 1 | -1 | undefined {
  const terms = e instanceof Add ? e.args : [e];
  const infs = terms.filter(isInf);
  if (infs.length !== 1 || !terms.every((a) => isInf(a) || isIntegerQ(a) === true)) return undefined;
  return isOo(first(infs)) ? 1 : -1;
}
/** SymPy is_extended_positive of a count. */
const extPositive = (n: Expr): boolean => isPositive(n) === true || infSign(n) === 1;

/**
 * The integers start, start + step, ... below stop (SymPy Range). start or stop may be infinite,
 * and start, stop and step may be symbolic (integer-valued) expressions, as in SymPy:
 * Range(0, n, 1) prints as \text{Range}\left(n\right) and its size, inf and sup are only
 * known when the assumptions tell.
 */
export class Range extends SetExpr {
  override get boundary(): SetExpr { return this; }
  override get isIterable(): boolean {
    const n = this.count();
    return n instanceof Rational && n.isInteger && !n.isNegative && this.args.every((a) => isIntegerQ(a) === true);
  }
  readonly args: readonly Expr[];
  /** SymPy `Range(stop)` or `Range(start, stop, step)` (canonical, with Range(0, 0, 1) when empty). */
  static of(start: ExprLike, stop?: ExprLike, step: ExprLike = 1): SetExpr {
    return range(start, stop, step);
  }
  /** @internal use Range.of() */
  constructor(
    readonly start: Expr,
    readonly stop: Expr,
    readonly step: Expr,
  ) {
    super();
    this.args = [start, stop, step];
  }
  get className(): string {
    return 'Range';
  }
  protected computeKey(): string {
    return `Range(${this.start.key},${this.stop.key},${this.step.key})`;
  }
  /** Known to be empty (the canonical empty Range(0, 0, 1)). */
  get isEmpty(): boolean {
    return this.start.key === this.stop.key;
  }
  /** SymPy is_empty: true, false, or 'unknown' when the assumptions do not tell. */
  get isEmptyQ(): Truth {
    try {
      return isZero(this.size) ?? 'unknown';
    } catch {
      return 'unknown';
    }
  }
  /** SymPy size: the number of elements (oo for an infinite Range); a RangeError when unknown. */
  get size(): Expr {
    if (this.isEmpty) return S.Zero;
    const n = this.count();
    if (infSign(n) !== undefined) return S.Infinity;
    if (isNonNegative(n) === true && this.args.every((a) => isIntegerQ(a) === true)) return impl.abs(fn('floor', [n]));
    throw new RangeError(INVALID_SYMBOLIC);
  }
  *[Symbol.iterator](): Generator<Expr> {
    const size = this.size;
    if (isInf(this.start)) throw new RangeError('Cannot iterate a range with an infinite start');
    if (isOo(size)) {
      for (let x = this.start; ; x = add(x, this.step)) yield x;
    }
    const count = asRat(size).p;
    for (let i = 0n; i < count; i++) yield add(this.start, mul(i, this.step));
  }
  /** SymPy is_finite_set. */
  override get isFiniteSet(): boolean {
    if (isIntegerQ(this.start) === true && isIntegerQ(this.stop) === true) return true;
    return !(this.size instanceof Special);
  }
  /** SymPy reversed: the same elements in the opposite order. */
  get reversed(): Range {
    if (hasSymbol(this) && !(extPositive(this.count()) && this.args.every(integerOrInf))) throw new RangeError('invalid method for symbolic range');
    if (this.isEmpty) return this;
    return new Range(add(this.stop, neg(this.step)), add(this.start, neg(this.step)), neg(this.step));
  }
  /**
   * SymPy r[i] for an integer index (0 and -1 are the ends; another index needs a known size).
   * A RangeError when the Range is symbolic and the element unknown, or the index out of range.
   */
  at(i: number): Expr {
    if (this.isEmpty) throw new RangeError('Range index out of range');
    if (!(this.args.every(integerOrInf) && extPositive(this.count()))) throw new RangeError(INVALID_SYMBOLIC);
    const ooslice = 'cannot slice from the end with an infinite value';
    if (i === 0) {
      if (isInf(this.start)) throw new RangeError(ooslice);
      return this.start;
    }
    if (i === -1) {
      if (isInf(this.stop)) throw new RangeError(ooslice);
      return add(this.stop, neg(this.step));
    }
    const n = this.size;
    const rv = add(i < 0 ? this.stop : this.start, mul(i, this.step));
    if (rv instanceof Special) throw new RangeError(ooslice);
    const val = div(add(rv, neg(this.start)), this.step);
    // (SymPy tests n - val >= 0, which takes r[n] for an element: Range(i, i + 6, 2)[3] is i + 6
    // there; the index must be below the size)
    const rel = infSign(val) !== undefined || (isNonNegative(val) === true && isPositive(add(n, neg(val))) === true);
    if (rel) return rv;
    if (isNonNegative(val) === false || isPositive(add(n, neg(val))) === false) throw new RangeError('Range index out of range');
    throw new RangeError(INVALID_SYMBOLIC);
  }
  /** A slice of the range, with omitted bounds interpreted as in SymPy Range. */
  slice(start?: number, stop?: number, step = 1): Range {
    for (const value of [start, stop, step]) if (value !== undefined && !Number.isSafeInteger(value)) throw new TypeError('slice indices must be integers');
    if (step === 0) throw new RangeError('slice step cannot be zero');
    const size = this.size;
    const stride = mul(step, this.step);
    const empty = (): Range => new Range(S.Zero, S.Zero, S.One);
    const make = (a: Expr, b: Expr): Range => cast(range(a, b, stride), Range);
    if (size instanceof Rational) {
      const n = size.p;
      const lower = step < 0 ? -1n : 0n;
      const upper = step < 0 ? n - 1n : n;
      const clip = (v: number | undefined, fallback: bigint): bigint => {
        if (v === undefined) return fallback;
        const index = BigInt(v);
        const position = index < 0n ? index + n : index;
        return position < lower ? lower : position > upper ? upper : position;
      };
      const a = clip(start, step < 0 ? upper : lower);
      const b = clip(stop, step < 0 ? lower : upper);
      const distance = step > 0 ? b - a : a - b;
      if (distance <= 0n) return empty();
      const magnitude = BigInt(Math.abs(step));
      const count = (distance + magnitude - 1n) / magnitude;
      const endpoint = a + count * BigInt(step);
      return make(add(this.start, mul(Rational.of(a), this.step)), add(this.start, mul(Rational.of(endpoint), this.step)));
    }
    const infinite = 'cannot slice from the end with an infinite value';
    const ambiguous = 'cannot unambiguously re-stride from the end with an infinite value';
    if (isInf(this.start) && isInf(this.stop)) throw new RangeError('slicing not possible on range with infinite start');
    if (isInf(this.stop)) return this.reversed.slice(stop === undefined ? undefined : -stop + 1, start === undefined ? undefined : -start, step).reversed;
    if (start === undefined) {
      if (stop === undefined) {
        if (step < 0) return make(this.at(-1), this.start);
        if (step > 1) throw new RangeError(ambiguous);
        return this;
      }
      if (stop < 0) return make(step < 0 ? this.at(-1) : this.start, this.at(stop));
      if (stop === 0 && step > 0) return empty();
      throw new RangeError(infinite);
    }
    if (start < 0) {
      if (stop === undefined) return make(this.at(start), step < 0 ? this.start : this.stop);
      if (stop < 0) return make(this.at(start), this.at(stop));
      if (stop === 0 && step > 0) return empty();
      throw new RangeError(infinite);
    }
    if (start === 0) {
      if (stop === undefined) {
        if (step < 0) throw new RangeError(infinite);
        if (step > 1) throw new RangeError(ambiguous);
        return this;
      }
      if (stop < 0) {
        if (step > 1) throw new RangeError(ambiguous);
        return step === 1 ? make(this.start, this.at(stop)) : empty();
      }
    }
    throw new RangeError(infinite);
  }
  /** (stop - start)/step. */
  count(): Expr {
    return div(add(this.stop, neg(this.start)), this.step);
  }
  printStr(p: (e: Expr) => string): string {
    return `Range(${p(this.start)}, ${p(this.stop)}, ${p(this.step)})`;
  }
  /**
   * What SymPy's LaTeX (most = 3) and pretty (most = 4) printers show: the elements, all of them
   * up to `most`, else the first two, an ellipsis and the last one (an infinite end is an
   * ellipsis); or, when the elements are unknown, the arguments of SymPy's
   * \text{Range}(...) form: Range(stop), Range(start, stop) when the step is 1, else all three.
   */
  printForm(most: number): { elements: (Expr | 'dots')[] } | { symbolic: Expr[] } {
    const D = 'dots' as const;
    try {
      if (isInf(this.start) && isInf(this.stop)) return { elements: isPositive(this.step) === true ? [D, S.NegOne, S.Zero, S.One, D] : [D, S.One, S.Zero, S.NegOne, D] };
      if (isInf(this.start)) {
        const last = this.at(-1);
        return { elements: [D, add(last, neg(this.step)), last] };
      }
      const n = this.size;
      if (isInf(this.stop)) return { elements: [this.start, add(this.start, this.step), D] };
      if (n instanceof Rational) {
        if (n.p <= BigInt(most)) return { elements: Array.from({ length: Number(n.p) }, (_, k) => add(this.start, mul(k, this.step))) };
        return { elements: [this.start, add(this.start, this.step), D, this.at(-1)] };
      }
    } catch {
      // the elements are unknown
    }
    const one = this.step.key === S.One.key;
    if (this.start.key === S.Zero.key) return { symbolic: one ? [this.stop] : [...this.args] };
    return { symbolic: one ? [this.start, this.stop] : [...this.args] };
  }
}

/** SymPy bool(Range): false when known empty, true when known not empty, a RangeError when unknown. */
function rangeNonEmpty(r: Range): boolean {
  const z = isZero(add(r.stop, neg(r.start)));
  if (z === undefined) throw new RangeError('cannot tell if Range is null or not');
  return !z;
}

/** SymPy Range._inf / _sup (sign 1 / -1) of a nonempty Range. */
function rangeEnd(r: Range, sign: 1 | -1): Expr {
  if (!rangeNonEmpty(r)) throw new NotImplementedError(`(EmptySet)._${sign === 1 ? 'inf' : 'sup'}`);
  const low = (): Expr => (sign === 1 ? r.start : add(r.stop, neg(r.step)));
  const high = (): Expr => (sign === 1 ? add(r.stop, neg(r.step)) : r.start);
  if (hasSymbol(r)) {
    if (r.args.every(integerOrInf)) {
      const dif = add(r.stop, neg(r.start));
      if (isPositive(r.step) === true && isPositive(dif) === true) return low();
      if (isNegative(r.step) === true && isNegative(dif) === true) return high();
    }
    throw new RangeError('invalid method for symbolic range');
  }
  return isPositive(r.step) === true ? low() : high();
}

/** SymPy Range.as_relational(x). */
function rangeAsRelational(r: Range, x: Expr): Expr {
  const a0 = isInf(r.start) ? r.reversed.start : r.start;
  const step = r.step;
  const offset = add(x, neg(a0));
  const residue = Mod(offset, step);
  const inSeq = Eq(step.freeSymbols().size > 0 && Mod.isApplied(residue) && at(residue.args, 1).key === step.key && offset.key !== first(residue.args).key && first(ordered([offset, first(residue.args)])) === offset
    ? new DefinedFunctionCall('Mod', [offset, step], residue.definition) : residue, 0);
  const ints = and(Eq(Mod(a0, 1), 0), Eq(Mod(step, 1), 0));
  const n = r.count();
  if (n instanceof Rational && n.isZero) return S.false;
  if (n instanceof Rational && n.isOne) return and(Eq(x, a0), ints);
  // (an integer is finite: -oo < x < oo holds, as SymPy's Lt evaluates for a finite x)
  const finite = isIntegerQ(x) === true;
  const lower = (lo: Expr): Expr => (isInf(lo) ? (finite ? S.true : Gt(x, lo)) : Ge(x, lo));
  const upper = (hi: Expr): Expr => (isInf(hi) ? (finite ? S.true : Lt(x, hi)) : Le(x, hi));
  let cond: Expr;
  try {
    cond = and(lower(inf(r)), upper(sup(r)));
  } catch {
    const [a, b] = [r.start, add(r.stop, neg(r.step))];
    cond = or(and(Ge(step, 1), lower(a), upper(b)), and(Le(step, -1), isInf(a) ? Lt(x, a) : Le(x, a), isInf(b) ? Lt(b, x) : Ge(x, b)));
  }
  return and(inSeq, ints, cond);
}

/** SymPy Range._contains: true, false, a condition, or undefined (an unevaluated Contains). */
function rangeContains(r: Range, x: Expr): Expr | undefined {
  if (r.isEmpty) return S.false;
  if (isInf(x)) return S.false;
  if (isIntegerQ(x) !== true) return notInteger(x) ? S.false : undefined;
  let n: Expr;
  if (hasSymbol(r)) {
    n = r.count();
    if (!extPositive(n) || !r.args.every(integerOrInf)) return undefined;
  } else n = r.size;
  let ref: Expr;
  if (!isInf(r.start)) ref = r.start;
  else if (!isInf(r.stop)) ref = r.stop;
  else return S.true;
  if (n instanceof Rational && n.isOne) return Eq(x, r.at(0));
  const res = Mod(add(ref, neg(x)), r.step);
  if (res instanceof Rational && res.isZero) {
    if (hasSymbol(r)) return rangeAsRelational(r, x);
    return and(Ge(x, inf(r)), Le(x, sup(r)));
  }
  if (res instanceof Rational && res.isInteger) return S.false;
  return undefined;
}

/**
 * SymPy Range(stop) or Range(start, stop, step): integer (or infinite) start and stop and a nonzero
 * integer (or infinite) step, or symbolic expressions that may be integers. The Range is made
 * canonical as in SymPy: the stop of a numeric Range is the first value not taken, an empty
 * Range is Range(0, 0, 1).
 */
export function range(startIn: ExprLike, stopIn?: ExprLike, stepIn: ExprLike = 1): SetExpr {
  let [start, stop, step] = stopIn === undefined ? [S.Zero, sympify(startIn), sympify(stepIn)] : [sympify(startIn), sympify(stopIn), sympify(stepIn)];
  if (step instanceof Rational && step.isZero) throw new TypeError('Range: step cannot be 0');
  for (const w of [start, stop, step]) {
    if (w instanceof Sym && (w.assumptions.infinite === true || w.assumptions.finite === false)) throw new RangeError('Range requires a finite integer or signed infinity');
    if (isInf(w) || (hasSymbol(w) && isIntegerQ(w) !== false)) continue;
    if (!(w instanceof Rational && w.isInteger)) throw new TypeError('Range: finite arguments to Range must be integers');
  }
  let end: Expr = stop;
  let nul = false;
  if ([start, stop, step].some(hasSymbol)) {
    const dif = add(stop, neg(start));
    const n = div(dif, step);
    if (n instanceof Rational) {
      if (dif instanceof Rational && dif.isZero) nul = true;
      else {
        end = add(start, mul(fn('floor', [n]), step));
        if (dif instanceof Rational) {
          if (isNegative(add(end, neg(stop))) === true) end = add(end, step);
        } else if (isNegative(add(div(end, stop), -1)) === true) end = add(end, step);
      }
    } else if (isNegative(n) === true || infSign(n) === -1) nul = true;
  } else if (isInf(start)) {
    const span = mul(step, add(stop, neg(start)));
    if ((span instanceof Special && span.name === 'nan') || cmpReal(span, S.Zero) !== 1) nul = true;
    else if (step instanceof Rational && isInf(stop) && step.p !== 1n && step.p !== -1n) {
      throw new TypeError(`Range: step size must be ${step.isNegative ? -1 : 1} in this case`);
    }
  } else {
    const oostep = isInf(step);
    if (oostep) step = isOo(step) ? S.One : S.NegOne;
    const n = fn('ceiling', [div(add(stop, neg(start)), step)]);
    if (cmpReal(n, S.Zero) !== 1) nul = true;
    else if (oostep) {
      step = S.One;
      end = add(start, step);
    } else end = add(start, mul(n, step));
  }
  if (nul) return new Range(S.Zero, S.Zero, S.One);
  return new Range(start, end, step);
}

/**
 * The integers of an interval as a Range (SymPy Intersection(Integers, Interval)),
 * or undefined when an end is not a known real number.
 */
function integersIn(iv: Interval, low: Expr): SetExpr | undefined {
  const end = (e0: Expr, open: boolean, up: boolean): Expr | undefined => {
    if (isInf(e0)) return e0;
    // a float with an integer value is that integer
    const e = e0 instanceof Float && Number.isInteger(e0.value) ? Rational.of(BigInt(e0.value)) : e0;
    let n: bigint;
    if (e instanceof Rational) {
      const fl = e.p >= 0n ? e.p / e.q : -((-e.p + e.q - 1n) / e.q);
      n = up ? (e.isInteger ? fl : fl + 1n) : fl;
      if (open && e.isInteger) n += up ? 1n : -1n;
    } else {
      const v = realValue(e);
      // a float end at an integer could be off by one
      if (v === undefined || Math.abs(v - Math.round(v)) < 1e-9) return undefined;
      n = BigInt(up ? Math.ceil(v) : Math.floor(v));
    }
    return Rational.of(n);
  };
  const lo = end(iv.start, iv.leftOpen, true);
  const hi = end(iv.end, iv.rightOpen, false);
  if (!lo || !hi) return undefined;
  const lo2 = cmpReal(lo, low) === -1 ? low : lo;
  const r = range(lo2, hi instanceof Rational ? add(hi, 1) : hi);
  return r.isEmpty ? EmptySet : r;
}

// ---------------------------------------------------------------------------
// ImageSet / ConditionSet
// ---------------------------------------------------------------------------

/** { expr(v) : v in base } (SymPy ImageSet(Lambda(v, expr), base)). */
export class ImageSet extends SetExpr {
  override get isIterable(): boolean { return this.baseSets.every((set) => set.isIterable); }
  /** Construct an ImageSet from the Lambda signature and its corresponding domains. */
  static of(this: void, lambda: LambdaNode, ...sets: SetExpr[]): SetExpr {
    if (!(lambda instanceof LambdaNode)) throw new RangeError('First argument must be a Lambda');
    const vars = lambda.args.slice(0, -1);
    if (vars.length !== sets.length || !sets.length) throw new RangeError('Incompatible ImageSet signature');
    if (sets.some((s) => !(s instanceof SetExpr))) throw new TypeError('ImageSet requires set domains');
    if (sets.some((s) => s.isEmptyQ === true)) return EmptySet;
    if (vars.length === 1 && first(vars).key === lambda.expr.key) return first(sets);
    if (!lambda.variables.some((v) => lambda.expr.has(v)) && sets.every((s) => s.isEmptyQ === false)) return finiteSet(lambda.expr);
    return new ImageSet(vars.length === 1 ? first(vars) : new TupleNode(vars), lambda.expr, first(sets), ...sets.slice(1));
  }
  *[Symbol.iterator](): Generator<Expr> {
    const seen = new Set<string>();
    for (const row of iproduct(...this.baseSets.map(elements))) {
      const value = this.lamda.call(...row);
      if (!seen.has(value.key)) yield value;
      seen.add(value.key);
    }
  }
  get basePset(): SetExpr { return productSet(...this.baseSets); }
  doit(): SetExpr {
    if (this.baseSets.length === 1) return imageSet(this.variable, this.expr, this.base);
    return this.baseSets.every((s) => s instanceof FiniteSet) ? finiteSet(...this) : this;
  }
  override freeSymbols(): Set<Expr> {
    return new Set([...this.lamda.freeSymbols(), ...this.baseSets.flatMap((s) => [...s.freeSymbols()])]);
  }
  asDummy(): ImageSet {
    const reps = this.lamda.canonicalVariables;
    return new ImageSet(xreplace(this.variable, reps), xreplace(this.expr, reps), canonicalSet(first(this.baseSets)), ...this.baseSets.slice(1).map(canonicalSet));
  }

  readonly args: readonly Expr[];
  constructor(
    readonly variable: Expr,
    readonly expr: Expr,
    firstBase: SetExpr,
    ...otherBases: SetExpr[]
  ) {
    super();
    this.domains = [firstBase, ...otherBases];
    this.base = otherBases.length ? productSet(...this.baseSets) : firstBase;
    this.args = [variable, expr, ...this.baseSets];
  }
  get className(): string {
    return 'ImageSet';
  }
  /** SymPy ImageSet.lamda: the mapping as a Lambda. */
  get lamda(): LambdaNode {
    const vars = this.baseSets.length > 1 ? this.variable.args : [this.variable];
    return new LambdaNode([...vars, this.expr]);
  }
  /** SymPy ImageSet.base_sets. */
  get baseSets(): SetExpr[] { return [...this.domains]; }
  private readonly domains: readonly SetExpr[];
  readonly base: SetExpr;
  protected computeKey(): string {
    return `ImageSet(${this.variable.key},${this.expr.key},${this.baseSets.map((s) => s.key).join(',')})`;
  }
  printStr(p: (e: Expr) => string): string {
    return `ImageSet(Lambda(${p(this.variable)}, ${p(this.expr)}), ${this.baseSets.map(p).join(', ')})`;
  }
}

function canonicalSet(s: SetExpr): SetExpr {
  return s instanceof ImageSet || s instanceof ConditionSet || s instanceof SetOp ? s.asDummy() : s;
}

/** { v in base : condition } (SymPy ConditionSet). */
export class ConditionSet extends SetExpr {
  readonly args: readonly Expr[];
  constructor(
    readonly variable: Expr,
    readonly condition: Expr,
    readonly base: SetExpr,
  ) {
    super();
    this.args = [variable, condition, base];
  }
  get className(): string {
    return 'ConditionSet';
  }
  /** SymPy ConditionSet.sym. */
  get sym(): Expr {
    return this.variable;
  }
  /** SymPy ConditionSet.base_set. */
  get baseSet(): SetExpr {
    return this.base;
  }
  get boundSymbols(): Expr[] { return this.predicate.variables; }
  private get predicate(): LambdaNode { return new LambdaNode([this.variable, this.condition]); }
  override freeSymbols(): Set<Expr> {
    return new Set([...this.predicate.freeSymbols(), ...this.base.freeSymbols()]);
  }
  asDummy(): ConditionSet {
    const reps = this.predicate.canonicalVariables;
    return new ConditionSet(xreplace(this.variable, reps), xreplace(this.condition, reps), canonicalSet(this.base));
  }
  membership(x: Expr): Expr {
    if (!sameSignature(this.variable, x)) return S.false;
    const inBase = containsQ(this.base, x);
    if (inBase === false) return S.false;
    try {
      const predicate = this.predicate.call(x);
      return inBase === true ? predicate : and(new Contains(x, this.base), predicate);
    } catch (error) {
      if (!(error instanceof TypeError)) throw error;
      return new Contains(x, this);
    }
  }
  override elementOf(x: Expr): Truth {
    const result = this.membership(x);
    return result === S.true ? true : result === S.false ? false : 'unknown';
  }
  /** SymPy ConditionSet(sym, condition, base) with the evaluation of its constructor. */
  static of(sym: Expr, condition: ExprLike | boolean, base: SetExpr = UniversalSet): SetExpr {
    return conditionSet(sym, condition, base);
  }
  protected computeKey(): string {
    return `ConditionSet(${this.variable.key},${this.condition.key},${this.base.key})`;
  }
  printStr(p: (e: Expr) => string): string {
    return `ConditionSet(${p(this.variable)}, ${p(this.condition)}, ${p(this.base)})`;
  }
}

/**
 * SymPy imageset(Lambda(v, expr), base): the image is evaluated for a finite
 * set, a union, an interval and a polynomial, a linear map of the integers
 * (in SymPy's canonical form) and a composition of image sets; otherwise an
 * ImageSet.
 */
export function imageSet(v: Expr, exprIn: ExprLike, base: SetExpr): SetExpr {
  const expr = sympify(exprIn);
  const r = setFunction(v, expr, base);
  if (r !== undefined && !(r instanceof ImageSet)) return r;
  const [v2, e2, b2] = r instanceof ImageSet ? [r.variable, r.expr, r.base] : [v, expr, base];
  if (v2.key === e2.key) return b2;
  // a composition: f(g(x)) for x in the base set of g
  if (b2 instanceof ImageSet) return imageSet(b2.variable, e2.subs([[v2, b2.expr]]), b2.base);
  return r ?? new ImageSet(v2, e2, b2);
}

/** SymPy _set_function(Lambda(v, expr), base), or undefined when it does not apply. */
function setFunction(v: Expr, expr: Expr, base: SetExpr): SetExpr | undefined {
  if (base === EmptySet) return EmptySet;
  if (base instanceof FiniteSet) return finiteSet(...base.args.map((a) => v instanceof TupleNode ? new LambdaNode([v, expr]).call(a) : expr.subs([[v, a]])));
  if (base instanceof Range && v instanceof Sym) {
    const linear = linearIn(expr, v);
    if (linear) {
      const n = base.size;
      if (n instanceof Rational) {
        const start = linear[0].mul(base.start).add(linear[1]).expand();
        return new ImageSet(v, add(start, mul(v, linear[0], base.step)), range(0, n));
      }
    }
  }
  if (base instanceof SetOp && base.op === 'Union') return union(...base.args.map((a) => imageSet(v, expr, a)));
  // a constant on a set that is not empty
  const standard: readonly SetExpr[] = [Integers, Naturals, Naturals0, Reals, Rationals, Complexes];
  const nonEmpty = standard.includes(base) || (base instanceof Interval && cmpReal(base.start, base.end) === -1);
  if (nonEmpty && v instanceof Sym && ![...expr.freeSymbols()].some((u) => u.key === v.key)) return finiteSet(expr);
  if ((base === Naturals || base === Naturals0) && v instanceof Sym) {
    const coefficients = polyCoefficients(expr, v);
    const slope = coefficients?.get(1);
    if (coefficients && [...coefficients.keys()].every((degree) => degree <= 1) && slope instanceof Rational && slope.isInteger && !slope.isZero) {
      const offset = coefficients.get(0) ?? S.Zero;
      if (isIntegerQ(offset) === true) return range(add(offset, base === Naturals ? slope : S.Zero), slope.isPositive ? S.Infinity : S.NegativeInfinity, slope);
    }
  }
  if (base === Integers && v instanceof Sym) return integersImage(v, expr);
  if (base === Reals && v instanceof Sym) return intervalImage(v, expr, new Interval(S.NegativeInfinity, S.Infinity, true, true));
  if (base instanceof Interval && v instanceof Sym) return intervalImage(v, expr, base);
  return undefined;
}

/** SymPy match_real_imag for a number: (re, im) with b = re + I*im, or undefined. */
function matchRealImag(b: Expr): [Expr, Expr] | undefined {
  const terms = b instanceof Add ? b.args : [b];
  const hasI = (t: Expr): boolean => t.key === S.I.key || t.args.some(hasI);
  const re = add(...terms.filter((t) => !hasI(t)));
  const im = mul(add(...terms.filter(hasI)), mul(-1, S.I));
  if (isReal(re) !== true || (!isZ(im) && isReal(im) !== true)) return undefined;
  return [re, im];
}

const isComparable = (e: Expr): boolean => realValue(e) !== undefined && Number.isFinite(realValue(e));
const hasFloat = (e: Expr): boolean => e instanceof Float || e.args.some(hasFloat);

/**
 * SymPy _set_function(Lambda, Integers): |n| maps onto Naturals0, and a
 * linear a*n + b is put in canonical form (the sign of n with fewer
 * negative terms, b reduced modulo a).
 */
function integersImage(n: Sym, expr0: Expr): SetExpr | undefined {
  if (expr0.key === fn('abs', [n]).key) return Naturals0;
  let expr = expr0;
  const c = expr.subs([[n, S.Zero]]);
  const fx = add(expr, mul(-1, c));
  const fmx = add(expr.subs([[n, mul(-1, n)]]), mul(-1, c));
  const negCount = (e: Expr): number => (e instanceof Add ? e.args : [e]).filter(couldExtractMinusSign).length;
  if (negCount(fmx) < negCount(fx)) expr = add(fmx, c);
  // SymPy matches expr against a*n + b structurally: each term is free of n or a product with the
  // factor n itself, so I*(2*n*pi + pi) (a product holding a sum) is left as it is
  const linearTerm = (t: Expr): boolean => !t.has(n) || t.key === n.key || (t instanceof Mul && t.args.filter((f) => f.has(n)).length === 1 && t.args.some((f) => f.key === n.key));
  const pc = (expr instanceof Add ? expr.args : [expr]).every(linearTerm) ? polyCoefficients(expr, n) : undefined;
  if (pc && [...pc.keys()].every((d) => d <= 1) && pc.has(1)) {
    // the coefficients are free of n
    const a = getOrThrow(pc, 1);
    let b = pc.get(0) ?? S.Zero;
    if (!hasFloat(a) && !hasFloat(b)) {
      if (a.key === S.One.key || a.key === S.NegOne.key) b = add(...(b instanceof Add ? b.args : [b]).filter((t) => isIntegerQ(t) !== true));
      const ri = b.freeSymbols().size ? undefined : matchRealImag(b);
      if (ri && isComparable(a)) {
        const [br, bi] = ri;
        if (!isZ(br) && isComparable(br)) b = add(Mod(br, a), mul(S.I, bi));
      } else if (ri && isComparable(mul(a, mul(-1, S.I)))) {
        const [br, bi] = ri;
        const ai = mul(a, mul(-1, S.I));
        if (!isZ(bi) && isComparable(bi)) b = add(br, mul(S.I, Mod(bi, ai)));
      }
      expr = add(mul(a, n), b);
    }
  }
  return expr.key === expr0.key ? undefined : new ImageSet(n, expr, Integers);
}

/**
 * SymPy _set_function(Lambda, Interval) for a polynomial with real numeric
 * coefficients: the interval between the least and greatest of the values
 * at the ends and at the critical points inside. An end is open unless the
 * extreme value is attained (at a closed finite end or an inner critical
 * point); SymPy decides this by comparing values with critical points,
 * which can close an end that is not attained.
 */
function intervalImage(v: Sym, expr: Expr, iv: Interval): SetExpr | undefined {
  if (expr instanceof Piecewise) {
    let available: SetExpr = iv;
    const images: SetExpr[] = [];
    for (const [value, condition] of expr.pairs) {
      let part = available;
      if (condition !== S.true) {
        if (!(condition instanceof Rel) || condition.lhs.key !== v.key || condition.rhs.has(v)) return undefined;
        const b = condition.rhs;
        const domains = { Lt: () => interval(S.NegativeInfinity, b, true, true), Le: () => interval(S.NegativeInfinity, b),
          Gt: () => interval(b, S.Infinity, true, true), Ge: () => interval(b, S.Infinity), Eq: () => finiteSet(b), Ne: () => complement(Reals, finiteSet(b)) };
        part = intersection(available, domains[condition.op]());
      }
      images.push(imageSet(v, value, part));
      available = complement(available, part);
      if (available === EmptySet) break;
    }
    return union(...images);
  }
  const pc = polyCoefficients(expr, v);
  if (!pc) return rationalIntervalImage(v, expr, iv);
  if (![...pc.values()].every((c) => !c.freeSymbols().size && isComparable(c))) return undefined;
  const deg = Math.max(...pc.keys());
  if (deg < 1) return undefined;
  const lead = getOrThrow(pc, deg);
  const candidates: { value: Expr; attained: boolean }[] = [];
  const endValue = (e: Expr, open: boolean, sign: 1 | -1): void => {
    if (isInf(e)) {
      // the limit of the polynomial at +-oo: the sign of its leading term
      const pos = (cmpReal(lead, S.Zero) === 1) === (sign === 1 || deg % 2 === 0);
      candidates.push({ value: pos ? S.Infinity : S.NegativeInfinity, attained: false });
    } else candidates.push({ value: expr.subs([[v, e]]), attained: !open });
  };
  endValue(iv.start, iv.leftOpen, -1);
  endValue(iv.end, iv.rightOpen, 1);
  if (deg > 1) {
    const d = add(...[...pc].filter(([k]) => k > 0).map(([k, c]) => mul(k, c, pow(v, k - 1))));
    let rs: Expr[];
    try {
      rs = rootsDict(d, v, { multiple: true });
    } catch {
      return undefined;
    }
    // (roots finds every critical point, or throws)
    for (const r of rs) {
      if (isReal(r) !== true) continue;
      if (containsQ(iv, r) === true) candidates.push({ value: expr.subs([[v, r]]), attained: true });
    }
  }
  const pick = (sign: 1 | -1): [Expr, boolean] | undefined => {
    let best = first(candidates).value;
    for (const c of candidates) {
      const k = cmpReal(c.value, best);
      if (k === undefined) return undefined;
      if (k * sign < 0) best = c.value;
    }
    return [best, candidates.some((c) => c.attained && cmpReal(c.value, best) === 0)];
  };
  const lo = pick(1);
  const hi = pick(-1);
  if (!lo || !hi) return undefined;
  return interval(lo[0], hi[0], !lo[1], !hi[1]);
}

/** Real rational images on the components between poles and stationary points. */
function rationalIntervalImage(v: Sym, expr: Expr, iv: Interval): SetExpr | undefined {
  const [p, q] = asNumerDenom(expr);
  if (!q.has(v) || !polyCoefficients(p, v) || !polyCoefficients(q, v)) return undefined;
  if ([...expr.freeSymbols()].some((x) => x.key !== v.key) || iv.freeSymbols().size) return undefined;
  try {
    const poles = rootsDict(q, v, { multiple: true });
    const derivative = add(mul(p.diff(v), q), neg(mul(p, q.diff(v)))).expand();
    const critical = rootsDict(derivative, v, { multiple: true });
    const inside = openInterval(iv.start, iv.end);
    const cuts = [...new Map([...poles, ...critical].filter((x) => isReal(x) === true && containsQ(inside, x) === true).map((x) => [x.key, x])).values()];
    cuts.sort((a, b) => expectType(cmpReal(a, b), (k): k is number => typeof k === 'number', 'ordered real critical points'));
    const endpoints = [iv.start, ...cuts, iv.end];
    const images = endpoints.slice(1).map((hi, i) => {
      const lo = at(endpoints, i);
      const singular = (x: Expr): boolean => isInf(x) || poles.some((r) => r.key === x.key);
      const left = singular(lo) ? expr.limit(v, lo, '+') : expr.subs([[v, lo]]);
      const right = singular(hi) ? expr.limit(v, hi, '-') : expr.subs([[v, hi]]);
      const leftOpen = singular(lo) || i === 0 && iv.leftOpen;
      const rightOpen = singular(hi) || hi.key === iv.end.key && iv.rightOpen;
      const order = cmpReal(left, right);
      if (order === undefined) throw new NotImplementedError('Cannot order rational image endpoints');
      return order <= 0 ? interval(left, right, leftOpen, rightOpen) : interval(right, left, rightOpen, leftOpen);
    });
    return union(...images);
  } catch {
    return undefined;
  }
}

function sameSignature(a: Expr, b: Expr): boolean {
  if (!(a instanceof TupleNode)) return !(b instanceof TupleNode);
  return b instanceof TupleNode && a.args.length === b.args.length && a.args.every((v, i) => sameSignature(v, at(b.args, i)));
}

/**
 * SymPy ConditionSet(sym, condition, base) with its evaluation: a true
 * condition gives the base set and a false one the empty set, a finite base
 * set is filtered, and a nested ConditionSet is merged.
 */
export function conditionSet(symIn: Expr, conditionIn: ExprLike | boolean, baseIn: SetExpr = UniversalSet): SetExpr {
  let sym = symIn;
  let base = baseIn;
  let condition: Expr = typeof conditionIn === 'boolean' ? (conditionIn ? S.true : S.false) : sympify(conditionIn);
  if (!(base instanceof SetExpr)) throw new TypeError('ConditionSet requires a set domain');
  if (condition instanceof FiniteSet) condition = and(...condition.args.map((e) => Eq(e, 0)));
  else if (!(condition instanceof Contains)) condition = asBoolean(condition);
  if (condition === S.true) return base;
  if (condition === S.false || base === EmptySet) return EmptySet;
  const predicate = new LambdaNode([sym, condition]);
  if (base instanceof ConditionSet && !sameSignature(sym, base.variable)) throw new TypeError('Incompatible ConditionSet signatures');
  if (base instanceof Interval && contains(base, sym) === S.false) throw new TypeError('ConditionSet symbol lies outside the domain');
  let know: SetExpr | undefined;
  if (base instanceof FiniteSet) {
    const yes: Expr[] = [];
    const maybe: Expr[] = [];
    for (const a of base.args) {
      if (condition instanceof Rel && !['Eq', 'Ne'].includes(condition.op) && isReal(a) === undefined &&
        ((condition.lhs.key === sym.key && condition.rhs.key === a.key) || (condition.rhs.key === sym.key && condition.lhs.key === a.key))) {
        maybe.push(a);
        continue;
      }
      const c = sameSignature(sym, a) ? predicate.call(a) : S.false;
      if (c === S.true) yes.push(a);
      else if (c !== S.false) maybe.push(a);
    }
    if (!maybe.length) return finiteSet(...yes);
    know = finiteSet(...yes);
    base = finiteSet(...maybe);
  }
  if (base instanceof ConditionSet) {
    const { variable: s, condition: c, base: b } = base;
    const innerVars = base.boundSymbols;
    const outerVars = predicate.variables;
    const overlaps = (expr: Expr, variable: Expr): boolean => {
      const names = new Set([...variable.freeSymbols()].map((v) => v.key));
      return [...expr.freeSymbols()].some((v) => names.has(v.key));
    };
    if (s.key === sym.key) {
      condition = and(condition, c);
      base = b;
    } else if (!overlaps(c, sym)) {
      condition = and(condition, xreplace(c, innerVars.map((v, i) => [v, at(outerVars, i)])));
      base = b;
    } else if (!overlaps(condition, s)) {
      condition = and(xreplace(condition, outerVars.map((v, i) => [v, at(innerVars, i)])), c);
      sym = s;
      base = b;
    }
  }
  // ConditionSet(x, Contains(x, A), B) is A & B
  if (condition instanceof Contains && condition.element.key === sym.key) return intersection(condition.set, base);
  const rv = new ConditionSet(sym, condition, base);
  return know === undefined ? rv : union(know, rv);
}

// ---------------------------------------------------------------------------
// Union / Intersection / Complement
// ---------------------------------------------------------------------------

class SetOp extends SetExpr {
  asDummy(): SetOp { return new SetOp(this.op, this.args.map(canonicalSet)); }
  *[Symbol.iterator](): Generator<Expr> {
    if (this.op === 'Union') {
      yield* roundrobin(...this.args.map(elements));
      return;
    }
    const source = this.op === 'Complement' ? first(this.args) : this.args.find((s) => s.isIterable);
    if (!source) throw new TypeError('Intersection needs an iterable operand');
    for (const x of elements(source)) if (this.hasElement(x)) yield x;
  }
  /** SymPy: a Union of iterable sets, an Intersection with an iterable set and a Complement of an iterable set iterate. */
  override get isIterable(): boolean {
    if (this.op === 'Union') return this.args.every((s) => s.isIterable);
    if (this.op === 'Intersection') return this.args.some((s) => s.isIterable);
    return first(this.args).isIterable;
  }
  override get isEmptyQ(): Truth {
    const values = this.args.map((s) => s.isEmptyQ);
    if (this.op === 'Union') return values.every((v) => v === true) ? true : values.includes(false) ? false : 'unknown';
    return 'unknown';
  }
  override get boundary(): SetExpr {
    if (this.op !== 'Union') return super.boundary;
    return complement(union(...this.args.map((s) => s.boundary)), union(...this.args.map((s) => s.interior)));
  }
  override get isFiniteSet(): Truth {
    const values = this.args.map((s) => s.isFiniteSet);
    if (this.op === 'Union') return truthAnd(...values);
    if (this.op === 'Intersection') return values.includes(true) ? true : 'unknown';
    const a = at(values, 0);
    return a === true ? true : a === false && at(values, 1) === true ? false : 'unknown';
  }
  override get measure(): Expr {
    if (this.op !== 'Union') throw new NotImplementedError(`measure of ${this.op}`);
    // Inclusion-exclusion also handles intervals whose overlap is symbolic.
    const a = first(this.args);
    const b = union(...this.args.slice(1));
    return add(a.measure, b.measure, neg(intersection(a, b).measure));
  }
  readonly args: readonly SetExpr[];
  /** Union and Intersection keep their arguments in canonical order, also unevaluated (SymPy orders them in __new__). */
  constructor(
    readonly op: 'Union' | 'Intersection' | 'Complement',
    args: readonly SetExpr[],
  ) {
    super();
    this.args = op === 'Complement' ? args : op === 'Union' ? setArgsOrdered(args).map((s) => cast(s, SetExpr)) : sortSets([...args]);
  }
  get className(): string {
    return this.op;
  }
  protected computeKey(): string {
    return `${this.op}(${this.args.map((a) => a.key).join(',')})`;
  }
  printStr(p: (e: Expr) => string): string {
    const args = this.op === 'Union' ? sortSets([...this.args]) : this.args;
    return `${this.op}(${args.map(p).join(', ')})`;
  }
}
export { SetOp };

// ---------------------------------------------------------------------------
// ProductSet / PowerSet / DisjointUnion / SymmetricDifference
// ---------------------------------------------------------------------------

/** Cardinality for sets with an explicit finite length. */
function finiteLength(s: SetExpr): number {
  if (s === EmptySet) return 0;
  if (s instanceof FiniteSet) return s.args.length;
  if (s instanceof Range && s.isIterable) return Number(asRat(s.size).p);
  if (s instanceof ProductSetNode || s instanceof PowerSetNode || s instanceof DisjointUnionNode) return s.length;
  throw new TypeError(`Cannot determine a finite length for ${s.className}`);
}

/** The Cartesian product of sets (SymPy ProductSet); its elements are Tuples. */
export class ProductSetNode extends SetExpr {
  override get isEmptyQ(): Truth {
    const values = this.args.map((s) => s.isEmptyQ);
    return values.includes(true) ? true : values.every((v) => v === false) ? false : 'unknown';
  }
  get length(): number {
    return this.args.reduce((n, s) => n * finiteLength(s), 1);
  }
  override get measure(): Expr { return mul(...this.args.map((s) => s.measure)); }
  override get isIterable(): boolean { return this.args.every((s) => s.isIterable); }
  *[Symbol.iterator](): Generator<Expr> {
    for (const row of iproduct(...this.args.map(elements))) yield new TupleNode(row);
  }
  override get boundary(): SetExpr {
    return union(...this.args.map((_, i) => productSet(...this.args.map((s, j) => i === j ? s.boundary : s.closure))));
  }
  override get isFiniteSet(): Truth {
    if (this.args.some((s) => s.isEmpty || (s instanceof FiniteSet && s.args.length === 0))) return true;
    const values = this.args.map((s) => s.isFiniteSet);
    if (values.every((v) => v === true)) return true;
    const nonempty = this.args.every((s, i) => at(values, i) === false
      || s instanceof FiniteSet
      || s instanceof PowerSetNode
      || (s instanceof Range && s.isEmptyQ === false));
    return values.includes(false) && nonempty ? false : 'unknown';
  }
  constructor(readonly args: readonly SetExpr[]) {
    super();
  }
  get className(): string {
    return 'ProductSet';
  }
  /** SymPy ProductSet.sets. */
  get sets(): SetExpr[] {
    return [...this.args];
  }
  protected computeKey(): string {
    return `ProductSet(${this.args.map((a) => a.key).join(',')})`;
  }
  printStr(p: (e: Expr) => string): string {
    return `ProductSet(${this.args.map(p).join(', ')})`;
  }
  /** SymPy LatexPrinter._print_ProductSet: A \\times B, or A^{n} for a power of one set. */
  printLatex(p: (e: Expr) => string): string {
    const paren = (s: SetExpr): string => (s instanceof SetOp || s instanceof SymmetricDifferenceNode || s instanceof ProductSetNode ? `\\left(${p(s)}\\right)` : p(s));
    if (this.args.every((s) => s.key === first(this.args).key)) return `${paren(first(this.args))}^{${this.args.length}}`;
    return this.args.map(paren).join(' \\times ');
  }
  /** SymPy ProductSet.flatten: nested products as one product. */
  flatten(): SetExpr {
    const go = (xs: readonly SetExpr[]): SetExpr[] => xs.flatMap((x) => (x instanceof ProductSetNode ? go(x.args) : [x]));
    return productSet(...go(this.args));
  }
  /** SymPy ProductSet._contains: a Tuple of as many elements, each in its set. */
  override elementOf(x: Expr): Truth {
    if (x instanceof Sym) return 'unknown';
    if (!(x instanceof TupleNode) || x.args.length !== this.args.length) return false;
    const cs = this.args.map((s, i) => containsQ(s, at(x.args, i)));
    return cs.every((c) => c === true) ? true : cs.some((c) => c === false) ? false : 'unknown';
  }
}

/** SymPy ProductSet(*sets): the empty product is {()}, and a product with an empty factor is empty. */
export function productSet(...sets: SetExpr[]): SetExpr {
  if (!sets.length) return finiteSet(new TupleNode([]));
  if (sets.some((x) => x === EmptySet)) return EmptySet;
  return new ProductSetNode(sets);
}

/** SymPy ProductSet(A, B, ...). */
export const ProductSet = /* @__PURE__ */ callableClass(ProductSetNode, productSet);
export type ProductSet = ProductSetNode;

/** The set of all subsets of a set (SymPy PowerSet). */
export class PowerSetNode extends SetExpr {
  /** Number of subsets of an explicitly finite base set. */
  get length(): number {
    return 2 ** finiteLength(this.arg);
  }
  override get isFiniteSet(): Truth { return this.arg.isFiniteSet; }
  readonly args: readonly Expr[];
  constructor(readonly arg: SetExpr) {
    super();
    if (!(arg instanceof SetExpr)) throw new RangeError('PowerSet base must be a set');
    this.args = [arg];
  }
  get className(): string {
    return 'PowerSet';
  }
  protected computeKey(): string {
    return `PowerSet(${this.arg.key})`;
  }
  printStr(p: (e: Expr) => string): string {
    return `PowerSet(${p(this.arg)})`;
  }
  /** SymPy LatexPrinter._print_PowerSet. */
  printLatex(p: (e: Expr) => string): string {
    return `\\mathcal{P}\\left(${p(this.arg)}\\right)`;
  }
  /** SymPy PowerSet._contains: a set is an element when it is a subset of the argument. */
  override elementOf(x: Expr): Truth {
    return x instanceof SetExpr ? tri(isSubset(x, this.arg)) : 'unknown';
  }
  /** SymPy PowerSet.rewrite(FiniteSet): the subsets of a finite set. */
  rewriteAsFiniteSet(): SetExpr {
    return this.arg instanceof FiniteSet || this.arg === EmptySet ? powerset(this.arg) : this;
  }
}

/** SymPy PowerSet(A): unevaluated (use powerset(A) or rewriteAsFiniteSet for the subsets of a finite set). */
export const PowerSet = /* @__PURE__ */ callableClass(PowerSetNode, (s: SetExpr): PowerSetNode => new PowerSetNode(s));
export type PowerSet = PowerSetNode;

/** SymPy Set.powerset(): the subsets of a finite set, {EmptySet} for the empty set, otherwise PowerSet(s). */
export function powerset(s: SetExpr): SetExpr {
  if (s === EmptySet) return finiteSet(EmptySet);
  if (s instanceof FiniteSet) return s.powerset();
  return new PowerSetNode(s);
}

/** The disjoint union of sets: the pairs (element, index of its set) (SymPy DisjointUnion). */
export class DisjointUnionNode extends SetExpr {
  override get isIterable(): boolean { return !this.isEmpty && this.args.every((s) => s.isEmpty || s.isIterable); }
  override get isFiniteSet(): Truth { return truthAnd(...this.args.map((s) => s.isFiniteSet)); }
  get length(): number {
    return this.args.reduce((count, s) => count + finiteLength(s), 0);
  }
  constructor(readonly args: readonly SetExpr[]) {
    super();
    if (args.some((s) => !(s instanceof SetExpr))) throw new TypeError('DisjointUnion requires sets');
  }
  get className(): string {
    return 'DisjointUnion';
  }
  /** SymPy DisjointUnion.sets. */
  get sets(): SetExpr[] {
    return [...this.args];
  }
  get isEmpty(): boolean {
    return this.args.every((a) => a.isEmpty);
  }
  protected computeKey(): string {
    return `DisjointUnion(${this.args.map((a) => a.key).join(',')})`;
  }
  printStr(p: (e: Expr) => string): string {
    return `DisjointUnion(${this.args.map(p).join(', ')})`;
  }
  /** SymPy's LaTeX form (the default function form). */
  printLatex(p: (e: Expr) => string): string {
    return `\\operatorname{DisjointUnion}\\left(${this.args.map(p).join(', ')}\\right)`;
  }
  /** SymPy DisjointUnion.rewrite(Union): the union of the products (set_i x {i}). */
  rewriteAsUnion(): SetExpr {
    return this.args.reduce<SetExpr>((acc, s, i) => union(acc, productSet(s, finiteSet(i))), EmptySet);
  }
  /** SymPy DisjointUnion._contains: a pair (x, i) with x in the i-th set. */
  override elementOf(x: Expr): Truth {
    if (!(x instanceof TupleNode) || x.args.length !== 2) return false;
    const i = at(x.args, 1);
    if (!(i instanceof Rational && i.isInteger) || i.p < 0n || i.p >= BigInt(this.args.length)) return false;
    return tri(containsQ(at(this.args, Number(i.p)), at(x.args, 0)));
  }
}

/** SymPy DisjointUnion(A, B, ...). */
export const DisjointUnion = /* @__PURE__ */ callableClass(DisjointUnionNode, (...sets: SetExpr[]): DisjointUnionNode => new DisjointUnionNode(sets));
export type DisjointUnion = DisjointUnionNode;

/** The elements in exactly one of two sets, unevaluated (SymPy SymmetricDifference(a, b, evaluate=False)). */
export class SymmetricDifferenceNode extends SetExpr {
  constructor(readonly args: readonly SetExpr[]) {
    super();
  }
  get className(): string {
    return 'SymmetricDifference';
  }
  protected computeKey(): string {
    return `SymmetricDifference(${this.args.map((a) => a.key).join(',')})`;
  }
  printStr(p: (e: Expr) => string): string {
    return `SymmetricDifference(${this.args.map(p).join(', ')})`;
  }
  override elementOf(x: Expr): Truth {
    const [a, b] = this.args.map((s) => containsQ(s, x));
    return a === undefined || b === undefined ? 'unknown' : a !== b;
  }
}

/**
 * SymPy SymmetricDifference(a, b) (a.symmetric_difference(b)): (a \ b) | (b \ a),
 * and a itself when b is empty; unevaluated with `evaluate: false`.
 * SymPy gives b for UniversalSet.symmetric_difference(b), which is wrong
 * (U ^ B is U \ B); the complement is kept here.
 */
export function symmetricDifference(a: SetExpr, b: SetExpr, opts: { evaluate?: boolean } = {}): SetExpr {
  if (opts.evaluate === false) return new SymmetricDifferenceNode([a, b]);
  if (b === EmptySet) return a;
  if (a === EmptySet) return b;
  return union(complement(b, a), complement(a, b));
}

/** SymPy SymmetricDifference(A, B). */
export const SymmetricDifference = /* @__PURE__ */ callableClass(SymmetricDifferenceNode, symmetricDifference);
export type SymmetricDifference = SymmetricDifferenceNode;

const sortSets = (xs: SetExpr[]): SetExpr[] => [...xs].sort((a, b) => compareKeys(sortKey(a), sortKey(b)));

/** Is x known not to be an integer (by its assumptions, or as a real number away from the integers)? */
function notInteger(x: Expr): boolean {
  if (isIntegerQ(x) === false) return true;
  const v = x.freeSymbols().size ? undefined : realValue(x);
  return v !== undefined && Math.abs(v - Math.round(v)) > 1e-9;
}

const IRRATIONAL = new Set(['pi', 'E', 'GoldenRatio', 'TribonacciConstant']);

/** Does the set contain x? true/false, or undefined when undecidable. */
export function containsQ(s: SetExpr, x: Expr): boolean | undefined {
  if (s === EmptySet) return false;
  if (s === UniversalSet) return true;
  if (s === Complexes && x instanceof TupleNode) {
    if (x.args.length !== 2) throw new RangeError('expecting Tuple of length 2');
    const parts = x.args.map((a) => containsQ(Reals, a));
    return parts.includes(false) ? false : parts.every((a) => a === true) ? true : undefined;
  }
  const numericDomain = s instanceof NamedSet || s instanceof Interval;
  if (numericDomain && ((x instanceof ExtensionExpr && !x.isScalar) || x instanceof BasicNode || x instanceof SetExpr || x instanceof TupleNode || x instanceof BoolAtom)) return false;
  if (s === Rationals) {
    if (x instanceof Rational || isIntegerQ(x) === true) return true;
    // oo, I and the irrational constants pi, E, GoldenRatio and TribonacciConstant are not rational
    if (x instanceof Special || isReal(x) === false || (x instanceof Constant && IRRATIONAL.has(x.name))) return false;
    return undefined;
  }
  if (s === Reals) {
    if (x instanceof Special || x.has(S.ComplexInfinity) || x.has(S.NaN)) return false;
    if (isReal(x) === false) return false;
    const v = realValue(x);
    if (v !== undefined) return true;
    if (!x.freeSymbols().size && isComparable(fn('im', [x])) && isZero(fn('im', [x])) === false) return false;
    return impl.isReal?.(x) ?? undefined;
  }
  if (s === Complexes) {
    // oo, -oo, zoo and nan are not complex numbers; a symbol may be infinite unless it is real
    if (x instanceof Special) return false;
    return x.freeSymbols().size === 0 || impl.isReal?.(x) === true ? true : undefined;
  }
  if (s === Integers || s === Naturals || s === Naturals0) {
    if (x instanceof Rational) return x.isInteger && (s === Integers || (s === Naturals ? x.p > 0n : x.p >= 0n));
    return notInteger(x) ? false : undefined;
  }
  if (s instanceof Range) {
    const v = rangeContains(s, x);
    return v === S.true ? true : v === S.false ? false : undefined;
  }
  if (s instanceof ImageSet) return imageContains(s, x);
  if (s instanceof FiniteSet) {
    if (s.args.some((a) => a.key === x.key)) return true;
    // an element differs when its numeric order or the evaluated equality says so (SymPy FiniteSet._contains)
    const unknown = s.args.some((a) => cmpReal(a, x) === undefined && Eq(a, x) !== S.false);
    return unknown ? undefined : false;
  }
  if (s instanceof Interval) {
    if (isInf(x) || isReal(x) === false) return false;
    // each end by its numeric order, else by the assumptions of the difference (SymPy evaluates start <= x <= end)
    const side = (from: Expr, to: Expr, open: boolean): boolean | undefined => {
      const order = cmpReal(from, to);
      if (order !== undefined) return open ? order < 0 : order <= 0;
      if (isInf(from) || isInf(to)) return isReal(x) === true ? true : undefined;
      const width = add(to, neg(from));
      const holds = open ? isPositive(width) : isNonNegative(width);
      if (holds === true) return true;
      return (open ? isNonNegative(neg(width)) : isNegative(width)) === true ? false : undefined;
    };
    const okLo = side(s.start, x, s.leftOpen);
    const okHi = side(x, s.end, s.rightOpen);
    if (okLo === false || okHi === false) return false;
    return okLo === true && okHi === true ? true : undefined;
  }
  if (s instanceof SetOp) {
    const parts = s.args.map((a) => containsQ(a, x));
    if (s.op === 'Union') return parts.some((v) => v === true) ? true : parts.every((v) => v === false) ? false : undefined;
    if (s.op === 'Intersection') return parts.every((v) => v === true) ? true : parts.some((v) => v === false) ? false : undefined;
    const [a, b] = parts;
    if (a === false || b === true) return false;
    if (a === true && b === false) return true;
    return undefined;
  }
  const v = s.elementOf(x);
  return v === 'unknown' ? undefined : v;
}

/** A number cannot equal a tuple, a set, or a matrix. */
function elementEquality(a: Expr, b: Expr): Expr {
  const nonScalar = (e: Expr): boolean => e instanceof SetExpr || e instanceof TupleNode || (e instanceof ExtensionExpr && !e.isScalar);
  if ((nonScalar(a) && (b instanceof Rational || b instanceof Float)) || (nonScalar(b) && (a instanceof Rational || a instanceof Float))) return S.false;
  return Eq(a, b);
}

function membershipTruth(s: SetExpr, x: Expr): Truth {
  const result = contains(s, x);
  return result === S.true ? true : result === S.false ? false : 'unknown';
}

/** A decided membership, or 'unknown'. */
const tri = (v: boolean | undefined): Truth => v ?? 'unknown';

/**
 * SymPy ImageSet._contains for a number x and a polynomial expression: x is in
 * the image when a root of expr = x is in the base set.
 */
function imageContains(s: ImageSet, x: Expr): boolean | undefined {
  const v = s.variable;
  if (!sameSignature(s.expr, x)) return false;
  if (x instanceof SetExpr) return s.expr instanceof SetExpr ? undefined : false;
  if (s.variable instanceof TupleNode && s.base instanceof ProductSetNode) {
    const base = s.base;
    // Polar coordinates have a unique inverse at nonzero radius for a
    // nonnegative radial domain and angles in [0, 2*pi).
    if (v.args.length === 2 && x instanceof TupleNode && x.args.length === 2 && s.expr instanceof TupleNode) {
      const [r, t] = [at(v.args, 0), at(v.args, 1)];
      const domainR = at(base.args, 0), domainT = at(base.args, 1);
      const polar = new TupleNode([mul(r, fn('cos', [t])), mul(r, fn('sin', [t]))]);
      if (s.expr.key === polar.key && isSubset(domainR, interval(0, S.Infinity)) === true && isSubset(domainT, interval(0, mul(2, S.Pi), false, true)) === true &&
          x.args.every((c) => isReal(c) === true)) {
        const z = add(at(x.args, 0), mul(S.I, at(x.args, 1)));
        if (isZero(z) === true) return containsQ(domainR, S.Zero);
        if (isZero(z) === false) {
          const radius = fn('abs', [z]), theta = Mod(fn('arg', [z]), mul(2, S.Pi));
          const result = truthAnd(tri(containsQ(domainR, radius)), tri(containsQ(domainT, theta)));
          return result === 'unknown' ? undefined : result;
        }
      }
    }
    const values = x instanceof TupleNode ? x.args : [x];
    const outputs = s.expr instanceof TupleNode ? s.expr.args : [s.expr];
    // A coordinate depending on just one parameter can rule out membership independently.
    for (const [i, output] of outputs.entries()) {
      const parameters = s.variable.args.filter((p) => output.has(p));
      if (parameters.length !== 1) continue;
      const p = first(parameters);
      if (imageContains(new ImageSet(p, output, at(base.args, s.variable.args.indexOf(p))), at(values, i)) === false) return false;
    }
  }
  if (!(v instanceof Sym) || x.freeSymbols().size || x instanceof Float || x instanceof TupleNode) return undefined;
  const eq = add(s.expr, mul(-1, x));
  const [numerator, denominator] = asNumerDenom(eq);
  const pc = polyCoefficients(numerator, v);
  if (!pc) return undefined;
  let rs: Expr[];
  try {
    rs = rootsDict(numerator, v, { multiple: true });
  } catch {
    // no formula for the roots
    return undefined;
  }
  const inBase = rs.map((r) => isZero(denominator.subs([[v, r]])) === true ? false : containsQ(s.base, r));
  if (inBase.some((c) => c === true)) return true;
  // all the roots are known and none is in the base set
  return rs.length === Math.max(...pc.keys()) && inBase.every((c) => c === false) ? false : undefined;
}

/** SymPy Contains(x, S): x is an element of the set, when that is not decided. */
export class Contains extends ExtensionExpr {
  constructor(
    readonly element: Expr,
    readonly set: SetExpr,
  ) {
    super('Contains', [element, set]);
    if (!(set instanceof SetExpr)) throw new TypeError('Contains requires a set');
  }
  get binarySymbols(): Set<Expr> { return new Set(this.set.args.flatMap((s) => [...binarySymbols(s).values()])); }
  asSet(): SetExpr { return this.set; }
  /** Rebuilding evaluates (Contains(x, Integers).subs(x, 2) is true). */
  withArgs(args: readonly Expr[]): Expr {
    return contains(cast(at(args, 1), SetExpr, 'Contains set'), at(args, 0));
  }
  /** SymPy LatexPrinter: x \in S. */
  override printLatex(print: (e: Expr) => string): string {
    return `${print(this.element)} \\in ${print(this.set)}`;
  }
}

/**
 * SymPy Set.contains: true or false, a condition on x (for intervals,
 * finite sets and unions, intersections and complements of them), or an
 * unevaluated Contains.
 */
export function contains(s: SetExpr, x: Expr): Expr {
  if (s instanceof Interval && (x === S.ComplexInfinity || x === S.NaN)) return S.false;
  const v = containsQ(s, x);
  if (v !== undefined) return v ? S.true : S.false;
  if (s === Reals || s instanceof Interval) return asRelational(s, x);
  if (s instanceof FiniteSet) return or(...s.args.map((a) => elementEquality(a, x)));
  if (s instanceof ConditionSet) return s.membership(x);
  if (s instanceof Range) {
    // a condition on the symbols of the Range (SymPy Range._contains)
    const c = rangeContains(s, x);
    if (c !== undefined) return c;
  }
  if (s instanceof ProductSetNode && x instanceof TupleNode && s.args.length === x.args.length) return and(...s.args.map((a, i) => contains(a, at(x.args, i))));
  if (s instanceof SetOp) {
    const parts = s.args.map((a) => contains(a, x));
    if (s.op === 'Union') return or(...parts);
    if (s.op === 'Intersection') return and(...parts);
    return and(at(parts, 0), not(at(parts, 1)));
  }
  return new Contains(x, s);
}

function intervalParts(s: SetExpr): Interval[] | undefined {
  if (s instanceof Interval) return [s];
  if (s === Reals) return [new Interval(S.NegativeInfinity, S.Infinity, true, true)];
  if (s instanceof SetOp && s.op === 'Union') {
    const ivs = s.args.filter((a) => a instanceof Interval);
    if (ivs.length === s.args.length) return ivs;
  }
  return undefined;
}

/** Union of sets, merging overlapping intervals and absorbing points. */
export function union(...sets0: SetExpr[]): SetExpr {
  const sets = sets0.flatMap((s) => (s instanceof SetOp && s.op === 'Union' ? s.args : [s])).filter((s) => s !== EmptySet);
  if (!sets.length) return EmptySet;
  if (sets.includes(UniversalSet)) return UniversalSet;
  // Coordinate unions commute with either complex-region parametrization.
  const region = sets.find((s) => s.className === 'CartesianComplexRegion' || s.className === 'PolarComplexRegion');
  if (region) {
    const compatible = sets.filter((s) => s.className === region.className || (region.className === 'CartesianComplexRegion' && isSubset(s, Reals) === true));
    if (compatible.length > 1) {
      const coordinates = compatible.map((s) => s.className === region.className ? cast(at(s.args, 0), SetExpr) : productSet(s, finiteSet(0)));
      const merged = cast(region.withArgs([union(...coordinates)]), SetExpr);
      return union(merged, ...sets.filter((s) => !compatible.includes(s)));
    }
  }
  // the classes with their own rule combine pairwise (SymPy union_sets)
  if (sets.some((s) => s.unionSelf !== SetExpr.prototype.unionSelf)) {
    for (const [i, a] of sets.entries()) {
      for (const [j, b] of sets.entries()) {
        const merged = i === j ? undefined : a.unionSelf(b);
        if (merged !== undefined) return union(merged, ...sets.filter((_, k) => k !== i && k !== j));
      }
    }
  }
  if (sets.includes(Complexes) && sets.every((s) => isSubset(s, Complexes) === true)) return Complexes;
  // the rationals contain the integers and the naturals (SymPy union_sets)
  if (sets.includes(Rationals) && sets.every((s) => s === Rationals || s === Integers || s === Naturals || s === Naturals0)) return Rationals;
  if (sets.some((s) => s === Reals) && sets.every((s) => s === Reals || s === Rationals || s === Integers || s === Naturals || s === Naturals0 || (s instanceof Interval && cmpReal(s.start, s.end) !== undefined) || (s instanceof FiniteSet && s.args.every((a) => containsQ(Reals, a) === true)))) return Reals;
  let ivs: Interval[] = [];
  const points: Expr[] = [];
  const others: SetExpr[] = [];
  for (const s of sets) {
    if (s instanceof Interval) ivs.push(s);
    else if (s === Reals) ivs.push(new Interval(S.NegativeInfinity, S.Infinity, true, true));
    else if (s instanceof FiniteSet) points.push(...s.args);
    else others.push(s);
  }
  // merge intervals
  ivs = mergeIntervals(ivs);
  // absorb points
  const rest: Expr[] = [];
  for (const pt of points) {
    let absorbed = false as boolean; // set inside a callback
    ivs = ivs.map((iv) => {
      if (absorbed) return iv;
      if (containsQ(iv, pt) === true) {
        absorbed = true;
        return iv;
      }
      if (!isInf(pt) && iv.leftOpen && cmpReal(iv.start, pt) === 0) {
        absorbed = true;
        return new Interval(iv.start, iv.end, false, iv.rightOpen);
      }
      if (!isInf(pt) && iv.rightOpen && cmpReal(iv.end, pt) === 0) {
        absorbed = true;
        return new Interval(iv.start, iv.end, iv.leftOpen, false);
      }
      return iv;
    });
    if (!absorbed) rest.push(pt);
  }
  ivs = mergeIntervals(ivs);
  const out: SetExpr[] = ivs.map((iv) => (isNegOo(iv.start) && isOo(iv.end) ? Reals : iv));
  if (rest.length) out.push(finiteSet(...rest));
  out.push(...mergeProducts(others));
  if (out.length === 1) return first(out);
  return new SetOp('Union', sortSets(out));
}

/**
 * SymPy union_sets(ProductSet, ProductSet): a product inside another is
 * absorbed, and two products of two sets that share a factor merge
 * (A x B | A x C = A x (B | C)).
 */
function mergeProducts(sets0: SetExpr[]): SetExpr[] {
  const sets = [...sets0];
  for (let i = 0; i < sets.length; i++) {
    for (let j = 0; j < sets.length; j++) {
      const a = at(sets, i);
      const b = at(sets, j);
      if (i === j || !(a instanceof ProductSetNode && b instanceof ProductSetNode)) continue;
      let m: SetExpr | undefined;
      if (isSubset(b, a) === true) m = a;
      else if (a.args.length === 2 && b.args.length === 2) {
        if (at(a.args, 0).key === at(b.args, 0).key) m = productSet(at(a.args, 0), union(at(a.args, 1), at(b.args, 1)));
        else if (at(a.args, 1).key === at(b.args, 1).key) m = productSet(union(at(a.args, 0), at(b.args, 0)), at(a.args, 1));
      }
      if (m) {
        sets.splice(Math.max(i, j), 1);
        sets.splice(Math.min(i, j), 1, m);
        return mergeProducts(sets);
      }
    }
  }
  return sets;
}

function mergeIntervals(ivs0: Interval[]): Interval[] {
  const ivs = [...ivs0];
  let changed = true;
  while (changed) {
    changed = false;
    outer: for (let i = 0; i < ivs.length; i++) {
      const iv = at(ivs, i);
      for (let j = i + 1; j < ivs.length; j++) {
        const m = mergeTwo(iv, at(ivs, j));
        if (m) {
          ivs.splice(j, 1);
          ivs[i] = m;
          changed = true;
          break outer;
        }
      }
    }
  }
  return ivs;
}

function mergeTwo(aIn: Interval, bIn: Interval): Interval | undefined {
  let a = aIn;
  let b = bIn;
  // order so that a starts first
  const c = cmpReal(a.start, b.start);
  if (c === undefined) return undefined;
  if (c > 0 || (c === 0 && a.leftOpen && !b.leftOpen)) [a, b] = [b, a];
  // overlap or touch: b.start <= a.end
  const t = cmpReal(b.start, a.end);
  if (t === undefined) return undefined;
  if (t > 0) return undefined;
  if (t === 0 && a.rightOpen && b.leftOpen) return undefined;
  const e = cmpReal(a.end, b.end);
  if (e === undefined) return undefined;
  let end = a.end;
  let rightOpen = a.rightOpen;
  if (e < 0 || (e === 0 && a.rightOpen && !b.rightOpen)) {
    end = b.end;
    rightOpen = b.rightOpen;
  }
  const leftOpen = cmpReal(a.start, b.start) === 0 ? a.leftOpen && b.leftOpen : a.leftOpen;
  return new Interval(a.start, end, leftOpen, rightOpen);
}

function intersectFinite(sets: readonly SetExpr[]): SetExpr {
  const finite = sets.filter((s) => s instanceof FiniteSet);
  const rest = sets.filter((s) => !(s instanceof FiniteSet));
  const other = intersection(...rest);
  if (other === EmptySet) return EmptySet;
  const others = other instanceof SetOp && other.op === 'Intersection' ? other.args : [other];
  const candidates = new Map(finite.flatMap((s) => s.args.map((x) => [x.key, x] as const)));
  const possible = [...candidates.values()].filter((x) => others.every((s) => membershipTruth(s, x) !== false));
  const common = possible.filter((x) => finite.every((s) => s.args.some((v) => v.key === x.key)));
  const unresolved = possible.filter((x) => !common.includes(x));
  const residues = finite.map((s) => finiteSet(...s.args.filter((v) => unresolved.includes(getOrThrow(candidates, v.key)))));
  const remaining = unresolved.filter((x) => residues.every((s) => membershipTruth(s, x) !== false));
  const fs = residues.map((s) => finiteSet(...common, ...s.args.filter((x) => remaining.some((v) => v.key === x.key))));
  const min = fs.find((s) => s.args.length === common.length);
  const reduced = min ? [min] : fs;
  if (reduced.includes(EmptySet)) return EmptySet;
  const needed = others.filter((s) => reduced.some((f) => f.args.some((x) => membershipTruth(s, x) !== true)));
  const result = [...new Map([...reduced, ...needed].map((s) => [s.key, s])).values()];
  return result.length === 1 ? first(result) : new SetOp('Intersection', result);
}

/** Intersection of sets. */
export function intersection(...sets: SetExpr[]): SetExpr {
  if (sets.some((s) => s === EmptySet)) return EmptySet;
  if (!sets.length) return UniversalSet;
  const flat = sets.flatMap((s) => s instanceof SetOp && s.op === 'Intersection' ? s.args : [s]);
  if (flat.length > 1 && flat.some((s) => s instanceof FiniteSet) && !flat.some((s) => s instanceof ConditionSet)) return intersectFinite(flat);
  let acc: SetExpr = first(sets);
  for (const s of sets.slice(1)) acc = intersectTwo(acc, s);
  return acc;
}

function intersectTwo(a: SetExpr, b: SetExpr): SetExpr {
  if (a === EmptySet || b === EmptySet) return EmptySet;
  if (a === UniversalSet) return b;
  if (b === UniversalSet) return a;
  if (a.key === b.key) return a;
  const own = a.intersectSelf(b) ?? b.intersectSelf(a);
  if (own !== undefined) return own;
  if (a instanceof ConditionSet) return conditionSet(a.variable, a.condition, intersection(a.base, b));
  if (b instanceof ConditionSet) return conditionSet(b.variable, b.condition, intersection(a, b.base));
  if (a instanceof FiniteSet || b instanceof FiniteSet) return intersectFinite([a, b]);
  const intIv = (u: SetExpr, v: SetExpr) => (u === Integers || u === Naturals || u === Naturals0) && v instanceof Interval;
  const ints: [SetExpr, Interval] | undefined = intIv(a, b) ? [a, cast(b, Interval)] : intIv(b, a) ? [b, cast(a, Interval)] : undefined;
  if (ints) {
    const [z, iv] = ints;
    const r = integersIn(iv, z === Naturals ? S.One : z === Naturals0 ? S.Zero : S.NegativeInfinity);
    if (r) return r;
  }
  if ((a === Reals && (b === Integers || b === Naturals || b === Naturals0)) || (b === Reals && (a === Integers || a === Naturals || a === Naturals0))) return a === Reals ? b : a;
  if (a === Reals && b instanceof Interval) return b;
  if (b === Reals && a instanceof Interval) return a;
  const special = intersectSpecial(a, b) ?? intersectSpecial(b, a);
  if (special) return special;
  const pa = intervalParts(a);
  const pb = intervalParts(b);
  if (pa && pb) {
    const out: SetExpr[] = [];
    for (const x of pa) for (const y of pb) out.push(intersectIntervals(x, y));
    return union(...out);
  }
  if (a instanceof SetOp && a.op === 'Union') return union(...a.args.map((s) => intersectTwo(s, b)));
  if (b instanceof SetOp && b.op === 'Union') return union(...b.args.map((s) => intersectTwo(a, s)));
  return new SetOp('Intersection', sortSets([a, b]));
}

/** The SymPy intersection_sets handlers for Rationals, Range, ImageSet and ProductSet (undefined when none applies). */
function intersectSpecial(a: SetExpr, b: SetExpr): SetExpr | undefined {
  // Both coordinate maps are monotone in their parameter sets, including the
  // non-injective polar map at radius zero. Containment is safe without needing
  // a coordinate inverse or discarding points represented at several angles.
  if ((a.className === 'PolarComplexRegion' || a.className === 'CartesianComplexRegion') && a.className === b.className) {
    const left = cast(at(a.args, 0), SetExpr), right = cast(at(b.args, 0), SetExpr);
    if (isSubset(left, right) === true) return a;
    if (isSubset(right, left) === true) return b;
    if (a.className === 'CartesianComplexRegion') {
      const coordinates = intersection(left, right);
      return coordinates === EmptySet ? EmptySet : cast(a.withArgs([coordinates]), SetExpr);
    }
    // A positive-radius polar coordinate has a unique normalized angle.
    // Zero belongs to every angle, so preserve it even for disjoint sectors.
    const coordinates = intersection(left, right);
    const origin = containsQ(a, S.Zero) === true && containsQ(b, S.Zero) === true;
    const region = coordinates === EmptySet ? EmptySet : cast(a.withArgs([coordinates]), SetExpr);
    return origin && containsQ(region, S.Zero) !== true ? union(region, finiteSet(0)) : region;
  }
  if ((a.className === 'CartesianComplexRegion' || a.className === 'PolarComplexRegion') && isSubset(b, Reals) === true) {
    const coordinates = cast(at(a.args, 0), SetExpr);
    const parts = coordinates instanceof SetOp && coordinates.op === 'Union' ? coordinates.args : [coordinates];
    const realParts: SetExpr[] = [];
    for (const part of parts) {
      const p = cast(part, ProductSetNode);
      const radius = at(p.args, 0), angle = at(p.args, 1);
      if (containsQ(angle, S.Zero) === true) realParts.push(radius);
      if (a.className === 'PolarComplexRegion') {
        if (containsQ(angle, S.Pi) === true) {
          const variable = new Sym('x', { real: true });
          realParts.push(imageSet(variable, neg(variable), radius));
        }
        if (containsQ(radius, S.Zero) === true) realParts.push(finiteSet(0));
      }
    }
    return intersection(union(...realParts), b);
  }
  if (a === Complexes && isSubset(b, Complexes) === true) return b;
  const integral = (s: SetExpr): boolean => s === Integers || s === Naturals || s === Naturals0 || s instanceof Range;
  if (a === Rationals && (integral(b) || b === Rationals)) return b;
  if (a === Rationals && b === Reals) return a;
  if (a instanceof Range) return intersectRange(a, b);
  if (a instanceof ImageSet) return intersectImage(a, b);
  if (a instanceof ProductSetNode && b instanceof ProductSetNode) {
    if (a.args.length !== b.args.length) return EmptySet;
    return productSet(...a.args.map((x, i) => intersection(x, at(b.args, i))));
  }
  return undefined;
}

const isNumberOrInf = (e: Expr): boolean => isInf(e) || (!e.freeSymbols().size && realValue(e) !== undefined);

/** The integer at or above (up) or below a real number, or +-oo. */
function roundInt(e: Expr, up: boolean): Expr | undefined {
  if (isInf(e)) return e;
  const v = fn(up ? 'ceiling' : 'floor', [e]);
  return v instanceof Rational ? v : undefined;
}

/** SymPy intersection_sets(Range, Integers / Reals / Naturals / Interval / Range). */
function intersectRange(r: Range, o: SetExpr): SetExpr | undefined {
  if (o === Integers || o === Reals || o === Rationals || o === Complexes) return r;
  // (SymPy does not intersect a symbolic Range with an interval or a Range)
  if (hasSymbol(r)) return undefined;
  if (o === Naturals || o === Naturals0) return intersectRange(r, new Interval(o === Naturals ? S.One : S.Zero, S.Infinity, false, true));
  // the ends of a Range are integers or infinite
  if (r.isEmpty) return EmptySet;
  if (o instanceof Interval) {
    if (!isNumberOrInf(o.start) || !isNumberOrInf(o.end)) return undefined;
    // the integers of the interval as a Range with step 1
    const lo0 = cmpReal(o.start, inf(r)) === 1 ? o.start : inf(r);
    const hi0 = cmpReal(o.end, sup(r)) === -1 ? o.end : sup(r);
    const lo1 = roundInt(lo0, true);
    const hi1 = roundInt(hi0, false);
    if (!lo1 || !hi1) return undefined;
    // (SymPy: n in o raises TypeError when membership is not decided)
    const loIn = isInf(lo1) || containsQ(o, lo1);
    const hiIn = isInf(hi1) || containsQ(o, hi1);
    if (loIn === undefined || hiIn === undefined) return undefined;
    const lo = loIn ? lo1 : add(lo1, 1);
    const hi = hiIn ? hi1 : add(hi1, -1);
    if (cmpReal(lo, hi) === 1) return EmptySet;
    return intersectRanges(r, cast(range(lo, isInf(hi) ? hi : add(hi, 1)), Range));
  }
  if (o instanceof Range && !hasSymbol(o)) return intersectRanges(r, o);
  return undefined;
}

const floorMod = (a: bigint, m: bigint): bigint => ((a % m) + m) % m;
const asRat = (e: Expr): Rational => expectType(e, (v): v is Rational => v instanceof Rational, 'rational number');
const isZ = (e: Expr): boolean => e instanceof Rational && e.isZero;

/**
 * SymPy intersection_sets(Range, Range) for numeric ranges: the common
 * arithmetic progression (by the Chinese remainder theorem) clipped to the
 * common bounds, with a positive step.
 */
function intersectRanges(a: Range, b: Range): SetExpr {
  if (a.isEmpty || b.isEmpty) return EmptySet;
  // both ends infinite: the set of all integers
  if (isInf(a.start) && isInf(a.stop)) return b;
  if (isInf(b.start) && isInf(b.stop)) return a;
  const ends = (r: Range): { lo: Expr; hi: Expr; m: bigint; res: bigint } => {
    const lo = inf(r);
    const hi = sup(r);
    const st = asRat(r.step).p;
    const m = st < 0n ? -st : st;
    const fin = asRat(isInf(lo) ? hi : lo);
    return { lo, hi, m, res: floorMod(fin.p, m) };
  };
  const p = ends(a);
  const q = ends(b);
  if (cmpReal(q.hi, p.lo) === -1 || cmpReal(q.lo, p.hi) === 1) return EmptySet;
  const [g, u] = gcdext(p.m, q.m);
  if ((q.res - p.res) % g !== 0n) return EmptySet;
  const L = (p.m / g) * q.m;
  const x = floorMod(p.res + p.m * floorMod(((q.res - p.res) / g) * u, q.m / g), L);
  const lo = cmpReal(p.lo, q.lo) === 1 ? p.lo : q.lo;
  const hi = cmpReal(p.hi, q.hi) === -1 ? p.hi : q.hi;
  const step = Rational.of(L);
  if (lo instanceof Rational) {
    const first = lo.p + floorMod(x - lo.p, L);
    if (hi instanceof Rational && first > hi.p) return EmptySet;
    return range(Rational.of(first), hi instanceof Rational ? Rational.of(hi.p + 1n) : hi, step);
  }
  const h = asRat(hi).p;
  const last = h - floorMod(h - x, L);
  return range(lo, Rational.of(last + L), step);
}

/** a*n + b for an expression linear in n (a free of n and nonzero), or undefined. */
function linearIn(e: Expr, n: Expr): [Expr, Expr] | undefined {
  if (!(n instanceof Sym)) return undefined;
  const pc = polyCoefficients(e, n);
  if (!pc || !pc.has(1) || [...pc.keys()].some((d) => d > 1)) return undefined;
  // the coefficients are free of n, and a is not zero
  return [getOrThrow(pc, 1), pc.get(0) ?? S.Zero];
}

/** A translated, possibly reflected, even power of an integer parameter. */
function integerPowerImage(s: ImageSet): { offset: bigint; sign: bigint; degree: bigint } | undefined {
  if (s.base !== Integers) return undefined;
  const [offset, terms] = asCoeffAdd(s.expr);
  if (!(offset instanceof Rational && offset.isInteger) || terms.length !== 1) return undefined;
  const [sign, factors] = asCoeffMul(first(terms));
  if (!(sign instanceof Rational && (sign.isOne || sign.key === S.NegOne.key)) || factors.length !== 1) return undefined;
  const power = first(factors);
  if (!(power instanceof Pow && power.exp instanceof Rational && power.exp.isInteger && power.exp.p > 0n && power.exp.p % 2n === 0n)) return undefined;
  const linear = linearIn(power.base, s.variable);
  if (!linear || !(linear[0] instanceof Rational && (linear[0].isOne || linear[0].key === S.NegOne.key)) || !(linear[1] instanceof Rational && linear[1].isInteger)) return undefined;
  return { offset: offset.p, sign: sign.p, degree: power.exp.p };
}

/** Oppositely directed even powers intersect in a bounded integer interval. */
function intersectPowerImages(a: ImageSet, b: ImageSet): SetExpr | undefined {
  const left = integerPowerImage(a), right = integerPowerImage(b);
  if (!left || !right || left.sign === right.sign) return undefined;
  const span = left.sign * (right.offset - left.offset);
  if (span < 0n) return EmptySet;
  const [bound] = integerNthroot(span, left.degree);
  // Large finite searches remain represented by the symbolic intersection.
  if (bound > 10000n) return undefined;
  const points: Expr[] = [];
  for (let n = 0n; n <= bound; n++) {
    const term = n ** left.degree;
    if (integerNthroot(span - term, right.degree)[1]) points.push(Rational.of(left.offset + left.sign * term));
  }
  return finiteSet(...points);
}

/**
 * SymPy intersection_sets(ImageSet, Set): for images of the integers under
 * linear maps with rational coefficients the common values (solving the
 * linear diophantine equation f(n) = g(m)), and for a linear image and an
 * interval the image of the integers whose values fall in the interval.
 */
function intersectImage(s: ImageSet, o: SetExpr): SetExpr | undefined {
  const n = s.variable;
  if (n instanceof Sym && (o === Reals || o instanceof Interval) && isSubset(s.base, Reals) === true) {
    const parameter = new Dummy('t', { real: true });
    const expr = s.expr.subs([[n, parameter]]);
    if (expr.has(S.I)) {
      const im = fn('im', [expr]);
      const [numerator] = asNumerDenom(im);
      const pc = polyCoefficients(numerator, parameter);
      // SymPy keeps an unfactored nonlinear imaginary part as a condition on the parameter.
      if (o === Reals && im instanceof Add && pc && Math.max(...pc.keys()) > 1 && !asNumerDenom(expr)[1].has(parameter)) {
        const real = fn('re', [expr]).subs([[parameter, n]]);
        const index = real.has(n) && real.freeSymbols().size === 1 ? new Sym('x') : n;
        return new ImageSet(index, real.subs([[n, index]]), conditionSet(n, Eq(im.subs([[parameter, n]]), 0), s.base));
      }
      if (pc?.size && Math.max(...pc.keys()) > 0) {
        try {
          const roots = rootsDict(numerator, parameter, { multiple: true });
          if (roots.every((r) => containsQ(s.base, r) !== undefined)) {
            const values = roots.filter((r) => containsQ(s.base, r) === true).map((r) => expr.subs([[parameter, r]]));
            return intersection(finiteSet(...values), o);
          }
        } catch {
          // An unresolved imaginary-part equation leaves the intersection symbolic.
        }
      }
    } else if (o === Reals && polyCoefficients(expr, parameter) && isReal(expr) === true) return imageSet(n, s.expr, s.base);
    if (o instanceof Interval && s.expr instanceof Fn && s.expr.name === 'log' && first(s.expr.args).key === n.key && s.base === Integers) {
      const indices = intersection(Integers, interval(pow(S.E, o.start), pow(S.E, o.end), o.leftOpen, o.rightOpen));
      if (indices instanceof Range && indices.isIterable) return finiteSet(...[...indices].map((r) => fn('log', [r])));
    }
  }
  const f = linearIn(s.expr, s.variable);
  if (!f) {
    if (o instanceof ImageSet) return intersectPowerImages(s, o);
    if (o === Integers && s.base === Integers && n instanceof Sym) {
      // If P(n)/(c*n) is an integer, n must divide the integer constant P(0).
      const [num, den] = asNumerDenom(s.expr);
      const poly = polyCoefficients(num, n), linear = linearIn(den, n);
      const c = poly?.get(0);
      if (poly && [...poly.values()].every((a) => a instanceof Rational && a.isInteger) && c instanceof Rational && !c.isZero &&
          linear && isZ(linear[1]) && linear[0] instanceof Rational && linear[0].isInteger) {
        const candidates = divisors(c.p).flatMap((d) => [Rational.of(d), Rational.of(-d)]);
        return finiteSet(...candidates.map((d) => s.expr.subs([[n, d]])).filter((v) => isIntegerQ(v) === true));
      }
    }
    return undefined;
  }
  if (s.base === Integers && (o === Integers || (o instanceof ImageSet && o.base === Integers))) {
    const g = o instanceof ImageSet ? linearIn(o.expr, o.variable) : ([S.One, S.Zero] as [Expr, Expr]);
    if (!g) return undefined;
    const scale = f[0] instanceof Rational ? S.One : f[0];
    if (scale.freeSymbols().size || isZero(scale) !== false) return undefined;
    const coefficients = [...f, ...g].map((c) => div(c, scale));
    if (!coefficients.every((c) => c instanceof Rational)) return undefined;
    const [a1, b1, a2, b2] = [at(coefficients, 0), at(coefficients, 1), at(coefficients, 2), at(coefficients, 3)];
    // a1*n - a2*m = b2 - b1, scaled to integers
    const D = [a1, b1, a2, b2].reduce((d, c) => (d * c.q) / gcd(d, c.q), 1n);
    const scaled = (c: Rational): bigint => (c.p * D) / c.q;
    const [A1, B1, A2, B2] = [scaled(a1), scaled(b1), scaled(a2), scaled(b2)];
    const [gg, u] = gcdext(A1, -A2);
    const rhs = B2 - B1;
    if (rhs % gg !== 0n) return EmptySet;
    const n0 = (rhs / gg) * u;
    // n = n0 + (A2/g)*t: the values f(n0) + a1*(A2/g)*t
    const n = s.variable;
    return imageSet(n, add(mul(scale, a1, Rational.of(A2 / gg), n), mul(scale, a1, Rational.of(n0)), mul(scale, b1)), Integers);
  }
  if (o instanceof Interval && f.every((c) => !c.freeSymbols().size && isComparable(c))) {
    const [a, b] = f;
    const inv = (e: Expr): Expr => (isInf(e) ? ((cmpReal(a, S.Zero) === 1) === isOo(e) ? S.Infinity : S.NegativeInfinity) : mul(add(e, mul(-1, b)), pow(a, -1)));
    const neg = cmpReal(a, S.Zero) === -1;
    const [lo, hi] = neg ? [inv(o.end), inv(o.start)] : [inv(o.start), inv(o.end)];
    const [lopen, ropen] = neg ? [o.rightOpen, o.leftOpen] : [o.leftOpen, o.rightOpen];
    let rs = intersection(s.base, interval(lo, hi, lopen, ropen));
    if (rs === EmptySet) return EmptySet;
    if (rs instanceof Range && !isInf(rs.start) && !isInf(rs.stop)) rs = finiteSet(...rangeElements(rs));
    return imageSet(s.variable, s.expr, rs);
  }
  return undefined;
}

/** The elements of a finite Range. */
function rangeElements(r: Range): Expr[] {
  const out: Expr[] = [];
  const [start, stop] = [asRat(r.start).p, asRat(r.stop).p];
  // the ranges of an intersection have a positive step
  for (let k = start; k < stop; k += asRat(r.step).p) out.push(Rational.of(k));
  return out;
}

function intersectIntervals(a: Interval, b: Interval): SetExpr {
  const cs = cmpReal(a.start, b.start);
  const ce = cmpReal(a.end, b.end);
  if (cs === undefined || ce === undefined) return new SetOp('Intersection', sortSets([a, b]));
  const canonical = (u: Expr, v: Expr): Expr => {
    if (u.key === v.key) return u;
    if (hasFloat(u) !== hasFloat(v)) return hasFloat(u) ? u : v;
    return first(ordered([u, v]));
  };
  const [start, lo] = cs > 0 ? [a.start, a.leftOpen] : cs < 0 ? [b.start, b.leftOpen] : [canonical(a.start, b.start), a.leftOpen || b.leftOpen];
  const [end, ro] = ce < 0 ? [a.end, a.rightOpen] : ce > 0 ? [b.end, b.rightOpen] : [canonical(a.end, b.end), a.rightOpen || b.rightOpen];
  return interval(start, end, lo, ro);
}

/** a \ b. */
export function complement(a: SetExpr, b: SetExpr): SetExpr {
  if (b === EmptySet) return a;
  if (a === EmptySet || b === UniversalSet || a.key === b.key) return EmptySet;
  if (a instanceof SetOp && a.op === 'Union') return union(...a.args.map((s) => complement(s, b)));
  if (a instanceof SetOp && a.op === 'Complement') return new SetOp('Complement', [at(a.args, 0), union(at(a.args, 1), b)]);
  // remove the finite parts first (SymPy's Union orders FiniteSet before the other sets), so the result does not
  // depend on the order of the union's arguments
  if (b instanceof SetOp && b.op === 'Union' && !(intervalParts(a) && intervalParts(b))) {
    return [...b.args.filter((s) => s instanceof FiniteSet), ...b.args.filter((s) => !(s instanceof FiniteSet))].reduce(complement, a);
  }
  if (a instanceof NamedSet && b instanceof NamedSet && isSubset(a, b) === true) return EmptySet;
  if (a instanceof ProductSetNode && b instanceof ProductSetNode) {
    if (a.args.length !== b.args.length) return a;
    return union(...a.args.map((_, i) => productSet(...a.args.map((factor, j) => i === j ? complement(factor, at(b.args, j)) : factor))));
  }
  if (a instanceof FiniteSet && b instanceof FiniteSet) {
    const remaining = a.args.filter((x) => !b.args.some((y) => x.key !== y.key && cmpReal(x, y) === 0));
    if (remaining.length !== a.args.length) return complement(finiteSet(...remaining), b);
  }
  if (b instanceof FiniteSet) {
    const relevant = b.args.filter((x) => containsQ(a, x) !== false);
    if (relevant.length !== b.args.length) return complement(a, finiteSet(...relevant));
  }
  if (a instanceof FiniteSet) {
    const keep: Expr[] = [];
    const unknown: Expr[] = [];
    for (const x of a.args) {
      const c = containsQ(b, x);
      if (c === false) keep.push(x);
      else if (c === undefined) unknown.push(x);
    }
    if (unknown.length) {
      // A shared symbol can also equal a remaining element after substitution.
      // Keep its exclusion on the unknown elements of the difference.
      if (b instanceof FiniteSet && b.args.some((y) => a.args.some((v) => v.equals(y)) && unknown.some((v) => containsQ(finiteSet(y), v) === undefined))) {
        return union(finiteSet(...keep), new SetOp('Complement', [finiteSet(...unknown), b]));
      }
      // SymPy FiniteSet._complement: the elements of b that are elements of a are taken out of both; what is
      // subtracted from the rest are the elements of b whose membership in a is open ({i, j, k} - {j} = {i, k})
      const open = b instanceof FiniteSet ? finiteSet(...b.args.filter((y) => containsQ(a, y) === undefined)) : b;
      // (a smaller difference is reduced again, as SymPy's Complement does)
      const reduced = unknown.length < a.args.length || open.key !== b.key;
      return union(finiteSet(...keep), reduced ? complement(finiteSet(...unknown), open) : new SetOp('Complement', [finiteSet(...unknown), open]));
    }
    return finiteSet(...keep);
  }
  const pa = intervalParts(a);
  const points = b instanceof FiniteSet ? b.args.map((x) => [x, realValue(x)] as const) : undefined;
  if (pa && points && points.some(([, v]) => v !== undefined) && points.some(([, v]) => v === undefined)) {
    const known = finiteSet(...points.filter(([, v]) => v !== undefined).map(([p]) => p));
    const rest = finiteSet(...points.filter(([, v]) => v === undefined).map(([p]) => p));
    const split = complement(a, known);
    return a === Reals ? new SetOp('Complement', [split, rest]) : complement(split, rest);
  }
  if (pa && points?.every((pv): pv is readonly [Expr, number] => pv[1] !== undefined)) {
    let parts: SetExpr[] = pa;
    for (const [pt] of [...points].sort((p, q) => p[1] - q[1])) {
      if (parts.some((iv) => containsQ(iv, pt) === undefined)) return new SetOp('Complement', [a, b]);
      parts = parts.flatMap((iv) => {
        if (!(iv instanceof Interval) || containsQ(iv, pt) !== true) return [iv];
        return [interval(iv.start, pt, iv.leftOpen, true), interval(pt, iv.end, true, iv.rightOpen)];
      });
    }
    return union(...parts);
  }
  const pb = intervalParts(b);
  if (pa && pb) {
    let parts: SetExpr[] = pa;
    for (const y of pb) {
      parts = parts.flatMap((x) => {
        if (!(x instanceof Interval)) return [x];
        const left = interval(x.start, y.start, x.leftOpen, !y.leftOpen);
        const right = interval(y.end, x.end, !y.rightOpen, x.rightOpen);
        const inter = intersectIntervals(x, y);
        if (inter === EmptySet) return [x];
        return [left, right];
      });
    }
    return union(...parts);
  }
  return new SetOp('Complement', [a, b]);
}

/** Is a a subset of b (true/false/undefined)? */
export function isSubset(a: SetExpr, b: SetExpr): boolean | undefined {
  if (!(a instanceof SetExpr && b instanceof SetExpr)) throw new RangeError('Inclusion requires two sets');
  if (a === EmptySet || b === UniversalSet || a.key === b.key) return true;
  if (a instanceof Interval && b === Complexes) return true;
  if (a instanceof SetOp && a.op === 'Union') {
    const parts = a.args.map((s) => isSubset(s, b));
    return parts.includes(false) ? false : parts.every((c) => c === true) ? true : undefined;
  }
  if (a instanceof ImageSet && b === Reals && a.variable instanceof Sym && isSubset(a.base, Reals) === true) {
    const p = polyCoefficients(a.expr, a.variable);
    if (p && [...p.values()].every((c) => isReal(c) === true)) return true;
  }
  if (a instanceof ProductSetNode && b instanceof FiniteSet && a.args.every((s) => s instanceof FiniteSet)) {
    if (a.length > b.args.length) return false;
    const points = b.args.filter((p) => a.elementOf(p) === true);
    if (points.length === a.length) return true;
  }
  if (a instanceof Range && b instanceof FiniteSet && a.isIterable) {
    if (asRat(a.size).p > BigInt(b.args.length)) return false;
    return isSubset(finiteSet(...a), b);
  }
  if (a instanceof Range && b instanceof Interval && a.isIterable) return a.isEmpty || isSubset(finiteSet(a.at(0), a.at(-1)), b);
  if (a === UniversalSet) return false;
  if (a instanceof PowerSetNode && b instanceof PowerSetNode) return isSubset(a.arg, b.arg);
  if (a.isFiniteSet === false && b.isFiniteSet === true) return false;
  if (a instanceof NamedSet && b instanceof NamedSet) {
    const order = [Naturals, Naturals0, Integers, Rationals, Reals, Complexes];
    return order.indexOf(a) < order.indexOf(b);
  }
  if (a instanceof ProductSetNode && b instanceof ProductSetNode) {
    if (a.args.length !== b.args.length) return false;
    const cs = a.args.map((x, i) => isSubset(x, at(b.args, i)));
    // the factors of a product are not empty
    return cs.every((c) => c === true) ? true : cs.some((c) => c === false) ? false : undefined;
  }
  // an unbounded set is not in an interval with a finite end
  if ((a === Reals || a === Integers) && b instanceof Interval && !(isNegOo(b.start) && isOo(b.end))) return false;
  if (b === Reals && (a instanceof Interval || (a instanceof FiniteSet && a.args.every((x) => containsQ(Reals, x) === true)))) return true;
  if (a instanceof FiniteSet) {
    const cs = a.args.map((x) => membershipTruth(b, x));
    return cs.every((c) => c === true) ? true : cs.some((c) => c === false) ? false : undefined;
  }
  // an interval of more than one point is uncountable
  if (a instanceof Interval && (b === Integers || b === Naturals || b === Naturals0) && cmpReal(a.start, a.end) === -1) return false;
  const c = complement(a, b);
  if (c === EmptySet) return true;
  // a remainder with symbols may be empty for some values of them
  if (c instanceof SetOp || c.freeSymbols().size) return undefined;
  return false;
}

/** The set as a condition on x (SymPy as_relational). */
export function asRelational(s: SetExpr, x: Expr): Expr {
  if (s === EmptySet) return S.false;
  if (s === Reals) return and(Lt(S.NegativeInfinity, x), Lt(x, S.Infinity));
  if (s === Integers || s === Naturals || s === Naturals0) {
    const lower = s === Integers ? Lt(S.NegativeInfinity, x) : Ge(x, s === Naturals ? 1 : 0);
    return and(lower, Lt(x, S.Infinity), Eq(fn('floor', [x]), x));
  }
  if (s instanceof Interval) {
    const left = s.leftOpen ? Lt(s.start, x) : Le(s.start, x);
    const right = s.rightOpen ? Lt(x, s.end) : Le(x, s.end);
    return and(left, right);
  }
  if (s instanceof FiniteSet) return or(...s.args.map((a) => Eq(x, a)));
  if (s instanceof SetOp && s.op === 'Union') {
    const [a, b] = s.args;
    // SymPy combines two intervals separated by a single excluded endpoint.
    if (s.args.length === 2 && a instanceof Interval && b instanceof Interval && a.rightOpen && b.leftOpen && a.end.key === b.start.key) {
      return and(asRelational(interval(a.start, b.end, a.leftOpen, b.rightOpen), x), not(Eq(x, a.end)));
    }
    return or(...s.args.map((a) => asRelational(a, x)));
  }
  if (s instanceof SetOp && s.op === 'Intersection') return and(...s.args.map((a) => asRelational(a, x)));
  if (s instanceof ProductSetNode && x instanceof TupleNode && s.args.length === x.args.length && x.args.every((v) => v instanceof Sym)) return and(...s.args.map((a, i) => asRelational(a, at(x.args, i))));
  if (s instanceof ConditionSet) return sameSignature(s.variable, x)
    ? and(contains(s.base, x), new LambdaNode([s.variable, s.condition]).call(x)) : S.false;
  if (s instanceof SetOp && s.op === 'Complement') return and(asRelational(at(s.args, 0), x), not(asRelational(at(s.args, 1), x)));
  if (s instanceof Range) return rangeAsRelational(s, x);
  throw new NotImplementedError('as_relational: unsupported set');
}

/** The least (sign 1) or greatest (sign -1) of xs, or Min / Max of them when they do not compare. */
function extreme(xs: readonly Expr[], sign: 1 | -1): Expr {
  let best = first(xs);
  for (const x of xs.slice(1)) {
    const c = cmpReal(x, best);
    if (c === undefined) return sign === 1 ? Min(...xs) : Max(...xs);
    if (c * sign < 0) best = x;
  }
  return best;
}

/** Infimum of a real set (SymPy Set.inf). */
export function inf(s: SetExpr): Expr {
  if (s instanceof Interval) return s.start;
  if (s === Reals || s === Integers) return S.NegativeInfinity;
  if (s === Naturals) return S.One;
  if (s === Naturals0) return S.Zero;
  if (s instanceof FiniteSet) return extreme(s.args, 1);
  if (s instanceof Range) return rangeEnd(s, 1);
  if (s instanceof SetOp && s.op === 'Union') return extreme(s.args.map(inf), 1);
  throw new NotImplementedError('inf: unsupported set');
}

/** Supremum of a real set (SymPy Set.sup). */
export function sup(s: SetExpr): Expr {
  if (s instanceof Interval) return s.end;
  if (s === Reals || s === Integers || s === Naturals || s === Naturals0) return S.Infinity;
  if (s instanceof FiniteSet) return extreme(s.args, -1);
  if (s instanceof Range) return rangeEnd(s, -1);
  if (s instanceof SetOp && s.op === 'Union') return extreme(s.args.map(sup), -1);
  throw new NotImplementedError('sup: unsupported set');
}

/** A set node rebuilt from new arguments (subs, xreplace and the traversals), evaluated like its constructor. */
function rebuildSet(e: Expr, args: readonly Expr[]): Expr {
  const sets = (): SetExpr[] => args.map((a) => cast(a, SetExpr, 'set argument'));
  if (e instanceof Interval) return interval(at(args, 0), at(args, 1), at(args, 2) === S.true, at(args, 3) === S.true);
  if (e instanceof FiniteSet) return finiteSet(...args);
  if (e instanceof Range) return range(at(args, 0), at(args, 1), at(args, 2));
  // SymPy rebuilds an ImageSet without evaluating it (imageset() evaluates, ImageSet() does not)
  if (e instanceof ImageSet) return new ImageSet(at(args, 0), at(args, 1), cast(at(args, 2), SetExpr, 'base set'), ...args.slice(3).map((s) => cast(s, SetExpr)));
  if (e instanceof ConditionSet) return conditionSet(at(args, 0), at(args, 1), cast(at(args, 2), SetExpr, 'base set'));
  if (e instanceof SetOp) return e.op === 'Union' ? union(...sets()) : e.op === 'Intersection' ? intersection(...sets()) : complement(...pairOf(sets()));
  if (e instanceof ProductSetNode) return productSet(...sets());
  if (e instanceof PowerSetNode) return new PowerSetNode(first(sets()));
  if (e instanceof DisjointUnionNode) return new DisjointUnionNode(sets());
  if (e instanceof SymmetricDifferenceNode) return new SymmetricDifferenceNode(sets());
  // a set of another module (ComplexRegion) rebuilds itself
  return cast(e, SetExpr, 'set').withArgs(args);
}

const pairOf = (xs: SetExpr[]): [SetExpr, SetExpr] => [at(xs, 0), at(xs, 1)];

/**
 * SymPy _eval_subs of the sets that bind a variable: the variable of an
 * ImageSet is not substituted, and ConditionSet substitutes in its base set
 * first (and in its condition unless the variable is replaced).
 */
function subsSet(e: Expr, old: Expr, nw: Expr, sub: (x: Expr) => Expr): Expr | undefined {
  if (e instanceof ImageSet && (e.variable.key === old.key || e.variable instanceof TupleNode && e.lamda.variables.some((v) => v.key === old.key))) {
    const bases = e.baseSets.map((b) => cast(sub(b), SetExpr, 'base set'));
    return bases.every((b, i) => b === at(e.baseSets, i)) ? e : new ImageSet(e.variable, e.expr, first(bases), ...bases.slice(1));
  }
  if (e instanceof ConditionSet) {
    const insym = e.variable.key === old.key || e.boundSymbols.some((v) => v.key === old.key);
    const base = cast(sub(e.base), SetExpr, 'base set');
    if (base.key !== e.base.key) return conditionSet(e.variable, insym ? e.condition : sub(e.condition), base);
    if (insym) return e;
    // a symbol-like replacement goes into the condition (SymPy _diff_wrt)
    return nw instanceof Sym ? conditionSet(e.variable, sub(e.condition), e.base) : e;
  }
  return undefined;
}

const previousRelation = impl.relational?.bind(impl);
impl.relational = (op, a, b) => {
  if ((op === 'Eq' || op === 'Ne') && (a instanceof SetExpr || b instanceof SetExpr)) {
    let equal: Truth = 'unknown';
    if (a instanceof SetExpr && b instanceof SetExpr) equal = truthAnd(tri(isSubset(a, b)), tri(isSubset(b, a)));
    else if (a instanceof Rational || b instanceof Rational || a instanceof Float || b instanceof Float) equal = false;
    if (equal !== 'unknown') return equal === (op === 'Eq') ? S.true : S.false;
  }
  return previousRelation?.(op, a, b);
};

impl.rebuildSet = rebuildSet;
impl.subsSet = subsSet;
impl.emptySet = () => EmptySet;
impl.interval = (a, b) => interval(a, b);
impl.setIntersection = (a, b) => intersection(cast(a, SetExpr, 'intersection operand'), cast(b, SetExpr, 'intersection operand'));

// SymPy PowerSet.rewrite(FiniteSet) and DisjointUnion.rewrite(Union) through rewrite(e, target); sets are
// classified by their kind ('Set') in the rewrite rules
registerRewrite('Set', 'FiniteSet', (_args, e) => (e instanceof PowerSetNode ? e.rewriteAsFiniteSet() : undefined));
registerRewrite('Set', 'PowerSet', (_args, e) => e instanceof FiniteSet ? e.rewriteAsPowerSet() : undefined);
registerRewrite('Set', 'Union', (_args, e) => (e instanceof DisjointUnionNode ? e.rewriteAsUnion() : undefined));

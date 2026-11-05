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
import { Add, Constant, Expr, ExtensionExpr, Float, Mul, Rational, S, Special, Sym, impl } from '../core/nodes';
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

/** Base class of all sets. */
export abstract class SetExpr extends Expr {
  readonly kind = 'Set' as const;
  abstract get className(): string;
  get isEmpty(): boolean {
    return false;
  }
  /** A set of the same class with new arguments (the sets of this module are rebuilt by rebuildSet). */
  withArgs(_args: readonly Expr[]): Expr {
    return this;
  }
  /** SymPy Set._contains for the set classes that define it: true, false or 'unknown'. */
  elementOf(_x: Expr): Truth {
    return 'unknown';
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
    return undefined;
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

// ---------------------------------------------------------------------------
// Interval
// ---------------------------------------------------------------------------

export class Interval extends SetExpr {
  readonly args: readonly Expr[];
  /** SymPy `Interval(a, b, left_open, right_open)` (EmptySet or a point when degenerate). */
  static of(a: ExprLike, b: ExprLike, leftOpen = false, rightOpen = false): SetExpr {
    return interval(a, b, leftOpen, rightOpen);
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
    return `Interval${m}(${p(a)}, ${p(b)})`;
  }
}

/** Interval(a, b) with open ends; empty or degenerate intervals simplify. */
export function interval(aIn: ExprLike, bIn: ExprLike, leftOpenIn = false, rightOpenIn = false): SetExpr {
  let leftOpen = leftOpenIn;
  let rightOpen = rightOpenIn;
  const a = sympify(aIn);
  const b = sympify(bIn);
  const c = cmpReal(a, b);
  if (c === 1) return EmptySet;
  if (c === 0) {
    if (leftOpen || rightOpen) return EmptySet;
    if (isInf(a)) return EmptySet;
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
  /** SymPy is_finite_set. */
  get isFiniteSet(): boolean {
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
  const inSeq = Eq(Mod(add(x, neg(a0)), step), 0);
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
  readonly args: readonly Expr[];
  constructor(
    readonly variable: Expr,
    readonly expr: Expr,
    readonly base: SetExpr,
  ) {
    super();
    this.args = [variable, expr, base];
  }
  get className(): string {
    return 'ImageSet';
  }
  /** SymPy ImageSet.lamda: the mapping as a Lambda. */
  get lamda(): LambdaNode {
    return new LambdaNode([this.variable, this.expr]);
  }
  /** SymPy ImageSet.base_sets. */
  get baseSets(): SetExpr[] {
    return [this.base];
  }
  protected computeKey(): string {
    return `ImageSet(${this.variable.key},${this.expr.key},${this.base.key})`;
  }
  printStr(p: (e: Expr) => string): string {
    return `ImageSet(Lambda(${p(this.variable)}, ${p(this.expr)}), ${p(this.base)})`;
  }
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
  if (base instanceof FiniteSet) return finiteSet(...base.args.map((a) => expr.subs([[v, a]])));
  if (base instanceof SetOp && base.op === 'Union') return union(...base.args.map((a) => imageSet(v, expr, a)));
  // a constant on a set that is not empty
  const standard: readonly SetExpr[] = [Integers, Naturals, Naturals0, Reals, Rationals, Complexes];
  const nonEmpty = standard.includes(base) || (base instanceof Interval && cmpReal(base.start, base.end) === -1);
  if (nonEmpty && v instanceof Sym && ![...expr.freeSymbols()].some((u) => u.key === v.key)) return finiteSet(expr);
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
  const pc = polyCoefficients(expr, v);
  if (!pc || ![...pc.values()].every((c) => !c.freeSymbols().size && isComparable(c))) return undefined;
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

/**
 * SymPy ConditionSet(sym, condition, base) with its evaluation: a true
 * condition gives the base set and a false one the empty set, a finite base
 * set is filtered, and a nested ConditionSet is merged.
 */
export function conditionSet(symIn: Expr, conditionIn: ExprLike | boolean, baseIn: SetExpr = UniversalSet): SetExpr {
  let sym = symIn;
  let base = baseIn;
  let condition: Expr = typeof conditionIn === 'boolean' ? (conditionIn ? S.true : S.false) : sympify(conditionIn);
  if (condition === S.true) return base;
  if (condition === S.false || base === EmptySet) return EmptySet;
  let know: SetExpr | undefined;
  if (base instanceof FiniteSet) {
    const yes: Expr[] = [];
    const maybe: Expr[] = [];
    for (const a of base.args) {
      const c = condition.subs([[sym, a]]);
      if (c === S.true) yes.push(a);
      else if (c !== S.false) maybe.push(a);
    }
    if (!maybe.length) return finiteSet(...yes);
    know = finiteSet(...yes);
    base = finiteSet(...maybe);
  }
  if (base instanceof ConditionSet) {
    const { variable: s, condition: c, base: b } = base;
    if (s.key === sym.key) {
      condition = and(condition, c);
      base = b;
    } else if (![...c.freeSymbols()].some((u) => u.key === sym.key)) {
      condition = and(condition, xreplace(c, [[s, sym]]));
      base = b;
    } else if (![...condition.freeSymbols()].some((u) => u.key === s.key)) {
      condition = and(xreplace(condition, [[sym, s]]), c);
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
  constructor(
    readonly op: 'Union' | 'Intersection' | 'Complement',
    readonly args: readonly SetExpr[],
  ) {
    super();
  }
  get className(): string {
    return this.op;
  }
  protected computeKey(): string {
    return `${this.op}(${this.args.map((a) => a.key).join(',')})`;
  }
  printStr(p: (e: Expr) => string): string {
    return `${this.op}(${this.args.map(p).join(', ')})`;
  }
}
export { SetOp };

// ---------------------------------------------------------------------------
// ProductSet / PowerSet / DisjointUnion / SymmetricDifference
// ---------------------------------------------------------------------------

/** The Cartesian product of sets (SymPy ProductSet); its elements are Tuples. */
export class ProductSetNode extends SetExpr {
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
  readonly args: readonly Expr[];
  constructor(readonly arg: SetExpr) {
    super();
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
  constructor(readonly args: readonly SetExpr[]) {
    super();
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
  if (s === Rationals) {
    if (x instanceof Rational || isIntegerQ(x) === true) return true;
    // oo, I and the irrational constants pi, E, GoldenRatio and TribonacciConstant are not rational
    if (x instanceof Special || isReal(x) === false || (x instanceof Constant && IRRATIONAL.has(x.name))) return false;
    return undefined;
  }
  if (s === Reals) {
    if (isInf(x)) return false;
    const v = realValue(x);
    return v === undefined ? (impl.isReal?.(x) ?? undefined) : true;
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
    const unknown = s.args.some((a) => cmpReal(a, x) === undefined);
    return unknown ? undefined : false;
  }
  if (s instanceof Interval) {
    if (isInf(x)) return false;
    const lo = cmpReal(s.start, x);
    const hi = cmpReal(x, s.end);
    if (lo === undefined || hi === undefined) return undefined;
    const okLo = s.leftOpen ? lo < 0 : lo <= 0;
    const okHi = s.rightOpen ? hi < 0 : hi <= 0;
    return okLo && okHi;
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

/** A decided membership, or 'unknown'. */
const tri = (v: boolean | undefined): Truth => v ?? 'unknown';

/**
 * SymPy ImageSet._contains for a number x and a polynomial expression: x is in
 * the image when a root of expr = x is in the base set.
 */
function imageContains(s: ImageSet, x: Expr): boolean | undefined {
  const v = s.variable;
  if (!(v instanceof Sym) || x.freeSymbols().size) return undefined;
  const eq = add(s.expr, mul(-1, x));
  const pc = polyCoefficients(eq, v);
  if (!pc) return undefined;
  let rs: Expr[];
  try {
    rs = rootsDict(eq, v, { multiple: true });
  } catch {
    // no formula for the roots
    return undefined;
  }
  const inBase = rs.map((r) => containsQ(s.base, r));
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
  }
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
  const v = containsQ(s, x);
  if (v !== undefined) return v ? S.true : S.false;
  if (s === Reals || s instanceof Interval) return asRelational(s, x);
  if (s instanceof FiniteSet) return or(...s.args.map((a) => Eq(a, x)));
  if (s instanceof Range) {
    // a condition on the symbols of the Range (SymPy Range._contains)
    const c = rangeContains(s, x);
    if (c !== undefined) return c;
  }
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
  // the rationals contain the integers and the naturals (SymPy union_sets)
  if (sets.includes(Rationals) && sets.every((s) => s === Rationals || s === Integers || s === Naturals || s === Naturals0)) return Rationals;
  if (sets.some((s) => s === Reals) && sets.every((s) => s === Reals || s instanceof Interval || (s instanceof FiniteSet && s.args.every((a) => containsQ(Reals, a) === true)))) return Reals;
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
      if (iv.leftOpen && cmpReal(iv.start, pt) === 0) {
        absorbed = true;
        return new Interval(iv.start, iv.end, false, iv.rightOpen);
      }
      if (iv.rightOpen && cmpReal(iv.end, pt) === 0) {
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

/** Intersection of sets. */
export function intersection(...sets: SetExpr[]): SetExpr {
  if (sets.some((s) => s === EmptySet)) return EmptySet;
  let acc: SetExpr = first(sets);
  for (const s of sets.slice(1)) acc = intersectTwo(acc, s);
  return acc;
}

function intersectTwo(a: SetExpr, b: SetExpr): SetExpr {
  if (a === EmptySet || b === EmptySet) return EmptySet;
  if (a === UniversalSet) return b;
  if (b === UniversalSet) return a;
  const fo: [FiniteSet, SetExpr] | undefined = a instanceof FiniteSet ? [a, b] : b instanceof FiniteSet ? [b, a] : undefined;
  if (fo !== undefined) {
    const [f, o] = fo;
    const keep: Expr[] = [];
    const unknown: Expr[] = [];
    for (const x of f.args) {
      const c = containsQ(o, x);
      if (c === true) keep.push(x);
      else if (c === undefined) unknown.push(x);
    }
    // like SymPy, the elements known to be in o stay in the unevaluated intersection
    if (unknown.length) return new SetOp('Intersection', sortSets([finiteSet(...keep, ...unknown), o]));
    return finiteSet(...keep);
  }
  const intIv = (u: SetExpr, v: SetExpr) => (u === Integers || u === Naturals || u === Naturals0) && v instanceof Interval;
  const ints: [SetExpr, Interval] | undefined = intIv(a, b) ? [a, cast(b, Interval)] : intIv(b, a) ? [b, cast(a, Interval)] : undefined;
  if (ints) {
    const [z, iv] = ints;
    const r = integersIn(iv, z === Naturals ? S.One : z === Naturals0 ? S.Zero : S.NegativeInfinity);
    if (r) return r;
  }
  if ((a === Reals && (b === Integers || b === Naturals || b === Naturals0)) || (b === Reals && (a === Integers || a === Naturals || a === Naturals0))) return a === Reals ? b : a;
  if (a === Reals && (b instanceof Interval || b === Reals)) return b;
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
  if (o === Integers || o === Reals || o === Rationals) return r;
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

/**
 * SymPy intersection_sets(ImageSet, Set): for images of the integers under
 * linear maps with rational coefficients the common values (solving the
 * linear diophantine equation f(n) = g(m)), and for a linear image and an
 * interval the image of the integers whose values fall in the interval.
 */
function intersectImage(s: ImageSet, o: SetExpr): SetExpr | undefined {
  const f = linearIn(s.expr, s.variable);
  if (!f) return undefined;
  if (s.base === Integers && (o === Integers || (o instanceof ImageSet && o.base === Integers))) {
    const g = o instanceof ImageSet ? linearIn(o.expr, o.variable) : ([S.One, S.Zero] as [Expr, Expr]);
    if (!g || ![...f, ...g].every((c) => c instanceof Rational)) return undefined;
    const [a1, b1, a2, b2] = [asRat(f[0]), asRat(f[1]), asRat(g[0]), asRat(g[1])];
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
    return imageSet(n, add(mul(a1, Rational.of(A2 / gg), n), mul(a1, Rational.of(n0)), b1), Integers);
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
  const [start, lo] = cs > 0 ? [a.start, a.leftOpen] : cs < 0 ? [b.start, b.leftOpen] : [a.start, a.leftOpen || b.leftOpen];
  const [end, ro] = ce < 0 ? [a.end, a.rightOpen] : ce > 0 ? [b.end, b.rightOpen] : [a.end, a.rightOpen || b.rightOpen];
  return interval(start, end, lo, ro);
}

/** a \ b. */
export function complement(a: SetExpr, b: SetExpr): SetExpr {
  if (b === EmptySet) return a;
  if (a === EmptySet || b === UniversalSet) return EmptySet;
  if (a instanceof FiniteSet) {
    const keep: Expr[] = [];
    const unknown: Expr[] = [];
    for (const x of a.args) {
      const c = containsQ(b, x);
      if (c === false) keep.push(x);
      else if (c === undefined) unknown.push(x);
    }
    if (unknown.length) return union(finiteSet(...keep), new SetOp('Complement', [finiteSet(...unknown), b]));
    return finiteSet(...keep);
  }
  const pa = intervalParts(a);
  const points = b instanceof FiniteSet ? b.args.map((x) => [x, realValue(x)] as const) : undefined;
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
  if (a === EmptySet || b === UniversalSet || a.key === b.key) return true;
  if (a === UniversalSet) return false;
  if ((a === Integers || a === Naturals || a === Naturals0) && (b === Rationals || b === Reals || b === Complexes)) return true;
  if (a === Rationals && (b === Reals || b === Complexes)) return true;
  if ((a === Naturals || a === Naturals0) && b === Integers) return true;
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
    const cs = a.args.map((x) => containsQ(b, x));
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
  if (s instanceof SetOp && s.op === 'Union') return or(...s.args.map((a) => asRelational(a, x)));
  if (s instanceof SetOp && s.op === 'Intersection') return and(...s.args.map((a) => asRelational(a, x)));
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
  if (e instanceof ImageSet) return new ImageSet(at(args, 0), at(args, 1), cast(at(args, 2), SetExpr, 'base set'));
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
  if (e instanceof ImageSet && e.variable.key === old.key) {
    const base = cast(sub(e.base), SetExpr, 'base set');
    return base === e.base ? e : new ImageSet(e.variable, e.expr, base);
  }
  if (e instanceof ConditionSet) {
    const insym = e.variable.key === old.key;
    const base = cast(sub(e.base), SetExpr, 'base set');
    if (base.key !== e.base.key) return conditionSet(e.variable, insym ? e.condition : sub(e.condition), base);
    if (insym) return e;
    // a symbol-like replacement goes into the condition (SymPy _diff_wrt)
    return nw instanceof Sym ? conditionSet(e.variable, sub(e.condition), e.base) : e;
  }
  return undefined;
}

impl.rebuildSet = rebuildSet;
impl.subsSet = subsSet;
impl.emptySet = () => EmptySet;
impl.interval = (a, b) => interval(a, b);
impl.setIntersection = (a, b) => intersection(cast(a, SetExpr, 'intersection operand'), cast(b, SetExpr, 'intersection operand'));

// SymPy PowerSet.rewrite(FiniteSet) and DisjointUnion.rewrite(Union) through rewrite(e, target); sets are
// classified by their kind ('Set') in the rewrite rules
registerRewrite('Set', 'FiniteSet', (_args, e) => (e instanceof PowerSetNode ? e.rewriteAsFiniteSet() : undefined));
registerRewrite('Set', 'Union', (_args, e) => (e instanceof DisjointUnionNode ? e.rewriteAsUnion() : undefined));

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy AccumulationBounds (AccumBounds): a closed interval of real
 * values with interval arithmetic. Arithmetic with other expressions is
 * performed by add/mul/pow (core/ops.ts) through impl.accumBounds, and the
 * monotone and periodic functions map intervals (functions/elementary).
 */

import type { Expr, ExprLike } from './nodes';
import { Add, ExtensionExpr, Fn, Mul, Pow, Rational, S, Special, impl, isNum } from './nodes';
import { isIntegerQ, isKnownExtendedReal, isNegative, isNonNegative, isPositive, isReal } from './assumptions';
import { add, mul, pow, sympify } from './ops';
import { Le } from './logic';
import { and } from './boolalg';
import { callableClass } from './callable';
import { NotLoadedError } from './errors';
import { at, cast } from './guard';

const isInf = (e: Expr): boolean => e instanceof Special && e.name === 'oo';
const isNegInf = (e: Expr): boolean => e instanceof Special && e.name === '-oo';
/** Numeric value of a real bound (+-Infinity for +-oo). */
const val = (e: Expr): number => (isInf(e) ? Infinity : isNegInf(e) ? -Infinity : e.toNumber());
const lt = (a: Expr, b: Expr): boolean => isNegative(add(a, mul(-1, b))) === true;
const minOf = (xs: Expr[]): Expr => xs.reduce((m, x) => (lt(x, m) ? x : m));
const maxOf = (xs: Expr[]): Expr => xs.reduce((m, x) => (lt(m, x) ? x : m));
/** a*b with 0*oo = 0 (the product of interval bounds). */
const bmul = (a: Expr, b: Expr): Expr => {
  const z = (e: Expr) => e instanceof Rational && e.isZero;
  return z(a) || z(b) ? S.Zero : mul(a, b);
};

const setsNotLoaded = (): never => {
  throw new NotLoadedError("sets are not available: import '@symjs/symjs/sets' (or '@symjs/symjs')");
};

const asAB = (e: Expr): AccumBoundsNode => cast(e, AccumBoundsNode, 'AccumBounds operand');

/**
 * A closed interval [min, max] of real values (SymPy AccumulationBounds).
 *
 * @see SymPy `sympy.calculus.accumulationbounds.AccumulationBounds`
 * @example
 * ```ts
 * import { AccumBoundsNode, ex } from '@symjs/symjs';
 *
 * new AccumBoundsNode(ex`1`, ex`3`).mid; // => 2
 * ```
 */
export class AccumBoundsNode extends ExtensionExpr {
  /**
   * Creates an `AccumBoundsNode`.
   *
   * @param min - The lower endpoint.
   * @param max - The upper endpoint.
   */
  constructor(min: Expr, max: Expr) {
    super('AccumBounds', [min, max]);
  }
  /**
   * Rebuilds the node with the supplied arguments.
   *
   * @param args - The replacement arguments, in node order.
   * @returns The expression rebuilt with the new arguments.
   */
  withArgs(args: readonly Expr[]): Expr {
    return accumBounds(at(args, 0), at(args, 1));
  }
  /**
   * The lower bound.
   *
   * @returns The lower bound.
   * @see SymPy `sympy.calculus.accumulationbounds.AccumulationBounds.min`
   */
  get min(): Expr {
    return at(this.args, 0);
  }
  /**
   * The upper bound.
   *
   * @returns The upper bound.
   * @see SymPy `sympy.calculus.accumulationbounds.AccumulationBounds.max`
   */
  get max(): Expr {
    return at(this.args, 1);
  }
  /**
   * max - min (SymPy delta).
   *
   * @returns The interval width.
   * @see SymPy `sympy.calculus.accumulationbounds.AccumulationBounds.delta`
   */
  get delta(): Expr {
    return add(this.max, mul(-1, this.min));
  }
  /**
   * (min + max)/2 (SymPy mid).
   *
   * @returns The interval midpoint.
   * @see SymPy `sympy.calculus.accumulationbounds.AccumulationBounds.mid`
   */
  get mid(): Expr {
    return mul(add(this.min, this.max), Rational.of(1n, 2n));
  }
  /**
   * Every accumulation bound is extended real.
   *
   * @returns True for an interval of extended real values.
   */
  override isRealSelf(): boolean {
    return true;
  }
  /**
   * A real interval is its own conjugate and adjoint.
   *
   * @returns A real interval is its own conjugate and adjoint.
   */
  override conjugateSelf(): Expr {
    return this;
  }
  /**
   * Computes the adjoint of this node.
   *
   * @returns The adjoint of this node.
   */
  override adjointSelf(): Expr {
    return this;
  }
  /**
   * Formats the node in LaTeX using the supplied child printer.
   *
   * @param print - The printer to use for child expressions.
   * @returns The formatted string.
   */
  override printLatex(print: (e: Expr) => string): string {
    return `\\left\\langle ${print(this.min)}, ${print(this.max)}\\right\\rangle`;
  }
  /**
   * x lies in the interval (SymPy `x in AccumBounds(...)`).
   *
   * @param x - The argument of the function.
   * @returns Whether the point belongs to the interval.
   * @throws TypeError when the argument is nonreal or membership is undecidable.
   */
  contains(x: ExprLike): boolean {
    const e = sympify(x);
    if (!isKnownExtendedReal(e)) throw new TypeError('Input must be a real number');
    if (isInf(e) || isNegInf(e)) return isNegInf(this.min) || isInf(this.max);
    const inside = and(Le(this.min, e), Le(e, this.max));
    if (inside === S.true) return true;
    if (inside === S.false) return false;
    throw new TypeError('Cannot determine membership in AccumBounds');
  }
  /**
   * The intersection with another AccumBounds, an Interval or a FiniteSet (SymPy intersection).
   *
   * @param other - The other operand.
   * @returns The intersection with another AccumBounds, an Interval or a FiniteSet (SymPy intersection).
   * @see SymPy `sympy.calculus.accumulationbounds.AccumulationBounds.intersection`
   */
  intersection(other: Expr): Expr {
    if (other instanceof AccumBoundsNode) {
      const lo = lt(this.min, other.min) ? other.min : this.min;
      const hi = lt(this.max, other.max) ? this.max : other.max;
      if (lt(hi, lo)) return impl.emptySet === undefined ? setsNotLoaded() : impl.emptySet();
      return accumBounds(lo, hi);
    }
    if (impl.setIntersection === undefined || impl.interval === undefined) return setsNotLoaded();
    return impl.setIntersection(impl.interval(this.min, this.max), other);
  }
  /**
   * The union with an overlapping AccumBounds (SymPy union).
   *
   * @param other - The other operand.
   * @returns The resulting set.
   * @throws RangeError when the intervals do not overlap.
   * @see SymPy `sympy.calculus.accumulationbounds.AccumulationBounds.union`
   */
  union(other: AccumBoundsNode): Expr {
    if (lt(this.max, other.min) || lt(other.max, this.min)) throw new RangeError('AccumBounds.union: the intervals do not overlap');
    return accumBounds(minOf([this.min, other.min]), maxOf([this.max, other.max]));
  }
}

/** AccumBounds(min, max); a single point is the number itself (SymPy). */
export function accumBounds(minIn: ExprLike, maxIn: ExprLike): Expr {
  const lo = sympify(minIn);
  const hi = sympify(maxIn);
  if (!isKnownExtendedReal(lo) || !isKnownExtendedReal(hi)) throw new TypeError('AccumBounds: the bounds must be real numbers');
  if (lt(hi, lo)) throw new RangeError('AccumBounds: the lower bound must not exceed the upper bound');
  if (lo.key === hi.key) return lo;
  return new AccumBoundsNode(lo, hi);
}

/**
 * Constructs a closed interval containing the possible accumulation values.
 *
 * @param minIn - The min in.
 * @param maxIn - The max in.
 * @returns A closed accumulation interval or its value when the endpoints coincide.
 * @throws TypeError when an endpoint is not known to be extended real.
 * @throws RangeError when the lower endpoint exceeds the upper endpoint.
 * @see SymPy `sympy.calculus.accumulationbounds.AccumulationBounds`
 * @example
 * ```ts
 * import { AccumBounds } from '@symjs/symjs';
 *
 * AccumBounds(1, 3); // => AccumBounds(1, 3)
 * ```
 */
export const AccumBounds = /* @__PURE__ */ callableClass(AccumBoundsNode, accumBounds);

// ---- interval arithmetic used by add/mul/pow -------------------------------------------

/** The sum of intervals and a number; a non-real number stays beside them (SymPy AccumBounds(1, 2) + I). */
function abAdd(abs: readonly Expr[], c: Expr): Expr {
  if (!isKnownExtendedReal(c)) return new Add([c, ...abs]);
  if ((isInf(c) && abs.some((a) => isNegInf(asAB(a).min))) || (isNegInf(c) && abs.some((a) => isInf(asAB(a).max)))) return accumBounds(S.NegativeInfinity, S.Infinity);
  const mins = abs.map((a) => asAB(a).min);
  const maxes = abs.map((a) => asAB(a).max);
  const lo = mins.some(isNegInf) ? S.NegativeInfinity : add(c, ...mins);
  const hi = maxes.some(isInf) ? S.Infinity : add(c, ...maxes);
  return accumBounds(lo, hi);
}

/** The product of intervals and a number; a non-real number stays beside them (SymPy I*AccumBounds(1, 2)). */
function abMul(abs: readonly Expr[], c: Expr): Expr {
  // The whole extended real line absorbs products, including an indeterminate scalar factor.
  const full = abs.find((x) => asAB(x).min === S.NegativeInfinity && asAB(x).max === S.Infinity);
  if (full !== undefined) return full;
  if (isReal(c) !== true) return new Mul([c, ...abs]);
  let { min: lo, max: hi } = asAB(at(abs, 0));
  for (const x of abs.slice(1)) {
    const a = asAB(x);
    const cands = [bmul(lo, a.min), bmul(lo, a.max), bmul(hi, a.min), bmul(hi, a.max)];
    [lo, hi] = [minOf(cands), maxOf(cands)];
  }
  if (isNum(c) && c.isZero) return accumBounds(isNegInf(lo) ? lo : S.Zero, isInf(hi) ? hi : S.Zero);
  if (isPositive(c)) return accumBounds(bmul(c, lo), bmul(c, hi));
  if (isNegative(c)) return accumBounds(bmul(c, hi), bmul(c, lo));
  return new Mul([c, ...abs]);
}

/** An interval raised to a number. */
function abPow(a: AccumBoundsNode, e: Expr): Expr {
  if (e instanceof AccumBoundsNode) {
    if (!(isPositive(a.min) || (isNonNegative(a.min) && isNonNegative(e.min)))) return new Pow(a, e);
    if (e.freeSymbols().size > 0 || a.freeSymbols().size > 0) return new Pow(a, e);
    const powers = [abPow(a, e.min), abPow(a, e.max)];
    const endpoints = powers.flatMap((p) => p instanceof AccumBoundsNode ? [p.min, p.max] : [p]);
    return accumBounds(minOf(endpoints), maxOf(endpoints));
  }
  // SymPy AccumBounds.__pow__: [a, b]**-oo = (1/[a, b])**oo
  if (e === S.NegativeInfinity) return pow(abPow(a, S.NegOne), S.Infinity);
  if (e === S.Infinity) {
    const [lo, hi] = [val(a.min), val(a.max)];
    if (lo >= 0) return hi < 1 ? S.Zero : lo > 1 ? S.Infinity : accumBounds(S.Zero, S.Infinity);
    if (hi < 0) return lo > -1 ? S.Zero : hi < -1 ? S.ComplexInfinity : S.NaN;
    if (lo > -1) return hi < 1 ? S.Zero : accumBounds(S.Zero, S.Infinity);
    return accumBounds(S.NegativeInfinity, S.Infinity);
  }
  if (e instanceof Rational && e.q === 1n) {
    const n = e.p;
    if (n === 0n) return S.One;
    if (n > 0n) {
      const p = (x: Expr) => pow(x, e);
      if (n % 2n === 1n || val(a.min) >= 0) return accumBounds(p(a.min), p(a.max));
      if (val(a.max) <= 0) return accumBounds(p(a.max), p(a.min));
      return accumBounds(S.Zero, maxOf([p(a.min), p(a.max)]));
    }
    // negative powers: 1/[a, b] (an interval, as 1/b < 1/a when 0 is outside, else (-oo, oo))
    // with 0 as an end point: 1/[0, b] = [1/b, oo], 1/[a, 0] = [-oo, 1/a]
    const [lo, hi] = [val(a.min), val(a.max)];
    const inv =
      lo > 0 || hi < 0
        ? accumBounds(pow(a.max, -1), pow(a.min, -1))
        : lo === 0 && hi > 0
          ? accumBounds(pow(a.max, -1), S.Infinity)
          : hi === 0 && lo < 0
            ? accumBounds(S.NegativeInfinity, pow(a.min, -1))
            : accumBounds(S.NegativeInfinity, S.Infinity);
    return n === -1n ? inv : abPow(asAB(inv), Rational.of(-n));
  }
  // a fractional power of a nonnegative interval is monotone; 0**e = oo for e < 0
  if (isNonNegative(a.min) === true && isNonNegative(e) === true) return accumBounds(pow(a.min, e), pow(a.max, e));
  if (isNonNegative(a.min) === true && isNegative(e) === true) return accumBounds(pow(a.max, e), a.min.equals(S.Zero) ? S.Infinity : pow(a.min, e));
  if (isIntegerQ(e) === true && (isPositive(a.min) === true || isNegative(a.max) === true)) {
    const ends = [pow(a.min, e), pow(a.max, e)];
    return accumBounds(new Fn('Min', ends), new Fn('Max', ends));
  }
  // SymPy leaves a fractional power of an interval containing negative numbers unevaluated
  return new Pow(a, e);
}

impl.accumBounds = {
  is: (e: Expr): e is Expr => e instanceof AccumBoundsNode,
  add: (abs: readonly Expr[], c: Expr) => abAdd(abs, c),
  mul: (abs: readonly Expr[], c: Expr) => abMul(abs, c),
  pow: (a: Expr, e: Expr) => abPow(asAB(a), e),
  bounds: (a: Expr) => {
    const ab = asAB(a);
    return [ab.min, ab.max];
  },
  make: (lo: Expr, hi: Expr) => accumBounds(lo, hi),
};

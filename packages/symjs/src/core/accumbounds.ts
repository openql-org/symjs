// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy AccumulationBounds (AccumBounds): a closed interval of real
 * values with interval arithmetic. Arithmetic with other expressions is
 * performed by add/mul/pow (core/ops.ts) through impl.accumBounds, and the
 * monotone and periodic functions map intervals (functions/elementary).
 */

import type { Expr, ExprLike } from './nodes';
import { ExtensionExpr, Rational, S, Special, impl } from './nodes';
import { add, mul, pow, sympify } from './ops';
import { callableClass } from './callable';
import { NotImplementedError } from './errors';

const isInf = (e: Expr): boolean => e instanceof Special && e.name === 'oo';
const isNegInf = (e: Expr): boolean => e instanceof Special && e.name === '-oo';
/** Numeric value of a real bound (+-Infinity for +-oo). */
const val = (e: Expr): number => (isInf(e) ? Infinity : isNegInf(e) ? -Infinity : e.toNumber());
const lt = (a: Expr, b: Expr): boolean => val(a) < val(b);
const minOf = (xs: Expr[]): Expr => xs.reduce((m, x) => (lt(x, m) ? x : m));
const maxOf = (xs: Expr[]): Expr => xs.reduce((m, x) => (lt(m, x) ? x : m));
/** a*b with 0*oo = 0 (the product of interval bounds). */
const bmul = (a: Expr, b: Expr): Expr => {
  const z = (e: Expr) => e instanceof Rational && e.isZero;
  return z(a) || z(b) ? S.Zero : mul(a, b);
};

/** A closed interval [min, max] of real values (SymPy AccumulationBounds). */
export class AccumBoundsNode extends ExtensionExpr {
  constructor(min: Expr, max: Expr) {
    super('AccumBounds', [min, max]);
  }
  withArgs(args: readonly Expr[]): Expr {
    return accumBounds(args[0]!, args[1]!);
  }
  /** The lower bound. */
  get min(): Expr {
    return this.args[0]!;
  }
  /** The upper bound. */
  get max(): Expr {
    return this.args[1]!;
  }
  /** max - min (SymPy delta). */
  get delta(): Expr {
    return add(this.max, mul(-1, this.min));
  }
  /** (min + max)/2 (SymPy mid). */
  get mid(): Expr {
    return mul(add(this.min, this.max), Rational.of(1n, 2n));
  }
  override printLatex(print: (e: Expr) => string): string {
    return `\\left\\langle ${print(this.min)}, ${print(this.max)}\\right\\rangle`;
  }
  /** x lies in the interval (SymPy `x in AccumBounds(...)`). */
  contains(x: ExprLike): boolean {
    const v = val(sympify(x));
    return val(this.min) <= v && v <= val(this.max);
  }
  /** The intersection with another AccumBounds, an Interval or a FiniteSet (SymPy intersection). */
  intersection(other: Expr): Expr {
    if (other instanceof AccumBoundsNode) {
      const lo = lt(this.min, other.min) ? other.min : this.min;
      const hi = lt(this.max, other.max) ? this.max : other.max;
      if (lt(hi, lo)) return impl.emptySet!();
      return accumBounds(lo, hi);
    }
    return impl.setIntersection!(impl.interval!(this.min, this.max), other);
  }
  /** The union with an overlapping AccumBounds (SymPy union). */
  union(other: AccumBoundsNode): Expr {
    if (lt(this.max, other.min) || lt(other.max, this.min)) throw new RangeError('AccumBounds.union: the intervals do not overlap');
    return accumBounds(minOf([this.min, other.min]), maxOf([this.max, other.max]));
  }
}

/** AccumBounds(min, max); a single point is the number itself (SymPy). */
export function accumBounds(minIn: ExprLike, maxIn: ExprLike): Expr {
  const lo = sympify(minIn);
  const hi = sympify(maxIn);
  if (lo.freeSymbols().size || hi.freeSymbols().size) throw new TypeError('AccumBounds: the bounds must be real numbers');
  if (lt(hi, lo)) throw new RangeError('AccumBounds: the lower bound must not exceed the upper bound');
  if (lo.key === hi.key) return lo;
  return new AccumBoundsNode(lo, hi);
}

/** SymPy AccumBounds(min, max), callable and usable with instanceof. */
export const AccumBounds = /* @__PURE__ */ callableClass(AccumBoundsNode, accumBounds);

// ---- interval arithmetic used by add/mul/pow -------------------------------------------

/** The sum of intervals and a number. */
function abAdd(abs: AccumBoundsNode[], c: Expr): Expr {
  const lo = add(c, ...abs.map((a) => a.min));
  const hi = add(c, ...abs.map((a) => a.max));
  return accumBounds(lo, hi);
}

/** The product of intervals and a number. */
function abMul(abs: AccumBoundsNode[], c: Expr): Expr {
  let lo: Expr = c;
  let hi: Expr = c;
  for (const a of abs) {
    const cands = [bmul(lo, a.min), bmul(lo, a.max), bmul(hi, a.min), bmul(hi, a.max)];
    [lo, hi] = [minOf(cands), maxOf(cands)];
  }
  return accumBounds(lo, hi);
}

/** An interval raised to a number. */
function abPow(a: AccumBoundsNode, e: Expr): Expr {
  const v = val(e);
  if (e instanceof Rational && e.q === 1n) {
    const n = e.p;
    if (n === 0n) return S.One;
    if (n > 0n) {
      const p = (x: Expr) => pow(x, e);
      if (n % 2n === 1n || val(a.min) >= 0) return accumBounds(p(a.min), p(a.max));
      if (val(a.max) <= 0) return accumBounds(p(a.max), p(a.min));
      return accumBounds(S.Zero, maxOf([p(a.min), p(a.max)]));
    }
    // negative powers: 1/[a, b]
    const inv = val(a.min) > 0 || val(a.max) < 0 ? accumBounds(pow(a.max, -1), pow(a.min, -1)) : accumBounds(S.NegativeInfinity, S.Infinity);
    return n === -1n ? inv : abPow(inv as AccumBoundsNode, Rational.of(-n));
  }
  if (val(a.min) >= 0 && v > 0) return accumBounds(pow(a.min, e), pow(a.max, e));
  if (val(a.min) > 0 && v < 0) return accumBounds(pow(a.max, e), pow(a.min, e));
  throw new NotImplementedError(`AccumBounds ** ${String(v)}`);
}

impl.accumBounds = {
  is: (e: Expr): e is Expr => e instanceof AccumBoundsNode,
  add: (abs: readonly Expr[], c: Expr) => abAdd(abs as AccumBoundsNode[], c),
  mul: (abs: readonly Expr[], c: Expr) => abMul(abs as AccumBoundsNode[], c),
  pow: (a: Expr, e: Expr) => abPow(a as AccumBoundsNode, e),
  bounds: (a: Expr) => [(a as AccumBoundsNode).min, (a as AccumBoundsNode).max],
  make: (lo: Expr, hi: Expr) => accumBounds(lo, hi),
};

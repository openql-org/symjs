// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Entry point `@symjs/symjs/sets`: sets (intervals, finite sets, image and
 * condition sets).
 */

// every entry point brings the core with its registrations
import './core';

export {
  SetExpr,
  Interval,
  FiniteSet,
  ImageSet,
  ConditionSet,
  Range,
  imageSet as imageset,
  EmptySet,
  Reals,
  Integers,
  Naturals,
  Naturals0,
  Complexes,
  union as Union,
  intersection as Intersection,
  complement as Complement,
  contains,
  Contains,
  asRelational,
  inf,
  sup,
  Rationals,
  UniversalSet,
  ProductSet,
  ProductSetNode,
  PowerSet,
  PowerSetNode,
  powerset,
  DisjointUnion,
  DisjointUnionNode,
  SymmetricDifference,
  SymmetricDifferenceNode,
  symmetricDifference,
} from './sets/sets';
export { OmegaPower, OmegaPowerNode, Ordinal, OrdinalNode, convertOrdinal, omega, ord0 } from './sets/ordinals';
export type { OrdinalLike } from './sets/ordinals';
export { ComplexRegion, ComplexRegionNode, CartesianComplexRegion, PolarComplexRegion, normalizeThetaSet } from './sets/complexregion';

// ---- deprecated names (kept during 0.x, removed in 1.0; see docs/api-policy.md) ----

import { SetOp as _SetOp_ } from './sets/sets';
import { imageSet as _imageSet_ } from './sets/sets';
import { interval as _interval_ } from './sets/sets';
import { openInterval as _openInterval_ } from './sets/sets';
import { Lopen as _Lopen_ } from './sets/sets';
import { Ropen as _Ropen_ } from './sets/sets';
import { finiteSet as _finiteSet_ } from './sets/sets';
import { union as _union_ } from './sets/sets';
import { complement as _complement_ } from './sets/sets';
import { containsQ as _containsQ_, isSubset as _isSubset_, type SetExpr as _SetExpr_ } from './sets/sets';
import { type Truth, toTruth as _toTruth_ } from './core/truth';
import type { Expr as _Expr_ } from './core/nodes';

/**
 * An unevaluated union, intersection or complement of sets.
 *
 * @deprecated Internal; removed from the public API in 1.0.
 */
export const SetOp = _SetOp_;

/** @deprecated Internal; removed from the public API in 1.0. */
export type SetOp = _SetOp_;

/**
 * Alias for {@link imageset}.
 *
 * @deprecated Use {@link imageset}.
 * @param v - The value to examine.
 * @param exprIn - The input expression.
 * @param base - The base of the power.
 * @returns The image of the base set under the mapping.
 * @see SymPy `sympy.sets.sets.imageset`
 * @example
 * ```ts
 * import { ex, finiteSet, imageSet } from '@symjs/symjs';
 *
 * imageSet(ex`x`, ex`x**2`, finiteSet(1, 2)); // => {1, 4}
 * ```
 */
export const imageSet = _imageSet_;

/**
 * Alias for {@link Interval.of}.
 *
 * @deprecated Use {@link Interval.of}.
 * @param aIn - The first operand.
 * @param bIn - The second operand.
 * @param leftOpenIn - The left open in.
 * @param rightOpenIn - The right open in.
 * @returns The resulting set.
 * @see SymPy `sympy.sets.sets.Interval`
 * @example
 * ```ts
 * import { interval } from '@symjs/symjs';
 *
 * interval(0, 1); // => Interval(0, 1)
 * ```
 */
export const interval = _interval_;

/**
 * Alias for {@link Interval.open}.
 *
 * @deprecated Use {@link Interval.open}.
 * @param a - The first operand.
 * @param b - The second operand.
 * @returns The resulting set.
 * @see SymPy `sympy.sets.sets.Interval.open`
 */
export const openInterval = _openInterval_;

/**
 * Alias for {@link Interval.Lopen}.
 *
 * @deprecated Use {@link Interval.Lopen}.
 * @param a - The first operand.
 * @param b - The second operand.
 * @returns The resulting set.
 * @see SymPy `sympy.sets.sets.Interval.Lopen`
 */
export const Lopen = _Lopen_;

/**
 * Alias for {@link Interval.Ropen}.
 *
 * @deprecated Use {@link Interval.Ropen}.
 * @param a - The first operand.
 * @param b - The second operand.
 * @returns The resulting set.
 * @see SymPy `sympy.sets.sets.Interval.Ropen`
 */
export const Ropen = _Ropen_;

/**
 * Alias for {@link FiniteSet.of}.
 *
 * @deprecated Use {@link FiniteSet.of}.
 * @param xs - The operands, in order.
 * @returns The resulting set.
 * @see SymPy `sympy.sets.sets.FiniteSet`
 * @example
 * ```ts
 * import { finiteSet } from '@symjs/symjs';
 *
 * finiteSet(1, 2, 3, 4); // => {1, 2, 3, 4}
 * ```
 */
export const finiteSet = _finiteSet_;

/**
 * Alias for {@link Union}.
 *
 * @deprecated Use {@link Union}.
 * @param sets0 - The sets0.
 * @returns The resulting set.
 * @see SymPy `sympy.sets.sets.Union`
 * @example
 * ```ts
 * import { finiteSet, union } from '@symjs/symjs';
 *
 * union(finiteSet(1), finiteSet(2)); // => {1, 2}
 * ```
 */
export const union = _union_;

/**
 * Alias for {@link Complement}.
 *
 * @deprecated Use {@link Complement}.
 * @param a - The first operand.
 * @param b - The second operand.
 * @returns The resulting set.
 * @see SymPy `sympy.sets.sets.Complement`
 * @example
 * ```ts
 * import { complement, finiteSet } from '@symjs/symjs';
 *
 * complement(finiteSet(1, 2), finiteSet(2)); // => {1}
 * ```
 */
export const complement = _complement_;

/**
 * Tests whether an element belongs to a set.
 *
 * @deprecated Internal; removed from the public API in 1.0.
 * @param s - The input value.
 * @param x - The argument of the function.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 */
export const containsQ = (s: _SetExpr_, x: _Expr_): Truth => _toTruth_(_containsQ_(s, x));

/**
 * A is a subset of b (true, false or 'unknown').
 *
 * @param a - The first operand.
 * @param b - The second operand.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 * @see SymPy `sympy.sets.sets.Set.is_subset`
 * @example
 * ```ts
 * import { finiteSet, isSubset } from '@symjs/symjs';
 *
 * isSubset(finiteSet(1), finiteSet(1, 2)); // => True
 * ```
 */
export function isSubset(a: _SetExpr_, b: _SetExpr_): Truth {
  return _toTruth_(_isSubset_(a, b));
}
export { nargs } from './sets/sets';
export { SetExpression, SetExpressionNode } from './sets/setexpr';

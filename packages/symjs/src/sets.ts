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

/** @deprecated Internal; removed from the public API in 1.0. */
export const SetOp = _SetOp_;

/** @deprecated Internal; removed from the public API in 1.0. */
export type SetOp = _SetOp_;

/** @deprecated Use `imageset`. */
export const imageSet = _imageSet_;

/** @deprecated Use `Interval.of`. */
export const interval = _interval_;

/** @deprecated Use `Interval.open`. */
export const openInterval = _openInterval_;

/** @deprecated Use `Interval.Lopen`. */
export const Lopen = _Lopen_;

/** @deprecated Use `Interval.Ropen`. */
export const Ropen = _Ropen_;

/** @deprecated Use `FiniteSet.of`. */
export const finiteSet = _finiteSet_;

/** @deprecated Use `Union`. */
export const union = _union_;

/** @deprecated Use `Complement`. */
export const complement = _complement_;

/** @deprecated Internal; removed from the public API in 1.0. */
export const containsQ = (s: _SetExpr_, x: _Expr_): Truth => _toTruth_(_containsQ_(s, x));

/** SymPy is_subset: a is a subset of b (true, false or 'unknown'). */
export function isSubset(a: _SetExpr_, b: _SetExpr_): Truth {
  return _toTruth_(_isSubset_(a, b));
}

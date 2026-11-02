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
  isSubset,
  asRelational,
  inf,
  sup,
} from './sets/sets';

// ---- deprecated names (kept during 0.x, removed in 1.0; see docs/api-policy.md) ----

import { SetOp as _SetOp_ } from './sets/sets';
import { imageSet as _imageSet_ } from './sets/sets';
import { interval as _interval_ } from './sets/sets';
import { openInterval as _openInterval_ } from './sets/sets';
import { Lopen as _Lopen_ } from './sets/sets';
import { Ropen as _Ropen_ } from './sets/sets';
import { finiteSet as _finiteSet_ } from './sets/sets';
import { union as _union_ } from './sets/sets';
import { intersection as _intersection_ } from './sets/sets';
import { complement as _complement_ } from './sets/sets';
import { containsQ as _containsQ_ } from './sets/sets';

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

/** @deprecated Use `Intersection`. */
export const intersection = _intersection_;

/** @deprecated Use `Complement`. */
export const complement = _complement_;

/** @deprecated Internal; removed from the public API in 1.0. */
export const containsQ = _containsQ_;

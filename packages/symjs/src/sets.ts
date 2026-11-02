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
  SetOp,
  ImageSet,
  ConditionSet,
  imageSet,
  EmptySet,
  Reals,
  Integers,
  Naturals,
  Naturals0,
  Complexes,
  interval,
  openInterval,
  Lopen,
  Ropen,
  finiteSet,
  union,
  intersection,
  complement,
  contains,
  containsQ,
  isSubset,
  asRelational,
  inf,
  sup,
} from './sets/sets';

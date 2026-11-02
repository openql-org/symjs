// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Entry point `@symjs/symjs/polys`: polynomials (factorization, roots,
 * Groebner bases, partial fractions, algebraic numbers).
 */

// every entry point brings the core with its registrations
import './core';

export {
} from './polys/poly';
export {
  Poly,
  PolificationFailed,
  factor,
  factorNc,
  factorListExpr as factorList,
  polyGcd as gcd,
  polyLcm as lcm,
  polyDiv as div,
  degree,
  termsGcd,
  horner,
  interpolate,
  resultant,
  discriminant,
} from './polys/sympoly';

export { rootsDict as roots } from './polys/poly';
export { sqfNorm, minimalPolynomial } from './polys/sympoly';
export { Monomial } from './polys/monomial';
export { polyFromExpr, parallelPolyFromExpr, gff, type PolyOptions } from './polys/fromexpr';
export { RootSum, RootSumNode, apartList, assemblePartfracList } from './polys/rootsum';
export type { PartfracTerm } from './polys/rootsum';
export {
  AlgebraicNumber,
} from './polys/numberfields';
export {
  CRootOf,
  rootOf as rootof,
} from './polys/rootof';
export {
  apart,
} from './polys/partfrac';
export {
  nroots,
} from './polys/nroots';
export {
  symmetrize,
  rationalInterpolate,
} from './polys/polyfuncs';
export {
  groebner,
  GroebnerBasis,
  reduced,
} from './polys/groebner';
export type { MonomialOrder } from './polys/groebner';

// ---- deprecated names (kept during 0.x, removed in 1.0; see docs/api-policy.md) ----

import { UPoly as _UPoly_ } from './polys/poly';
import { polyCoefficients as _polyCoefficients_ } from './polys/poly';
import { type NoMatchResult, orNoMatch as _orNoMatch_ } from './core/truth';
import type { Expr as _Expr_, ExprLike as _ExprLike_, Sym as _Sym_ } from './core/nodes';
import { factorPoly as _factorPoly_ } from './polys/poly';
import { polyDiv as _polyDiv_ } from './polys/sympoly';
import { sortGens as _sortGens_ } from './polys/sympoly';
import { mgcd as _mgcd_ } from './polys/mpoly';
import { mlcm as _mlcm_ } from './polys/mpoly';
import { divExact as _divExact_ } from './polys/mpoly';
import { rootOf as _rootOf_ } from './polys/rootof';
import { symmetrizeExpr as _symmetrizeExpr_ } from './polys/polyfuncs';

/** @deprecated Internal; removed from the public API in 1.0. */
export const UPoly = _UPoly_;

/** @deprecated Internal; removed from the public API in 1.0. */
export type UPoly = _UPoly_;

/** @deprecated Internal; removed from the public API in 1.0. */
export const polyCoefficients = (e: _ExprLike_, x: _Sym_): Map<number, _Expr_> | NoMatchResult => _orNoMatch_(_polyCoefficients_(e, x));

/** @deprecated Internal; removed from the public API in 1.0. */
export const factorPoly = _factorPoly_;

/** @deprecated Use `div`. */
export const polyDiv = _polyDiv_;

/** @deprecated Internal; removed from the public API in 1.0. */
export const sortGens = _sortGens_;

/** @deprecated Internal; removed from the public API in 1.0. */
export const mgcd = _mgcd_;

/** @deprecated Internal; removed from the public API in 1.0. */
export const mlcm = _mlcm_;

/** @deprecated Internal; removed from the public API in 1.0. */
export const divExact = (f: _Expr_, g: _Expr_, vars: readonly _Sym_[]): _Expr_ | NoMatchResult => _orNoMatch_(_divExact_(f, g, vars));

/** @deprecated Use `rootof`. */
export const rootOf = _rootOf_;

/** @deprecated Internal; removed from the public API in 1.0. */
export const symmetrizeExpr = _symmetrizeExpr_;

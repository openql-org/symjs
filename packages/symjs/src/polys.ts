// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Entry point `@symjs/symjs/polys`: polynomials (factorization, roots,
 * Groebner bases, partial fractions, algebraic numbers).
 */

// every entry point brings the core with its registrations
import './core';

export { UPoly, polyCoefficients, roots, factorPoly } from './polys/poly';
export {
  Poly,
  PolificationFailed,
  factor,
  factorNc,
  factorListExpr as factorList,
  polyGcd as gcd,
  polyLcm as lcm,
  polyDiv,
  degree,
  termsGcd,
  horner,
  interpolate,
  resultant,
  discriminant,
  sortGens,
} from './polys/sympoly';
export { mgcd, mlcm, divExact } from './polys/mpoly';
export { AlgebraicNumber } from './polys/numberfields';
export { CRootOf, rootOf } from './polys/rootof';
export { apart } from './polys/partfrac';
export { nroots } from './polys/nroots';
export { symmetrize, symmetrizeExpr, rationalInterpolate } from './polys/polyfuncs';
export { groebner, GroebnerBasis, reduced } from './polys/groebner';
export type { MonomialOrder } from './polys/groebner';

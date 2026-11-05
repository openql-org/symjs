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
  PurePoly,
  asPoly,
  invert,
  gcdList,
  lcmList,
  sqf,
} from './polys/sympoly';

export { rootsDict as roots } from './polys/poly';
export { sqfNorm } from './polys/sympoly';
export type { FactorList, FactorListFrac, FactorListOptions } from './polys/sympoly';
export { minimalPolynomial } from './polys/numberfields';
export { fieldIsomorphism, primitiveElement, toNumberField } from './polys/numberfields/subfield';
export type { PrimitiveElementOptions } from './polys/numberfields/subfield';
export type { MinimalPolynomialOptions } from './polys/numberfields';
export {
  Monomial,
  monomialMul,
  monomialDiv,
  monomialLdiv,
  monomialPow,
  monomialGcd,
  monomialLcm,
  monomialDivides,
  monomialMax,
  monomialMin,
  monomialDeg,
  monomialCount,
  itermonomials,
} from './polys/monomial';
export type { ExponentVector } from './polys/monomial';
export { LexOrder, GradedLexOrder, ReversedGradedLexOrder, InverseOrder, lex, grlex, grevlex, ilex, igrlex, igrevlex, monomialKey, compareMonomialKeys } from './polys/orderings';
export type { MonomialKey, MonomialOrdering } from './polys/orderings';
export {
  BasePolynomialError,
  PolynomialDivisionFailed,
  OperationNotSupported,
  HeuristicGCDFailed,
  ModularGCDFailed,
  HomomorphismFailed,
  IsomorphismFailed,
  ExtraneousFactors,
  EvaluationFailed,
  RefinementFailed,
  NotReversible,
  NotAlgebraic,
  UnificationFailed,
  UnsolvableFactorError,
  GeneratorsError,
  GeneratorsNeeded,
  ComputationFailed,
  UnivariatePolynomialError,
  MultivariatePolynomialError,
  OptionError,
  FlagError,
} from './polys/polyerrors';
export { ZZ, QQ, RR, EX, Domain, IntegerRing, RationalField, RealField, ExpressionDomain, Expression, PolynomialRing, FractionField, GlobalPolynomialRing, OldFractionField, DMP, DMF, CoercionFailed } from './polys/domains';
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
  viete,
} from './polys/polyfuncs';
export {
  groebner,
  GroebnerBasis,
  reduced,
  isZeroDimensional,
} from './polys/groebner';
export type { MonomialOrder } from './polys/groebner';
export {
  jacobiPoly,
  gegenbauerPoly,
  chebyshevtPoly,
  chebyshevuPoly,
  hermitePoly,
  hermiteProbPoly,
  legendrePoly,
  laguerrePoly,
} from './polys/orthopolys';
export type { NamedPolyOptions, NamedPolyResult } from './polys/orthopolys';
export {
  swinnertonDyerPoly,
  cyclotomicPoly,
  symmetricPoly,
  randomPoly,
  interpolatingPoly,
} from './polys/specialpolys';
export type { RandomPolyOptions } from './polys/specialpolys';

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
export {
  gfCrt, gfCrt1, gfCrt2, gfInt, gfDegree, gfLC, gfTC, gfStrip, gfTrunc, gfNormal, gfFromDict, gfToDict, gfFromIntPoly, gfToIntPoly, gfNeg,
  gfAddGround, gfSubGround, gfMulGround, gfQuoGround, gfAdd, gfSub, gfMul, gfSqr, gfAddMul, gfSubMul, gfExpand, gfDiv, gfRem, gfQuo, gfExquo,
  gfLshift, gfRshift, gfPow, gfFrobeniusMonomialBase, gfFrobeniusMap, gfPowMod, gfGcd, gfLcm, gfCofactors, gfGcdex, gfMonic, gfDiff, gfEval,
  gfMultiEval, gfCompose, gfComposeMod, gfTraceMap, gfRandom, gfIrreducible, gfIrredPBenOr, gfIrredPRabin, gfIrreducibleP, gfSqfP, gfSqfPart,
  gfSqfList, gfQmatrix, gfQbasis, gfBerlekamp, gfDdfZassenhaus, gfEdfZassenhaus, gfDdfShoup, gfEdfShoup, gfZassenhaus, gfShoup, gfFactorSqf,
  gfFactor, gfValue,
} from './polys/galoistools';
export type { GFPoly, GFFactorization, GFFactorMethod } from './polys/galoistools';

// sparse polynomial rings (SymPy sympy.polys.rings) and the IPolys methods (sympy.polys.compatibility)
export { PolyRing, PolyElement, ring, xring, vring, sring } from './polys/rings';
export type { RingSymbols, DomainLike, OrderLike, GenLike, SringOptions, Monom } from './polys/rings';
export { IPolys } from './polys/compatibility';
// dense polynomial representation and distributed modules (SymPy densebasic, distributedmodules)
export * from './polys/densebasic';
export * from './polys/distributedmodules';
export { Options, buildOptions, allowedFlags, preprocessDomain } from './polys/polyoptions';
export type { OptionArgs } from './polys/polyoptions';
export { constructDomain } from './polys/constructor';
export type { ConstructDomainOptions } from './polys/constructor';
// the domains of sympy.polys.domains beyond ZZ, QQ, RR and EX
export { PythonMPQ, PythonMPQ as MPQ } from './polys/domains/pythonrational';
export { FiniteField, ModularInteger, GF, FF } from './polys/domains/finitefield';
export { GaussianIntegerRing, GaussianRationalField, GaussianElement, GaussianInteger, GaussianRational, ZZ_I, QQ_I } from './polys/domains/gaussiandomains';
export { AlgebraicField, ANP } from './polys/domains/algebraicfield';
export { ComplexField, CC } from './polys/domains/complexfield';
export { ExpressionRawDomain, EXRAW } from './polys/domains/expressionrawdomain';
// matrices over domains (SymPy sympy.polys.matrices)
export { DM } from './polys/matrices/domainmatrix';
export type { DomainMatrixRows, DomainFactor } from './polys/matrices/domainmatrix';
export { DDM } from './polys/matrices/ddm';
export type { Shape } from './polys/matrices/ddm';
export { SDM, sdmBerk, sdmIrref, sdmRrefDen, sdmMatmul, sdmTranspose, sdmDotvec, sdmMatvecmul, sdmNullspaceFromRref, sdmParticularFromRref, binopDict, unopDict } from './polys/matrices/sdm';
export { DomainScalar } from './polys/matrices/domainscalar';
export { ddmTranspose, ddmIadd, ddmIsub, ddmIneg, ddmImul, ddmIrmul, ddmImatmul, ddmIrref, ddmIrrefDen, ddmIdet, ddmIinv, ddmIluSplit, ddmIlu, ddmIluSolve, ddmBerk } from './polys/matrices/dense';
export { DMError, DMBadInputError, DMDomainError, DMNotAField, DMFormatError, DMNonInvertibleMatrixError, DMRankError, DMShapeError, DMNonSquareMatrixError, DMValueError } from './polys/matrices/exceptions';

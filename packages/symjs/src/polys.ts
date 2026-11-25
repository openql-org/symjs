// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * Entry point `@symjs/symjs/polys`: polynomials (factorization, roots,
 * Groebner bases, partial fractions, algebraic numbers).
 * @module
 */

// every entry point brings the core with its registrations
import './core';
// polynomial rings and fraction fields over the non-ground coefficient domains
import './polys/domains/compositedomain';

export {
} from './polys/poly';
export {
  Poly,
  PolificationFailed,
  factor,
  factorNc,
  preprocessRoots,
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
  sqfList,
  toRationalCoeffs,
} from './polys/sympoly';

export { rootsInRadicals as roots, type RootOptions } from './polys/poly';
export { dictFromExpr, parallelDictFromExpr } from './polys/polyutils';
export type { DictFromExprOptions } from './polys/polyutils';
export { bernoulliPoly, bernoulliCPoly, genocchiPoly, eulerPoly, andrePoly, dupBernoulli, dupBernoulliC, dupGenocchi, dupEuler, dupAndre } from './polys/appellseqs';
export { dispersion, dispersionset } from './polys/dispersion';
export { eqsToMatrix, solveLinSys, sympyEqsToRing } from './polys/solvers';
export { sqfNorm } from './polys/sympoly';
export type { FactorList, FactorListFrac, FactorListOptions, PolyConstructionOptions, PolynomialDomainOptions } from './polys/sympoly';
export { minimalPolynomial } from './polys/numberfields';
export { fieldIsomorphism, fieldIsomorphismPslq, isIsomorphismPossible, primitiveElement, toNumberField } from './polys/numberfields/subfield';
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
export { lbpNum, lbpPolyn, lbpSign, cpCmp, cpKey, criticalPair, f5Reduce, f5b, groebnerGcd, groebnerLcm, isGroebner, isMinimal, isReduced, isRewritableOrComparable, lbp, lbpCmp, lbpKey, lbpMulTerm, lbpSub, redGroebner, sPoly, sig, sigCmp, sigKey, sigMult, spoly } from './polys/groebnertools';
export type { CriticalPair, LabeledPolynomial, Signature } from './polys/groebnertools';
export { LexOrder, GradedLexOrder, ReversedGradedLexOrder, InverseOrder, lex, grlex, grevlex, ilex, igrlex, igrevlex, monomialKey, compareMonomialKeys, ProductOrder, buildProductOrder } from './polys/orderings';
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
export type { AlgebraicNumberOptions } from './polys/numberfields';
export {
  CRootOf,
  ComplexRootOf,
  RootOf,
  rootOf as rootof,
} from './polys/rootof';
export type { RootOfOptions } from './polys/rootof';
export { ComplexInterval, countComplexRoots, refineRealRoot, isolateRealRoots, isolateRealRootsSqf, isolateRealRootsList, isolateComplexRootsSqf } from './polys/rootisolation';
export {
  apart,
} from './polys/partfrac';
export type { ApartOptions } from './polys/partfrac';
export {
  nroots,
} from './polys/nroots';
export {
  symmetrize,
  rationalInterpolate,
  viete,
} from './polys/polyfuncs';
export {
  GroebnerBasis,
  reduced,
  isZeroDimensional,
} from './polys/groebner';
export type { GroebnerOptions, MonomialOrder } from './polys/groebner';
export { groebnerWithDomain as groebner } from './polys/groebnertools';
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

/**
 * A univariate polynomial represented by its coefficients.
 *
 * @deprecated Internal; removed from the public API in 1.0.
 */
export const UPoly = _UPoly_;

/** @deprecated Internal; removed from the public API in 1.0. */
export type UPoly = _UPoly_;

/**
 * Collects the coefficients of a polynomial by exponent.
 *
 * @deprecated Internal; removed from the public API in 1.0.
 * @param e - The input expression.
 * @param x - The argument of the function.
 * @returns The matching result, or `NoMatch` when the required form is absent.
 */
export const polyCoefficients = (e: _ExprLike_, x: _Sym_): Map<number, _Expr_> | NoMatchResult => _orNoMatch_(_polyCoefficients_(e, x));

/**
 * Factors a polynomial into irreducible factors with multiplicities.
 *
 * @deprecated Internal; removed from the public API in 1.0.
 */
export const factorPoly = _factorPoly_;

/**
 * Alias for {@link div}.
 *
 * @deprecated Use {@link div}.
 * @param f - The function or expression to transform.
 * @param g - The second function.
 * @param gens - The gens.
 * @returns The polynomial quotient and remainder.
 * @see SymPy `sympy.polys.polytools.div`
 * @example
 * ```ts
 * import { ex, polyDiv, symbols } from '@symjs/symjs';
 *
 * polyDiv(ex`x**2 - 1`, ex`x - 1`, [symbols('x')[0]]); // => [x + 1, 0]
 * ```
 */
export const polyDiv = _polyDiv_;

/**
 * Orders polynomial generators.
 *
 * @deprecated Internal; removed from the public API in 1.0.
 */
export const sortGens = _sortGens_;

/**
 * Computes a multivariate polynomial greatest common divisor.
 *
 * @deprecated Internal; removed from the public API in 1.0.
 */
export const mgcd = _mgcd_;

/**
 * Computes a multivariate polynomial least common multiple.
 *
 * @deprecated Internal; removed from the public API in 1.0.
 */
export const mlcm = _mlcm_;

/**
 * Divides polynomials exactly in the specified generators.
 *
 * @deprecated Internal; removed from the public API in 1.0.
 * @param f - The function or expression to transform.
 * @param g - The second function.
 * @param vars - The polynomial generators.
 * @returns The matching result, or `NoMatch` when the required form is absent.
 */
export const divExact = (f: _Expr_, g: _Expr_, vars: readonly _Sym_[]): _Expr_ | NoMatchResult => _orNoMatch_(_divExact_(f, g, vars));

/**
 * Alias for {@link rootof}.
 *
 * @deprecated Use {@link rootof}.
 * @param f - The function or expression to transform.
 * @param index - The index.
 * @param opts - `radicals` enables radical expressions for supported roots.
 * @returns The selected root of the polynomial.
 * @see SymPy `sympy.polys.rootoftools.rootof`
 */
export const rootOf = _rootOf_;

/**
 * Expresses a polynomial in elementary symmetric polynomials and a remainder.
 *
 * @deprecated Internal; removed from the public API in 1.0.
 */
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
export { FracField, FracElement, field, xfield, vfield, sfield } from './polys/fields';
export type { FracInput, FracSubstitutions } from './polys/fields';
export { PuiseuxRing, PuiseuxPoly, puiseuxRing } from './polys/puiseux';
export { PolynomialRingBase } from './polys/domains/oldpolynomialring';
export { QuotientRing } from './polys/domains/quotientring';
export { Module, FreeModule, SubModule, QuotientModule, ModuleElement, ModuleOrder } from './polys/agca/modules';
export type { ModuleInput } from './polys/agca/modules';
export { ModuleImplementedIdeal } from './polys/agca/ideals';
export { ModuleHomomorphism, homomorphism } from './polys/agca/homomorphisms';
export { identityHom, inclusionHom, quotientHom } from './polys/agca/homomorphisms';
export { ExtensionElement, FiniteExtension } from './polys/agca/extensions';
export type { PuiseuxMonom, PuiseuxTerm } from './polys/puiseux';
export { powXin, rsTrunc, rsMul, rsSquare, rsDiff, rsIntegrate, rsIsPuiseux, rsPow, rsSeriesInversion, rsNthRoot, rsExp, rsSin, rsCos, rsCosSin, rsCoshSinh, rsSinh, rsCosh, rsAsin, rsAsinh, rsAtan, rsAtanh, rsLambertW, rsTan, rsTanh, rsCot, rsLog, rsSeriesFromList, rsSubs, rsSeriesReversion, rsPuiseux, rsFun, rsHadamardExp, rsNewton, rsComposeAdd, rsSeries } from './polys/ringseries';
export type { SeriesPoly, SeriesFunction } from './polys/ringseries';
export type { RingSymbols, DomainLike, OrderLike, GenLike, SringOptions, Monom } from './polys/rings';
export { IPolys, hasAssocRing } from './polys/compatibility';
// dense polynomial representation and distributed modules (SymPy densebasic, distributedmodules)
export * from './polys/densebasic';
export * from './polys/densearith';
export * from './polys/modulargcd';
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
export { RealElement, ComplexElement, MPContext, type MPContextOptions } from './polys/domains/mpelements';
export { ComplexField, CC } from './polys/domains/complexfield';
export { ExpressionRawDomain, EXRAW } from './polys/domains/expressionrawdomain';
// matrices over domains (SymPy sympy.polys.matrices)
export { DM } from './polys/matrices/domainmatrix';
export type { DomainMatrixRows, DomainFactor } from './polys/matrices/domainmatrix';
export { DDM } from './polys/matrices/ddm';
export type { Shape } from './polys/matrices/ddm';
export { SDM, sdmBerk, sdmIrref, sdmRrefDen, sdmMatmul, sdmTranspose, sdmDotvec, sdmMatvecmul, sdmNullspaceFromRref, sdmParticularFromRref, binopDict, unopDict } from './polys/matrices/index';
export { DomainScalar } from './polys/matrices/domainscalar';
export { ddmTranspose, ddmIadd, ddmIsub, ddmIneg, ddmImul, ddmIrmul, ddmImatmul, ddmIrref, ddmIrrefDen, ddmIdet, ddmIinv, ddmIluSplit, ddmIlu, ddmIluSolve, ddmBerk } from './polys/matrices/dense';
export { DMError, DMBadInputError, DMDomainError, DMNotAField, DMFormatError, DMNonInvertibleMatrixError, DMRankError, DMShapeError, DMNonSquareMatrixError, DMValueError } from './polys/matrices/exceptions';

export { extractFundamentalDiscriminant, isolate, AlgIntPowers, coeffSearch, supplementASubspace, isRat, isInt, getNumDenom } from './polys/numberfields/utilities';
export type { RationalLike } from './polys/numberfields/utilities';
// modules, orders and prime ideals of number fields (SymPy sympy.polys.numberfields.modules, basis, primes);
// Module, ModuleElement and ModuleHomomorphism are exported with a NumberField prefix (the names are those of agca)
export {
  Module as NumberFieldModule,
  ModuleElement as NumberFieldModuleElement,
  ModuleHomomorphism as NumberFieldModuleHomomorphism,
  PowerBasis,
  PowerBasisElement,
  Submodule,
  ModuleEndomorphism,
  InnerEndomorphism,
  EndomorphismRing,
  findMinPoly,
  toCol,
  makeModElt,
  isSqMaxrankHNF,
} from './polys/numberfields/modules';
export type { MultTab, HnfOptions, HomomorphismCodomain } from './polys/numberfields/modules';
export { roundTwo, nilradicalModP, PrimeIdeal, primeDecomp, primeValuation } from './polys/numberfields/index';
export type { RoundTwoOptions, PrimeDecompOptions } from './polys/numberfields/index';
export { ClosureFailure, StructureError, MissingUnityError } from './polys/numberfields/exceptions';
export { rootFactors, rootsQuintic } from './polys/polyroots';
export { PolyQuintic } from './polys/polyquinticconst';
export { PolyMatrix, MutablePolyDenseMatrix, MutablePolyMatrix, PolyMatrixRing } from './polys/polymatrix';
export type { PolyMatrixOptions, PolyMatrixEntry, PolyMatrixGens, PolyMatrixEntryFunction, PolyMatrixArgument } from './polys/polymatrix';
export { DixonResultant, MacaulayResultant } from './polys/multivariateresultants';
export * from './polys/densetools';
export { dmpSqfNorm } from './polys/sqfreetools';
export { matrixFglm } from './polys/fglmtools';
export { domEigenvects, domEigenvectsToSympy } from './polys/matrices/eigen';
export type { RationalEigenvectors, AlgebraicEigenvectors } from './polys/matrices/eigen';
export { _linsolve, _linEq2dict, _linearEqToDict, sympyDictToDm } from './polys/matrices/linsolve';
export {
  galoisGroup, hasSquareDisc, MaxTriesException, tschirnhausenTransformation, GaloisGroupException, Resolvent, ResolventException, defineResolvents,
  generateLambdaLookup, getResolventByLookup, sVars, sparseSymmetrizeResolventCoeffs, wrap,
} from './polys/numberfields/index';
export type { GaloisGroupOptions, GaloisGroupResult, TschirnhausenOptions, ResolventDefinition, ResolventRootLambda, ResolventTarget } from './polys/numberfields/index';

export { rootsBinomial, rootsQuadratic, rootsCubic, rootsCyclotomic } from './polys/polyroots';
export { dupCauchyUpperBound, dupCauchyLowerBound, dupMignotteSepBoundSquared } from './polys/rootbounds';

export { groebnerInRing } from './polys/groebnertools';

export { sylvester, bezout, backwardEye, res, resQ, resZ, subresultantsSylv, subresultantsBezout, subresultantsPg, subresultantsAmv, subresultantsAmvQ, subresultantsRem, subresultantsVv, subresultantsVv2, modifiedSubresultantsSylv, modifiedSubresultantsBezout, modifiedSubresultantsPg, modifiedSubresultantsAmv, euclidQ, sturmQ, quoZ, remZ, euclidAmv, euclidPg, sturmAmv, sturmPg } from './polys/subresultantsqqzz';

export { DMPJs } from './polys/polyclasses';
export { dupTrialDivision, dmpZzMignotteBound, dupZzHenselStep, dupZzHenselLift, dmpZzWang, dmpZzWangNonDivisors } from './polys/factortools';
export { dupEuclideanPrs, dupPrimitivePrs } from './polys/euclidtools';

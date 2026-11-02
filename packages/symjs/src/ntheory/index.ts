// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Number theory (SymPy sympy.ntheory and sympy.ntheory.modular).
 *
 * Conventions: integer inputs accept expressions, JavaScript integers and
 * bigints; integer results are bigints; Python lists are arrays, tuples
 * fixed-length arrays, dicts Maps and sets Sets; Python generators are
 * generators. Where SymPy returns None, a value that does not exist is
 * NoMatch and a randomized method that failed is Unsolved.
 */

export { Sieve, sieve } from './sieve';
export { Random, rng, seed } from './random';
export type { RandInt } from './random';
export { FactorCache, factorCache, isMersennePrime, isGaussianPrime, MERSENNE_PRIME_EXPONENTS } from './primetest';
export { prime, nextprime, prevprime, primerange, randprime, primorial, cycleLength, composite, compositepi } from './generate';
export type { IntLike } from './intutil';
export {
  multiplicity,
  multiplicityInFactorial,
  perfectPower,
  pollardRho,
  pollardPm1,
  factorint,
  factorrat,
  primefactors,
  divisors,
  properDivisors,
  divisorCount,
  properDivisorCount,
  smoothness,
  smoothnessP,
  mersennePrimeExponent,
  abundance,
  isPerfect,
  isAbundant,
  isDeficient,
  isAmicable,
  dra,
  drm,
} from './factor';
export type { FactorintOptions, PerfectPowerOptions, PollardRhoOptions, PollardPm1Options } from './factor';
export { ecm } from './ecm';
export type { EcmOptions } from './ecm';
export { qs, qsFactor } from './qs';
export type { QsOptions } from './qs';
export { digits, countDigits, isPalindromic } from './digits';
export { crt, crt1, crt2, solveCongruence, symmetricResidue } from './modular';
export {
  nOrder,
  primitiveRoot,
  isPrimitiveRoot,
  sqrtMod,
  sqrtModIter,
  isQuadResidue,
  isNthpowResidue,
  nthrootMod,
  quadraticResidues,
  discreteLog,
  quadraticCongruence,
  polynomialCongruence,
  linearCongruence,
  gfCsolve,
} from './residue';
export { binomialCoefficients, binomialCoefficientsList, multinomialCoefficients, multinomialCoefficientsIterator } from './multinomial';
export { continuedFraction, continuedFractionPeriodic, continuedFractionIterator, continuedFractionConvergents, continuedFractionReduce } from './continued';
export type { ContinuedFraction } from './continued';
export { egyptianFraction } from './egyptian';
export type { EgyptianAlgorithm } from './egyptian';
export { npartitions } from './partitions';

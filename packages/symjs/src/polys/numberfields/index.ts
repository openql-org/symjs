// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The orders and prime ideals of number fields (round_two,
 * prime_decomp, prime_valuation), re-exported through this side-effect-free
 * module: basis.ts and primes.ts register AlgebraicField.maximalOrder,
 * discriminant, integralBasis and primesAbove on load, and a bundle includes
 * them only when one of these exports is used (like SDM, see
 * docs/api-policy.md). Without a bundler the polys entry loads them.
 */

export { roundTwo, nilradicalModP } from './basis';
export type { RoundTwoOptions } from './basis';
export { PrimeIdeal, primeDecomp, primeValuation } from './primes';
export type { PrimeDecompOptions } from './primes';

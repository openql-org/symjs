// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Entry point `@symjs/symjs/special`: special and combinatorial functions
 * (Gamma, zeta, error functions, Bessel and Airy functions, polar numbers, ...).
 */

// every entry point brings the core with its registrations
import './core';

export { Mod } from './functions/mod';

export {
  factorial,
  factorial2,
  binomial,
  ff,
  rf,
  subfactorial,
  harmonic,
  catalan,
  gamma,
  loggamma,
  polygamma,
  digamma,
  trigamma,
  lowergamma,
  uppergamma,
  beta,
  betainc,
  betaincRegularized,
  zeta,
  erf,
  erfc,
  erfi,
  erf2,
  erfinv,
  erfcinv,
  erf2inv,
  Ei,
  LambertW,
  li,
  Li,
  Si,
  Ci,
  Shi,
  Chi,
  expint,
  E1,
  fresnels,
  fresnelc,
  sign,
  floor,
  Rem,
  ceiling,
  atan2,
  Min,
  Max,
  expandFunc,
} from './functions/special';
export {
  besselj,
  bessely,
  besseli,
  besselk,
  airyai,
  airybi,
  airyaiprime,
  airybiprime,
  hankel1,
  hankel2,
  marcumq,
} from './functions/bessel';
export { hn1, hn2, jnZeros, sphericalBesselFn } from './functions/sphericalbessel';
export { Ynm, YnmC, Znm } from './functions/sphericalharmonics';
export { mathieus, mathieuc, mathieusprime, mathieucprime } from './functions/mathieu';
export {
  bernoulli,
  euler,
  genocchi,
  bell,
  fibonacci,
  lucas,
  tribonacci,
  partition,
  totientFn as totient,
  reducedTotient,
  mobius,
  divisorSigma,
  primenu,
  primeomega,
  primepiFn as primepi,
  multigamma,
  frac,
  isprime,
  isCarmichael,
  findCarmichaelNumbersInRange,
  findFirstNCarmichaels,
  carmichael,
  jacobiSymbol,
  kroneckerSymbol,
  firstMotzkins,
  motzkinNumbersInRange,
  isMotzkin,
  binomialMod,
  legendreSymbol,
  motzkin,
  andre,
} from './functions/combinatorial';
export {
  polarify,
  expPolar,
  polarLift,
  periodicArgument,
  principalBranch,
  unbranchedArgument,
  unpolarify,
  extractBranchFactor,
} from './functions/polar';
export { Hyper, MeijerG, hyper, meijerg, appellf1, jn, yn, expandJn, KroneckerDelta, kroneckersimp } from './functions/hyper';
export { lerchphi, polylog, dirichletEta, riemannXi, stieltjes } from './functions/zeta';
export { ellipticK, ellipticF, ellipticE, ellipticPi } from './functions/elliptic';
export { LeviCivita, Eijk } from './functions/tensorfns';
export {
  jacobi,
  jacobiNormalized,
  gegenbauer,
  chebyshevt,
  chebyshevu,
  chebyshevtRoot,
  chebyshevuRoot,
  legendre,
  assocLegendre,
  hermite,
  hermiteProb,
  laguerre,
  assocLaguerre,
} from './functions/polynomials';

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
} from './functions/special/special';
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
} from './functions/special/bessel';
export { hn1, hn2, jnZeros, sphericalBesselFn } from './functions/special/sphericalbessel';
export { Ynm, YnmC, Znm } from './functions/special/sphericalharmonics';
export { mathieus, mathieuc, mathieusprime, mathieucprime } from './functions/special/mathieufunctions';
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
  udivisorSigma,
  nC,
  nP,
  nD,
  nT,
  stirling,
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
} from './functions/combinatorial/numbers';
export {
  polarify,
  expPolar,
  polarLift,
  periodicArgument,
  principalBranch,
  unbranchedArgument,
  unpolarify,
  extractBranchFactor,
  matchRealImag,
} from './functions/elementary/complexes';
export { Hyper, MeijerG, hyper, meijerg, appellf1, jn, yn, expandJn, KroneckerDelta, kroneckersimp } from './functions/special/hyper';
export { lerchphi, polylog, dirichletEta, riemannXi, stieltjes } from './functions/special/zetafunctions';
export { ellipticK, ellipticF, ellipticE, ellipticPi } from './functions/special/ellipticintegrals';
export { LeviCivita, Eijk } from './functions/special/tensorfunctions';
export { isAboveFermi, isBelowFermi, isOnlyAboveFermi, isOnlyBelowFermi, indicesContainEqualInformation, preferredIndex, killableIndex } from './functions/special/tensorfunctions';
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
} from './functions/special/polynomials';
export { migcdex, ipartfrac, fermatCoords, cos3, cos5, cos17, cos257, cosTable } from './functions/elementary/trigonometricspecial';
import './functions/special/errorfunctions';
export { order, argument } from './functions/special/bessel';
export { bsplineBasis, bsplineBasisSet, interpolatingSpline } from './functions/special/bsplines';

export { ff, rf } from './functions/combinatorial/factorials';

// Mod, KroneckerDelta and LeviCivita in parsed strings: parsing may not import the special functions
import { parserHooks as _parserHooks_ } from './parsing/parser';
import { Mod as _Mod_ } from './functions/mod';
import { LeviCivita as _LeviCivita_ } from './functions/special/tensorfunctions';
_parserHooks_.constructors.set('Mod', (args) => _Mod_(...args));
_parserHooks_.constructors.set('LeviCivita', (args) => _LeviCivita_(...args));
import { at as _at_ } from './core/guard';
// hyper, the Chebyshev roots and motzkin in parsed strings
import { hyper as _hyper_ } from './functions/special/hyper';
import { chebyshevtRoot as _chebyshevtRoot_, chebyshevuRoot as _chebyshevuRoot_ } from './functions/special/polynomials';
import { motzkin as _motzkin_ } from './functions/combinatorial/numbers';
import { Rational as _Rational_, type Expr as _ExprT_ } from './core/nodes';
import { SymFunction as _SymFunction_ } from './core/undef';
const _isTuple_ = (a: _ExprT_ | readonly _ExprT_[]): a is readonly _ExprT_[] => Array.isArray(a);
_parserHooks_.tupleConstructors.set('hyper', (args) => {
  const [ap, bq, z] = [_at_(args, 0), _at_(args, 1), _at_(args, 2)];
  // (SymPy: a TypeError from Tuple(*ap) for a parameter list that is not a tuple)
  if (!_isTuple_(ap) || !_isTuple_(bq)) throw new TypeError('hyper() takes tuples as its first two arguments');
  if (_isTuple_(z)) throw new SyntaxError('hyper() takes an expression as its third argument');
  return _hyper_(ap, bq, z);
});
_parserHooks_.constructors.set('chebyshevt_root', (args) => _chebyshevtRoot_(_at_(args, 0), _at_(args, 1)));
_parserHooks_.constructors.set('chebyshevu_root', (args) => _chebyshevuRoot_(_at_(args, 0), _at_(args, 1)));
_parserHooks_.constructors.set('motzkin', (args) => {
  const n = _at_(args, 0);
  return n instanceof _Rational_ && n.isInteger && n.p >= 0n ? _Rational_.of(_motzkin_(Number(n.p))) : _SymFunction_('motzkin')(n);
});

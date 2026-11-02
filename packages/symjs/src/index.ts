// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Entry point of the base module `@symjs/symjs`: the core computer
 * algebra system. Domain-specific extend modules are separate packages
 * (packages/* in the repository) that depend on this one.
 *
 * NOTE: several modules register implementations into the core `impl`
 * registry on load; they are all imported here so the fluent API works.
 */

import { Assumptions, Sym } from './core/nodes';
import { expandSymbolNames } from './core/numberutils';

// core
export {
  Expr,
  Rational,
  Float,
  Sym,
  Wild,
  WildFunction,
  Dummy,
  Constant,
  Add,
  Mul,
  Pow,
  Fn,
  BoolAtom,
  Rel,
  Piecewise,
  Integral,
  Limit,
  Order,
  Special,
  UndefFn,
  Derivative,
  S,
  pi,
  E,
  I,
  oo,
  zoo,
  nan,
  compareExpr,
  isRational,
  isFloat,
  isSymbol,
  isAdd,
  isMul,
  isPow,
  isFn,
  isInteger,
  isNum,
  ExtensionExpr,
} from './core/nodes';
export type {
  Kind,
  ExprLike,
  ComplexValue,
  NumericValues,
  EvalfOptions,
  Substitution,
  Assumptions,
  FnName,
  Num,
  ConstantName,
  RelOp,
} from './core/nodes';
export { sympify, add, mul, pow, sub, div, neg, sqrt, exp, rational, splitCoeff, asBaseExp } from './core/ops';
export { isReal, isPositive, isNegative, isNonNegative, isNonZero, isZero, isIntegerQ } from './core/assumptions';
export {
  keepCoeff,
  argsCnc,
  argsCncSplit,
  coeff,
  asIndependent,
  asCoeffAdd,
  asCoeffMul,
  primitive,
  asContentPrimitive,
  extractMultiplicatively,
  extractAdditively,
  asCoefficient,
  isPolynomial,
  isRationalFunction,
  isConstant,
  asRealImag,
  asNumerDenom,
  atoms,
  hasFree,
  asCoefficientsDict,
  asTwoTerms,
  hasXfree,
  isAlgebraicExpr,
  dummyEq,
  isMeromorphic,
} from './core/methods';
export { root, cbrt, realRoot } from './core/ops';
export { subs, xreplace, freeSymbols, mapBottomUp, rebuild } from './core/traverse';
export { match, replace, find, ordered, countOps, countOpsVisual, isInstance } from './core/match';
export type { Query, Replacement } from './core/match';

// functions
export {
  fn,
  sin,
  cos,
  tan,
  asin,
  acos,
  atan,
  sinh,
  cosh,
  tanh,
  log,
  abs,
  re,
  im,
  arg,
  conjugate,
  dagger,
  adjoint,
  transpose,
} from './functions/elementary';
export { cot, sec, csc, acot, asec, acsc, coth, sech, csch, asinh, acosh, atanh, acoth, asech, acsch, sinc } from './functions/trigext';

// special functions
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
  ceiling,
  atan2,
  Min,
  Max,
  expandFunc,
} from './functions/special';
export { besselj, bessely, besseli, besselk, airyai, airybi, airyaiprime, airybiprime } from './functions/bessel';

// calculus
export { diff } from './calculus/diff';
export { doit } from './calculus/doit';
export { Function, functions, derivative } from './core/undef';
export type { UndefinedFunction } from './core/undef';
export { integrate } from './integrals/integrate';
export { transformIntegral, principalValue } from './integrals/transform';
export { limit } from './series/limits';
export { Sum, Product, summation, product, doitConcrete, reverseOrder, Concrete } from './concrete/summations';
export { series, O } from './series/series';

// logic
export { rel, Eq, Ne, Lt, Le, Gt, Ge, piecewise } from './core/logic';

// simplification
export {
  expand,
  expandMul,
  expand_mul,
  expand_multinomial,
  expand_power_exp,
  expand_power_base,
  expand_log,
  expand_trig,
  expand_complex,
} from './simplify/expand';
export type { ExpandHints } from './simplify/expand';
export { simplify } from './simplify/simplify';
export { besselsimp } from './simplify/besselsimp';
export { powsimp, powdenest, logcombine, posify } from './simplify/powsimp';
export type { PowsimpOptions } from './simplify/powsimp';
export { radsimp, collect } from './simplify/radsimp';
export { rewrite, registerRewrite, rewriteRules } from './simplify/rewrite';
export { gcdTerms, factorTerms, collectConst, signsimp, keepCoeff as keepCoeffSympy, unevaluatedAdd } from './simplify/exprtools';
export { trigsimp, exptrigsimp, rewriteExp, rewriteTrig, expsimp, exptotrig, combineExp } from './simplify/trigsimp';
export { together, cancel, fraction , ratsimp } from './simplify/rational';

// polynomials
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

// solvers
export {
  solve,
  asEquation,
  linsolve,
  linearEqToMatrix,
  nonlinsolve,
  solveLinear,
  solveUndeterminedCoeffs,
  nsolve,
  invertEquation,
} from './solvers/solve';
export { dsolve, homogeneousOrder, odeOrder } from './solvers/ode';

// numerics
export { piecewiseIntegrate } from './integrals/integrate';
export { apart } from './polys/partfrac';
export { nroots } from './polys/nroots';
export { sumIsConvergent, sumIsAbsolutelyConvergent } from './concrete/summations';
export { symmetrize, symmetrizeExpr, rationalInterpolate } from './polys/polyfuncs';
export { separatevars } from './simplify/separatevars';
export { groebner, GroebnerBasis, reduced } from './polys/groebner';
export type { MonomialOrder } from './polys/groebner';
export { evalf, evalfPrec, toComplex, lambdify } from './numeric/evalf';
export { float } from './numeric/floatctor';
export { round } from './numeric/round';
export { precToDps, dpsToPrec } from './numeric/mpf';

// printing / parsing
export { str } from './printing/str';
export { asOrderedTerms as orderedTerms, asOrderedFactors as orderedFactors, sortKey, compareKeys } from './printing/sortkey';
export { couldExtractMinusSign } from './core/ops';
export { latex } from './printing/latex';
export { parse, ex } from './parsing/parser';
export type { ParseOptions } from './parsing/parser';

// matrices
export { Matrix } from './matrices/matrix';
export * as linalg from './matrices/linalg';
export {
  rref,
  echelonForm,
  rank,
  nullspace,
  columnspace,
  rowspace,
  eigenvects,
  isDiagonalizable,
  diagonalize,
  matrixExp,
  matrixLog,
  analyticFunc,
  cholesky,
  ldl,
  luDecomposition,
  qrDecomposition,
  dot,
  cross,
  singularValues,
  norm,
  pinv,
  jacobian,
  blockDiag,
  rotAxis1,
  rotAxis2,
  rotAxis3,
  rotCcwAxis1,
  rotCcwAxis2,
  rotCcwAxis3,
  rotGivens,
  jordanBlock, pinvSolve, multiplyElementwise, companion, permanent, connectedComponents, stronglyConnectedComponents } from './matrices/linalg';


/** Create a symbol. */
export function symbol(name: string, assumptions: Assumptions = {}): Sym {
  return new Sym(name, assumptions);
}

type Trim<S extends string> = S extends ` ${infer R}` ? Trim<R> : S extends `${infer R} ` ? Trim<R> : S;
type SplitNames<S extends string> =
  Trim<S> extends `${infer A},${infer B}`
    ? [...SplitNames<A>, ...SplitNames<B>]
    : Trim<S> extends `${infer A} ${infer B}`
      ? [...SplitNames<A>, ...SplitNames<B>]
      : Trim<S> extends ''
        ? []
        : [Trim<S>];

/** Tuple of symbols matching the names in a string literal, e.g. 'x y' -> [Sym, Sym]. */
type ToSyms<T extends readonly unknown[]> = { [K in keyof T]: Sym };
export type SymbolTuple<S extends string> = string extends S ? Sym[] : ToSyms<SplitNames<S>>;

/**
 * Create several symbols at once from a space- or comma-separated list.
 * With a string literal the result is a typed tuple.
 *
 * @example
 * const [theta, phi] = symbols('theta phi', { real: true });
 */
export function symbols<S extends string>(names: S, assumptions: Assumptions = {}): SymbolTuple<S> {
  return expandSymbolNames(names).map((n) => new Sym(n, assumptions)) as SymbolTuple<S>;
}

export {
  rationalFromFloat,
  rationalFromString,
  integerLog,
  expandSymbolNames,
  igcd,
  ilcm,
  integerNthroot,
  trailing,
  numDigits,
  modInverse,
  limitDenominator,
} from './core/numberutils';
export { nfloat, comp, nsimplify } from './numeric/nfloat';
export { factorInt } from './core/numbers';
export { leadterm, asLeadingTerm, getn, extractLeadingOrder } from './series/series';
export { finiteDiffWeights, asFiniteDifference } from './calculus/finitediff';
export { sqrtdenest } from './simplify/sqrtdenest';

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
export { BoolOp, and, or, not } from './core/boolalg';
export {
  solveset,
  solveUnivariateInequality,
  solvePolyInequality,
  solveRationalInequalities,
  reduceInequalities,
  periodicity,
  singularities,
  stationaryPoints,
  isIncreasing,
  isStrictlyIncreasing,
  isDecreasing,
  isStrictlyDecreasing,
  isMonotonic,
  isConvex,
  maximum,
  minimum,
  asExprSetPairs,
  notEmptyIn,
  piecewiseExclusive,
} from './solvers/inequalities';
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
  jacobiSymbol,
  kroneckerSymbol,
  firstMotzkins,
  motzkinNumbersInRange,
  isMotzkin,
} from './functions/combinatorial';
export { polarify, expPolar, polarLift, periodicArgument, principalBranch, unbranchedArgument, unpolarify, extractBranchFactor } from './functions/polar';
export { factorSystem, factorSystemCond, solvePolySystem } from './solvers/polysys';
export { rsolve, rsolveHyper, rsolvePoly, rsolveRatio } from './solvers/recurr';

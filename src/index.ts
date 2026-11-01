// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Public entry point of symjs.
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
} from './core/methods';
export { subs, xreplace, freeSymbols, countOps, mapBottomUp, rebuild } from './core/traverse';

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
} from './functions/elementary';

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

// calculus
export { diff } from './calculus/diff';
export { Function, functions, derivative } from './core/undef';
export type { UndefinedFunction } from './core/undef';
export { integrate } from './integrals/integrate';
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
export { powsimp } from './simplify/powsimp';
export { radsimp, collect } from './simplify/radsimp';
export { trigsimp, rewriteExp, rewriteTrig, expsimp, exptotrig, combineExp } from './simplify/trigsimp';
export { together, cancel, fraction } from './simplify/rational';

// polynomials
export { UPoly, polyCoefficients, roots, factorPoly } from './polys/poly';
export {
  Poly,
  PolificationFailed,
  factor,
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
} from './solvers/solve';
export { dsolve, odeOrder } from './solvers/ode';

// numerics
export { evalf, evalfPrec, toComplex, lambdify } from './numeric/evalf';
export { float } from './numeric/floatctor';
export { round } from './numeric/round';
export { precToDps, dpsToPrec } from './numeric/mpf';

// printing / parsing
export { str } from './printing/str';
export { asOrderedTerms as orderedTerms, asOrderedFactors as orderedFactors, sortKey } from './printing/sortkey';
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
} from './matrices/linalg';

// quantum
export * as gates from './quantum/gates';

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

export { rationalFromFloat, rationalFromString, integerLog, expandSymbolNames } from './core/numberutils';

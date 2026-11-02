// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Entry point `@symjs/symjs/core`: expression trees, arithmetic and
 * assumptions, symbols and undefined functions, elementary functions,
 * substitution and pattern matching, differentiation, expansion, numerical
 * evaluation, parsing and printing (str and LaTeX).
 *
 * The core does not import any other feature area; features such as
 * simplification or integration are late-bound and become available when
 * their entry point (or the root `@symjs/symjs`) is imported.
 */

import { Assumptions, Sym } from './core/nodes';
import { expandSymbolNames } from './core/numberutils';

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
export { diff } from './calculus/diff';
export { Function, functions, derivative } from './core/undef';
export type { UndefinedFunction } from './core/undef';
export { rel, Eq, Ne, Lt, Le, Gt, Ge, piecewise } from './core/logic';
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
export { evalf, evalfPrec, toComplex, lambdify } from './numeric/evalf';
export { float } from './numeric/floatctor';
export { round } from './numeric/round';
export { precToDps, dpsToPrec } from './numeric/mpf';
export { str } from './printing/str';
export { asOrderedTerms as orderedTerms, asOrderedFactors as orderedFactors, sortKey, compareKeys } from './printing/sortkey';
export { couldExtractMinusSign } from './core/ops';
export { latex } from './printing/latex';
export { parse, ex } from './parsing/parser';
export type { ParseOptions } from './parsing/parser';
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
export { BoolOp, and, or, not } from './core/boolalg';

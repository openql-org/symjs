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

import type { Assumptions, Expr as ExprNode, ExprLike as ExprLikeT } from './core/nodes';
import { Derivative as DerivativeNode, Piecewise as PiecewiseNode, Sym as SymbolNode } from './core/nodes';
import { expandSymbolNames as expandNames } from './core/numberutils';
import { derivative as derivativeFn } from './core/undef';
import { piecewise as piecewiseFn } from './core/logic';
import { sympify as sympifyFn } from './core/ops';
import { callableClass } from './core/callable';
import { Subs as subsFn, SubsNode } from './core/subsnode';
import { Lambda as lambdaFn, LambdaNode } from './core/lambda';

export {
  Expr,
  Rational,
  Float,
  Sym,
  Wild,
  WildFunction,
  Dummy,
  Constant as NumberSymbol,
  Add,
  Mul,
  Pow,
  Fn as AppliedFunction,
  BoolAtom as BooleanAtom,
  Rel,
  Integral,
  Limit,
  Order,
  UndefFn as AppliedUndef,
  S,
  pi,
  E,
  I,
  oo,
  zoo,
  nan,
  isRational,
  isFloat,
  isSymbol,
  isAdd,
  isMul,
  isPow,
  isFn as isFunction,
  isInteger,
  isNum as isNumber,
  ExtensionExpr,
} from './core/nodes';
export { ExprMap } from './core/exprmap';
export { Indexed, IndexedBase } from './core/indexed';
export { Factors } from './core/factors';
export { AccumBounds, AccumBoundsNode } from './core/accumbounds';
export {
  isReal,
  isPositive,
  isNegative,
  isNonNegative,
  isNonZero,
  isZero,
  isIntegerValued,
  match,
  extractMultiplicatively,
  extractAdditively,
  asCoefficient,
  isMeromorphic,
} from './core/public';
export { isTrue, isFalse, isUnknown, truthNot, truthAnd, truthOr, NoMatch, NoMatchResult, isNoMatch, Unsolved, UnsolvedResult, isUnsolved } from './core/truth';
export type { Truth } from './core/truth';
export { classKey } from './printing/sortkey';
export { expand_power_base as separate } from './simplify/expand';
export { Q, ask, refine, AppliedPredicate, Predicate, registerHandler, removeHandler, AssumptionsContext, globalAssumptions, assuming } from './core/refine';
export type { Assumption, PredicateName, PredicateHandler } from './core/refine';
export {
  SympifyError,
  PoleError,
  PrecisionExhausted,
  EvalfValueError,
  NonlinearError,
  NotImplementedError,
  NotLoadedError,
  PolynomialError,
  DomainError,
  ExactQuotientFailed,
  NotInvertible,
  MatrixError,
  ShapeError,
  NonSquareMatrixError,
  NonInvertibleMatrixError,
  NonPositiveDefiniteMatrixError,
  seterr,
} from './core/errors';
export { Basic, BasicNode } from './core/basic';
export { Kind, NumberKind, BooleanKind, UndefinedKind } from './core/kind';
export { SymNumber, RealNumber, Atom, AtomicExpr, FunctionClass, UnevaluatedExpr, DeferredVector, genericExpr } from './core/classes';
export { defineFunction, implementedFunction, DefinedFunctionCall } from './core/defun';
export type { DefinedFunction, FunctionDefinition } from './core/defun';
export type {
  ExprKind,
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
export { sympify, sympifyMethod, converter } from './core/sympify';
export type { Sympifiable } from './core/sympify';
export {
  add,
  mul,
  pow,
  sub,
  neg,
  sqrt,
  exp,
  asBaseExp,
} from './core/ops';
export {
  argsCnc,
  coeff,
  asIndependent,
  asCoeffAdd,
  asCoeffMul,
  primitive,
  asContentPrimitive,
  isPolynomial,
  isRationalFunction,
  isConstant,
  asRealImag,
  asNumerDenom,
  atoms,
  hasFree,
  asCoefficientsDict,
  asCoeffExponent,
  asPowersDict,
  isSame,
  equalValued,
  asTerms,
  asTwoTerms,
  hasXfree,
  isAlgebraicExpr,
  dummyEq,
} from './core/methods';
export {
  root,
  cbrt,
  realRoot,
} from './core/ops';
export {
  subs,
  xreplace,
  freeSymbols,
  mapBottomUp as bottomUp,
  rebuild,
  use,
  preorderTraversal,
  PreorderTraversal,
} from './core/traverse';
export { Tuple, TupleNode, Dict, DictNode } from './core/containers';
export {
  replace,
  find,
  ordered,
  countOps,
  count,
} from './core/match';
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
  abs as Abs,
  re,
  im,
  arg,
  conjugate,
  dagger,
  adjoint,
  transpose,
} from './functions/elementary/elementary';
export {
  cot,
  sec,
  csc,
  acot,
  asec,
  acsc,
  coth,
  sech,
  csch,
  asinh,
  acosh,
  atanh,
  acoth,
  asech,
  acsch,
  sinc,
} from './functions/elementary/trigext';
export {
  diff,
  fdiff,
} from './calculus/diff';
export {
  SymFunction,
} from './core/undef';
export type { UndefinedFunction } from './core/undef';
export {
  Eq,
  Ne,
  Lt,
  Le,
  Gt,
  Ge,
} from './core/logic';
export {
  expand,
  expand_mul as expandMul,
  expand_multinomial as expandMultinomial,
  expand_power_exp as expandPowerExp,
  expand_power_base as expandPowerBase,
  expand_log as expandLog,
  expand_trig as expandTrig,
  expand_complex as expandComplex,
} from './simplify/expand';
export type { ExpandHints } from './simplify/expand';
export {
  evalf,
  toComplex,
  lambdify,
} from './numeric/evalf';
export {
  float,
} from './numeric/floatctor';
export {
  round,
} from './numeric/round';
export {
  precToDps,
  dpsToPrec,
} from './numeric/mpf';
export {
  str,
  str as sstr,
} from './printing/str';
export {
  asOrderedTerms,
  asOrderedFactors,
  sortKey,
} from './printing/sortkey';
export type { TermOrder } from './printing/sortkey';
export {
  couldExtractMinusSign,
} from './core/ops';
export {
  latex,
} from './printing/latex';
export { StrPrinter, sstrrepr, printLatex, multilineLatex } from './printing/printers';
export type { StrPrintable, MultilineLatexOptions } from './printing/printers';
export {
  parse,
  parse as parseExpr,
  ex,
} from './parsing/parser';
export type { ParseOptions } from './parsing/parser';
/** Create a symbol. */
export function symbol(name: string, assumptions: Assumptions = {}): SymbolNode {
  return new SymbolNode(name, assumptions);
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
type ToSyms<T extends readonly unknown[]> = { [K in keyof T]: SymbolNode };
export type SymbolTuple<S extends string> = string extends S ? SymbolNode[] : ToSyms<SplitNames<S>>;
/**
 * Create several symbols at once from a space- or comma-separated list.
 * With a string literal the result is a typed tuple.
 *
 * @example
 * const [theta, phi] = symbols('theta phi', { real: true });
*/
export function symbols<S extends string>(names: S, assumptions: Assumptions = {}): SymbolTuple<S> {
  // oxlint-disable-next-line typescript/no-unsafe-type-assertion -- the tuple length is computed from the literal type S, which the type system cannot relate to the runtime split
  return expandNames(names).map((n) => new SymbolNode(n, assumptions)) as SymbolTuple<S>;
}
export {
  integerLog,
  igcd,
  ilcm,
  integerNthroot,
  trailing,
  numDigits,
  modInverse,
  limitDenominator,
} from './core/numberutils';
export {
  nfloat,
  comp,
  nsimplify,
} from './numeric/nfloat';
export {
  and as And,
  or as Or,
  not as Not,
  xor as Xor,
} from './core/boolalg';

const isCountPair = (v: ExprNode | readonly [ExprNode, number]): v is readonly [ExprNode, number] => Array.isArray(v);

/**
 * SymPy `Derivative(expr, *variables)`: an unevaluated derivative. Each
 * variable is a symbol or a `[symbol, count]` pair. Also the node class
 * (`e instanceof Derivative`).
 */
export const Derivative = /* @__PURE__ */ callableClass(
  DerivativeNode,
  (expr: ExprLikeT, ...variables: (ExprNode | readonly [ExprNode, number])[]): ExprNode =>
    derivativeFn(
      sympifyFn(expr),
      variables.map((v): [ExprNode, number] => (isCountPair(v) ? [v[0], v[1]] : [v, 1])),
    ),
);
export type Derivative = DerivativeNode;

/**
 * SymPy `Piecewise((expr, cond), ...)` with `[expr, cond]` pairs. Also the
 * node class (`e instanceof Piecewise`).
 */
export const Piecewise = /* @__PURE__ */ callableClass(PiecewiseNode, piecewiseFn);
export type Piecewise = PiecewiseNode;

/**
 * SymPy `Subs(expr, variables, point)`: an unevaluated substitution (one
 * variable and point, or arrays of them). Also the node class.
 */
export const Subs = /* @__PURE__ */ callableClass(SubsNode, subsFn);
export type Subs = SubsNode;

/** SymPy `Lambda(variables, expr)`: an anonymous function (`.call(...)` applies it). Also the node class. */
export const Lambda = /* @__PURE__ */ callableClass(LambdaNode, lambdaFn);
export type Lambda = LambdaNode;

// ---- deprecated names (kept during 0.x, removed in 1.0; see docs/api-policy.md) ----

import { Constant as _Constant_ } from './core/nodes';
import { Fn as _Fn_ } from './core/nodes';
import { BoolAtom as _BoolAtom_ } from './core/nodes';
import { Special as _Special_ } from './core/nodes';
import { UndefFn as _UndefFn_ } from './core/nodes';
import { compareExpr as _compareExpr_ } from './core/nodes';
import { isFn as _isFn_ } from './core/nodes';
import { isNum as _isNum_ } from './core/nodes';
import { rational as _rational_ } from './core/ops';
import { splitCoeff as _splitCoeff_ } from './core/ops';
import { keepCoeff as _keepCoeff_ } from './core/methods';
import { argsCncSplit as _argsCncSplit_ } from './core/methods';
import { mapBottomUp as _mapBottomUp_ } from './core/traverse';
import * as _pub_ from './core/public';
import { countOpsVisual as _countOpsVisual_ } from './core/match';
import { isInstance as _isInstance_ } from './core/match';
import { functions as _functions_ } from './core/undef';
import { derivative as _derivative_ } from './core/undef';
import { rel as _rel_ } from './core/logic';
import { piecewise as _piecewise_ } from './core/logic';
import { expand_mul as _expand_mul_ } from './simplify/expand';
import { expand_multinomial as _expand_multinomial_ } from './simplify/expand';
import { expand_power_exp as _expand_power_exp_ } from './simplify/expand';
import { expand_power_base as _expand_power_base_ } from './simplify/expand';
import { expand_log as _expand_log_ } from './simplify/expand';
import { expand_trig as _expand_trig_ } from './simplify/expand';
import { expand_complex as _expand_complex_ } from './simplify/expand';
import { evalfPrec as _evalfPrec_ } from './numeric/evalf';
import { asOrderedTerms as _orderedTerms_ } from './printing/sortkey';
import { asOrderedFactors as _orderedFactors_ } from './printing/sortkey';
import { compareKeys as _compareKeys_ } from './printing/sortkey';
import { rationalFromFloat as _rationalFromFloat_ } from './core/numberutils';
import { rationalFromString as _rationalFromString_ } from './core/numberutils';
import { expandSymbolNames as _expandSymbolNames_ } from './core/numberutils';
import { factorInt as _factorInt_ } from './core/numbers';
import { Sym as _Sym_ } from './core/nodes';
import { SymNumber as _SymNumber_ } from './core/classes';
import { SymFunction as _SymFunction_ } from './core/undef';
import { BoolOp as _BoolOp_ } from './core/boolalg';
import { and as _and_ } from './core/boolalg';
import { or as _or_ } from './core/boolalg';
import { not as _not_ } from './core/boolalg';


/** @deprecated Use `NumberSymbol`. */
export const Constant = _Constant_;

/** @deprecated Use `NumberSymbol`. */
export type Constant = _Constant_;

/** @deprecated Use `AppliedFunction`. */
export const Fn = _Fn_;

/** @deprecated Use `AppliedFunction`. */
export type Fn = _Fn_;

/** @deprecated Use `BooleanAtom`. */
export const BoolAtom = _BoolAtom_;

/** @deprecated Use `BooleanAtom`. */
export type BoolAtom = _BoolAtom_;

/** @deprecated Internal; removed from the public API in 1.0. */
export const Special = _Special_;

/** @deprecated Internal; removed from the public API in 1.0. */
export type Special = _Special_;

/** @deprecated Use `AppliedUndef`. */
export const UndefFn = _UndefFn_;

/** @deprecated Use `AppliedUndef`. */
export type UndefFn = _UndefFn_;

/** @deprecated Internal; removed from the public API in 1.0. */
export const compareExpr = _compareExpr_;

/** @deprecated Use `isFunction`. */
export const isFn = _isFn_;

/** @deprecated Use `isNumber`. */
export const isNum = _isNum_;

/** @deprecated Use `Rational.of`. */
export const rational = _rational_;

/** @deprecated Internal; removed from the public API in 1.0. */
export const splitCoeff = _splitCoeff_;

/** @deprecated Use `isIntegerValued`. */
export const isIntegerQ = _pub_.isIntegerValued;

/** @deprecated Internal; removed from the public API in 1.0. */
export const keepCoeff = _keepCoeff_;

/** @deprecated Internal; removed from the public API in 1.0. */
export const argsCncSplit = _argsCncSplit_;

/** @deprecated Use `bottomUp`. */
export const mapBottomUp = _mapBottomUp_;

/** @deprecated Internal; removed from the public API in 1.0. */
export const countOpsVisual = _countOpsVisual_;

/** @deprecated Internal; removed from the public API in 1.0. */
export const isInstance = _isInstance_;

/** @deprecated Internal; removed from the public API in 1.0. */
export const functions = _functions_;

/** @deprecated Use `Derivative`. */
export const derivative = _derivative_;

/** @deprecated Internal; removed from the public API in 1.0. */
export const rel = _rel_;

/** @deprecated Use `Piecewise`. */
export const piecewise = _piecewise_;

/** @deprecated Use `expandMul`. */
export const expand_mul = _expand_mul_;

/** @deprecated Use `expandMultinomial`. */
export const expand_multinomial = _expand_multinomial_;

/** @deprecated Use `expandPowerExp`. */
export const expand_power_exp = _expand_power_exp_;

/** @deprecated Use `expandPowerBase`. */
export const expand_power_base = _expand_power_base_;

/** @deprecated Use `expandLog`. */
export const expand_log = _expand_log_;

/** @deprecated Use `expandTrig`. */
export const expand_trig = _expand_trig_;

/** @deprecated Use `expandComplex`. */
export const expand_complex = _expand_complex_;

/** @deprecated Internal; removed from the public API in 1.0. */
export const evalfPrec = _evalfPrec_;

/** @deprecated Use `asOrderedTerms`. */
export const orderedTerms = _orderedTerms_;

/** @deprecated Use `asOrderedFactors`. */
export const orderedFactors = _orderedFactors_;

/** @deprecated Internal; removed from the public API in 1.0. */
export const compareKeys = _compareKeys_;

/** @deprecated Internal; removed from the public API in 1.0. */
export const rationalFromFloat = _rationalFromFloat_;

/** @deprecated Internal; removed from the public API in 1.0. */
export const rationalFromString = _rationalFromString_;

/** @deprecated Internal; removed from the public API in 1.0. */
export const expandSymbolNames = _expandSymbolNames_;

/** @deprecated Use `factorint` from `@symjs/symjs/ntheory` (or the root entry); removed in 1.0. */
export const factorInt = _factorInt_;

/** @deprecated Internal; removed from the public API in 1.0. */
export const BoolOp = _BoolOp_;

/** @deprecated Internal; removed from the public API in 1.0. */
export type BoolOp = _BoolOp_;

/** @deprecated Use `And`. */
export const and = _and_;

/** @deprecated Use `Or`. */
export const or = _or_;

/** @deprecated Use `Not`. */
export const not = _not_;

// SymPy names that are JavaScript globals (this module does not use the globals)

/** @deprecated Use `Sym` (`Symbol` shadows the JavaScript global); removed in 1.0. */
export const Symbol = _Sym_;

/** @deprecated Use `Sym` (`Symbol` shadows the JavaScript global); removed in 1.0. */
export type Symbol = _Sym_;

/** @deprecated Use `SymNumber` (`Number` shadows the JavaScript global); removed in 1.0. */
export const Number = _SymNumber_;

/** @deprecated Use `SymFunction` (`Function` shadows the JavaScript global); removed in 1.0. */
export const Function = _SymFunction_;

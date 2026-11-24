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
import { Add as AddNode, Expr as ExprClass, Derivative as DerivativeNode, Dummy as DummyNode, Mul as MulNode, Piecewise as PiecewiseNode, Pow as PowNode, Sym as SymbolNode, registerHead, Rational as RationalNode, impl } from './core/nodes';
import type { Head } from './core/nodes';
import { expandSymbolNames as expandNames } from './core/numberutils';
import { derivative as derivativeFn } from './core/undef';
import { piecewise as piecewiseFn } from './core/logic';
import { add as addFn, mul as mulFn, pow as powFn, sympify as sympifyFn } from './core/ops';
import { callableClass } from './core/callable';
import { Subs as subsFn, SubsNode } from './core/subsnode';
import { Lambda as lambdaFn, LambdaNode } from './core/lambda';
export { Id } from './core/lambda';

export { inverse } from './core/inverse';
export { epsilonEq } from './numeric/comparison';

export {
  Expr,
  Rational,
  Float,
  Wild,
  WildFunction,
  Constant as NumberSymbol,
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
export { Factors, Term } from './core/factors';
export { FactRules } from './core/facts';
export { AccumBounds, AccumBoundsNode } from './core/accumbounds';
export {
  isReal,
  isPositive,
  isNegative,
  isZero,
  isIntegerValued,
  match,
  extractMultiplicatively,
  extractAdditively,
  asCoefficient,
  isMeromorphic,
  matches,
  getO,
} from './core/public';
export { isIrrational, isAlgebraic, isComplex, isFinite, isPrime, isEven, isOdd, isImaginary, isHermitian, isAntihermitian, isExtendedNegative, isExtendedPositive, isPolar } from './core/public';
export { isNonnegative, isNonpositive, isNonzero, isComposite, isExtendedNonpositive, isExtendedNonzero, isNoninteger, isTranscendental, isCommutative, isSingular } from './core/public';
export { canonicalRelation } from './core/logic';
export { Relational, isEq, isNeq, isGe, isLe, isGt, isLt, reversed, reversedSign, negated, relationalEquals } from './core/relational';
export { disambiguate, uniquelyNamedSymbol } from './core/symbol';
export type { UniqueSymbolOptions } from './core/symbol';
export { unchanged } from './core/expr';
export { isTrue, isFalse, isUnknown, truthNot, truthAnd, truthOr, fuzzyBool, fuzzyAnd, fuzzyOr, fuzzyNot, fuzzyXor, fuzzyNand, NoMatch, NoMatchResult, isNoMatch, Unsolved, UnsolvedResult, isUnsolved } from './core/truth';
export type { Truth, FuzzyLike } from './core/truth';
export { classKey } from './printing/sortkey';
export { expand_power_base as separate } from './simplify/expand';
export { Q, ask, refine, AppliedPredicate, Predicate, AskHandler, registerHandler, removeHandler, AssumptionsContext, globalAssumptions, assuming } from './core/refine';
export type { Assumption, PredicateName, PredicateHandler } from './core/refine';
export { assumptions, checkAssumptions, commonAssumptions, failingAssumptions } from './core/checkassumptions';
export type { AssumptionName, AssumptionValues } from './core/checkassumptions';
export {
  SympifyError,
  PoleError,
  PrecisionExhausted,
  EvalfValueError,
  NonlinearError,
  NotImplementedError,
  ReorderError,
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
export { Kind, NumberKind, BooleanKind, UndefinedKind, TupleKind } from './core/kind';
export { SymNumber, RealNumber, Atom, AtomicExpr, FunctionClass, UnevaluatedExpr, DeferredVector, genericExpr } from './core/classes';
export { evaluate, globalParameters } from './core/parameters';
export { Transform } from './core/rules';
export { defineFunction, implementedFunction, DefinedFunctionCall, arity } from './core/defun';
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
  isConstantTruth,
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
  asDummy,
  assumptions0,
  canonicalVariables,
  iterFreeArgs,
  exprFreeSymbols,
  isScalar,
  asExpr,
  copy,
  removeO,
  normal,
  nseries,
  rcall,
  prod,
} from './core/methods';
export {
  root,
  cbrt,
  realRoot,
} from './core/ops';
export {
  subs,
  subsFunction,
  xreplace,
  freeSymbols,
  mapBottomUp as bottomUp,
  rebuild,
  use,
  preorderTraversal,
  PreorderTraversal,
  piecewiseFold,
} from './core/traverse';
export { iterArgs, Tuple, TupleNode, Dict, DictNode } from './core/containers';
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
  period,
} from './functions/elementary/trigext';
import { diff as scalarDiff } from './calculus/diff';
import { booleanCalculus } from './core/boolalg';
export { fdiff } from './calculus/diff';

/**
 * Differentiates an expression `order` times with respect to `x`; Boolean
 * functions of binary symbols are differentiated as Boolean derivatives. A
 * derivative that cannot be computed is returned as a `Derivative`.
 *
 * @param ex - The expression to differentiate.
 * @param x - The variable.
 * @param order - The order of the derivative.
 * @returns The derivative.
 * @see SymPy `sympy.core.function.diff`
 * @example
 * ```ts
 * import { diff, ex, SymFunction, symbols } from '@symjs/symjs';
 *
 * const [x, y] = symbols('x y');
 * const f = SymFunction('f');
 * diff(ex`sin(x)`, x); // => cos(x)
 * diff(f(x), x, 3); // => Derivative(f(x), (x, 3))
 * diff(diff(ex`sin(x)*cos(y)`, x, 2), y, 2); // => sin(x)*cos(y)
 * ```
 */
export function diff(ex: ExprLikeT, x: ExprNode, order: ExprLikeT = 1): ExprNode {
  const e = sympifyFn(ex);
  if (e.kind === 'BoolOp' || e.kind === 'Extension') {
    const count = sympifyFn(order);
    if (count instanceof RationalNode && count.isInteger && count.p > 0n && count.p <= BigInt(globalThis.Number.MAX_SAFE_INTEGER)) {
      const first = booleanCalculus.derivative?.(e, x);
      if (first !== undefined) return scalarDiff(first, x, count.p - 1n);
    }
  }
  return scalarDiff(e, x, order);
}
impl.diff = diff;
export {
  FunctionHead,
  SymFunction,
} from './core/undef';
export type { UndefinedFunction, FunctionClassLike } from './core/undef';
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
  isComparable,
  pureComplex,
  scaledZero,
  toComplex,
  lambdify,
} from './numeric/evalf';
export type { RawEvalfResult, ScaledZero, RawMpfTuple } from './numeric/evalf';
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
export type { LatexOptions, LatexPrintable, LatexMatrix, LatexObject } from './printing/latex';
export { StrPrinter, sstr, sstrrepr, printLatex, multilineLatex } from './printing/printers';
export type { StrPrintable, MultilineLatexOptions, SstrOptions } from './printing/printers';
export {
  parse,
  parse as parseExpr,
  ex,
  tokenSplittable,
} from './parsing/parser';
export { kernS } from './parsing/sympify';
export type { ParseOptions, ParseTransformation } from './parsing/parser';
/**
 * Create a symbol.
 *
 * @param name - The symbolic name or names.
 * @param assumptions - The facts to assume.
 * @returns The newly constructed symbol.
 * @see SymPy `sympy.core.symbol.Symbol`
 * @example
 * ```ts
 * import { isPositive, symbol } from '@symjs/symjs';
 *
 * isPositive(symbol('x', { positive: true })); // => True
 * ```
 */
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
/** The tuple of symbols corresponding to the names in a string literal. */
export type SymbolTuple<S extends string> = string extends S ? SymbolNode[] : ToSyms<SplitNames<S>>;
/**
 * Creates symbols from a list of names separated by spaces or commas. Ranges
 * such as `x:3` or `a(1:3)` give numbered names. With a string literal the
 * result is a typed tuple.
 *
 * @param names - The names.
 * @param assumptions - The assumptions of every symbol (`real`, `positive`, ...).
 * @returns The symbols, in the order of the names.
 * @see SymPy `sympy.core.symbol.symbols`
 * @example
 * ```ts
 * import { isReal, symbols } from '@symjs/symjs';
 *
 * symbols('x,y'); // => [x, y]
 * symbols('x:5'); // => [x0, x1, x2, x3, x4]
 * symbols('x5:10,y:3'); // => [x5, x6, x7, x8, x9, y0, y1, y2]
 * const [theta] = symbols('theta', { real: true });
 * isReal(theta); // => True
 * ```
 */
export function symbols<S extends string>(names: S, assumptions: Assumptions = {}): SymbolTuple<S> {
  // oxlint-disable-next-line typescript/no-unsafe-type-assertion -- the tuple length is computed from the literal type S, which the type system cannot relate to the runtime split
  return expandNames(names).map((n) => new SymbolNode(n, assumptions)) as SymbolTuple<S>;
}
/**
 * The symbols of `names`, as `symbols` creates
 * them. SymPy also binds them in the caller's namespace; JavaScript has no
 * such namespace, so var only returns them (`const [x, y] = sj.var('x y')`).
 *
 * @remarks
 * For `var('x')`, SymPy displays `x`. For `var('a,ab,abc')`, SymPy displays `(a, ab, abc)`.
 * @param names - The symbolic name or names.
 * @param assumptions - The facts to assume.
 * @returns The symbols corresponding to the expanded names.
 * @see SymPy `sympy.core.symbol.var`
 * @example
 * ```ts
 * import { var as symbolsVar } from '@symjs/symjs';
 *
 * symbolsVar('x'); // => [x]
 * symbolsVar('a,ab,abc'); // => [a, ab, abc]
 * ```
 */
function symbolsVar<S extends string>(names: S, assumptions: Assumptions = {}): SymbolTuple<S> {
  return symbols(names, assumptions);
}
export { symbolsVar as var };
export {
  integerLog,
  igcd,
  igcdex,
  igcdLehmer,
  intValued,
  approximationInterval,
  ilcm,
  integerNthroot,
  isqrt,
  trailing,
  numDigits,
  modInverse,
  limitDenominator,
  mpfNorm,
} from './core/numberutils';
export {
  nfloat,
  comp,
  nsimplify,
} from './numeric/nfloat';
export {
  and as And,
  or as Or,
  xor as Xor,
} from './core/boolalg';

/**
 * Logical negation of one proposition.
 *
 * @param x - The argument of the function.
 * @returns The logical negation of the proposition.
 * @see SymPy `sympy.logic.boolalg.Not`
 * @example
 * ```ts
 * import { Not, ex } from '@symjs/symjs';
 *
 * Not(true); // => False
 * Not(ex`x`); // => ~x
 * ```
 */
export function Not(x: ExprLikeT | boolean): ExprNode {
  if (arguments.length !== 1) throw new TypeError('Not requires one argument');
  return _not_(x);
}

type DerivativeVariable = ExprNode | readonly [ExprNode, number];
const isCountPair = (v: DerivativeVariable): v is readonly [ExprNode, number] => Array.isArray(v);
const isDerivativeVariable = (v: DerivativeVariable | EvaluateOptions): v is DerivativeVariable => Array.isArray(v) || v instanceof ExprClass;

/**
 * An unevaluated derivative of `expr` with respect to the variables, each a
 * symbol (or a function application) or a `[symbol, count]` pair. With a last
 * argument `{ evaluate: true }` the derivative is computed, as {@link diff}
 * does. Also the node class (`e instanceof Derivative`).
 *
 * @see SymPy `sympy.core.function.Derivative`
 * @param expr - The input expression.
 * @param rest - Differentiation variables or variable-count pairs, optionally followed by `{ evaluate: true }`.
 * @returns The derivative, held unevaluated unless evaluation is requested.
 * @example
 * ```ts
 * import { Derivative, ex, SymFunction, symbols } from '@symjs/symjs';
 *
 * const [x, y] = symbols('x y');
 * const f = SymFunction('f');
 * Derivative(ex`sin(x)`, x); // => Derivative(sin(x), x)
 * Derivative(ex`x**3*y`, [x, 2], y); // => Derivative(x**3*y, (x, 2), y)
 * Derivative(ex`x**2`, x, { evaluate: true }); // => 2*x
 * Derivative(f(x).pow(2), f(x), { evaluate: true }); // => 2*f(x)
 * ```
 */
export const Derivative = /* @__PURE__ */ callableClass(
  DerivativeNode,
  (expr: ExprLikeT, ...rest: (DerivativeVariable | EvaluateOptions)[]): ExprNode => {
    const last = rest[rest.length - 1];
    const options = last !== undefined && !isDerivativeVariable(last) ? last : undefined;
    const pairs = (options === undefined ? rest : rest.slice(0, -1)).map((v): [ExprNode, number] => {
      if (!isDerivativeVariable(v)) throw new TypeError('the options object must be the last argument');
      return isCountPair(v) ? [v[0], v[1]] : [v, 1];
    });
    const e = sympifyFn(expr);
    if (options?.evaluate === true) return pairs.reduce((acc, [v, n]) => diff(acc, v, n), e);
    return derivativeFn(e, pairs);
  },
);
export type Derivative = DerivativeNode;

/**
 * Constructs a piecewise expression from ordered `[expr, cond]` pairs. The first true condition selects
 * the value. Use `e instanceof Piecewise` to recognize a piecewise node.
 *
 * @param args - Expression-condition pairs in priority order, followed by optional evaluation settings.
 * @returns The value of the first applicable branch or a symbolic piecewise expression.
 * @see SymPy `sympy.functions.elementary.piecewise.Piecewise`
 * @example
 * ```ts
 * import { Piecewise } from '@symjs/symjs';
 *
 * Piecewise([1, false], [2, true]); // => 2
 * ```
 */
export const Piecewise = /* @__PURE__ */ callableClass(PiecewiseNode, piecewiseFn);
export type Piecewise = PiecewiseNode;

/**
 * An unevaluated substitution (one
 * variable and point, or arrays of them). Also the node class.
 *
 * @param exprIn - The input expression.
 * @param variables - The variables to substitute.
 * @param point - The values at which to evaluate the expression.
 * @returns The expression with the substitution held unevaluated.
 * @see SymPy `sympy.core.function.Subs`
 * @example
 * ```ts
 * import { Subs, ex } from '@symjs/symjs';
 *
 * Subs(ex`z + f(x)*sin(y)`, [ex`x`, ex`y`], [0, 1]); // => Subs(z + f(x)*sin(y), (x, y), (0, 1))
 * ```
 */
export const Subs = /* @__PURE__ */ callableClass(SubsNode, subsFn);
export type Subs = SubsNode;

/**
 * An anonymous function (`.call(...)` applies it). Also the node class.
 *
 * @param variables - The bound parameters.
 * @param expr - The function body.
 * @returns The symbolic anonymous function.
 * @see SymPy `sympy.core.function.Lambda`
 * @example
 * ```ts
 * import { Lambda, ex, symbols } from '@symjs/symjs';
 *
 * Lambda(symbols('x')[0], ex`x**2`).call(3); // => 9
 * ```
 */
export const Lambda = /* @__PURE__ */ callableClass(LambdaNode, lambdaFn);

/** The options of SymPy's Add, Mul and Pow: `{ evaluate: false }` keeps the node as it is built. */
export interface EvaluateOptions {
  /** Whether to simplify the expression during construction. */
  evaluate?: boolean;
}

const isEvaluateOptions = (v: unknown): v is EvaluateOptions => typeof v === 'object' && v !== null && !(v instanceof ExprClass);

/** The arguments and whether to evaluate: a trailing options object is taken off. */
function evaluateArgs(args: readonly (ExprLikeT | EvaluateOptions)[]): [ExprNode[], boolean] {
  const last = args[args.length - 1];
  const options = isEvaluateOptions(last) ? last : undefined;
  const xs = (options === undefined ? args : args.slice(0, -1)).map((a) => {
    if (isEvaluateOptions(a)) throw new TypeError('the options object must be the last argument');
    return sympifyFn(a);
  });
  return [xs, options?.evaluate !== false];
}

/**
 * `Add(x, y)` is x + y with automatic evaluation, `Add(x, x, { evaluate: false })` stays a sum; `func(x + y) === Add`.
 *
 * @param args - The terms followed by an optional `evaluate` setting.
 * @returns The sum of the operands.
 * @see SymPy `sympy.core.add.Add`
 * @example
 * ```ts
 * import { Add, ex } from '@symjs/symjs';
 *
 * Add(ex`x`, 1); // => x + 1
 * Add(ex`x`, ex`x`); // => 2*x
 * ```
 */
export const Add = /* @__PURE__ */ callableClass(AddNode, (...args: (ExprLikeT | EvaluateOptions)[]): ExprNode => {
  const [xs, evaluate] = evaluateArgs(args);
  return evaluate ? addFn(...xs) : new AddNode(xs);
});
export type Add = AddNode;
/**
 * `Mul(x, y)` is x*y with automatic evaluation, `{ evaluate: false }` keeps the product; `func(x*y) === Mul`.
 *
 * @param args - The factors followed by an optional `evaluate` setting.
 * @returns The product of the operands.
 * @see SymPy `sympy.core.mul.Mul`
 * @example
 * ```ts
 * import { Mul, ex } from '@symjs/symjs';
 *
 * Mul(ex`x`, 1); // => x
 * Mul(ex`x`, ex`x`); // => x**2
 * ```
 */
export const Mul = /* @__PURE__ */ callableClass(MulNode, (...args: (ExprLikeT | EvaluateOptions)[]): ExprNode => {
  const [xs, evaluate] = evaluateArgs(args);
  return evaluate ? mulFn(...xs) : new MulNode(xs);
});
export type Mul = MulNode;
/**
 * `Pow(x, 2)` is x**2 with automatic evaluation, `{ evaluate: false }` keeps the power; `func(x**2) === Pow`.
 *
 * @param base - The base of the power.
 * @param exp - The exponent.
 * @param options - Set `evaluate` to false to keep the power unevaluated.
 * @returns The resulting power.
 * @see SymPy `sympy.core.power.Pow`
 */
export const Pow = /* @__PURE__ */ callableClass(PowNode, (base: ExprLikeT, exp: ExprLikeT, options: EvaluateOptions = {}): ExprNode =>
  options.evaluate === false ? new PowNode(sympifyFn(base), sympifyFn(exp)) : powFn(base, exp));
export type Pow = PowNode;
/**
 * Creates a symbol, a named variable with optional assumptions. Two symbols
 * with the same name and assumptions are equal. Callable with or without
 * `new`; also the node class (`e instanceof Sym`). {@link symbols} creates
 * several at once.
 *
 * @see SymPy `sympy.core.symbol.Symbol`
 * @param name - The symbolic name or names.
 * @param assumptions - The facts to assume.
 * @returns The newly constructed symbol.
 * @example
 * ```ts
 * import { ex, isPositive, sqrt, Sym } from '@symjs/symjs';
 *
 * const x = Sym('x');
 * const y = Sym('y', { positive: true });
 * x.equals(Sym('x')); // => True
 * isPositive(y); // => True
 * sqrt(y.pow(2)); // => y
 * ex`x + 1`.has(x); // => True
 * ```
 */
export const Sym = /* @__PURE__ */ callableClass(SymbolNode, (name: string, assumptions: Assumptions = {}): SymbolNode => new SymbolNode(name, assumptions));
export type Sym = SymbolNode;
/**
 * A symbol unique to its creation, `Dummy('x')` or with `new`; `func(d) === Dummy`.
 *
 * @param name - The symbolic name or names.
 * @param assumptions - The facts to assume.
 * @returns The newly constructed symbol.
 * @see SymPy `sympy.core.symbol.Dummy`
 * @example
 * ```ts
 * import { Dummy } from '@symjs/symjs';
 *
 * Dummy('x').equals(Dummy('x')); // => False
 * ```
 */
export const Dummy = /* @__PURE__ */ callableClass(DummyNode, (name?: string, assumptions: Assumptions = {}): DummyNode => new DummyNode(name, assumptions));
export type Dummy = DummyNode;
registerHead(AddNode, Add);
registerHead(MulNode, Mul);
registerHead(PowNode, Pow);
registerHead(SymbolNode, Sym);
registerHead(DummyNode, Dummy);

/**
 * The head of an expression, the public constructor or function that builds it from
 * its arguments. `func(sin(x)) === sin`, `func(x + y) === Add`, and `func(e)(...e.args)` equals `e`
 * for an expression with arguments; an atom (a symbol, a number) is not rebuilt from its arguments,
 * as in SymPy. `Sum` and `Product` take their limits as `[k, a, b]` arrays while their nodes hold
 * them flat: `rebuild(e, args)` rebuilds those.
 *
 * @param e - The input expression.
 * @returns The callable expression head.
 * @see SymPy `sympy.core.basic.Basic.func`
 * @example
 * ```ts
 * import { Add, ex, func } from '@symjs/symjs';
 *
 * func(ex`x + y`) === Add; // => True
 * ```
 */
export function func(e: ExprLikeT): Head {
  return sympifyFn(e).func;
}
export type { Head };
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
import { SymNumber as _SymNumber_ } from './core/classes';
import { SymFunction as _SymFunction_ } from './core/undef';
import { BoolOp as _BoolOp_ } from './core/boolalg';
import { and as _and_ } from './core/boolalg';
import { or as _or_ } from './core/boolalg';
import { not as _not_ } from './core/boolalg';


/**
 * Alias for {@link NumberSymbol}.
 *
 * @deprecated Use {@link NumberSymbol}.
 * @see SymPy `sympy.core.numbers.NumberSymbol`
 */
export const Constant = _Constant_;

/** @deprecated Use `NumberSymbol`. */
export type Constant = _Constant_;

/**
 * Alias for {@link AppliedFunction}.
 *
 * @deprecated Use {@link AppliedFunction}.
 * @see SymPy `sympy.core.function.Function`
 * @example
 * ```ts
 * import { Fn, ex } from '@symjs/symjs';
 *
 * new Fn('sin', [ex`x`]); // => sin(x)
 * ```
 */
export const Fn = _Fn_;

/** @deprecated Use `AppliedFunction`. */
export type Fn = _Fn_;

/**
 * Alias for {@link BooleanAtom}.
 *
 * @deprecated Use {@link BooleanAtom}.
 * @see SymPy `sympy.logic.boolalg.BooleanAtom`
 */
export const BoolAtom = _BoolAtom_;

/** @deprecated Use `BooleanAtom`. */
export type BoolAtom = _BoolAtom_;

/**
 * An expression node for a signed infinity, complex infinity or indeterminate number.
 *
 * @deprecated Internal; removed from the public API in 1.0.
 */
export const Special = _Special_;

/** @deprecated Internal; removed from the public API in 1.0. */
export type Special = _Special_;

/**
 * Alias for {@link AppliedUndef}.
 *
 * @deprecated Use {@link AppliedUndef}.
 * @see SymPy `sympy.core.function.AppliedUndef`
 */
export const UndefFn = _UndefFn_;

/** @deprecated Use `AppliedUndef`. */
export type UndefFn = _UndefFn_;

/**
 * Compares two expressions in canonical order.
 *
 * @deprecated Internal; removed from the public API in 1.0.
 */
export const compareExpr = _compareExpr_;

/**
 * Alias for {@link isFunction}.
 *
 * @deprecated Use {@link isFunction}.
 * @param e - The input expression.
 * @param name - The symbolic name or names.
 * @returns Whether the expression belongs to the indicated node class.
 * @see SymPy `sympy.core.expr.Expr.is_Function`
 */
export const isFn = _isFn_;

/**
 * Alias for {@link isNumber}.
 *
 * @deprecated Use {@link isNumber}.
 * @param e - The input expression.
 * @returns Whether the expression belongs to the indicated node class.
 * @see SymPy `sympy.core.expr.Expr.is_Number`
 */
export const isNum = _isNum_;

/**
 * Alias for {@link Rational.of}.
 *
 * @deprecated Use {@link Rational.of}.
 * @param p - The integer numerator.
 * @param q - The nonzero integer denominator.
 * @returns The rational number in lowest terms.
 * @see SymPy `sympy.core.numbers.Rational`
 * @example
 * ```ts
 * import { rational } from '@symjs/symjs';
 *
 * rational(1, 2); // => 1/2
 * rational(3, 4); // => 3/4
 * ```
 */
export const rational = _rational_;

/**
 * Separates the numeric coefficient of a product from its remaining factors.
 *
 * @deprecated Internal; removed from the public API in 1.0.
 */
export const splitCoeff = _splitCoeff_;

/**
 * Alias for {@link isIntegerValued}.
 *
 * @deprecated Use {@link isIntegerValued}.
 * @param e - The input expression.
 * @returns The truth value, or `'unknown'` if the assumptions do not determine it.
 * @see SymPy `sympy.core.expr.Expr.is_integer`
 */
export const isIntegerQ = _pub_.isIntegerValued;

/**
 * Attaches a coefficient to an expression while preserving its additive grouping.
 *
 * @deprecated Internal; removed from the public API in 1.0.
 */
export const keepCoeff = _keepCoeff_;

/**
 * Partitions the factors of a product into commutative and ordered noncommutative factors.
 *
 * @deprecated Internal; removed from the public API in 1.0.
 */
export const argsCncSplit = _argsCncSplit_;

/**
 * Alias for {@link bottomUp}.
 *
 * @deprecated Use {@link bottomUp}.
 * @param e - The input expression.
 * @param f - The transformation to apply to each selected subexpression.
 * @returns The transformed root after visiting all its descendants.
 * @see SymPy `sympy.core.traversal.bottom_up`
 */
export const mapBottomUp = _mapBottomUp_;

/**
 * Represents the operation count as a sum of named operations.
 *
 * @deprecated Internal; removed from the public API in 1.0.
 */
export const countOpsVisual = _countOpsVisual_;

/**
 * Tests an object against an expression class.
 *
 * @deprecated Internal; removed from the public API in 1.0.
 */
export const isInstance = _isInstance_;

/**
 * Creates undefined function heads from a list of names.
 *
 * @deprecated Internal; removed from the public API in 1.0.
 */
export const functions = _functions_;

/**
 * Alias for {@link Derivative}.
 *
 * @deprecated Use {@link Derivative}.
 * @param expr - The input expression.
 * @param variables - The differentiation variables paired with their multiplicities.
 * @param evaluated - Whether to evaluate the derivative immediately.
 * @returns The derivative, held unevaluated unless evaluation is requested.
 * @see SymPy `sympy.core.function.Derivative`
 * @example
 * ```ts
 * import { derivative, ex } from '@symjs/symjs';
 *
 * derivative(ex`x**2`, [[ex`x`, 1]]); // => Derivative(x**2, x)
 * ```
 */
export const derivative = _derivative_;

/**
 * Builds a comparison from an operator and two expressions.
 *
 * @deprecated Internal; removed from the public API in 1.0.
 */
export const rel = _rel_;

/**
 * Alias for {@link Piecewise}.
 *
 * @deprecated Use {@link Piecewise}.
 * @param args - Expression-condition pairs in priority order, followed by optional evaluation settings.
 * @returns The value of the first applicable branch or a symbolic piecewise expression.
 * @see SymPy `sympy.functions.elementary.piecewise.Piecewise`
 * @example
 * ```ts
 * import { piecewise } from '@symjs/symjs';
 *
 * piecewise([1, false], [2, true]); // => 2
 * ```
 */
export const piecewise = _piecewise_;

/**
 * Alias for {@link expandMul}.
 *
 * @deprecated Use {@link expandMul}.
 * @param e - The input expression.
 * @returns The expanded expression.
 * @see SymPy `sympy.core.function.expand_mul`
 * @example
 * ```ts
 * import { ex, expand_mul } from '@symjs/symjs';
 *
 * expand_mul(ex`x*(x + 1)`); // => x**2 + x
 * ```
 */
export const expand_mul = _expand_mul_;

/**
 * Alias for {@link expandMultinomial}.
 *
 * @deprecated Use {@link expandMultinomial}.
 * @param e - The input expression.
 * @returns The expanded expression.
 * @see SymPy `sympy.core.function.expand_multinomial`
 * @example
 * ```ts
 * import { ex, expand_multinomial } from '@symjs/symjs';
 *
 * expand_multinomial(ex`(x + 1)**2`); // => x**2 + 2*x + 1
 * ```
 */
export const expand_multinomial = _expand_multinomial_;

/**
 * Alias for {@link expandPowerExp}.
 *
 * @deprecated Use {@link expandPowerExp}.
 * @param e - The input expression.
 * @param force - Whether to apply identities without checking the usual assumptions.
 * @returns The expanded expression.
 * @see SymPy `sympy.core.function.expand_power_exp`
 * @example
 * ```ts
 * import { ex, expand_power_exp } from '@symjs/symjs';
 *
 * expand_power_exp(ex`3**(y + 2)`); // => 9*3**y
 * expand_power_exp(ex`x**(y + 2)`); // => x**(y + 2)
 * ```
 */
export const expand_power_exp = _expand_power_exp_;

/**
 * Alias for {@link expandPowerBase}.
 *
 * @deprecated Use {@link expandPowerBase}.
 * @param e - The input expression.
 * @param opts - `force` permits splitting without positivity assumptions and `deep` controls recursion.
 * @returns The expanded expression.
 * @see SymPy `sympy.core.function.expand_power_base`
 * @example
 * ```ts
 * import { ex, expand_power_base } from '@symjs/symjs';
 *
 * expand_power_base(ex`(x*y)**z`); // => (x*y)**z
 * expand_power_base(ex`(2*exp(y))**x`); // => 2**x*exp(y)**x
 * ```
 */
export const expand_power_base = _expand_power_base_;

/**
 * Alias for {@link expandLog}.
 *
 * @deprecated Use {@link expandLog}.
 * @param e - The input expression.
 * @param options - A force flag or an object with `force` to ignore sign conditions, `deep` to recurse and `factor` to factor integer arguments.
 * @param legacy - The optional `factor` and `deep` settings when the preceding argument is the Boolean force flag.
 * @returns The expanded expression.
 * @see SymPy `sympy.core.function.expand_log`
 * @example
 * ```ts
 * import { ex, expand_log } from '@symjs/symjs';
 *
 * expand_log(ex`log(x*y)`, { force: true }); // => log(x) + log(y)
 * ```
 */
export const expand_log = _expand_log_;

/**
 * Alias for {@link expandTrig}.
 *
 * @deprecated Use {@link expandTrig}.
 * @param e - The input expression.
 * @returns The expanded expression.
 * @see SymPy `sympy.core.function.expand_trig`
 * @example
 * ```ts
 * import { ex, expand_trig } from '@symjs/symjs';
 *
 * expand_trig(ex`(x + y)*sin(x + y)`); // => (x + y)*(sin(x)*cos(y) + sin(y)*cos(x))
 * ```
 */
export const expand_trig = _expand_trig_;

/**
 * Alias for {@link expandComplex}.
 *
 * @deprecated Use {@link expandComplex}.
 * @param e - The input expression.
 * @returns The expanded expression.
 * @see SymPy `sympy.core.function.expand_complex`
 * @example
 * ```ts
 * import { ex, expand_complex } from '@symjs/symjs';
 *
 * expand_complex(ex`sqrt(I)`); // => sqrt(2)/2 + sqrt(2)*I/2
 * expand_complex(ex`exp(z)`); // => I*exp(re(z))*sin(im(z)) + exp(re(z))*cos(im(z))
 * ```
 */
export const expand_complex = _expand_complex_;

/**
 * Evaluates an expression at a specified binary precision.
 *
 * @deprecated Internal; removed from the public API in 1.0.
 */
export const evalfPrec = _evalfPrec_;

/**
 * Alias for {@link asOrderedTerms}.
 *
 * @deprecated Use {@link asOrderedTerms}.
 * @param e - The input expression.
 * @param order - The order.
 * @returns The terms or factors in canonical order.
 * @see SymPy `sympy.core.expr.Expr.as_ordered_terms`
 * @example
 * ```ts
 * import { ex, orderedTerms } from '@symjs/symjs';
 *
 * orderedTerms(ex`sin(x)**2*cos(x) + sin(x)**2 + 1`); // => [sin(x)**2*cos(x), sin(x)**2, 1]
 * orderedTerms(ex`x + 1/x`); // => [x, 1/x]
 * ```
 */
export const orderedTerms = _orderedTerms_;

/**
 * Alias for {@link asOrderedFactors}.
 *
 * @deprecated Use {@link asOrderedFactors}.
 * @param e - The input expression.
 * @returns The terms or factors in canonical order.
 * @see SymPy `sympy.core.expr.Expr.as_ordered_factors`
 */
export const orderedFactors = _orderedFactors_;

/**
 * Compares structural ordering keys for expressions.
 *
 * @deprecated Internal; removed from the public API in 1.0.
 */
export const compareKeys = _compareKeys_;

/**
 * Converts a binary floating-point value to its exact rational representation.
 *
 * @deprecated Internal; removed from the public API in 1.0.
 */
export const rationalFromFloat = _rationalFromFloat_;

/**
 * Parses a string as an exact rational number.
 *
 * @deprecated Internal; removed from the public API in 1.0.
 */
export const rationalFromString = _rationalFromString_;

/**
 * Expands symbol-name ranges into individual names.
 *
 * @deprecated Internal; removed from the public API in 1.0.
 */
export const expandSymbolNames = _expandSymbolNames_;

/**
 * Alias for {@link factorint}.
 *
 * @deprecated Use {@link factorint} from `@symjs/symjs/ntheory` (or the root entry); removed in 1.0.
 * @param nIn - The index.
 * @returns The prime factors and their multiplicities.
 * @see SymPy `sympy.ntheory.factor_.factorint`
 * @example
 * ```ts
 * import { factorInt } from '@symjs/symjs';
 *
 * factorInt(12n); // => {2: 2, 3: 1}
 * ```
 */
export const factorInt = _factorInt_;

/**
 * An expression node for a logical operation.
 *
 * @deprecated Internal; removed from the public API in 1.0.
 */
export const BoolOp = _BoolOp_;

/** @deprecated Internal; removed from the public API in 1.0. */
export type BoolOp = _BoolOp_;

/**
 * Alias for {@link And}.
 *
 * @deprecated Use {@link And}.
 * @param xs - The propositions to combine.
 * @returns The simplified Boolean expression.
 * @see SymPy `sympy.logic.boolalg.And`
 * @example
 * ```ts
 * import { and } from '@symjs/symjs';
 *
 * and(true, false); // => False
 * ```
 */
export const and = _and_;

/**
 * Alias for {@link Or}.
 *
 * @deprecated Use {@link Or}.
 * @param xs - The propositions to combine.
 * @returns The simplified Boolean expression.
 * @see SymPy `sympy.logic.boolalg.Or`
 * @example
 * ```ts
 * import { or } from '@symjs/symjs';
 *
 * or(true, false); // => True
 * ```
 */
export const or = _or_;

/**
 * Alias for {@link Not}.
 *
 * @deprecated Use {@link Not}.
 * @param x0 - The proposition to negate.
 * @returns The simplified Boolean expression.
 * @see SymPy `sympy.logic.boolalg.Not`
 * @example
 * ```ts
 * import { ex, not } from '@symjs/symjs';
 *
 * not(true); // => False
 * not(ex`x`); // => ~x
 * ```
 */
export const not = _not_;

import { isNonnegative as _isNonnegative_, isNonpositive as _isNonpositive_, isNonzero as _isNonzero_ } from './core/public';

/**
 * Alias for {@link isNonnegative}.
 *
 * @deprecated Use {@link isNonnegative} (SymPy is_nonnegative converted mechanically); removed in 1.0.
 * @param e - The input expression.
 * @returns The truth value, or `'unknown'` if the assumptions do not determine it.
 * @see SymPy `sympy.core.expr.Expr.is_nonnegative`
 */
export const isNonNegative = _isNonnegative_;

/**
 * Alias for {@link isNonpositive}.
 *
 * @deprecated Use {@link isNonpositive} (SymPy is_nonpositive converted mechanically); removed in 1.0.
 * @param e - The input expression.
 * @returns The truth value, or `'unknown'` if the assumptions do not determine it.
 * @see SymPy `sympy.core.expr.Expr.is_nonpositive`
 */
export const isNonPositive = _isNonpositive_;

/**
 * Alias for {@link isNonzero}.
 *
 * @deprecated Use {@link isNonzero} (SymPy is_nonzero converted mechanically); removed in 1.0.
 * @param e - The input expression.
 * @returns The truth value, or `'unknown'` if the assumptions do not determine it.
 * @see SymPy `sympy.core.expr.Expr.is_nonzero`
 */
export const isNonZero = _isNonzero_;

// SymPy names that are JavaScript globals (this module does not use the globals)

/**
 * Alias for {@link Sym}.
 *
 * @deprecated Use {@link Sym} (`Symbol` shadows the JavaScript global); removed in 1.0.
 * @param name - The symbolic name or names.
 * @param assumptions - The facts to assume.
 * @returns A symbol with the given name and assumptions.
 * @see SymPy `sympy.core.symbol.Symbol`
 * @example
 * ```ts
 * import { Symbol, isPositive } from '@symjs/symjs';
 *
 * isPositive(Symbol('x', { positive: true })); // => True
 * ```
 */
export const Symbol = Sym;

/** @deprecated Use `Sym` (`Symbol` shadows the JavaScript global); removed in 1.0. */
export type Symbol = SymbolNode;

/**
 * Alias for {@link SymNumber}.
 *
 * @deprecated Use {@link SymNumber} (`Number` shadows the JavaScript global); removed in 1.0.
 * @param x - The argument of the function.
 * @returns The numeric expression.
 * @see SymPy `sympy.core.numbers.Number`
 */
export const Number = _SymNumber_;

/**
 * Alias for {@link SymFunction}.
 *
 * @deprecated Use {@link SymFunction} (`Function` shadows the JavaScript global); removed in 1.0.
 * @param name - The symbolic name or names.
 * @param options - Use `nargs` to restrict the allowed argument counts and assumption flags to describe function values.
 * @returns The callable undefined function.
 * @see SymPy `sympy.core.function.Function`
 * @example
 * ```ts
 * import { Function, ex } from '@symjs/symjs';
 *
 * Function('f')(ex`x`); // => f(x)
 * ```
 */
export const Function = _SymFunction_;

export { complexAccuracy, evalfRaw, getIntegerPart } from './numeric/evalf';
export type { EvalfResult } from './numeric/evalf';
export { LatticeOp } from './core/operations';
export type { LatticeOperation } from './core/operations';

// adjoint and transpose in parsed strings (FnName heads without a parser entry)
import { parserHooks as _parserHooks_ } from './parsing/parser';
import { adjoint as _adjoint_, transpose as _transpose_ } from './functions/elementary/elementary';
import { at as _atCore_ } from './core/guard';
_parserHooks_.constructors.set('adjoint', (args) => _adjoint_(_atCore_(args, 0)));
_parserHooks_.constructors.set('transpose', (args) => _transpose_(_atCore_(args, 0)));

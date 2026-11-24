// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The special math functions of the C99 standard library as symbolic
 * functions (SymPy codegen/cfunctions.py): expm1, log1p, exp2, log2, fma,
 * log10, Sqrt, Cbrt, hypot and the predicates isnan and isinf. Each is a
 * callable class like SymPy's function classes: `expm1(x)` builds (or
 * evaluates) the application, `e instanceof expm1` tests for it, and the
 * class carries SymPy's class members (`expm1.eval`, `expm1.nargs`, ...).
 * The applications differentiate, expand (expand_func), rewrite, evaluate
 * numerically to any precision and compile with lambdify.
 *
 * Ported from SymPy 1.14 (BSD 3-Clause, see LICENSE).
 */

import type { Expr, ExprLike } from '../core/nodes';
import { Add, ExtensionExpr, Float, Fn, Pow, Rational, Rel, S, UndefFn, impl, registerHead } from '../core/nodes';
import { NotLoadedError } from '../core/errors';
import { basicCompare } from '../core/compare';
import type { SetExpr } from '../sets/sets';
import type { ComplexValue as C, Substitution, Sym } from '../core/nodes';
import { BooleanKind } from '../core/kind';
import type { Kind } from '../core/kind';
import { add, couldExtractMinusSign as coreCouldExtractMinusSign, div, exp, mul, pow, sqrt, sub, sympify } from '../core/ops';
import { at, getOrThrow } from '../core/guard';
import { callableClass } from '../core/callable';
import { ask, Q, refine as refineExpr, registerHandler } from '../core/refine';
import type { Assumption, PredicateName } from '../core/refine';
import type { NoMatchResult, Truth } from '../core/truth';
import { NoMatch } from '../core/truth';
import { freeSymbols, subs, xreplace as xreplaceExpr } from '../core/traverse';
import * as methods from '../core/methods';
import { count as countExpr, countOps as countOpsExpr, find as findExpr, replace as replaceExpr } from '../core/match';
import type { Query } from '../core/match';
import { match as matchExpr } from '../core/public';
import { classKey as classKeyOf, sortKey as sortKeyOf } from '../printing/sortkey';
import type { Key } from '../printing/sortkey';
import { dpsToPrec, precToDps, toRational } from '../numeric/mpf';
import { evalAdaptive, fromMpc } from '../numeric/mpeval';
import { numericExtensions } from '../numeric/evalf';
import { c, cadd, cdiv, cexp, clog, cmul, cpow } from '../numeric/complex';
import { log } from '../functions/elementary/elementary';
import { expandFuncRules, floor } from '../functions/special/special';
import { Mod } from '../functions/mod';
import { finiteSet } from '../sets/sets';
import { asBoolean, binarySymbols as binarySymbolsOf, Implies } from '../logic/boolalg';
import { toAnf as toAnfExpr, toNnf as toNnfExpr } from '../logic/normalforms';

/** The rules of one function class (SymPy's class body). */
interface Rules {
  /** Accepted argument counts (SymPy nargs). */
  readonly nargs: number;
  /** SymPy eval: the value of the application, or undefined to keep it. */
  readonly eval?: (args: readonly Expr[]) => Expr | undefined;
  /** SymPy fdiff(index + 1): the partial derivative in the argument at `index`. */
  readonly fdiff?: (self: Expr, args: readonly Expr[], index: number) => Expr;
  /** SymPy _eval_expand_func. */
  readonly expandFunc?: (args: readonly Expr[]) => Expr;
  /** SymPy _eval_rewrite_as_<target>. */
  readonly rewrite?: Readonly<Record<string, (args: readonly Expr[]) => Expr>>;
  /** SymPy _eval_is_<predicate>, decided in the assumptions context. */
  readonly assumptions?: Readonly<Record<string, (args: readonly Expr[], assumptions: Assumption) => Truth>>;
  /**
   * The exact expression whose value is the numeric value of the application
   * (the arguments being numbers given exactly), or undefined when the
   * application has no numeric value (SymPy _eval_evalf and mpmath).
   */
  readonly numeric?: (args: readonly Expr[]) => Expr | undefined;
  /** The value for complex arguments, used by lambdify. */
  readonly lambdify?: (args: readonly C[]) => C;
  /** SymPy _eval_evalf of log2: a non-numeric application evaluates its rewrite in terms of log. */
  readonly evalfRewrite?: (args: readonly Expr[]) => Expr;
  /** A boolean-valued function (SymPy BooleanFunction). */
  readonly boolean?: true;
}

/** A function class: its rules, its node class and the callable class (SymPy's class object). */
interface Registered {
  readonly rules: Rules;
  readonly Node: new (name: string, args: readonly Expr[]) => CFunctionBase;
  cls?: unknown;
}

const REGISTRY = new Map<string, Registered>();
const registered = (name: string): Registered => getOrThrow(REGISTRY, name);

/**
 * SymPy Function._should_evalf: the binary precision of a Float argument (or
 * of a complex number with Float parts), else -1.
 */
function floatPrecision(a: Expr): number {
  if (a instanceof Float) return a.prec;
  if (!(a instanceof Add) || a.args.length !== 2) return -1;
  const [re, im] = [at(a.args, 0), at(a.args, 1)];
  const imPart = im.args.length === 2 && at(im.args, 1) === S.I ? at(im.args, 0) : undefined;
  return re instanceof Float && imPart instanceof Float ? Math.max(re.prec, imPart.prec) : -1;
}

/** The exact rational value of a Float (others unchanged), so that a rewrite evaluates without rounding. */
const exact = (a: Expr): Expr => {
  if (!(a instanceof Float)) return a;
  const [p, q] = toRational(a.mpf);
  return Rational.of(p, q);
};

/** The error for a late-bound implementation of an entry point that is not loaded. */
function notLoaded(name: string, entry: string): never {
  throw new NotLoadedError(`${name} is not available: import '@symjs/symjs/${entry}' (or '@symjs/symjs')`);
}

/** An application of one of the functions of this module (SymPy's Function and BooleanFunction instances). */
abstract class CFunctionBase extends ExtensionExpr {
  /** @internal */
  protected get rules(): Rules {
    return registered(this.name).rules;
  }
  withArgs(args: readonly Expr[]): Expr {
    return apply(this.name, args);
  }
  override kindSelf(): Kind | undefined {
    return this.rules.boolean ? BooleanKind : undefined;
  }
  override isRealSelf(): boolean | undefined {
    const r = this.rules.assumptions?.['real']?.(this.args, true);
    return r === undefined || r === 'unknown' ? undefined : r;
  }
  override diffSelf(x: Expr, d: (e: Expr, x: Expr) => Expr): Expr | undefined {
    const fdiff = this.rules.fdiff;
    if (fdiff === undefined) return undefined;
    return add(...this.args.map((a, i) => (a.has(x) ? mul(fdiff(this, this.args, i), d(a, x)) : 0)));
  }
  override rewriteSelf(target: string, args: readonly Expr[]): Expr | undefined {
    return this.rules.rewrite?.[target]?.(args);
  }
  override numericValue(dps: number): Expr | undefined {
    if (this.args.some((a) => !a.isNumber)) return undefined;
    const value = this.rules.numeric?.(this.args.map(exact));
    if (value === undefined) return undefined;
    const prec = dpsToPrec(dps);
    return fromMpc(evalAdaptive(value, prec), prec);
  }
  override evalfSelf(evalfArg: (e: Expr) => Expr): Expr | undefined {
    // a number is evaluated by numericValue; SymPy keeps any other application (Sqrt(2).evalf() == Sqrt(2))
    if (this.args.every((a) => a.isNumber) && this.rules.numeric?.(this.args.map(exact)) !== undefined) return undefined;
    const rewritten = this.rules.evalfRewrite?.(this.args);
    return rewritten === undefined ? this : evalfArg(rewritten);
  }
  override printLatex(print: (e: Expr) => string): string {
    // SymPy prints an applied function: \operatorname{log}_{2}{\left(x \right)}
    return this.rules.boolean ? super.printLatex(print) : print(new UndefFn(this.name, this.args));
  }

  /** SymPy fdiff(argindex): the derivative in the argument at position argindex (from 1). */
  fdiff(argindex = 1): Expr {
    const fdiff = this.rules.fdiff;
    if (fdiff === undefined || !Number.isInteger(argindex) || argindex < 1 || argindex > this.args.length) {
      throw new RangeError(`Invalid operation with argument number ${argindex} for Function ${this.toString()}`);
    }
    return fdiff(this, this.args, argindex - 1);
  }

  // SymPy Basic attributes
  /** SymPy assumptions0: the assumptions given to the expression; none for a function application. */
  get assumptions0(): Map<string, boolean> {
    return new Map();
  }
  /** SymPy canonical_variables: the bound variables and their canonical dummies; none for a function application. */
  get canonicalVariables(): Map<Expr, Expr> {
    return new Map();
  }
  /** SymPy default_assumptions: the assumptions of the class; none for these functions. */
  get defaultAssumptions(): Map<string, boolean> {
    return new Map();
  }
  /** SymPy expr_free_symbols: the free symbols of the expression. */
  get exprFreeSymbols(): Set<Expr> {
    return freeSymbols(this);
  }
  /** SymPy floordiv (Python //): floor(self/other). */
  floordiv(other: ExprLike): Expr {
    return floor(div(this, other));
  }
  /** SymPy mod (Python %): Mod(self, other). */
  mod(other: ExprLike): Expr {
    return Mod(this, other);
  }

  // SymPy class flags: a function application is none of these
  get isAdd(): boolean { return false; }
  get isAlgebraicNumber(): boolean { return false; }
  /** SymPy is_Boolean: true for isnan and isinf. */
  get isBoolean(): boolean { return this.rules.boolean === true; }
  get isDerivative(): boolean { return false; }
  get isDummy(): boolean { return false; }
  get isEquality(): boolean { return false; }
  get isFloat(): boolean { return false; }
  get isIndexed(): boolean { return false; }
  get isMatAdd(): boolean { return false; }
  get isMatMul(): boolean { return false; }
  get isMatrix(): boolean { return false; }
  get isMul(): boolean { return false; }
  get isNot(): boolean { return false; }
  get isNumberSymbol(): boolean { return false; }
  get isOrder(): boolean { return false; }
  get isPiecewise(): boolean { return false; }
  get isPoint(): boolean { return false; }
  get isPoly(): boolean { return false; }
  get isPow(): boolean { return false; }
  get isRelational(): boolean { return false; }
  /** SymPy is_Symbol and is_symbol. */
  get isSymbol(): boolean { return false; }
  get isVector(): boolean { return false; }
  get isWild(): boolean { return false; }

  // SymPy assumption attributes (is_real, is_positive, ...): true, false or 'unknown'
  private query(name: PredicateName): Truth {
    return ask(Q[name](this));
  }
  get isAlgebraic(): Truth { return this.query('algebraic'); }
  get isAntihermitian(): Truth { return this.query('antihermitian'); }
  get isComplex(): Truth { return this.query('complex'); }
  get isComposite(): Truth { return this.query('composite'); }
  get isEven(): Truth { return this.query('even'); }
  get isExtendedNegative(): Truth { return this.query('extended_negative'); }
  get isExtendedNonnegative(): Truth { return this.query('extended_nonnegative'); }
  get isExtendedNonpositive(): Truth { return this.query('extended_nonpositive'); }
  get isExtendedNonzero(): Truth { return this.query('extended_nonzero'); }
  get isExtendedPositive(): Truth { return this.query('extended_positive'); }
  get isExtendedReal(): Truth { return this.query('extended_real'); }
  get isFinite(): Truth { return this.query('finite'); }
  get isHermitian(): Truth { return this.query('hermitian'); }
  get isImaginary(): Truth { return this.query('imaginary'); }
  get isInfinite(): Truth { return this.query('infinite'); }
  /** SymPy is_integer (is_Integer, the class flag, is false for a function application). */
  get isInteger(): Truth { return this.query('integer'); }
  get isIrrational(): Truth { return this.query('irrational'); }
  get isNegative(): Truth { return this.query('negative'); }
  get isNoninteger(): Truth { return this.query('noninteger'); }
  get isNonnegative(): Truth { return this.query('nonnegative'); }
  /** Alias of isNonnegative (the spelling of the core function isNonNegative). */
  get isNonNegative(): Truth { return this.isNonnegative; }
  get isNonpositive(): Truth { return this.query('nonpositive'); }
  get isNonzero(): Truth { return this.query('nonzero'); }
  /** Alias of isNonzero (the spelling of the core function isNonZero). */
  get isNonZero(): Truth { return this.isNonzero; }
  get isOdd(): Truth { return this.query('odd'); }
  /** SymPy is_polar: not known for these functions. */
  get isPolar(): Truth { return 'unknown'; }
  get isPositive(): Truth { return this.query('positive'); }
  get isPrime(): Truth { return this.query('prime'); }
  /** SymPy is_rational (is_Rational, the class flag, is false for a function application). */
  get isRational(): Truth { return this.query('rational'); }
  get isReal(): Truth { return this.query('real'); }
  get isTranscendental(): Truth { return this.query('transcendental'); }
  get isZero(): Truth { return this.query('zero'); }

  // SymPy Basic methods, as thin aliases of the public functions
  asContentPrimitive(opts: { clear?: boolean; radical?: boolean } = {}): [Rational, Expr] {
    return methods.asContentPrimitive(this, opts);
  }
  asDummy(): Expr {
    return methods.asDummy(this);
  }
  atoms(pred?: (a: Expr) => boolean): Expr[] {
    return methods.atoms(this, pred);
  }
  classKey(): Key {
    return classKeyOf(this);
  }
  compare(other: Expr): number {
    return basicCompare(this, other);
  }
  copy(): Expr {
    return methods.copy(this);
  }
  couldExtractMinusSign(): boolean {
    return coreCouldExtractMinusSign(this);
  }
  count(query: Query): number {
    return countExpr(this, query);
  }
  countOps(): number {
    return countOpsExpr(this);
  }
  doit(): Expr {
    return impl.doit ? impl.doit(this) : notLoaded('doit', 'calculus');
  }
  dummyEq(other: ExprLike, symbol?: Expr): boolean {
    return methods.dummyEq(this, other, symbol);
  }
  find(query: Query): Expr[] {
    return findExpr(this, query);
  }
  hasFree(...patterns: ExprLike[]): boolean {
    return methods.hasFree(this, ...patterns);
  }
  hasXfree(items: readonly Expr[]): boolean {
    return methods.hasXfree(this, items);
  }
  isHypergeometric(k: Expr): boolean {
    return impl.isHypergeometric ? impl.isHypergeometric(this, k) : notLoaded('isHypergeometric', 'simplify');
  }
  isSame(other: unknown): boolean {
    return methods.isSame(this, other);
  }
  match(pattern: ExprLike): Map<Sym, Expr> | NoMatchResult {
    return matchExpr(this, pattern);
  }
  matches(expr: ExprLike): Map<Sym, Expr> | NoMatchResult {
    return matchExpr(expr, this);
  }
  rcall(...args: ExprLike[]): Expr {
    return methods.rcall(this, ...args);
  }
  refine(assumptions: Assumption = true): Expr {
    return refineExpr(this, assumptions);
  }
  replace(...args: Parameters<typeof replaceExpr> extends [unknown, ...infer R] ? R : never): ReturnType<typeof replaceExpr> {
    return replaceExpr(this, ...args);
  }
  sortKey(): Key {
    return sortKeyOf(this);
  }
  xreplace(rule: Substitution): Expr {
    return xreplaceExpr(this, rule);
  }
}

/**
 * An application of expm1, log1p, exp2, log2, fma, log10, Sqrt, Cbrt or
 * hypot (SymPy Function).
 *
 * @experimental May change in a minor release.
 */
export abstract class CFunction extends CFunctionBase {
  /**
   * Indicates whether the function admits Taylor expansion in its argument.
   *
   * @returns Whether a Taylor expansion in the argument is supported.
   */
  override get isTaylorExpandable(): boolean {
    return true;
  }
}

/**
 * An application of isnan or isinf (SymPy BooleanFunction).
 *
 * @experimental May change in a minor release.
 */
export abstract class CBooleanFunction extends CFunctionBase {
  /**
   * Finds the values of the free symbol that satisfy the predicate.
   *
   * @returns The set of real solutions.
   */
  asSet(): Expr {
    return impl.asSet ? impl.asSet(this) : notLoaded('asSet', 'solvers');
  }
  /**
   * Lists the Boolean symbols in a call whose arguments are numeric.
   *
   * @returns An empty symbol map.
   */
  get binarySymbols(): Map<string, Expr> {
    return binarySymbolsOf(this);
  }
  /**
   * Converts the predicate to negation normal form.
   *
   * @param simplify - Whether to simplify the result.
   * @returns The predicate in negation normal form.
   */
  toNnf(simplify = true): Expr {
    return toNnfExpr(this, simplify);
  }
  /**
   * Converts the predicate to algebraic normal form.
   *
   * @param deep - The deep.
   * @returns The predicate in algebraic normal form.
   */
  toAnf(deep = true): Expr {
    return toAnfExpr(this, deep);
  }
  /**
   * Forms the implication from this predicate to the other proposition.
   *
   * @param other - The other operand.
   * @returns The corresponding implication.
   */
  rshift(other: ExprLike): Expr {
    return Implies(this, other);
  }
  /**
   * Forms the implication from the other proposition to this predicate.
   *
   * @param other - The other operand.
   * @returns The corresponding implication.
   */
  lshift(other: ExprLike): Expr {
    return Implies(other, this);
  }
}

/** The members of a function class (SymPy's class attributes and classmethods). */
interface ClassMembers {
  /** SymPy eval: the value of the application of the class to args, or NoMatch when it stays unevaluated. */
  eval(...args: ExprLike[]): Expr | NoMatchResult;
  /** SymPy nargs: the set of accepted argument counts. */
  readonly nargs: SetExpr;
  /** SymPy is_singular(a): whether a is a singularity; not known for these functions. */
  isSingular(a: ExprLike): Truth;
  /** SymPy default_assumptions of the class. */
  readonly defaultAssumptions: Map<string, boolean>;
  /** The function name (SymPy __name__). */
  readonly functionName: string;
}

/**
 * A function class of this module: call it to apply it, test applications
 * with instanceof.
 *
 * @experimental May change in a minor release.
 */
export type CFunctionClass = (abstract new (...args: never[]) => CFunction) & ((...args: ExprLike[]) => Expr) & ClassMembers;

/**
 * A boolean function class of this module (isnan, isinf).
 *
 * @experimental May change in a minor release.
 */
export type CBooleanFunctionClass = (abstract new (...args: never[]) => CBooleanFunction) &
  ((...args: ExprLike[]) => Expr) &
  ClassMembers & {
    /** SymPy binary_check_and_simplify: the arguments as booleans, an Eq or Ne of a boolean symbol replaced by false. */
    binaryCheckAndSimplify(...args: ExprLike[]): Expr[];
  };

/** Build or evaluate an application (SymPy Function.__new__). */
function apply(name: string, argsIn: readonly ExprLike[]): Expr {
  const { rules, Node } = registered(name);
  if (argsIn.length !== rules.nargs) throw new TypeError(`${name} takes exactly ${rules.nargs} argument${rules.nargs === 1 ? '' : 's'} (${argsIn.length} given)`);
  const args = argsIn.map(sympify);
  const value = rules.eval?.(args);
  if (value !== undefined) return value;
  const node = new Node(name, args);
  // Float arguments evaluate the application at their precision
  const prec = Math.min(...args.map(floatPrecision));
  return prec > 0 ? (node.numericValue(precToDps(prec)) ?? node) : node;
}

function defineClass(name: string, rules: Rules): CFunctionClass & CBooleanFunctionClass {
  const Node = rules.boolean ? class extends CBooleanFunction {} : class extends CFunction {};
  Object.defineProperties(Node, {
    name: { value: name },
    eval: { value: (...args: ExprLike[]): Expr | NoMatchResult => rules.eval?.(args.map(sympify)) ?? NoMatch },
    nargs: { get: (): SetExpr => finiteSet(rules.nargs) },
    isSingular: { value: (_a: ExprLike): Truth => 'unknown' },
    defaultAssumptions: { get: (): Map<string, boolean> => new Map() },
    functionName: { value: name },
    ...(rules.boolean ? { binaryCheckAndSimplify: { value: binaryCheckAndSimplify } } : {}),
  });
  const entry: Registered = { rules, Node };
  REGISTRY.set(name, entry);
  const expand = rules.expandFunc;
  if (expand) expandFuncRules[name] = (e) => expand(e.args);
  if (rules.lambdify) numericExtensions[name] = rules.lambdify;
  for (const [predicate, rule] of Object.entries(rules.assumptions ?? {})) {
    registerHandler(predicate, (e, assumptions) => (e instanceof Node ? rule(e.args, assumptions) : 'unknown'));
  }
  const cls = callableClass(Node, (...args: ExprLike[]): Expr => apply(name, args));
  entry.cls = cls;
  registerHead(Node, cls);
  // oxlint-disable-next-line typescript/no-unsafe-type-assertion -- the class members were added above with Object.defineProperties
  return cls as unknown as CFunctionClass & CBooleanFunctionClass;
}

/** SymPy BooleanFunction.binary_check_and_simplify. */
function binaryCheckAndSimplify(...argsIn: ExprLike[]): Expr[] {
  const args = argsIn.map((a) => asBoolean(a));
  const binary = new Map<string, Expr>();
  for (const a of args) for (const [k, v] of binarySymbolsOf(a)) binary.set(k, v);
  const reps: [Expr, Expr][] = [];
  const relations = (e: Expr): Rel[] => (e instanceof Rel ? [e] : e.args.flatMap(relations));
  for (const a of args) {
    for (const r of relations(a)) {
      if (![...binary.values()].some((x) => freeSymbols(r).has(x))) continue;
      if (r.op !== 'Eq' && r.op !== 'Ne') throw new TypeError(`Incompatible use of binary symbol in ${r.toString()}`);
      if (![r.lhs, r.rhs].some((s) => s === S.true || s === S.false)) reps.push([r, S.false]);
    }
  }
  return args.map((a) => (reps.length ? subs(a, reps) : a));
}

// ---------------------------------------------------------------------------
// The functions
// ---------------------------------------------------------------------------

const TWO = S.Two;
const TEN = Rational.of(10n);

/** a is E**b exactly when exp(b) did not evaluate (SymPy exp.eval returned None). */
const isExpOf = (e: Expr, b: Expr): boolean => e instanceof Pow && e.base.key === S.E.key && e.exp.key === b.key;
/** log(b) did not evaluate (SymPy log.eval returned None). */
const isLogOf = (e: Expr, b: Expr): boolean => e instanceof Fn && e.name === 'log' && at(e.args, 0).key === b.key;

const real = (a: Expr, assumptions: Assumption): Truth => ask(Q.real(a), assumptions);
const finite = (a: Expr, assumptions: Assumption): Truth => ask(Q.finite(a), assumptions);
const exp1 = (a: Expr): Expr => sub(exp(a), 1);
const log1 = (a: Expr): Expr => log(add(a, 1));
const logBase = (base: Expr) => (args: readonly Expr[]): Expr => div(log(at(args, 0)), log(base));
const sqrt1 = (args: readonly Expr[]): Expr => pow(at(args, 0), S.Half);
const cbrt1 = (args: readonly Expr[]): Expr => pow(at(args, 0), Rational.of(1n, 3n));
const hypot1 = (args: readonly Expr[]): Expr => sqrt(add(pow(at(args, 0), 2), pow(at(args, 1), 2)));
const fma1 = (args: readonly Expr[]): Expr => add(mul(at(args, 0), at(args, 1)), at(args, 2));
const exp21 = (args: readonly Expr[]): Expr => pow(TWO, at(args, 0));
const isReal1 = (z: C): boolean => z.im === 0;
/** The (first) argument. */
const a0 = (args: readonly Expr[]): Expr => at(args, 0);
const LN2 = c(Math.LN2);
const LN10 = c(Math.LN10);

/** SymPy log2.eval and log10.eval: a number whose logarithm is an atom, or a power of the base. */
function logBaseEval(base: Expr, a: Expr): Expr | undefined {
  if (a.isNumber) {
    const r = log(a, base);
    return r.args.length === 0 ? r : undefined;
  }
  return a instanceof Pow && a.base.key === base.key ? a.exp : undefined;
}

/**
 * Computes `exp(x) - 1` accurately for arguments near zero.
 *
 * @param args - The single numerical or symbolic argument.
 * @returns The value of `exp(x) - 1`.
 * @see SymPy `sympy.codegen.cfunctions.expm1`
 * @example
 * ```ts
 * import { evalf, expm1, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * expm1(x).diff(x); // => exp(x)
 * evalf(expm1(1e-10)); // => 1.00000000005000e-10
 * ```
 */
export const expm1: CFunctionClass = /* @__PURE__ */ defineClass('expm1', {
  nargs: 1,
  eval: (args) => {
    // (a Float argument is evaluated without cancellation instead)
    if (floatPrecision(a0(args)) > 0) return undefined;
    const e = exp(a0(args));
    return isExpOf(e, a0(args)) ? undefined : sub(e, 1);
  },
  fdiff: (_self, args) => exp(a0(args)),
  expandFunc: (args) => exp1(a0(args)),
  rewrite: { exp: (args) => exp1(a0(args)), tractable: (args) => exp1(a0(args)) },
  assumptions: { real: (args, h) => real(a0(args), h), finite: (args, h) => finite(a0(args), h) },
  numeric: (args) => exp1(a0(args)),
  lambdify: (zs) => {
    const z = at(zs, 0);
    return isReal1(z) ? c(Math.expm1(z.re)) : cadd(cexp(z), c(-1));
  },
});

/**
 * Computes `log(1 + x)` accurately for arguments near zero.
 *
 * @param args - The single numerical or symbolic argument.
 * @returns The value of `log(1 + x)`.
 * @see SymPy `sympy.codegen.cfunctions.log1p`
 * @example
 * ```ts
 * import { log1p, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * log1p(x).diff(x); // => 1/(x + 1)
 * ```
 */
export const log1p: CFunctionClass = /* @__PURE__ */ defineClass('log1p', {
  nargs: 1,
  eval: (args) => {
    if (a0(args) instanceof Rational) return log1(a0(args));
    // adding 1 to a Float is not exact: its exact value is used
    if (a0(args) instanceof Float) return log1(exact(a0(args)));
    const e = log1(a0(args));
    return isLogOf(e, add(a0(args), 1)) ? undefined : e;
  },
  fdiff: (_self, args) => div(1, add(a0(args), 1)),
  expandFunc: (args) => log1(a0(args)),
  rewrite: { log: (args) => log1(a0(args)), tractable: (args) => log1(a0(args)) },
  assumptions: {
    real: (args, h) => ask(Q.nonnegative(add(a0(args), 1)), h),
    finite: (args, h) => (ask(Q.zero(add(a0(args), 1)), h) === true ? false : finite(a0(args), h)),
    positive: (args, h) => ask(Q.positive(a0(args)), h),
    zero: (args, h) => ask(Q.zero(a0(args)), h),
    nonnegative: (args, h) => ask(Q.nonnegative(a0(args)), h),
  },
  numeric: (args) => log1(a0(args)),
  lambdify: (zs) => {
    const z = at(zs, 0);
    return isReal1(z) ? c(Math.log1p(z.re)) : clog(cadd(z, c(1)));
  },
});

/**
 * Raises two to the supplied exponent.
 *
 * @param args - The single numerical or symbolic argument.
 * @returns Two raised to the given exponent.
 * @see SymPy `sympy.codegen.cfunctions.exp2`
 * @example
 * ```ts
 * import { exp2, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * exp2(x).diff(x); // => log(2)*exp2(x)
 * ```
 */
export const exp2: CFunctionClass = /* @__PURE__ */ defineClass('exp2', {
  nargs: 1,
  eval: (args) => (a0(args).isNumber ? pow(TWO, a0(args)) : undefined),
  fdiff: (self) => mul(self, log(TWO)),
  expandFunc: exp21,
  rewrite: { Pow: exp21, tractable: exp21 },
  lambdify: (zs) => {
    const z = at(zs, 0);
    return isReal1(z) ? c(2 ** z.re) : cexp(cmul(z, LN2));
  },
});

/**
 * Computes the logarithm to base two.
 *
 * @param args - The single numerical or symbolic argument.
 * @returns The logarithm in the specified base.
 * @see SymPy `sympy.codegen.cfunctions.log2`
 * @example
 * ```ts
 * import { log2, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * log2(8); // => 3
 * log2(x).diff(x); // => 1/(x*log(2))
 * ```
 */
export const log2: CFunctionClass = /* @__PURE__ */ defineClass('log2', {
  nargs: 1,
  eval: (args) => logBaseEval(TWO, a0(args)),
  fdiff: (_self, args) => div(1, mul(log(TWO), a0(args))),
  expandFunc: logBase(TWO),
  rewrite: { log: logBase(TWO), tractable: logBase(TWO) },
  numeric: logBase(TWO),
  evalfRewrite: logBase(TWO),
  lambdify: (zs) => {
    const z = at(zs, 0);
    return isReal1(z) ? c(Math.log2(z.re)) : cdiv(clog(z), LN2);
  },
});

/**
 * Represents the fused multiply-add operation `x*y + z`.
 *
 * @param args - The two factors followed by the addend.
 * @returns The fused multiply-add expression.
 * @see SymPy `sympy.codegen.cfunctions.fma`
 * @example
 * ```ts
 * import { fma, symbols } from '@symjs/symjs';
 *
 * const [x, y, z] = symbols('x y z');
 * fma(x, y, z).diff(x); // => y
 * ```
 */
export const fma: CFunctionClass = /* @__PURE__ */ defineClass('fma', {
  nargs: 3,
  fdiff: (_self, args, i) => (i === 2 ? S.One : at(args, 1 - i)),
  expandFunc: fma1,
  rewrite: { tractable: fma1 },
  lambdify: (zs) => cadd(cmul(at(zs, 0), at(zs, 1)), at(zs, 2)),
});

/**
 * Computes the logarithm to base ten.
 *
 * @param args - The single numerical or symbolic argument.
 * @returns The logarithm in the specified base.
 * @see SymPy `sympy.codegen.cfunctions.log10`
 * @example
 * ```ts
 * import { log10, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * log10(100); // => 2
 * log10(x).diff(x); // => 1/(x*log(10))
 * ```
 */
export const log10: CFunctionClass = /* @__PURE__ */ defineClass('log10', {
  nargs: 1,
  eval: (args) => logBaseEval(TEN, a0(args)),
  fdiff: (_self, args) => div(1, mul(log(TEN), a0(args))),
  expandFunc: logBase(TEN),
  rewrite: { log: logBase(TEN), tractable: logBase(TEN) },
  numeric: logBase(TEN),
  lambdify: (zs) => {
    const z = at(zs, 0);
    return isReal1(z) ? c(Math.log10(z.re)) : cdiv(clog(z), LN10);
  },
});

/**
 * Represents the principal square root as an unevaluated function, including during numeric evaluation.
 *
 * @param args - The single numerical or symbolic argument.
 * @returns The symbolic root function.
 * @see SymPy `sympy.codegen.cfunctions.Sqrt`
 * @example
 * ```ts
 * import { Sqrt, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * Sqrt(x).diff(x); // => 1/(2*sqrt(x))
 * ```
 */
export const Sqrt: CFunctionClass = /* @__PURE__ */ defineClass('Sqrt', {
  nargs: 1,
  fdiff: (_self, args) => div(pow(a0(args), S.NegHalf), TWO),
  expandFunc: sqrt1,
  rewrite: { Pow: sqrt1, tractable: sqrt1 },
  lambdify: (zs) => cpow(at(zs, 0), c(0.5)),
});

/**
 * Represents the principal cube root as an unevaluated function, including during numeric evaluation.
 *
 * @param args - The single numerical or symbolic argument.
 * @returns The symbolic root function.
 * @see SymPy `sympy.codegen.cfunctions.Cbrt`
 * @example
 * ```ts
 * import { Cbrt, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * Cbrt(x).diff(x); // => 1/(3*x**(2/3))
 * ```
 */
export const Cbrt: CFunctionClass = /* @__PURE__ */ defineClass('Cbrt', {
  nargs: 1,
  fdiff: (_self, args) => div(pow(a0(args), Rational.of(-2n, 3n)), 3),
  expandFunc: cbrt1,
  rewrite: { Pow: cbrt1, tractable: cbrt1 },
  lambdify: (zs) => cpow(at(zs, 0), c(1 / 3)),
});

/**
 * Computes the Euclidean length `sqrt(x**2 + y**2)`.
 *
 * @param args - The two orthogonal components.
 * @returns The Euclidean length of the two components.
 * @see SymPy `sympy.codegen.cfunctions.hypot`
 * @example
 * ```ts
 * import { hypot, symbols } from '@symjs/symjs';
 *
 * const [x, y] = symbols('x y');
 * hypot(x, y).diff(x); // => x/hypot(x, y)
 * ```
 */
export const hypot: CFunctionClass = /* @__PURE__ */ defineClass('hypot', {
  nargs: 2,
  fdiff: (self, args, i) => div(mul(2, at(args, i)), mul(TWO, self)),
  expandFunc: hypot1,
  rewrite: { Pow: hypot1, tractable: hypot1 },
  // (mpmath hypot of real numbers)
  numeric: (args) => (args.every((a) => ask(Q.real(a)) === true) ? hypot1(args) : undefined),
  lambdify: (zs) => {
    const [x, y] = [at(zs, 0), at(zs, 1)];
    return isReal1(x) && isReal1(y) ? c(Math.hypot(x.re, y.re)) : cpow(cadd(cmul(x, x), cmul(y, y)), c(0.5));
  },
});

/**
 * Tests whether the argument is NaN.
 *
 * @param args - The single numerical or symbolic argument.
 * @returns The Boolean result or the unevaluated predicate.
 * @see SymPy `sympy.codegen.cfunctions.isnan`
 * @example
 * ```ts
 * import { isnan, S } from '@symjs/symjs';
 *
 * isnan(S.NaN); // => True
 * ```
 */
export const isnan: CBooleanFunctionClass = /* @__PURE__ */ defineClass('isnan', {
  nargs: 1,
  boolean: true,
  eval: (args) => (a0(args) === S.NaN ? S.true : a0(args).isNumber ? S.false : undefined),
});

/**
 * Tests whether the numeric argument is infinite.
 *
 * @param args - The single numerical or symbolic argument.
 * @returns The Boolean result or the unevaluated predicate.
 * @see SymPy `sympy.codegen.cfunctions.isinf`
 * @example
 * ```ts
 * import { isinf, S } from '@symjs/symjs';
 *
 * isinf(S.Infinity); // => True
 * ```
 */
export const isinf: CBooleanFunctionClass = /* @__PURE__ */ defineClass('isinf', {
  nargs: 1,
  boolean: true,
  eval: (args) => (ask(Q.infinite(a0(args))) === true ? S.true : ask(Q.finite(a0(args))) === true ? S.false : undefined),
});

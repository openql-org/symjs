// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Expression tree node classes.
 *
 * All nodes are immutable. Composite nodes (Add, Mul, Pow, Fn) must be created
 * through the canonicalizing constructors in `ops.ts` / `functions/`, never with
 * `new` directly from user code.
 *
 * Operations used by the fluent API are looked up through the `impl` registry,
 * which is populated by the other modules at load time. This keeps the class
 * definitions free of circular imports.
 */

import { InvariantError, NotImplementedError, NotLoadedError, SympifyError } from './errors';
import type { Kind } from './kind';
import { at } from './guard';
import { classOf } from './callable';
import { gcd, lcm } from './numbers';
import { deduceAllFacts } from './facts';
import { type Mpf, fromNumber as mpfFromNumber, fromRational as mpfFromRational, normalize as mpfNormalize, toNumber as mpfToNumber } from '../numeric/mpf';

/** The discriminant identifying the kind of an expression node. */
export type ExprKind =
  | 'Rational'
  | 'Float'
  | 'Symbol'
  | 'Constant'
  | 'Add'
  | 'Mul'
  | 'Pow'
  | 'Fn'
  | 'Special'
  | 'Bool'
  | 'Rel'
  | 'Piecewise'
  | 'Integral'
  | 'Limit'
  | 'Order'
  | 'Undef'
  | 'Derivative'
  | 'Concrete'
  | 'BoolOp'
  | 'Set'
  | 'Extension';

/** Anything that can be turned into an expression. */
export type ExprLike = Expr | number | bigint;

/** A limit of `integrate`: a variable, a variable followed by `[a, b]`, or the array `[x, a, b]`. */
export type IntegrateLimitArg = Sym | readonly [ExprLike, ExprLike] | readonly [Sym, ExprLike, ExprLike];

/** The options of `integrate`. */
export interface IntegrateOptions {
  /** `'none'` drops the convergence conditions of a definite integral (`'piecewise'`, the default, returns them as a `Piecewise`). */
  conds?: 'piecewise' | 'none';
  /** `false` skips the heuristic Risch algorithm. */
  heurisch?: boolean;
}

/** Complex number value used by numeric evaluation. */
export interface ComplexValue {
  /** The real component. */
  re: number;
  /** The imaginary component. */
  im: number;
}

/** Numeric values for symbols, keyed by symbol name or symbol. */
export type NumericValues =
  | Readonly<Record<string, number | ComplexValue | Expr>>
  | ReadonlyMap<Expr | string, number | ComplexValue | Expr>;

/** Options of evalf (SymPy keyword arguments). */
export interface EvalfOptions {
  /** Values substituted during evaluation (SymPy `subs=`). */
  subs?: NumericValues;
  /** Replace parts smaller than this (or than the precision when true) by zero. */
  chop?: boolean | number;
  /** Raise PrecisionExhausted if the requested accuracy cannot be achieved. */
  strict?: boolean;
  /** Maximum working precision in decimal digits. */
  maxn?: number;
}

/** Substitution specification. */
export type Substitution =
  | ReadonlyMap<Expr, ExprLike>
  | readonly (readonly [Expr, ExprLike])[]
  | Readonly<Record<string, ExprLike>>;

/** Facts attached to a symbol, such as whether it is real, positive, or commutative. */
export interface Assumptions {
  /** Whether the symbol is algebraic. */
  readonly algebraic?: boolean;
  /** Whether the symbol is antihermitian. */
  readonly antihermitian?: boolean;
  /** Whether the symbol is complex. */
  readonly complex?: boolean;
  /** Whether the symbol is composite. */
  readonly composite?: boolean;
  /** Whether the symbol is even. */
  readonly even?: boolean;
  /** Whether the symbol is extended negative. */
  readonly extendedNegative?: boolean;
  /** Whether the symbol is extended nonnegative. */
  readonly extendedNonnegative?: boolean;
  /** Whether the symbol is extended nonpositive. */
  readonly extendedNonpositive?: boolean;
  /** Whether the symbol is extended nonzero. */
  readonly extendedNonzero?: boolean;
  /** Whether the symbol is extended positive. */
  readonly extendedPositive?: boolean;
  /** Whether the symbol is extended real. */
  readonly extendedReal?: boolean;
  /** Whether the symbol is finite. */
  readonly finite?: boolean;
  /** Whether the symbol is hermitian. */
  readonly hermitian?: boolean;
  /** Whether the symbol is imaginary. */
  readonly imaginary?: boolean;
  /** Whether the symbol is infinite. */
  readonly infinite?: boolean;
  /** Whether the symbol is irrational. */
  readonly irrational?: boolean;
  /** Whether the symbol is noninteger. */
  readonly noninteger?: boolean;
  /** Whether the symbol is nonzero. */
  readonly nonzero?: boolean;
  /** Whether the symbol is odd. */
  readonly odd?: boolean;
  /** Whether the symbol is prime. */
  readonly prime?: boolean;
  /** Whether the symbol is rational. */
  readonly rational?: boolean;
  /** Whether the symbol is transcendental. */
  readonly transcendental?: boolean;
  /** Fermionic index restrictions (SymPy above_fermi / below_fermi). */
  readonly aboveFermi?: boolean;
  /** Whether the symbol is below fermi. */
  readonly belowFermi?: boolean;
  /** Whether the symbol is real. */
  readonly real?: boolean;
  /** Whether the symbol is positive. */
  readonly positive?: boolean;
  /** Whether the symbol is nonnegative. */
  readonly nonnegative?: boolean;
  /** Whether the symbol represents an integer. */
  readonly integer?: boolean;
  /** Whether the symbol is negative. */
  readonly negative?: boolean;
  /** Whether the symbol is nonpositive. */
  readonly nonpositive?: boolean;
  /** Whether multiplication by the symbol is commutative. Set to `false` for a noncommutative operator. */
  readonly commutative?: boolean;
  /** Whether the symbol represents a point on the Riemann surface of the logarithm. */
  readonly polar?: boolean;
  /**
   * Whether the symbol is zero. Zero implies an integer that is both nonnegative and nonpositive. A
   * positive, negative or noninteger symbol is nonzero.
   */
  readonly zero?: boolean;
}

/** Function names known to the library. */
export type FnName =
  | '_eis'
  | '_erfs'
  | 'adjoint'
  | 'transpose'
  | 'sin'
  | 'cos'
  | 'tan'
  | 'asin'
  | 'acos'
  | 'atan'
  | 'sinh'
  | 'cosh'
  | 'tanh'
  | 'log'
  | 'abs'
  | 're'
  | 'im'
  | 'arg'
  | 'conjugate'
  | 'cot'
  | 'sec'
  | 'csc'
  | 'acot'
  | 'asec'
  | 'acsc'
  | 'coth'
  | 'sech'
  | 'csch'
  | 'asinh'
  | 'acosh'
  | 'atanh'
  | 'acoth'
  | 'asech'
  | 'acsch'
  | 'sinc'
  | 'exp_polar'
  | 'polar_lift'
  | 'periodic_argument'
  | 'principal_branch'
  | SpecialFnName;

/** Special and combinatorial functions (see functions/special/special.ts). */
export type SpecialFnName =
  | 'factorial'
  | 'factorial2'
  | 'binomial'
  | 'ff'
  | 'rf'
  | 'subfactorial'
  | 'harmonic'
  | 'catalan'
  | 'gamma'
  | 'digamma'
  | 'trigamma'
  | 'loggamma'
  | 'polygamma'
  | 'lowergamma'
  | 'uppergamma'
  | 'beta'
  | 'zeta'
  | 'erf'
  | 'erfc'
  | 'erfi'
  | 'erf2'
  | 'erfinv'
  | 'erfcinv'
  | 'erf2inv'
  | 'Ei'
  | 'LambertW'
  | 'besselj'
  | 'bessely'
  | 'besseli'
  | 'besselk'
  | 'airyai'
  | 'airybi'
  | 'airyaiprime'
  | 'airybiprime'
  | 'li'
  | 'Li'
  | 'Si'
  | 'Ci'
  | 'Shi'
  | 'Chi'
  | 'expint'
  | 'fresnels'
  | 'fresnelc'
  | 'sign'
  | 'floor'
  | 'ceiling'
  | 'atan2'
  | 'Min'
  | 'Max'
  | 'bernoulli'
  | 'euler'
  | 'genocchi'
  | 'andre'
  | 'bell'
  | 'fibonacci'
  | 'lucas'
  | 'tribonacci'
  | 'partition'
  | 'totient'
  | 'reduced_totient'
  | 'mobius'
  | 'divisor_sigma'
  | 'udivisor_sigma'
  | 'legendre_symbol'
  | 'jacobi_symbol'
  | 'kronecker_symbol'
  | 'primenu'
  | 'primeomega'
  | 'primepi'
  | 'multigamma'
  | 'frac'
  | 'Rem'
  | 'jn'
  | 'yn'
  | 'hankel1'
  | 'hankel2'
  | 'hn1'
  | 'hn2'
  | 'marcumq'
  | 'Ynm'
  | 'Znm'
  | 'mathieus'
  | 'mathieuc'
  | 'mathieusprime'
  | 'mathieucprime'
  | 'KroneckerDelta'
  // zeta functions (functions/special/zetafunctions.ts), incomplete beta (functions/special/special.ts), elliptic integrals (functions/special/ellipticintegrals.ts), Appell F1 (functions/special/hyper.ts)
  | 'polylog'
  | 'lerchphi'
  | 'dirichlet_eta'
  | 'riemann_xi'
  | 'stieltjes'
  | 'betainc'
  | 'betainc_regularized'
  | 'elliptic_k'
  | 'elliptic_e'
  | 'elliptic_f'
  | 'elliptic_pi'
  | 'appellf1'
  // orthogonal polynomials (functions/special/polynomials.ts)
  | 'jacobi'
  | 'gegenbauer'
  | 'chebyshevt'
  | 'chebyshevu'
  | 'legendre'
  | 'assoc_legendre'
  | 'hermite'
  | 'hermite_prob'
  | 'laguerre'
  | 'assoc_laguerre';

/**
 * Late-bound implementations. Filled in by the modules that implement them.
 * @internal
 */
export interface Impl {
  sympify(x: ExprLike): Expr;
  add(...xs: ExprLike[]): Expr;
  mul(...xs: ExprLike[]): Expr;
  pow(b: ExprLike, e: ExprLike): Expr;
  str(e: Expr): string;
  latex(e: Expr): string;
  subs(e: Expr, s: Substitution): Expr;
  xreplace(e: Expr, s: Substitution): Expr;
  diff(e: Expr, x: Expr, n: ExprLike): Expr;
  coeff(e: Expr, x: ExprLike, n: number, right: boolean): Expr;
  expand(e: Expr): Expr;
  simplify(e: Expr): Expr;
  evalf(e: Expr, n?: number | NumericValues, opts?: EvalfOptions): Expr;
  isComparable(e: Expr): boolean;
  toComplex(e: Expr, values?: NumericValues): ComplexValue;
  rewrite?(this: void, e: Expr, target: string, opts?: { pattern?: readonly string[]; deep?: boolean; hints?: Readonly<Record<string, Expr>> }): Expr;
  ordered?(xs: readonly Expr[]): Expr[];
  expandFunc?(e: Expr): Expr;
  expandComplex?(e: Expr): Expr;
  polyReduce?(f: Expr, g: Expr, gens: readonly Expr[]): [Expr, Expr];
  gcdTermsOf?(terms: readonly Expr[]): Expr;
  cos?(e: Expr): Expr;
  sin?(e: Expr): Expr;
  sign?(e: Expr): Expr;
  isReal?(e: Expr): boolean | undefined;
  rationalFromFloat?(f: Float): Rational;
  couldExtractMinusSign?(e: Expr): boolean;
  /**
   * Compares the canonical sort keys of two expressions, returning a negative value when `a` sorts
   * before `b`.
   */
  compareSortKey?(a: Expr, b: Expr): number;
  /**
   * Collects terms with matching powers of the specified expressions.
   *
   * @see SymPy `sympy.simplify.radsimp.collect`
   */
  collect?(e: Expr, syms: readonly Expr[]): Expr;
  /** Leading term [c, e] of e ~ c*x**e as x -> 0+ (registered by series/series). */
  leadterm?(e: Expr, x: Sym): [Expr, Expr];
  /** Asymptotic containment, registered by series/series. */
  orderContains?: (order: Order, expr: Expr) => boolean | 'unknown';
  subsFunction?(expr: Expr, name: string, replacement: (...args: Expr[]) => Expr, arities?: readonly number[]): Expr;
  rebuildOrder?: (args: readonly Expr[]) => Expr;
  /** The value of a sum or product with finite integer limits, for evalf (registered by calculus/doit); undefined when it is not a number. */
  evalConcrete?(c: Expr): Expr | undefined;
  /** Lambert W function (registered by functions/special). */
  lambertW?(x: Expr, k?: number): Expr;
  /** Pattern matching (registered by core/match). */
  match?(e: Expr, pattern: Expr): Map<Sym, Expr> | undefined;
  /**
   * Checks whether a number equals zero by simplifying it or testing whether its minimal polynomial
   * is `x`.
   *
   * @see SymPy `sympy.core.expr.Expr.equals`
   */
  equalsZero?(e: Expr): true | undefined;
  /**
   * Simplifies radicals in a denominator by rationalizing it when possible.
   *
   * @see SymPy `sympy.simplify.radsimp.radsimp`
   */
  radsimp?(e: Expr): Expr;
  /** A node of the same type with new arguments, re-canonicalized (registered by core/traverse). */
  rebuild: (e: Expr, args: readonly Expr[]) => Expr;
  /** A named function applied with automatic evaluation (registered by functions/elementary). */
  fn?(this: void, name: FnName, args: readonly Expr[]): Expr;
  /**
   * Expands products over sums using only the multiplication expansion rule.
   *
   * @see SymPy `sympy.core.function.expand_mul`
   */
  expandMul?(e: Expr): Expr;
  /**
   * Computes the real and imaginary parts of exponentials and other functions by expanding them.
   *
   * @see SymPy `sympy.core.expr.Expr.as_real_imag`
   */
  asRealImagExpand?(e: Expr): [Expr, Expr];
  /**
   * Computes the real and imaginary parts of a rational power when possible. Other cases fall back
   * to `re` and `im`.
   *
   * @see SymPy `sympy.core.power.Pow.as_real_imag`
   */
  powRealImag?(e: Expr): [Expr, Expr] | undefined;
  /**
   * Arithmetic of nodes that define their own operators (SymPy _op_priority,
   * as Quaternion does; installed by registerArithmetic): add, mul or pow
   * of the sympified arguments, or sub of the two operands of a - b, or
   * undefined for the generic rules.
   */
  arithmetic?(op: 'add' | 'sub' | 'mul' | 'pow', args: readonly Expr[]): Expr | undefined;
  /**
   * A comparison op(lhs, rhs) decided by the function on the left (SymPy's
   * comparison operators of floor, ceiling and frac), or undefined.
   */
  relational?(op: RelOp, lhs: Expr, rhs: Expr): Expr | undefined;
  /** AccumBounds interval arithmetic (registered by core/accumbounds). */
  accumBounds?: {
    is(e: Expr): boolean;
    add(abs: readonly Expr[], c: Expr): Expr;
    mul(abs: readonly Expr[], c: Expr): Expr;
    pow(a: Expr, e: Expr): Expr;
    bounds(a: Expr): [Expr, Expr];
    make(lo: Expr, hi: Expr): Expr;
  };
  /** Sets (registered by sets/sets). */
  emptySet?(): Expr;
  interval?(a: Expr, b: Expr): Expr;
  setIntersection?(a: Expr, b: Expr): Expr;
  /** Heaviside(x), installed by the delta functions module. */
  heaviside?(x: Expr): Expr;
  /** A set node rebuilt from new arguments, evaluated (registered by sets/sets). */
  rebuildSet?: (e: Expr, args: readonly Expr[]) => Expr;
  /**
   * Substitutes into sets such as image sets and condition sets while respecting the scope of their
   * bound variables.
   */
  subsSet?: (e: Expr, old: Expr, nw: Expr, subs: (x: Expr) => Expr) => Expr | undefined;
  piecewiseFold?: (e: Expr) => Expr;
  /**
   * Factors a polynomial expression into irreducible factors over its coefficient domain.
   *
   * @see SymPy `sympy.polys.polytools.factor`
   */
  factor?(e: Expr): Expr;
  /**
   * Separates an expression into its numerator and denominator.
   *
   * @see SymPy `sympy.simplify.radsimp.fraction`
   */
  fraction?(e: Expr, options?: { exact?: boolean }): [Expr, Expr];
  conjugate(e: Expr): Expr;
  abs(e: Expr): Expr;
  freeSymbols(e: Expr): Set<Expr>;
  div(a: ExprLike, b: ExprLike): Expr;
  integrate(e: Expr, ...limits: (IntegrateLimitArg | IntegrateOptions | undefined)[]): Expr;
  /** Evaluate unevaluated objects when the calculus entry point is loaded. */
  doit?(e: Expr): Expr;
  /**
   * Returns the set of real values for which the Boolean expression is true.
   *
   * @see SymPy `sympy.logic.boolalg.Boolean.as_set`
   */
  asSet?(e: Expr): Expr;
  /**
   * Tests whether the ratio of consecutive terms is a rational function of the index `k`.
   *
   * @see SymPy `sympy.core.basic.Basic.is_hypergeometric`
   */
  isHypergeometric?(e: Expr, k: Expr): boolean;
  limit(e: Expr, z: Sym, z0: ExprLike, dir?: '+' | '-' | '+-'): Expr;
  series(e: Expr, x: Sym, x0?: ExprLike, n?: number, dir?: '+' | '-', opts?: { logx?: Expr; local?: boolean }): Expr;
}

/** An implementation provided by a feature area that has not been imported. */
function notLoaded(name: string, entry: string): never {
  throw new NotLoadedError(`${name} is not available: import '@symjs/symjs/${entry}' (or '@symjs/symjs')`);
}

/** The arithmetic of nodes that define their own operators, in the order the modules registered it. */
type ArithmeticHandler = (op: 'add' | 'sub' | 'mul' | 'pow', args: readonly Expr[]) => Expr | undefined;
const arithmeticHandlers: ArithmeticHandler[] = [];

/**
 * Registers the arithmetic of nodes that define their own operators (SymPy
 * _op_priority: quaternions, vectors and dyadics). A handler returns
 * undefined for operands it does not own; the handlers are tried in the
 * order of registration.
 */
export function registerArithmetic(handler: ArithmeticHandler): void {
  arithmeticHandlers.push(handler);
  impl.arithmetic = (op, args) => {
    for (const h of arithmeticHandlers) {
      const r = h(op, args);
      if (r !== undefined) return r;
    }
    return undefined;
  };
}

// oxlint-disable-next-line typescript/no-unsafe-type-assertion -- registry: the remaining entries are installed by the feature modules at import time
export const impl: Impl = {
  simplify: () => notLoaded('simplify', 'simplify'),
  integrate: () => notLoaded('integrate', 'calculus'),
  limit: () => notLoaded('limit', 'calculus'),
  series: () => notLoaded('series', 'calculus'),
} as Partial<Impl> as Impl;

/** The evaluating constructors used by Expr.fromiter, by class (registered by the modules defining them). */
const fromiterBuilders = new Map<unknown, (args: readonly Expr[]) => Expr>();

/** Registers the evaluating constructor of a class for SymPy fromiter (Add, Mul, Pow, MatAdd, ...). */
export function registerFromiter(cls: abstract new (...args: never[]) => Expr, build: (args: readonly Expr[]) => Expr): void {
  fromiterBuilders.set(cls, build);
}

/**
 * The head of an expression (SymPy `func`): a callable that builds the expression from its
 * arguments, `e.func(...e.args)` equals `e`.
 */
export type Head = (...args: ExprLike[]) => Expr;

/** The public constructors of node classes (registered by the modules exporting them). */
const classHeads = new Map<unknown, Head>();
/** The public functions of applied function names (`sin`, `log`, ...). */
const functionHeads = new Map<string, Head>();
/** Heads that depend on the node (a relation's operator, an undefined function's name). */
const headResolvers = new Map<unknown, (e: Expr) => Head>();
/** Heads made for classes without a registered public constructor, one per class. */
const derivedHeads = new Map<unknown, Map<string, Head>>();

/**
 * Registers the public constructor of a node class as the head of its instances. An atom's head is
 * its class (`Sym`), whose call takes a name rather than arguments, as SymPy's Symbol.func does.
 */
export function registerHead(cls: abstract new (...args: never[]) => Expr, head: Head | ((...args: never[]) => Expr)): void {
  // oxlint-disable-next-line typescript/no-unsafe-type-assertion -- an atom has no arguments, so its head is never called with arguments it does not take
  classHeads.set(cls, head as Head);
}

/** Registers a head that depends on the node, for the instances of a class. */
export function registerHeadResolver<T extends Expr>(cls: abstract new (...args: never[]) => T, resolve: (e: T) => Head | ((...args: never[]) => Expr)): void {
  // oxlint-disable-next-line typescript/no-unsafe-type-assertion -- the resolver of a class is only called with the instances of that class (headOf looks it up by the node's class); a head whose parameters differ from the node's arguments (Sum's [k, a, b] limits) is documented where it is registered
  headResolvers.set(cls, resolve as (e: Expr) => Head);
}

/**
 * Registers the public functions of applied function names, `[['sin', sin], ...]`, so that
 * `func(sin(x))` is `sin`.
 */
export function registerFunctionHeads(heads: readonly (readonly [string, Head])[]): void {
  for (const [name, f] of heads) functionHeads.set(name, f);
}

/** A rule on the rewritten arguments and the original expression. */
export type RewriteRule = (args: Expr[], self: Expr, hints?: Readonly<Record<string, Expr>>) => Expr | undefined;

/** The function rewrites, indexed by the function and target names. */
export const rewriteRules: Record<string, Record<string, RewriteRule>> = {};

/** @experimental May change in a minor release. */
export function registerRewrite(fnName: string, target: string, rule: RewriteRule): void {
  (rewriteRules[fnName] ??= {})[target] = rule;
}

/** Function facts queried by the predicate engine through its current assumptions. */
export const functionFactHandlers: Partial<Record<FnName, (
  fact: string,
  args: readonly Expr[],
  query: (fact: string, arg: Expr) => boolean | undefined,
) => boolean | undefined>> = {};

/** The SymPy name of a function head (`sin`, a function of defineFunction or SymFunction), if it has one. */
export function headName(head: (...args: never[]) => unknown): string | undefined {
  const own: unknown = Reflect.get(head, 'functionName');
  if (typeof own === 'string') return own;
  for (const [name, f] of functionHeads) if (f === head) return name;
  return undefined;
}

/** What distinguishes heads within a class: the function name, relation operator, limit direction, ... */
function headDiscriminator(e: Expr): string {
  return ['name', 'op', 'dir', 'kind2'].map((field) => {
    const v: unknown = Reflect.get(e, field);
    return typeof v === 'string' ? v : '';
  }).join('\u0000');
}

function headOf(e: Expr): Head {
  if (e instanceof Fn) {
    const registered = functionHeads.get(e.name);
    if (registered !== undefined) return registered;
  }
  for (let cls: unknown = e.constructor; typeof cls === 'function'; cls = Object.getPrototypeOf(cls)) {
    const resolve = headResolvers.get(cls);
    if (resolve !== undefined) return resolve(e);
    const registered = classHeads.get(cls);
    if (registered !== undefined) return registered;
  }
  // no public constructor registered: rebuild like this node (one head per class and discriminator)
  const byClass = derivedHeads.get(e.constructor) ?? new Map<string, Head>();
  derivedHeads.set(e.constructor, byClass);
  const discriminator = headDiscriminator(e);
  const derived = byClass.get(discriminator);
  if (derived !== undefined) return derived;
  const head: Head = (...args) => impl.rebuild(e, args.map((a) => impl.sympify(a)));
  byClass.set(discriminator, head);
  return head;
}

/** An item of fromiter's argument: an expression, or a number sympified. */
function fromiterItem(v: unknown): Expr {
  if (v instanceof Expr) return v;
  if (typeof v === 'number' || typeof v === 'bigint') return impl.sympify(v);
  throw new TypeError(`fromiter: cannot sympify ${String(v)}`);
}

/**
 * The base class of every expression: numbers, symbols, sums, products,
 * powers, function applications, relations and the other nodes. Expressions
 * are immutable and kept in a canonical form; two expressions are equal when
 * their {@link Expr.key | keys} are equal. The methods give the fluent
 * arithmetic (`x.add(1).pow(2)`) and the common operations of SymPy's `Expr`.
 *
 * @see SymPy `sympy.core.expr.Expr`
 * @example
 * ```ts
 * import { symbols } from '@symjs/symjs';
 *
 * const [x, y] = symbols('x y');
 * const e = x.add(y).pow(2);
 * e; // => (x + y)**2
 * e.expand(); // => x**2 + 2*x*y + y**2
 * e.diff(x); // => 2*x + 2*y
 * e.subs(y, 1); // => (x + 1)**2
 * e.args; // => [x + y, 2]
 * ```
 */
export abstract class Expr {
  /**
   * Constructs a node by passing the iterable's elements to the class constructor. Classes without a
   * registered constructor raise `NotImplementedError`.
   *
   * @param this - The node class on which the method is called.
   * @param args - The arguments in positional order.
   * @returns The class applied to the items of args (`Add.fromiter([x, y])` is x + y).
   * @see SymPy `sympy.core.expr.Expr.fromiter`
   */
  static fromiter(this: abstract new (...args: never[]) => Expr, args: Iterable<unknown>): Expr {
    const build = fromiterBuilders.get(classOf(this));
    if (build === undefined) throw new NotImplementedError(`${this.name}.fromiter is not supported`);
    return build([...args].map(fromiterItem));
  }
  /**
   * Unpacks an expression of this class and treats any other expression as a single operand.
   *
   * @param this - The node class on which the method is called.
   * @param exprIn - The input expression.
   * @returns The operand list.
   */
  static makeArgs(this: abstract new (...args: never[]) => Expr, exprIn: ExprLike): Expr[] {
    const expr = impl.sympify(exprIn);
    return expr instanceof this ? [...expr.args] : [expr];
  }
  /**
   * The node type of the expression (`'Symbol'`, `'Add'`, `'Pow'`, ...).
   * Use `instanceof` with the exported classes to test for a node type.
   */
  abstract readonly kind: ExprKind;
  /**
   * The arguments of the expression; empty for an atom.
   *
   * @see SymPy `sympy.core.basic.Basic.args`
   */
  abstract readonly args: readonly Expr[];
  #key: string | undefined;

  /**
   * Structural key: two expressions are equal iff their keys are equal.
   *
   * @returns The structural comparison key.
   */
  get key(): string {
    return (this.#key ??= this.computeKey());
  }

  protected abstract computeKey(): string;

  /**
   * Structural equality: the same expression in canonical form. It does not
   * test mathematical equality (`(x + 1)**2` and `x**2 + 2*x + 1` differ).
   *
   * @param other - The value to compare with; numbers are sympified.
   * @returns Whether the two expressions are the same.
   * @see SymPy `sympy.core.basic.Basic.__eq__`
   * @example
   * ```ts
   * import { ex, Rational } from '@symjs/symjs';
   *
   * ex`x + 1`.equals(ex`1 + x`); // => True
   * Rational.of(1, 2).equals(0.5); // => False
   * ex`(x + 1)**2`.equals(ex`x**2 + 2*x + 1`); // => False
   * ```
   */
  equals(other: ExprLike): boolean {
    const o = impl.sympify(other);
    return this === o || this.key === o.key;
  }

  /**
   * The head of the expression, the public constructor or function that builds it
   * from its arguments (`func(sin(x)) === sin`, `func(x + y) === Add`, `e.func(...e.args)` equals
   * `e`). An atom (a symbol, a number) has no arguments to rebuild it from, as in SymPy.
   *
   * @returns The callable expression head.
   * @see SymPy `sympy.core.expr.Expr.func`
   */
  get func(): Head {
    return headOf(this);
  }

  /**
   * Tests whether the expression is numeric, with no free symbols or undefined functions.
   *
   * @see SymPy `sympy.core.expr.Expr.is_number`
   * @returns Whether the expression represents a number.
   */
  get isNumber(): boolean {
    if (this instanceof Constant || this instanceof Special) return true;
    if (this instanceof Add || this instanceof Mul || this instanceof Pow || this instanceof Fn) return this.args.every((a) => a.isNumber);
    return false;
  }

  /**
   * Checks whether numerical evaluation produces a real number with nonzero precision.
   *
   * @returns Whether numerical evaluation permits a real-valued comparison.
   * @see SymPy `sympy.core.expr.Expr.is_comparable`
   */
  get isComparable(): boolean {
    return impl.isComparable(this);
  }

  /**
   * Tests whether the expression has no arguments.
   *
   * @see SymPy `sympy.core.basic.Basic.is_Atom`
   * @returns Whether the node has no arguments.
   */
  get isAtom(): boolean {
    return this.args.length === 0;
  }

  private _commutative?: boolean;
  /**
   * Determines whether multiplication by this expression commutes.
   *
   * @returns Whether multiplication by the expression commutes.
   * @see SymPy `sympy.core.expr.Expr.is_commutative`
   */
  get isCommutative(): boolean {
    this._commutative ??= this.computeCommutative();
    return this._commutative;
  }
  protected computeCommutative(): boolean {
    return this.args.every((a) => a.isCommutative);
  }

  // ---- fluent arithmetic -------------------------------------------------
  /**
   * Adds the other operand to this expression.
   *
   * @param o - The other term; numbers are sympified.
   * @returns The sum.
   * @see SymPy `sympy.core.expr.Expr.__add__`
   * @example
   * ```ts
   * import { Sym } from '@symjs/symjs';
   *
   * const x = Sym('x');
   * x.add(1).add(x); // => 2*x + 1
   * ```
   */
  add(o: ExprLike): Expr {
    return impl.add(this, o);
  }
  /**
   * Subtracts the other operand from this expression.
   *
   * @param o - The subtrahend.
   * @returns The difference.
   * @see SymPy `sympy.core.expr.Expr.__sub__`
   */
  sub(o: ExprLike): Expr {
    return impl.arithmetic?.('sub', [this, impl.sympify(o)]) ?? impl.add(this, impl.mul(-1, o));
  }
  /**
   * Multiplies this expression by the other operand.
   *
   * @param o - The other factor.
   * @returns The product.
   * @see SymPy `sympy.core.expr.Expr.__mul__`
   */
  mul(o: ExprLike): Expr {
    return impl.mul(this, o);
  }
  /**
   * Divides this expression by the other operand, using a rational quotient for integers.
   *
   * @param o - The divisor.
   * @returns The quotient.
   * @see SymPy `sympy.core.expr.Expr.__truediv__`
   * @example
   * ```ts
   * import { Rational, Sym } from '@symjs/symjs';
   *
   * Rational.of(1).div(3); // => 1/3
   * Sym('x').div(2); // => x/2
   * ```
   */
  div(o: ExprLike): Expr {
    return impl.div(this, o);
  }
  /**
   * Raises this expression to the supplied power.
   *
   * @param o - The exponent.
   * @returns The power.
   * @see SymPy `sympy.core.expr.Expr.__pow__`
   * @example
   * ```ts
   * import { Rational, Sym } from '@symjs/symjs';
   *
   * Sym('x').pow(2); // => x**2
   * Rational.of(8).pow(Rational.of(1, 3)); // => 2
   * ```
   */
  pow(o: ExprLike): Expr {
    return impl.pow(this, o);
  }
  /**
   * Negates this expression.
   *
   * @returns The negated expression.
   * @see SymPy `sympy.core.expr.Expr.__neg__`
   */
  neg(): Expr {
    return impl.mul(-1, this);
  }

  // ---- manipulation --------------------------------------------------------
  /**
   * Substitutes the pairs of `s`, one after the other, as {@link subs} does.
   *
   * @param s - The pairs `[old, new]`, as a `Map`, an array of pairs, or an
   *   object whose keys are symbol names.
   * @returns The expression after the substitution.
   * @see SymPy `sympy.core.basic.Basic.subs`
   * @example
   * ```ts
   * import { ex, pi, symbols } from '@symjs/symjs';
   *
   * const [x, y] = symbols('x y');
   * ex`1 + x*y`.subs(x, pi); // => pi*y + 1
   * ex`1 + x*y`.subs('x', 2); // => 2*y + 1
   * ex`1 + x*y`.subs({ x: pi, y: 2 }); // => 1 + 2*pi
   * ex`1 + x*y`.subs([[x, y], [y, 2]]); // => 5
   * ```
   */
  subs(s: Substitution): Expr;
  /**
   * Substitutes `to` for `from`.
   *
   * @param from - The expression to replace, or the name of a symbol.
   * @param to - The replacement.
   * @returns The expression after the substitution.
   */
  subs(from: Expr | string, to: ExprLike): Expr;
  subs(a: Substitution | Expr | string, b?: ExprLike): Expr {
    if (a instanceof Expr || typeof a === 'string') {
      if (b === undefined) throw new TypeError('subs(from, to) requires a replacement');
      return impl.subs(this, [[typeof a === 'string' ? new Sym(a) : a, b]]);
    }
    // SymPy subs raises SympifyError for an old value it cannot convert (a JavaScript Symbol('x'))
    if (typeof a !== 'object') throw new SympifyError(`Cannot convert ${String(a)} to an expression`, a);
    return impl.subs(this, a);
  }
  /**
   * Computes the nth derivative with respect to `x`, as in {@link diff}.
   *
   * @param x - The variable.
   * @param n - The order.
   * @returns The derivative.
   * @see SymPy `sympy.core.expr.Expr.diff`
   */
  diff(x: Expr, n: ExprLike = 1): Expr {
    return impl.diff(this, x, n);
  }
  /**
   * Computes the limit as `z` approaches `z0`, as in {@link limit}.
   *
   * @param z - The variable.
   * @param z0 - The point.
   * @param dir - `'+'` (the default), `'-'` or `'+-'`.
   * @returns The limit.
   * @see SymPy `sympy.core.expr.Expr.limit`
   */
  limit(z: Sym, z0: ExprLike, dir: '+' | '-' | '+-' = '+'): Expr {
    return impl.limit(this, z, z0, dir);
  }
  /**
   * Expands the expression about `x0` through the requested order, as in {@link series}.
   *
   * @param x - The variable.
   * @param x0 - The point of the expansion.
   * @param n - The order of the `Order` term.
   * @returns The series.
   * @see SymPy `sympy.core.expr.Expr.series`
   */
  series(x: Sym, x0: ExprLike = 0, n = 6): Expr {
    return impl.series(this, x, x0, n);
  }
  /**
   * Computes an antiderivative or a definite integral over the supplied limits, as in {@link integrate}.
   *
   * @param limits - The variables and their ranges (`x`, `x, [a, b]` or `[x, a, b]`), optionally
   *   followed by the options.
   * @returns The integral.
   * @see SymPy `sympy.core.expr.Expr.integrate`
   */
  integrate(...limits: (IntegrateLimitArg | IntegrateOptions | undefined)[]): Expr {
    return impl.integrate(this, ...limits);
  }
  /**
   * Extracts the coefficient of `x**n` from the terms of the expression without expanding it.
   *
   * @param x - The base of the power, or any expression.
   * @param n - The exponent; `0` gives the terms free of `x`.
   * @param right - For non-commutative factors, the coefficient on the left
   *   of `x` instead of on the right.
   * @returns The coefficient, `0` when there is none.
   * @see SymPy `sympy.core.expr.Expr.coeff`
   * @example
   * ```ts
   * import { ex, symbols } from '@symjs/symjs';
   *
   * const [x] = symbols('x');
   * ex`3*x**2 + a*x + b*x + c`.coeff(x); // => a + b
   * ex`3*x**2 + a*x + c`.coeff(x, 2); // => 3
   * ex`3*x**2 + a*x + c`.coeff(x, 0); // => c
   * ```
   */
  coeff(x: ExprLike, n = 1, right = false): Expr {
    return impl.coeff(this, x, n, right);
  }
  /**
   * Expands with the default hints, as {@link expand}.
   *
   * @returns The expanded expression.
   * @see SymPy `sympy.core.expr.Expr.expand`
   */
  expand(): Expr {
    return impl.expand(this);
  }
  /**
   * Simplifies with the default options, as {@link simplify}.
   *
   * @returns The simplified expression.
   * @see SymPy `sympy.core.basic.Basic.simplify`
   */
  simplify(): Expr {
    return impl.simplify(this);
  }
  /**
   * Computes the complex conjugate of the expression.
   *
   * @returns The conjugate.
   * @see SymPy `sympy.core.expr.Expr.conjugate`
   * @example
   * ```ts
   * import { ex, symbols } from '@symjs/symjs';
   *
   * const [x] = symbols('x', { real: true });
   * ex`2 + 3*I`.conjugate(); // => 2 - 3*I
   * ex`${x} + I*y`.conjugate(); // => x - I*conjugate(y)
   * ```
   */
  conjugate(): Expr {
    return impl.conjugate(this);
  }
  /**
   * Evaluates numerically to `n` significant digits (15 by default) in
   * arbitrary precision; symbols without values stay symbolic. Values as the
   * first argument are shorthand for `evalf(15, { subs: values })`.
   *
   * @param n - The number of significant digits, or the values of symbols.
   * @param opts - `subs` gives the values of symbols; `chop` drops tiny real
   *   or imaginary parts; `maxn` bounds the working precision.
   * @returns The numerical value.
   * @see SymPy `sympy.core.evalf.EvalfMixin.evalf`
   * @example
   * ```ts
   * import { ex, pi, Sym } from '@symjs/symjs';
   *
   * pi.evalf(); // => 3.14159265358979
   * ex`sqrt(2)`.evalf(30); // => 1.41421356237309504880168872421
   * ex`x**2 + 1`.evalf(5, { subs: new Map([[Sym('x'), 2]]) }); // => 5.0000
   * ```
   */
  evalf(n?: number | NumericValues, opts?: EvalfOptions): Expr {
    return impl.evalf(this, n, opts);
  }
  /**
   * Rewrites the expression in terms of another function.
   *
   * @param target - The name of the function to rewrite in terms of.
   * @param opts - `pattern` restricts the rewriting to the named functions;
   *   `deep: false` leaves the arguments alone.
   * @returns The rewritten expression.
   * @see SymPy `sympy.core.basic.Basic.rewrite`
   * @example
   * ```ts
   * import { ex } from '@symjs/symjs';
   *
   * ex`sin(x)`.rewrite('exp'); // => -I*(exp(I*x) - exp(-I*x))/2
   * ex`tan(x)`.rewrite('sin'); // => 2*sin(x)**2/sin(2*x)
   * ```
   */
  rewrite(target: string, opts?: { pattern?: readonly string[]; deep?: boolean; hints?: Readonly<Record<string, Expr>> }): Expr {
    if (!impl.rewrite) notLoaded('rewrite', 'simplify');
    return impl.rewrite(this, target, opts);
  }
  /**
   * Alias of {@link Expr.evalf}.
   *
   * @param n - The number of significant digits, or the values of symbols.
   * @param opts - As for `evalf`.
   * @returns The numerical value.
   * @see SymPy `sympy.core.evalf.EvalfMixin.n`
   */
  n(n?: number | NumericValues, opts?: EvalfOptions): Expr {
    return impl.evalf(this, n, opts);
  }
  /**
   * Evaluates numerically to a complex value in double precision.
   *
   * @param values - The values of the symbols; every free symbol needs one.
   * @returns The value as `{ re, im }`.
   */
  toComplex(values?: NumericValues): ComplexValue {
    return impl.toComplex(this, values);
  }
  /**
   * JavaScript's conversion of the expression to a primitive. A string is the printed form, so that
   * `'x = ' + expr` and template literals print it. A number (`2 * expr`, `Number(expr)`) is the
   * value of a real number; any other expression raises a TypeError, since JavaScript's arithmetic
   * operators do not apply to expressions (`2 * I` would otherwise be NaN).
   */
  [Symbol.toPrimitive](hint: 'number' | 'string' | 'default'): string | number {
    if (hint !== 'number') return this.toString();
    let value: number | undefined;
    if (this.freeSymbols().size === 0) {
      try {
        value = this.toNumber();
      } catch {
        value = undefined;
      }
    }
    if (value === undefined || Number.isNaN(value)) {
      throw new TypeError(`Cannot convert ${this.toString()} to a JavaScript number: JavaScript operators (+, -, *, /, **) do not apply to symjs expressions; use the methods .add(), .sub(), .mul(), .div(), .pow() or parse('...')`);
    }
    return value;
  }
  /**
   * Evaluates numerically to a real number in double precision.
   *
   * @param values - The values of the symbols; every free symbol needs one.
   * @param tol - The relative size of an imaginary part that is ignored.
   * @returns The value.
   * @throws RangeError when the value is not real.
   * @example
   * ```ts
   * import { ex } from '@symjs/symjs';
   *
   * ex`sqrt(2)/2`.toNumber(); // => 0.7071067811865476
   * ```
   */
  toNumber(values?: NumericValues, tol = 1e-12): number {
    const c = impl.toComplex(this, values);
    if (Math.abs(c.im) > tol * Math.max(1, Math.abs(c.re))) {
      throw new RangeError(`toNumber: value is not real (${c.re} + ${c.im}i)`);
    }
    return c.re;
  }
  /**
   * Collects symbols that occur outside the scope of any binding integral, sum, or lambda.
   *
   * @returns The free symbols.
   * @see SymPy `sympy.core.basic.Basic.free_symbols`
   * @example
   * ```ts
   * import { ex } from '@symjs/symjs';
   *
   * ex`x*y + sin(z)`.freeSymbols(); // => {x, y, z}
   * ex`Integral(x*y, (x, 0, 1))`.freeSymbols(); // => {y}
   * ```
   */
  freeSymbols(): Set<Expr> {
    return impl.freeSymbols(this);
  }
  /**
   * Checks for the operand as a subexpression, subsum, or subproduct.
   *
   * @param sub - The expression to look for.
   * @returns Whether it occurs.
   * @see SymPy `sympy.core.basic.Basic.has`
   * @example
   * ```ts
   * import { ex } from '@symjs/symjs';
   *
   * ex`sin(x) + y + 1`.has(ex`x`); // => True
   * ex`sin(x) + y + 1`.has(ex`y + 1`); // => True
   * ex`sin(x) + y + 1`.has(ex`z`); // => False
   * ```
   */
  has(sub: Expr): boolean {
    if (this.key === sub.key) return true;
    if (this.constructor === sub.constructor && (this instanceof Add || this instanceof Mul)) {
      const commutative = new Set(this.args.filter((a) => a.isCommutative).map((a) => a.key));
      if (sub.args.every((a) => !a.isCommutative || commutative.has(a.key))) {
        const order = this.args.filter((a) => !a.isCommutative);
        const pattern = sub.args.filter((a) => !a.isCommutative);
        if (!pattern.length || order.some((_, i) => pattern.every((a, j) => a.key === order[i + j]?.key))) return true;
      }
    }
    return this.args.some((a) => a.has(sub));
  }

  /**
   * Formats the expression using SymPy's string conventions.
   *
   * @returns The text of the expression.
   * @see SymPy `sympy.printing.str.sstr`
   */
  toString(): string {
    return impl.str(this);
  }
  /**
   * Formats the expression as LaTeX with the default settings of {@link latex}.
   *
   * @returns The LaTeX text.
   * @see SymPy `sympy.printing.latex.latex`
   */
  toLatex(): string {
    return impl.latex(this);
  }
  [Symbol.for('nodejs.util.inspect.custom')](): string {
    return `Expr(${this.toString()})`;
  }
}

// ---------------------------------------------------------------------------
// Atoms
// ---------------------------------------------------------------------------

/** Returns `e` as a rational number, or throws an `InvariantError` naming `what` if the type check fails. */
export function asRational(e: Expr, what = 'value'): Rational {
  if (!(e instanceof Rational)) throw new InvariantError(`${what} is not a Rational`);
  return e;
}

/**
 * An exact rational number `p/q` in lowest terms with `q > 0`; integers have
 * `q = 1`. Create one with {@link Rational.of}; arithmetic on rationals stays
 * exact.
 *
 * @see SymPy `sympy.core.numbers.Rational`
 * @example
 * ```ts
 * import { Rational } from '@symjs/symjs';
 *
 * const r = Rational.of(3, 6);
 * r; // => 1/2
 * [r.p, r.q]; // => [1, 2]
 * r.add(1); // => 3/2
 * Rational.of(2n ** 70n); // => 1180591620717411303424
 * ```
 */
export class Rational extends Expr {
  /** The node's discriminant. */
  readonly kind = 'Rational' as const;
  /**
   * The node's arguments in canonical order.
   *
   * @see SymPy `sympy.core.numbers.Rational.args`
   */
  readonly args: readonly Expr[] = [];
  /**
   * The numerator in lowest terms.
   *
   * @see SymPy `sympy.core.numbers.Rational.p`
   */
  readonly p: bigint;
  /**
   * The positive denominator in lowest terms.
   *
   * @see SymPy `sympy.core.numbers.Rational.q`
   */
  readonly q: bigint;

  private constructor(p: bigint, q: bigint) {
    super();
    this.p = p;
    this.q = q;
  }

  /**
   * Constructs a reduced rational number from an integer numerator and denominator.
   *
   * @param p - The integer numerator or denominator, respectively.
   * @param q - The integer numerator or denominator, respectively.
   * @param options - `gcd` supplies a known common divisor of the numerator and denominator.
   * @returns The reduced rational.
   * @throws RangeError when the denominator is zero or the supplied common divisor is invalid.
   */
  static of(p: bigint | number, q: bigint | number = 1n, options: { gcd?: bigint } = {}): Rational {
    let P = BigInt(p);
    let Q = BigInt(q);
    if (Q === 0n) throw new RangeError('Rational: division by zero');
    if (Q < 0n) {
      P = -P;
      Q = -Q;
    }
    const g = options.gcd ?? gcd(P, Q);
    if (options.gcd !== undefined && (g < 1n || P % g !== 0n || Q % g !== 0n)) throw new RangeError('Rational: invalid common divisor');
    if (g > 1n) {
      P /= g;
      Q /= g;
    }
    return new Rational(P, Q);
  }

  /**
   * Indicates whether the expression represents a number.
   *
   * @returns The numeric flag.
   * @see SymPy `sympy.core.numbers.Rational.is_number`
   */
  get isNumber(): boolean {
    return true;
  }
  /**
   * Tests whether the denominator is one.
   *
   * @returns Whether the number is integral.
   * @see SymPy `sympy.core.numbers.Rational.is_integer`
   */
  get isInteger(): boolean {
    return this.q === 1n;
  }
  /**
   * Tests whether the number equals the additive identity.
   *
   * @returns Whether the value is zero.
   * @see SymPy `sympy.core.numbers.Rational.is_zero`
   */
  get isZero(): boolean {
    return this.p === 0n;
  }
  /**
   * Tests whether the number equals the multiplicative identity.
   *
   * @returns True for one.
   */
  get isOne(): boolean {
    return this.p === 1n && this.q === 1n;
  }
  /**
   * Tests whether the number is strictly below zero.
   *
   * @returns True for negative values.
   * @see SymPy `sympy.core.numbers.Rational.is_negative`
   */
  get isNegative(): boolean {
    return this.p < 0n;
  }
  /**
   * Tests whether the number is strictly above zero.
   *
   * @returns True for positive values.
   * @see SymPy `sympy.core.numbers.Rational.is_positive`
   */
  get isPositive(): boolean {
    return this.p > 0n;
  }
  /**
   * Converts the value to a JavaScript number.
   *
   * @returns The nearest JavaScript number.
   */
  get value(): number {
    return Number(this.p) / Number(this.q);
  }
  protected computeKey(): string {
    return this.q === 1n ? `${this.p}` : `${this.p}/${this.q}`;
  }

  /** The integer result of a bitwise operation on this and other (a TypeError when one is not an integer). */
  private bits(other: Rational | number | bigint, op: (a: bigint, b: bigint) => bigint): Rational {
    const b = other instanceof Rational ? (other.q === 1n ? other.p : undefined) : typeof other === 'bigint' || Number.isInteger(other) ? BigInt(other) : undefined;
    if (this.q !== 1n || b === undefined) throw new TypeError('bitwise operations need integers');
    return Rational.of(op(this.p, b));
  }
  /**
   * Divides two numbers by their greatest common divisor.
   *
   * @param other - The other operand.
   * @returns The GCD and both cofactors.
   * @throws RangeError when both operands are exactly zero.
   * @see SymPy `sympy.core.numbers.Rational.cofactors`
   */
  cofactors(other: Num): [Num, Num, Num] {
    if (other instanceof Float) {
      const [g, b, a] = other.cofactors(this);
      return [g, a, b];
    }
    const g = Rational.of(gcd(this.p, other.p), lcm(this.q, other.q));
    if (g.isZero) throw new RangeError('cofactors of two exact zeros');
    return [g, Rational.of(this.p * g.q, this.q * g.p), Rational.of(other.p * g.q, other.q * g.p)];
  }
  /**
   * Complements the bits of the integer in two's complement representation.
   *
   * @returns The bitwise complement as an integer.
   * @throws TypeError when the operand is not an integer.
   */
  bitNot(): Rational {
    if (!this.isInteger) throw new TypeError('bitwise operations need integers');
    return Rational.of(~this.p);
  }
  /**
   * Shifts this integer left.
   *
   * @param n - The number of bit positions to shift.
   * @returns The integer multiplied by `2**n`.
   * @throws TypeError when either operand is not an integer.
   * @throws RangeError when the shift count is negative.
   */
  lshift(n: Rational | number | bigint): Rational {
    return this.bits(n, (a, b) => (b < 0n ? negativeShift() : a << b));
  }
  /**
   * Shifts this integer right.
   *
   * @param n - The number of bit positions to shift.
   * @returns The integer divided by `2**n`, rounded down.
   * @throws TypeError when either operand is not an integer.
   * @throws RangeError when the shift count is negative.
   */
  rshift(n: Rational | number | bigint): Rational {
    return this.bits(n, (a, b) => (b < 0n ? negativeShift() : a >> b));
  }
  /**
   * Computes the bitwise AND of the two integers.
   *
   * @param other - The other operand.
   * @returns The bitwise AND as an integer.
   * @throws TypeError when either operand is not an integer.
   */
  and(other: Rational | number | bigint): Rational {
    return this.bits(other, (a, b) => a & b);
  }
  /**
   * Computes the bitwise OR of the two integers.
   *
   * @param other - The other operand.
   * @returns The bitwise OR as an integer.
   * @throws TypeError when either operand is not an integer.
   */
  or(other: Rational | number | bigint): Rational {
    return this.bits(other, (a, b) => a | b);
  }
  /**
   * Computes the bitwise exclusive OR of the two integers.
   *
   * @param other - The other operand.
   * @returns The bitwise XOR as an integer.
   * @throws TypeError when either operand is not an integer.
   */
  xor(other: Rational | number | bigint): Rational {
    return this.bits(other, (a, b) => a ^ b);
  }
}

const negativeShift = (): never => {
  throw new RangeError('negative shift count');
};

/**
 * A floating-point number with a precision in bits (53, double precision, by
 * default). Numbers of higher precision come from `evalf`.
 *
 * @see SymPy `sympy.core.numbers.Float`
 * @example
 * ```ts
 * import { ex, Float, pi } from '@symjs/symjs';
 *
 * new Float(0.1); // => 0.100000000000000
 * new Float(0.25).add(ex`x`); // => x + 0.25
 * pi.evalf(30); // => 3.14159265358979323846264338328
 * ```
 */
export class Float extends Expr {
  /** The node's discriminant. */
  readonly kind = 'Float' as const;
  /**
   * The node's arguments in canonical order.
   *
   * @see SymPy `sympy.core.numbers.Float.args`
   */
  readonly args: readonly Expr[] = [];
  /** Exact binary value man * 2**exp. */
  readonly mpf: Mpf;
  /** Binary precision in bits (53 for the default 15 digits). */
  readonly prec: number;
  /**
   * A float from a JS number (rounded to `prec` bits) or a raw mpf value.
   *
   * @param prec binary precision; defaults to 53 (15 decimal digits).
   * @param valueIn - The value to convert.
   * @throws RangeError when a JavaScript number is nonfinite.
   */
  constructor(valueIn: number | Mpf, prec = 53) {
    super();
    let value = valueIn;
    if (typeof value === 'number') {
      if (!Number.isFinite(value)) throw new RangeError(`Float: non-finite value ${value}`);
      value = mpfFromNumber(value);
    }
    this.mpf = mpfNormalize(value.man, value.exp, prec);
    this.prec = prec;
  }
  /**
   * Uses a unit GCD and expresses both cofactors at the operands' working precision.
   *
   * @param other - The other operand.
   * @returns The unit gcd and the two operands converted to floating point.
   * @see SymPy `sympy.core.numbers.Float.cofactors`
   */
  cofactors(other: Num): [Float, Float, Float] {
    const prec = other instanceof Float ? Math.max(this.prec, other.prec) : this.prec;
    const value = other instanceof Float ? other.mpf : mpfFromRational(other.p, other.q, prec);
    return [new Float(1, prec), new Float(this.mpf, prec), new Float(value, prec)];
  }
  /**
   * Rounds the value to the nearest JavaScript double.
   *
   * @returns The nearest JavaScript number.
   */
  get value(): number {
    return mpfToNumber(this.mpf);
  }
  /**
   * Indicates whether the expression represents a number.
   *
   * @returns The numeric flag.
   * @see SymPy `sympy.core.numbers.Float.is_number`
   */
  get isNumber(): boolean {
    return true;
  }
  /**
   * Tests whether the number equals the additive identity.
   *
   * @returns Whether the value is zero.
   * @see SymPy `sympy.core.numbers.Float.is_zero`
   */
  get isZero(): boolean {
    return this.mpf.man === 0n;
  }
  /**
   * Tests whether the number is strictly below zero.
   *
   * @returns True for negative values.
   * @see SymPy `sympy.core.numbers.Float.is_negative`
   */
  get isNegative(): boolean {
    return this.mpf.man < 0n;
  }
  /**
   * Tests whether the number is strictly above zero.
   *
   * @returns True for positive values.
   * @see SymPy `sympy.core.numbers.Float.is_positive`
   */
  get isPositive(): boolean {
    return this.mpf.man > 0n;
  }
  protected computeKey(): string {
    if (this.prec === 53) {
      const s = `${this.value}`;
      return s.includes('.') || s.includes('e') ? `f${s}` : `f${s}.0`;
    }
    return `f${this.mpf.man}p${this.mpf.exp}_${this.prec}`;
  }
}

/** An exact rational number or a floating-point number. */
export type Num = Rational | Float;

/**
 * Tests whether an expression is a rational or floating-point number.
 *
 * @param e - The input expression.
 * @returns Whether the expression belongs to the indicated node class.
 * @see SymPy `sympy.core.expr.Expr.is_Number`
 */
export function isNum(e: Expr): e is Num {
  return e instanceof Rational || e instanceof Float;
}

/** A symbolic variable. */
export class Sym extends Expr {
  /** The discriminant identifying the expression node. */
  readonly kind = 'Symbol' as const;
  /** The operands of the expression in node order. */
  readonly args: readonly Expr[] = [];
  /** The facts supplied when constructing the symbol. */
  readonly assumptions: Assumptions;
  /**
   * All consequences of the assumptions used to construct this symbol.
   *
   * @see SymPy `sympy.core.symbol.Symbol.assumptions0`
   */
  get assumptions0(): Map<string, boolean> {
    return deduceAllFacts({ commutative: true, ...Object.fromEntries(Object.entries(this.assumptions).map(([k, v]) => [k.replace(/[A-Z]/g, (c) => `_${c.toLowerCase()}`), v])) });
  }

  /** Whether commutative=True was given explicitly: it is the default, and SymPy's srepr shows it only then. */
  readonly givenCommutative: boolean;
  /**
   * Creates a named symbol.
   *
   * @param name - The symbolic name.
   * @param assumptions - The facts to attach to the symbol.
   */
  constructor(/** The symbolic name. */ readonly name: string, assumptions: Assumptions = {}) {
    super();
    if (typeof name !== 'string') {
      throw new SyntaxError(`Invalid symbol name: ${JSON.stringify(name)}`);
    }
    const commutative: unknown = Reflect.get(assumptions, 'commutative');
    if (commutative !== undefined && typeof commutative !== 'boolean') throw new RangeError('commutativity must be true or false');
    const facts = deduceAllFacts(Object.fromEntries(Object.entries(assumptions).map(([k, v]) => [k.replace(/[A-Z]/g, (c) => `_${c.toLowerCase()}`), v])));
    const a: { -readonly [K in keyof Assumptions]: Assumptions[K] } = { ...assumptions };
    this.givenCommutative = a.commutative === true;
    if (a.commutative === true) delete a.commutative;
    // Keep the core sign/number flags available to the arithmetic hot paths.
    for (const k of ['real', 'positive', 'nonnegative', 'negative', 'nonpositive', 'integer', 'zero'] as const) {
      const v = facts.get(k);
      if (v === true || (v === false && ['real', 'integer', 'zero'].includes(k))) a[k] = v;
    }
    this.assumptions = Object.freeze(a);
  }

  protected computeCommutative(): boolean {
    return this.assumptions.commutative !== false;
  }

  /** The name as printed (Wild adds a trailing underscore, Dummy a leading one). */
  get printName(): string {
    return this.name;
  }

  /** The class name used to sort the symbol. Coordinate symbols use their own class name. */
  get sortClass(): string {
    return 'Symbol';
  }

  /** The numeric class priority in the sort key. Ordinary symbols use 2 and random symbols use 5. */
  get sortPriority(): number {
    return 2;
  }

  /**
   * Applies a substitution or exact replacement to expressions embedded in a symbol-like node. For
   * example, a random symbol can transform its probability space. A plain symbol has no embedded
   * expressions.
   *
   * @param _f - The transformation to apply to embedded expressions.
   * @returns The transformed node when the symbol provides a specialized substitution.
   */
  substituteInner(_f: (e: Expr) => Expr): Expr | undefined {
    return undefined;
  }

  /**
   * Lists free symbols contributed by a symbol-like node in addition to the symbol itself, such as the
   * index of a random indexed symbol.
   *
   * @returns The free symbols contributed by the embedded expressions.
   */
  innerFreeSymbols(): readonly Sym[] {
    return [];
  }

  /** LaTeX form when it is not derived from the name (SymPy BaseScalar._latex_form); undefined for a plain symbol. */
  get latexForm(): string | undefined {
    return undefined;
  }

  /** Pretty form when it is not derived from the name (SymPy BaseScalar._pretty_form); undefined for a plain symbol. */
  get prettyForm(): string | undefined {
    return undefined;
  }

  protected computeKey(): string {
    const a = this.assumptions;
    const flags = `${a.real ? 'r' : ''}${a.nonnegative ? 'n' : ''}${a.positive ? 'p' : ''}${a.integer ? 'i' : ''}${a.negative ? 'N' : ''}${a.nonpositive ? 'P' : ''}${a.commutative === false ? 'c' : ''}${a.polar ? 'o' : ''}${a.zero === false && !a.positive && !a.negative && a.integer !== false ? 'z' : ''}${a.zero === true ? 'Z' : ''}${a.integer === false ? 'I' : ''}`;
    const allFlags = flags + (a.aboveFermi === true ? 'A' : '') + (a.belowFermi === true ? 'B' : '');
    const legacy = deduceAllFacts(Object.fromEntries(Object.entries(a).filter(([k, v]) =>
      ['real', 'nonnegative', 'positive', 'integer', 'negative', 'nonpositive', 'commutative', 'polar', 'zero', 'aboveFermi', 'belowFermi'].includes(k) &&
      (v || ['integer', 'commutative', 'zero'].includes(k))).map(([k, v]) => [k.replace(/[A-Z]/g, (c) => `_${c.toLowerCase()}`), v])));
    const extra = [...this.assumptions0].filter(([k, v]) => k !== 'commutative' && legacy.get(k) !== v).sort(([k], [l]) => k.localeCompare(l));
    const suffix = extra.length ? JSON.stringify(extra) : '';
    return allFlags || suffix ? `$${this.name}[${allFlags}${suffix}]` : `$${this.name}`;
  }
}

/**
 * Represents a symbol whose index distinguishes it from other symbols with the same name. Its printed
 * name starts with an underscore.
 *
 * @see SymPy `sympy.core.symbol.Dummy`
 */
export class Dummy extends Sym {
  private static counter = 0;
  /** The unique index distinguishing this dummy from other symbols of the same name. */
  readonly dummyIndex: number;
  /**
   * Creates a distinct dummy symbol.
   *
   * @param name - The symbolic name.
   * @param assumptions - The facts to attach to the symbol.
   * @param index - The unique identifier for this dummy.
   */
  constructor(name = 'Dummy', assumptions: Assumptions = {}, index?: number) {
    super(name, assumptions);
    this.dummyIndex = index ?? ++Dummy.counter;
  }
  /** The symbol name prefixed with an underscore. */
  get printName(): string {
    return `_${this.name}`;
  }
  protected computeKey(): string {
    return `${super.computeKey()}#${this.dummyIndex}`;
  }
}

/**
 * Pattern symbol for match/replace; matches any expression not containing an excluded one.
 *
 * @see SymPy `sympy.core.symbol.Wild`
 * @example
 * ```ts
 * import { Wild } from '@symjs/symjs';
 *
 * new Wild('p').printName; // => p_
 * ```
 */
export class Wild extends Sym {
  /**
   * Expressions that cannot occur in a wildcard match.
   *
   * @see SymPy `sympy.core.symbol.Wild.exclude`
   */
  readonly exclude: readonly Expr[];
  /**
   * Predicates that a match for this wildcard must satisfy.
   *
   * @see SymPy `sympy.core.symbol.Wild.properties`
   */
  readonly properties: readonly ((e: Expr) => boolean)[];
  /**
   * Creates a `Wild`.
   *
   * @param name - The symbolic name or names.
   * @param opts - `exclude` rules out subexpressions, `properties` supplies match tests, and assumption flags constrain the wildcard.
   */
  constructor(
    name: string,
    opts: { exclude?: readonly ExprLike[]; properties?: readonly ((e: Expr) => boolean)[] } & Assumptions = {},
  ) {
    const { exclude = [], properties = [], ...assumptions } = opts;
    super(name, assumptions);
    this.exclude = exclude.map((e) => impl.sympify(e));
    this.properties = properties;
  }
  /**
   * Formats the wildcard name with its trailing underscore.
   *
   * @returns The printable name.
   */
  get printName(): string {
    return `${this.name}_`;
  }
  protected computeKey(): string {
    return `?${super.computeKey()}[${this.exclude.map((e) => e.key).join(',')}]${this.properties.length ? `{${this.properties.length}}` : ''}`;
  }
}

/**
 * Pattern matching an applied function (optionally with a given number of arguments).
 *
 * @see SymPy `sympy.core.function.WildFunction`
 * @example
 * ```ts
 * import { WildFunction } from '@symjs/symjs';
 *
 * new WildFunction('F').name; // => F
 * ```
 */
export class WildFunction extends Wild {
  /**
   * Creates a `WildFunction`.
   *
   * @param name - The symbolic name or names.
   * @param nargs - The allowed argument counts of the matched function.
   */
  constructor(name: string,
    /** The allowed argument counts of the matched function. */
    readonly nargs?: readonly number[]) {
    super(name);
  }
  protected computeKey(): string {
    return `?F${this.name}[${this.nargs?.join(',') ?? ''}]`;
  }
}

/** The names of the supported symbolic number constants. */
export type ConstantName = 'pi' | 'E' | 'I' | 'EulerGamma' | 'Catalan' | 'GoldenRatio' | 'TribonacciConstant';

/**
 * Mathematical constants: pi, E (Euler's number) and I (imaginary unit).
 *
 * @see SymPy `sympy.core.numbers.NumberSymbol`
 */
export class Constant extends Expr {
  /** The node's discriminant. */
  readonly kind = 'Constant' as const;
  /**
   * The node's arguments in canonical order.
   *
   * @see SymPy `sympy.core.numbers.NumberSymbol.args`
   */
  readonly args: readonly Expr[] = [];
  /**
   * Creates a `NumberSymbol`.
   *
   * @param name - The symbolic name or names.
   */
  constructor(
    /** The symbolic name. */
    readonly name: ConstantName) {
    super();
  }
  protected computeKey(): string {
    return `#${this.name}`;
  }
}

// ---------------------------------------------------------------------------
// Composite nodes (construct via ops.ts)
// ---------------------------------------------------------------------------

/** Sum. Canonical: numeric term first (if non-zero), remaining terms sorted. @internal ctor */
export class Add extends Expr {
  /** The discriminant identifying the expression node. */
  readonly kind = 'Add' as const;
  /**
   * Creates a sum from its terms.
   *
   * @param args - The operands in node order.
   */
  constructor(/** The operands of the expression in node order. */ readonly args: readonly Expr[]) {
    super();
  }
  protected computeKey(): string {
    return `+(${this.args.map((a) => a.key).join(',')})`;
  }
}

/** Product. Canonical: numeric coefficient first (if not 1), remaining factors sorted. @internal ctor */
export class Mul extends Expr {
  /** The discriminant identifying the expression node. */
  readonly kind = 'Mul' as const;
  /**
   * Creates a product from its factors.
   *
   * @param args - The operands in node order.
   */
  constructor(/** The operands of the expression in node order. */ readonly args: readonly Expr[]) {
    super();
  }
  protected computeKey(): string {
    return `*(${this.args.map((a) => a.key).join(',')})`;
  }
}

/** Power base^exp. `exp(x)` is represented as Pow(E, x). @internal ctor */
export class Pow extends Expr {
  /** The discriminant identifying the expression node. */
  readonly kind = 'Pow' as const;
  /** The operands of the expression in node order. */
  readonly args: readonly [Expr, Expr];
  /**
   * Creates a power from a base and exponent.
   *
   * @param base - The base of the power.
   * @param exp - The exponent.
   */
  constructor(base: Expr, exp: Expr) {
    super();
    this.args = [base, exp];
  }
  /**
   * The expression being raised to a power.
   *
   * @see SymPy `sympy.core.power.Pow.base`
   */
  get base(): Expr {
    return this.args[0];
  }
  /**
   * The exponent.
   *
   * @see SymPy `sympy.core.power.Pow.exp`
   */
  get exp(): Expr {
    return this.args[1];
  }
  protected computeKey(): string {
    return `^(${this.args[0].key},${this.args[1].key})`;
  }
}

/**
 * Application of a named function.
 *
 * @internal ctor
 *
 * @experimental May change in a minor release.
 * @see SymPy `sympy.core.function.Function`
 * @example
 * ```ts
 * import { AppliedFunction, ex } from '@symjs/symjs';
 *
 * new AppliedFunction('sin', [ex`x`]); // => sin(x)
 * ```
 */
export class Fn extends Expr {
  /** The node's discriminant. */
  readonly kind = 'Fn' as const;
  /**
   * Creates an `AppliedFunction`.
   *
   * @param name - The symbolic name or names.
   * @param args - The arguments in positional order.
   */
  constructor(
    /** The symbolic name. */
    readonly name: FnName,
    /**
     * The node's arguments in canonical order.
     *
     * @see SymPy `sympy.core.function.Function.args`
     */
    readonly args: readonly Expr[]) {
    super();
  }
  protected computeKey(): string {
    return `${this.name}(${this.args.map((a) => a.key).join(',')})`;
  }
}

export type SpecialName = 'oo' | '-oo' | 'zoo' | 'nan';

/** Extended values: oo, -oo, zoo (complex infinity) and nan. */
export class Special extends Expr {
  /** The discriminant identifying the expression node. */
  readonly kind = 'Special' as const;
  /** The operands of the expression in node order. */
  readonly args: readonly Expr[] = [];
  /**
   * Creates a special numerical value.
   *
   * @param name - The symbolic name.
   */
  constructor(/** The symbolic name. */ readonly name: SpecialName) {
    super();
  }
  /** Whether this value represents an infinity. */
  get isInfinite(): boolean {
    return this.name !== 'nan';
  }
  protected computeKey(): string {
    return `%${this.name}`;
  }
}

/**
 * Boolean constant (SymPy `true` / `false`).
 *
 * @see SymPy `sympy.logic.boolalg.BooleanAtom`
 */
export class BoolAtom extends Expr {
  /** The node's discriminant. */
  readonly kind = 'Bool' as const;
  /**
   * The node's arguments in canonical order.
   *
   * @see SymPy `sympy.logic.boolalg.BooleanAtom.args`
   */
  readonly args: readonly Expr[] = [];
  /**
   * Creates a `BooleanAtom`.
   *
   * @param value - The value to examine.
   */
  constructor(
    /** The truth value of the Boolean atom. */
    readonly value: boolean) {
    super();
  }
  protected computeKey(): string {
    return this.value ? '!true' : '!false';
  }
}

/** The comparison operator stored in a relational expression. */
export type RelOp = 'Eq' | 'Ne' | 'Lt' | 'Le' | 'Gt' | 'Ge';

/**
 * Relation such as Ne(a, 0). Construct with `rel()` in `logic.ts`.
 *
 * @internal ctor
 * @see SymPy `sympy.core.relational.Relational`
 * @example
 * ```ts
 * import { Rel, ex } from '@symjs/symjs';
 *
 * new Rel('Lt', ex`x`, ex`1`); // => x < 1
 * ```
 */
export class Rel extends Expr {
  /** The node's discriminant. */
  readonly kind = 'Rel' as const;
  /**
   * The node's arguments in canonical order.
   *
   * @see SymPy `sympy.core.relational.Relational.args`
   */
  readonly args: readonly [Expr, Expr];
  /**
   * Creates a `Rel`.
   *
   * @param op - The comparison operator.
   * @param lhs - The left-hand operand.
   * @param rhs - The right-hand operand.
   */
  constructor(
    /** The comparison operator identifying this relation. */
    readonly op: RelOp, lhs: Expr, rhs: Expr) {
    super();
    this.args = [lhs, rhs];
  }
  /**
   * Selects the operand on the left of the comparison.
   *
   * @returns The left-hand expression.
   * @see SymPy `sympy.core.relational.Relational.lhs`
   */
  get lhs(): Expr {
    return this.args[0];
  }
  /**
   * Selects the operand on the right of the comparison.
   *
   * @returns The right-hand expression.
   * @see SymPy `sympy.core.relational.Relational.rhs`
   */
  get rhs(): Expr {
    return this.args[1];
  }
  /**
   * Identifies the operator used to print the comparison.
   *
   * @returns The operator string.
   */
  get relOp(): string {
    return { Eq: '==', Ne: '!=', Lt: '<', Le: '<=', Gt: '>', Ge: '>=' }[this.op];
  }
  /**
   * Converts the inequality to its strict form.
   *
   * @returns A strict inequality.
   * @see SymPy `sympy.core.relational.Relational.strict`
   */
  get strict(): Rel {
    return new Rel(this.op === 'Le' ? 'Lt' : this.op === 'Ge' ? 'Gt' : this.op, this.lhs, this.rhs);
  }
  /**
   * Converts the inequality to its inclusive form.
   *
   * @returns A non-strict inequality.
   * @see SymPy `sympy.core.relational.Relational.weak`
   */
  get weak(): Rel {
    return new Rel(this.op === 'Lt' ? 'Le' : this.op === 'Gt' ? 'Ge' : this.op, this.lhs, this.rhs);
  }
  protected computeKey(): string {
    return `${this.op}(${this.args[0].key},${this.args[1].key})`;
  }
}

/** Piecewise((expr, cond), ...). Args are stored flat: [e1, c1, e2, c2, ...]. @internal ctor */
export class Piecewise extends Expr {
  /** The discriminant identifying the expression node. */
  readonly kind = 'Piecewise' as const;
  /**
   * Creates a piecewise expression from interleaved values and conditions.
   *
   * @param args - The operands in node order.
   */
  constructor(/** The operands of the expression in node order. */ readonly args: readonly Expr[]) {
    super();
  }
  /** The branch expressions paired with their conditions, in evaluation order. */
  get pairs(): [Expr, Expr][] {
    const out: [Expr, Expr][] = [];
    for (let i = 0; i < this.args.length; i += 2) out.push([at(this.args, i), at(this.args, i + 1)]);
    return out;
  }
  protected computeKey(): string {
    return `Piecewise(${this.args.map((a) => a.key).join(',')})`;
  }
}

/**
 * An unevaluated integral, with the arguments `[f, x]` (indefinite) or
 * `[f, x, a, b]` (definite). {@link integrate} returns it for an integral it
 * cannot compute; `doit` evaluates it.
 *
 * @see SymPy `sympy.integrals.integrals.Integral`
 * @example
 * ```ts
 * import { doit, ex, Integral } from '@symjs/symjs';
 *
 * const i = ex`Integral(x**2, (x, 0, 1))`;
 * i instanceof Integral; // => True
 * i.args; // => [x**2, x, 0, 1]
 * doit(i); // => 1/3
 * ```
 */
export class Integral extends Expr {
  /** The node's discriminant. */
  readonly kind = 'Integral' as const;
  /**
   * Creates an `Integral`.
   *
   * @param args - The integrand, integration variable and optional endpoints.
   */
  constructor(
    /**
     * The node's arguments in canonical order.
     *
     * @see SymPy `sympy.integrals.integrals.Integral.args`
     */
    readonly args: readonly Expr[]) {
    super();
  }
  /**
   * Identifies the expression integrated at this level of nesting.
   *
   * @returns The integrand.
   */
  get integrand(): Expr {
    return at(this.args, 0);
  }
  /**
   * Indicates whether the expression represents a number.
   *
   * @returns The numeric flag.
   * @see SymPy `sympy.integrals.integrals.Integral.is_number`
   */
  override get isNumber(): boolean {
    return this.freeSymbols().size === 0;
  }
  /**
   * Looks through nested integrals to find the original integrand.
   *
   * @returns The innermost expression.
   * @see SymPy `sympy.integrals.integrals.Integral.function`
   */
  get function(): Expr { return this.integrand instanceof Integral ? this.integrand.function : this.integrand; }
  /**
   * Variables bound by definite limits, including nested integral limits.
   *
   * @returns The resulting expressions in order.
   * @see SymPy `sympy.integrals.integrals.Integral.bound_symbols`
   */
  get boundSymbols(): Expr[] {
    return [...(this.integrand instanceof Integral ? this.integrand.boundSymbols : []), ...(this.args.length >= 3 ? [this.variable] : [])];
  }
  /**
   * Identifies the bound variable at the outermost level.
   *
   * @returns The outer integration variable.
   */
  get variable(): Expr {
    return at(this.args, 1);
  }
  /**
   * Identifies the endpoints of a definite integral when bounds are present.
   *
   * @returns The lower and upper endpoints, when supplied.
   * @see SymPy `sympy.integrals.integrals.Integral.limits`
   */
  get limits(): [Expr, Expr] | undefined {
    return this.args.length === 4 ? [at(this.args, 2), at(this.args, 3)] : undefined;
  }
  /** SymPy: an integral is commutative when its integrand is (the variable may be a matrix symbol). */
  protected override computeCommutative(): boolean {
    return this.integrand.isCommutative;
  }
  protected computeKey(): string {
    return `Integral(${this.args.map((a) => a.key).join(',')})`;
  }
}

/**
 * Application of an undefined function, e.g. f(x). Create with `Function('f')`.
 *
 * @see SymPy `sympy.core.function.AppliedUndef`
 */
export class UndefFn extends Expr {
  /** The node's discriminant. */
  readonly kind = 'Undef' as const;
  /**
   * Creates an `AppliedUndef`.
   *
   * @param name - The symbolic name or names.
   * @param args - The arguments in positional order.
   * @param givenFacts - The assumptions attached to the undefined function.
   */
  constructor(
    /** The symbolic name. */
    readonly name: string,
    /**
     * The node's arguments in canonical order.
     *
     * @see SymPy `sympy.core.function.AppliedUndef.args`
     */
    readonly args: readonly Expr[],
    /** The assumptions attached to the undefined function. */
    readonly givenFacts: ReadonlyMap<string, boolean> = new Map()) {
    super();
  }
  protected override computeCommutative(): boolean {
    return this.givenFacts.get('commutative') ?? super.computeCommutative();
  }
  protected computeKey(): string {
    const assumptions = this.givenFacts.size === 0 ? '' : JSON.stringify([...this.givenFacts].sort(([a], [b]) => a.localeCompare(b)));
    return `@${this.name}${assumptions}(${this.args.map((a) => a.key).join(',')})`;
  }
}

/**
 * Unevaluated derivative. args: [expr, v1, n1, v2, n2, ...] where ni are
 * nonnegative integer counts which may be symbolic (SymPy `variable_count`). @internal ctor
 */
export class Derivative extends Expr {
  /** The discriminant identifying the expression node. */
  readonly kind = 'Derivative' as const;
  /**
   * Creates a held derivative.
   *
   * @param args - The operands in node order.
   */
  constructor(/** The operands of the expression in node order. */ readonly args: readonly Expr[]) {
    super();
  }
  /**
   * The expression being differentiated.
   *
   * @see SymPy `sympy.core.function.Derivative.expr`
   */
  get expr(): Expr {
    return at(this.args, 0);
  }
  /** The differentiation variables paired with their exact orders. */
  get variableOrders(): [Expr, Expr][] {
    const out: [Expr, Expr][] = [];
    for (let i = 1; i < this.args.length; i += 2) out.push([at(this.args, i), this.args[i + 1] ?? S.One]);
    return out;
  }
  /**
   * Integer counts for algorithms that require a concrete derivative order.
   *
   * @throws RangeError when an order cannot be represented as a concrete integer count.
   * @see SymPy `sympy.core.function.Derivative.variable_count`
   */
  get variableCount(): [Expr, number][] {
    return this.variableOrders.map(([v, order]) => {
      if (!(order instanceof Rational && order.isInteger) || order.p > BigInt(Number.MAX_SAFE_INTEGER)) {
        throw new RangeError('a concrete derivative order is required');
      }
      return [v, Number(order.p)];
    });
  }
  /** The sum of the orders across differentiation variables. */
  get derivativeOrder(): Expr {
    return impl.add(...this.variableOrders.map(([, n]) => n));
  }
  /**
   * Reconstruct a derivative while preserving subclass behavior.
   *
   * @param args - The operands in node order.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Derivative { return new Derivative(args); }
  /**
   * Evaluate the derivative in variable order.
   *
   * @returns The evaluated derivative, with unresolved differentiations held symbolically.
   * @see SymPy `sympy.core.function.Derivative.doit`
   */
  doit(): Expr {
    let result = this.expr;
    for (const [variable, count] of this.variableOrders) result = impl.diff(result, variable, count);
    return result;
  }
  protected computeKey(): string {
    return `D(${this.args.map((a) => a.key).join(',')})`;
  }
}

/**
 * An unevaluated limit of `expr` as `variable` tends to `point` from the
 * side `dir` (`'+'`, `'-'` or `'+-'`). {@link limit} returns it for a limit
 * it cannot determine; `doit` evaluates it.
 *
 * @see SymPy `sympy.series.limits.Limit`
 * @example
 * ```ts
 * import { doit, ex } from '@symjs/symjs';
 *
 * const l = ex`Limit(sin(x)/x, x, 0)`;
 * l; // => Limit(sin(x)/x, x, 0, dir='+')
 * doit(l); // => 1
 * ex`Limit(1/x, x, 0, '-')`; // => Limit(1/x, x, 0, dir='-')
 * ```
 */
export class Limit extends Expr {
  /** The node's discriminant. */
  readonly kind = 'Limit' as const;
  /**
   * Creates a `Limit`.
   *
   * @param args - The expression, variable and limit point.
   * @param dir - The side from which the variable approaches the limit point.
   */
  constructor(
    /**
     * The node's arguments in canonical order.
     *
     * @see SymPy `sympy.series.limits.Limit.args`
     */
    readonly args: readonly Expr[],
    /**
     * The side from which the variable approaches the limit point.
     *
     * @see SymPy `sympy.series.limits.Limit.dir`
     */
    readonly dir: '+' | '-' | '+-' = '+') {
    super();
  }
  /**
   * Identifies the expression evaluated as the variable approaches its limit point.
   *
   * @returns The expression inside the limit.
   */
  get expr(): Expr {
    return at(this.args, 0);
  }
  /**
   * Identifies the variable that approaches the limit point.
   *
   * @returns The limit variable.
   */
  get variable(): Expr {
    return at(this.args, 1);
  }
  /**
   * Specifies the value approached by the limit variable.
   *
   * @returns The limit point.
   */
  get point(): Expr {
    return at(this.args, 2);
  }
  protected computeKey(): string {
    return `Limit(${this.args.map((a) => a.key).join(',')},${this.dir})`;
  }
}

/**
 * Order term O(expr) as variable -> point. args: [expr, variable, point];
 * expr is a power of the variable (or of variable - point).
 *
 * @internal ctor
 * @see SymPy `sympy.series.order.Order`
 * @example
 * ```ts
 * import { Order, ex } from '@symjs/symjs';
 *
 * new Order([ex`x**2`, ex`x`, ex`0`]); // => O(x**2)
 * ```
 */
export class Order extends Expr {
  /** The node's discriminant. */
  readonly kind = 'Order' as const;
  /**
   * Creates an `Order`.
   *
   * @param args - The expression and optional expansion variable and point.
   */
  constructor(
    /**
     * The node's arguments in canonical order.
     *
     * @see SymPy `sympy.series.order.Order.args`
     */
    readonly args: readonly Expr[]) {
    super();
  }
  /**
   * Identifies the expression that sets the asymptotic order.
   *
   * @returns The order's defining expression.
   * @see SymPy `sympy.series.order.Order.expr`
   */
  get expr(): Expr {
    return at(this.args, 0);
  }
  /**
   * Identifies the expansion variable of the asymptotic comparison.
   *
   * @returns The variable, when specified.
   */
  get variable(): Expr | undefined {
    return this.args[1];
  }
  /**
   * Identifies the point about which the order is defined, when specified.
   *
   * @returns The expansion point, when present.
   * @see SymPy `sympy.series.order.Order.point`
   */
  get point(): Expr | undefined {
    return this.args[2];
  }
  /**
   * Tests whether this order term bounds the expression at the expansion point.
   *
   * @param expr - The input expression.
   * @returns A truth value, possibly `'unknown'`.
   * @see SymPy `sympy.series.order.Order.contains`
   */
  contains(expr: ExprLike): boolean | 'unknown' {
    if (impl.orderContains === undefined) return notLoaded('Order.contains', 'calculus');
    return impl.orderContains(this, impl.sympify(expr));
  }
  protected computeKey(): string {
    return `O(${this.args.map((a) => a.key).join(',')})`;
  }
}

// ---------------------------------------------------------------------------
// Singletons
// ---------------------------------------------------------------------------

/**
 * The singleton numbers, constants and Booleans: `S.Zero`, `S.One`,
 * `S.Half`, `S.Pi`, `S.I`, `S.Infinity`, `S.NaN`, `S.true`, ... Each is a single
 * shared instance, so it can be compared with `===`.
 *
 * @see SymPy `sympy.core.singleton.S`
 * @example
 * ```ts
 * import { ex, S } from '@symjs/symjs';
 *
 * S.Half; // => 1/2
 * ex`x - x` === S.Zero; // => True
 * ```
 */
export const S = {
  Zero: Rational.of(0n),
  One: Rational.of(1n),
  NegOne: Rational.of(-1n),
  Two: Rational.of(2n),
  Half: Rational.of(1n, 2n),
  NegHalf: Rational.of(-1n, 2n),
  Pi: new Constant('pi'),
  E: new Constant('E'),
  I: new Constant('I'),
  EulerGamma: new Constant('EulerGamma'),
  Catalan: new Constant('Catalan'),
  GoldenRatio: new Constant('GoldenRatio'),
  TribonacciConstant: new Constant('TribonacciConstant'),
  Infinity: new Special('oo'),
  NegativeInfinity: new Special('-oo'),
  ComplexInfinity: new Special('zoo'),
  NaN: new Special('nan'),
  true: new BoolAtom(true),
  false: new BoolAtom(false),
} as const;

/**
 * The ratio of a circle's circumference to its diameter.
 *
 * @see SymPy `sympy.core.numbers.Pi`
 * @example
 * ```ts
 * import { cos, pi } from '@symjs/symjs';
 *
 * cos(pi); // => -1
 * pi.evalf(20); // => 3.1415926535897932385
 * ```
 */
export const pi = S.Pi;
/**
 * The base of the natural logarithm, `exp(1)`.
 *
 * @see SymPy `sympy.core.numbers.Exp1`
 * @example
 * ```ts
 * import { E, log } from '@symjs/symjs';
 *
 * log(E); // => 1
 * E.evalf(20); // => 2.7182818284590452354
 * ```
 */
export const E = S.E;
/**
 * The imaginary unit, `sqrt(-1)`.
 *
 * @see SymPy `sympy.core.numbers.ImaginaryUnit`
 * @example
 * ```ts
 * import { ex, I } from '@symjs/symjs';
 *
 * I.pow(2); // => -1
 * ex`(2 + 3*I)*(1 - I)`.expand(); // => 5 + I
 * ```
 */
export const I = S.I;
/**
 * Positive infinity, for limits, intervals and the bounds of integrals and sums.
 *
 * @see SymPy `sympy.core.numbers.Infinity`
 * @example
 * ```ts
 * import { ex, limit, oo, Sym } from '@symjs/symjs';
 *
 * limit(ex`1/x`, Sym('x'), oo); // => 0
 * oo.add(1); // => oo
 * ```
 */
export const oo = S.Infinity;
/**
 * Complex infinity, the infinity of the extended complex plane without a
 * direction (for example `1/0`).
 *
 * @see SymPy `sympy.core.numbers.ComplexInfinity`
 * @example
 * ```ts
 * import { ex } from '@symjs/symjs';
 *
 * ex`1/0`; // => zoo
 * ```
 */
export const zoo = S.ComplexInfinity;
/**
 * Not a number, the result of an undefined operation such as `0/0` or `oo - oo`.
 *
 * @see SymPy `sympy.core.numbers.NaN`
 * @example
 * ```ts
 * import { ex } from '@symjs/symjs';
 *
 * ex`oo - oo`; // => nan
 * ```
 */
export const nan = S.NaN;

/** Canonical ordering of arguments: numbers first, then by structural key. */
export function compareExpr(a: Expr, b: Expr): number {
  const an = isNum(a) ? 0 : 1;
  const bn = isNum(b) ? 0 : 1;
  if (an !== bn) return an - bn;
  return a.key < b.key ? -1 : a.key > b.key ? 1 : 0;
}

// ---------------------------------------------------------------------------
// Type guards
// ---------------------------------------------------------------------------

/**
 * Tests whether an expression is a rational number node.
 *
 * @param e - The input expression.
 * @returns True if an expression is a rational number node, otherwise false.
 * @see SymPy `sympy.core.expr.Expr.is_Rational`
 */
export const isRational = (e: Expr): e is Rational => e instanceof Rational;
/**
 * Tests whether an expression is a floating-point number node.
 *
 * @param e - The input expression.
 * @returns True if an expression is a floating-point number node, otherwise false.
 * @see SymPy `sympy.core.expr.Expr.is_Float`
 */
export const isFloat = (e: Expr): e is Float => e instanceof Float;
/**
 * Tests whether an expression is a symbol.
 *
 * @param e - The input expression.
 * @returns True if an expression is a symbol, otherwise false.
 * @see SymPy `sympy.core.expr.Expr.is_Symbol`
 */
export const isSymbol = (e: Expr): e is Sym => e instanceof Sym;
/**
 * Tests whether an expression is a sum.
 *
 * @param e - The input expression.
 * @returns True if an expression is a sum, otherwise false.
 * @see SymPy `sympy.core.expr.Expr.is_Add`
 */
export const isAdd = (e: Expr): e is Add => e instanceof Add;
/**
 * Tests whether an expression is a product.
 *
 * @param e - The input expression.
 * @returns True if an expression is a product, otherwise false.
 * @see SymPy `sympy.core.expr.Expr.is_Mul`
 */
export const isMul = (e: Expr): e is Mul => e instanceof Mul;
/**
 * Tests whether an expression is a power.
 *
 * @param e - The input expression.
 * @returns True if an expression is a power, otherwise false.
 * @see SymPy `sympy.core.expr.Expr.is_Pow`
 */
export const isPow = (e: Expr): e is Pow => e instanceof Pow;
/**
 * Tests whether an expression is an application of a known function, optionally by name.
 *
 * @param e - The input expression.
 * @param name - The symbolic name or names.
 * @returns Whether the expression belongs to the indicated node class.
 * @see SymPy `sympy.core.expr.Expr.is_Function`
 */
export const isFn = (e: Expr, name?: FnName): e is Fn =>
  e instanceof Fn && (name === undefined || e.name === name);
/**
 * Tests whether an expression is a rational number with denominator one.
 *
 * @param e - The input expression.
 * @returns True if an expression is a rational number with denominator one, otherwise false.
 * @see SymPy `sympy.core.expr.Expr.is_Integer`
 */
export const isInteger = (e: Expr): e is Rational => e instanceof Rational && e.q === 1n;

/**
 * Tests whether the expression is a sum, including a matrix sum.
 *
 * @see SymPy `sympy.core.expr.Expr.is_Add`
 */
export const isAddLike = (e: Expr): boolean => e instanceof Add || (e instanceof ExtensionExpr && e.assocOp === 'Add');
/**
 * Tests whether the expression is a product, including a matrix product.
 *
 * @see SymPy `sympy.core.expr.Expr.is_Mul`
 */
export const isMulLike = (e: Expr): boolean => e instanceof Mul || (e instanceof ExtensionExpr && e.assocOp === 'Mul');

/**
 * Base class for expression nodes defined outside the base module (extend
 * packages). Subclasses describe themselves through the methods below; the
 * base module calls them from rebuild/subs/xreplace, the str and LaTeX
 * printers, diff and adjoint/conjugate/transpose.
 */
export abstract class ExtensionExpr extends Expr {
  /** The node's discriminant. */
  readonly kind = 'Extension' as const;
  readonly #args: readonly Expr[];
  /**
   * Creates an `ExtensionExpr`.
   *
   * @param args - The arguments in positional order.
   * @param name - The symbolic name or names.
   */
  constructor(
    /** Class name used in the structural key and the default printers. */
    readonly name: string,
    args: readonly Expr[],
  ) {
    super();
    this.#args = args;
  }
  /**
   * Lists the operands of this expression node.
   *
   * @returns The argument sequence.
   */
  get args(): readonly Expr[] {
    return this.#args;
  }
  /**
   * Lists the symbolic operands visible to pattern searches, including tuple-valued arguments.
   *
   * @returns The resulting expressions in order.
   */
  searchArgs(): readonly Expr[] { return this.args; }

  /**
   * Rebuilds a node of the same class from replacement operands.
   *
   * @param args - The replacement arguments, in node order.
   * @returns The expression rebuilt with the new arguments.
   */
  abstract withArgs(args: readonly Expr[]): Expr;
  /**
   * Identifies nodes that support the structural operations of addition or multiplication.
   *
   * @returns `'Add'`, `'Mul'`, or `'none'`.
   */
  get assocOp(): 'Add' | 'Mul' | 'none' {
    return 'none';
  }
  /**
   * Indicates whether canonical ordering treats this node as an atom, sorting it by class and printed
   * form.
   *
   * @returns The atom-ordering flag.
   */
  get atomClass(): boolean {
    return false;
  }
  /**
   * Formats the node as text, using the function name and its arguments by default.
   *
   * @param print - The printer to use for child expressions.
   * @returns The formatted string.
   */
  printStr(print: (e: Expr) => string): string {
    return `${this.name}(${this.args.map(print).join(', ')})`;
  }
  /**
   * Formats the node as LaTeX, using operator notation by default.
   *
   * @param print - The printer to use for child expressions.
   * @returns The formatted string.
   */
  printLatex(print: (e: Expr) => string): string {
    return `\\operatorname{${this.name}}\\left(${this.args.map(print).join(', ')}\\right)`;
  }
  /**
   * Supplies the numeric value of an extension node to the requested decimal precision.
   *
   * @param _dps - The precision in decimal digits.
   * @returns A real or complex numeric expression when available.
   */
  numericValue(_dps: number): Expr | undefined {
    return undefined;
  }
  /**
   * Computes the derivative using the node's differentiation rule.
   *
   * @param _x - The differentiation variable.
   * @param _d - The callback for differentiating a subexpression.
   * @returns The derivative expression.
   */
  diffSelf(_x: Expr, _d: (e: Expr, x: Expr) => Expr): Expr | undefined {
    return undefined;
  }
  /**
   * Customizes numerical evaluation of an extension node using the supplied evaluator for its operands.
   *
   * @param _evalfArg - The callback for evaluating an argument numerically.
   * @param _dps - The precision in decimal digits.
   * @returns The specialized numeric expression when provided.
   */
  evalfSelf(_evalfArg: (e: Expr) => Expr, _dps: number): Expr | undefined {
    return undefined;
  }
  /**
   * Customizes trigonometric simplification of an extension node and its components.
   *
   * @param _trigsimp - The trigonometric simplifier for child expressions.
   * @returns The simplified expression when provided.
   */
  trigsimpSelf(_trigsimp: (e: Expr) => Expr): Expr | undefined {
    return undefined;
  }
  /**
   * Supplies the real and imaginary parts of an extension node.
   *
   * @returns The component pair when provided.
   */
  asRealImagSelf(): [Expr, Expr] | undefined {
    return undefined;
  }
  /**
   * Identifies the mathematical kind of an extension node.
   *
   * @returns The kind when provided.
   */
  kindSelf(): Kind | undefined {
    return undefined;
  }
  /**
   * Supplies an extension-specific transformation under adjunction, conjugation, or transposition.
   *
   * @returns The transformed expression when provided.
   */
  adjointSelf(): Expr | undefined {
    return undefined;
  }
  /**
   * Supplies a conjugation rule for the extension node.
   *
   * @returns The specialized result, or `undefined` to use the default behavior.
   */
  conjugateSelf(): Expr | undefined {
    return undefined;
  }
  /**
   * Supplies a transpose rule for the extension node.
   *
   * @returns The specialized result, or `undefined` to use the default behavior.
   */
  transposeSelf(): Expr | undefined {
    return undefined;
  }
  /**
   * Identifies free symbols explicitly for nodes with an opaque binding structure.
   *
   * @returns The free-symbol set when provided.
   */
  freeSymbolsSelf(): ReadonlySet<Expr> | undefined {
    return undefined;
  }
  /**
   * Identifies the argument positions that introduce bound variables and the arguments in their scope.
   *
   * @returns The binding and scope positions when provided.
   */
  bindings(): { variables: readonly number[]; scope: readonly number[] } | undefined {
    return undefined;
  }
  /**
   * Controls whether `doit` evaluates the operands before the node.
   *
   * @returns The recursive evaluation flag.
   */
  get doitDeep(): boolean {
    return true;
  }
  /**
   * Evaluates the extension node after its operands have been processed according to `doitDeep`.
   *
   * @returns The evaluated expression when provided.
   */
  doitSelf(): Expr | undefined {
    return undefined;
  }
  /**
   * Customizes substitution in the extension node using the supplied substitution operation.
   *
   * @param _old - The expression to replace.
   * @param _nw - The new expression.
   * @param _subs - The substitution callback for child expressions.
   * @returns The replacement expression when provided.
   */
  subsSelf(_old: Expr, _nw: Expr, _subs: (e: Expr) => Expr): Expr | undefined {
    return undefined;
  }
  /**
   * Matches the extension node as a pattern against the given expression.
   *
   * @param _expr - The input expression.
   * @returns The replacements or `false` for a handled mismatch.
   */
  matchesSelf(_expr: Expr): ReadonlyMap<Expr, Expr> | false | undefined {
    return undefined;
  }
  /**
   * Supplies an integration rule for this extension node over the given variable and optional limits.
   *
   * @param _x - The argument of the function.
   * @param _limits - The index and its inclusive lower and upper bounds.
   * @param _integrate - The integration callback for child expressions.
   * @returns The integral when provided.
   */
  integrateSelf(_x: Sym, _limits: readonly [Expr, Expr] | undefined, _integrate: (e: Expr) => Expr): Expr | undefined {
    return undefined;
  }
  /**
   * Customizes simplification of the extension node using the supplied simplifier for its operands.
   *
   * @param _simplify - The simplifier to apply to child expressions.
   * @returns The simplified expression when provided.
   */
  simplifySelf(_simplify: (e: Expr) => Expr): Expr | undefined {
    return undefined;
  }
  /**
   * Indicates whether the node is scalar for differentiation with respect to itself.
   *
   * @returns Whether the expression has scalar values.
   */
  get isScalar(): boolean {
    return true;
  }
  /**
   * Indicates whether derivatives with respect to a function argument can generate its Taylor series.
   *
   * @returns Whether a Taylor expansion in the argument is supported.
   */
  get isTaylorExpandable(): boolean {
    return false;
  }
  /**
   * Supplies an extension-specific answer about membership in the extended real numbers.
   *
   * @returns The known truth value when provided.
   */
  isRealSelf(): boolean | undefined {
    return undefined;
  }
  /**
   * Rewrites the node in terms of the requested target using its already rewritten arguments.
   *
   * @param _target - The target function or representation.
   * @param _args - The arguments in positional order.
   * @returns The rewritten expression when provided.
   */
  rewriteSelf(_target: string, _args: readonly Expr[]): Expr | undefined {
    return undefined;
  }
  /**
   * Customizes expansion of this node when it is the outermost expression.
   *
   * @param _hints - The additional options for the transformation.
   * @returns The expanded expression when provided.
   */
  expandTop(_hints: Readonly<Record<string, unknown>>): Expr | undefined {
    return undefined;
  }
  /**
   * Handles an extension-specific expansion hint on the node.
   *
   * @param _hint - The expansion rule to apply.
   * @param _hints - The additional options for the transformation.
   * @returns The hinted expansion when provided.
   */
  expandSelf(_hint: string, _hints: Readonly<Record<string, unknown>>): Expr | undefined {
    return undefined;
  }
  protected computeKey(): string {
    return `${this.name}(${this.args.map((a) => a.key).join(',')})`;
  }
}

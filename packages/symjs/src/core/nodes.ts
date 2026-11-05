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

import { InvariantError, NotImplementedError, NotLoadedError } from './errors';
import type { Kind } from './kind';
import { at } from './guard';
import { gcd } from './numbers';
import { type Mpf, fromNumber as mpfFromNumber, normalize as mpfNormalize, toNumber as mpfToNumber } from '../numeric/mpf';

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

/** Complex number value used by numeric evaluation. */
export interface ComplexValue {
  re: number;
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
}

/** Substitution specification. */
export type Substitution =
  | ReadonlyMap<Expr, ExprLike>
  | readonly (readonly [Expr, ExprLike])[]
  | Readonly<Record<string, ExprLike>>;

export interface Assumptions {
  readonly real?: boolean;
  readonly positive?: boolean;
  readonly nonnegative?: boolean;
  /** true for an integer symbol; false for a symbol known not to be an integer (SymPy integer=False). */
  readonly integer?: boolean;
  readonly negative?: boolean;
  readonly nonpositive?: boolean;
  /** false for non-commutative symbols (operators). */
  readonly commutative?: boolean;
  /** a point on the Riemann surface of the logarithm (SymPy polar=True). */
  readonly polar?: boolean;
  /**
   * false for a symbol known to be nonzero (SymPy zero=False), implied by positive, negative and
   * integer=false; true for a symbol known to be zero (SymPy zero=True), which implies integer,
   * nonnegative and nonpositive.
   */
  readonly zero?: boolean;
}

/** Function names known to the library. */
export type FnName =
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
  | 'bell'
  | 'fibonacci'
  | 'lucas'
  | 'tribonacci'
  | 'partition'
  | 'totient'
  | 'reduced_totient'
  | 'mobius'
  | 'divisor_sigma'
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
  diff(e: Expr, x: Expr, n: number): Expr;
  expand(e: Expr): Expr;
  simplify(e: Expr): Expr;
  evalf(e: Expr, n?: number | NumericValues, opts?: EvalfOptions): Expr;
  toComplex(e: Expr, values?: NumericValues): ComplexValue;
  rewrite?(e: Expr, target: string, opts?: { pattern?: readonly string[]; deep?: boolean }): Expr;
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
  /** SymPy sort_key order (a.sort_key() < b.sort_key() gives a negative number). */
  compareSortKey?(a: Expr, b: Expr): number;
  /** SymPy collect (registered by simplify/radsimp). */
  collect?(e: Expr, syms: readonly Expr[]): Expr;
  /** Leading term [c, e] of e ~ c*x**e as x -> 0+ (registered by series/series). */
  leadterm?(e: Expr, x: Sym): [Expr, Expr];
  /** The value of a sum or product with finite integer limits, for evalf (registered by calculus/doit); undefined when it is not a number. */
  evalConcrete?(c: Expr): Expr | undefined;
  /** Lambert W function (registered by functions/special). */
  lambertW?(x: Expr, k?: number): Expr;
  /** Pattern matching (registered by core/match). */
  match?(e: Expr, pattern: Expr): Map<Sym, Expr> | undefined;
  /**
   * SymPy Expr.equals(0) for a number: true when simplify gives 0 or the
   * minimal polynomial of an algebraic number is x, else undefined
   * (registered by simplify/simplify).
   */
  equalsZero?(e: Expr): true | undefined;
  /** SymPy radsimp (registered by simplify/sqrtdenest). */
  radsimp?(e: Expr): Expr;
  /** A named function applied with automatic evaluation (registered by functions/elementary). */
  fn?(name: FnName, args: readonly Expr[]): Expr;
  /** expand with only the mul hint (registered by simplify/expand). */
  expandMul?(e: Expr): Expr;
  /** as_real_imag of exp and functions (registered by simplify/expand). */
  asRealImagExpand?(e: Expr): [Expr, Expr];
  /**
   * Arithmetic of nodes that define their own operators (SymPy _op_priority,
   * as Quaternion does; installed by registerArithmetic): add, mul or pow
   * of the sympified arguments, or sub of the two operands of a - b, or
   * undefined for the generic rules.
   */
  arithmetic?(op: 'add' | 'sub' | 'mul' | 'pow', args: readonly Expr[]): Expr | undefined;
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
  /** A set node rebuilt from new arguments, evaluated (registered by sets/sets). */
  rebuildSet?: (e: Expr, args: readonly Expr[]) => Expr;
  /** SymPy Set._eval_subs: a set that binds a variable (ImageSet, ConditionSet) substituted, or undefined for the generic rule. */
  subsSet?: (e: Expr, old: Expr, nw: Expr, subs: (x: Expr) => Expr) => Expr | undefined;
  /** SymPy factor (set by the polys module). */
  factor?(e: Expr): Expr;
  /** SymPy fraction (registered by simplify/rational). */
  fraction?(e: Expr): [Expr, Expr];
  conjugate(e: Expr): Expr;
  abs(e: Expr): Expr;
  freeSymbols(e: Expr): Set<Sym>;
  integrate(e: Expr, x: Sym, limits?: [ExprLike, ExprLike]): Expr;
  /** Evaluate unevaluated objects when the calculus entry point is loaded. */
  doit?(e: Expr): Expr;
  limit(e: Expr, z: Sym, z0: ExprLike, dir?: '+' | '-' | '+-'): Expr;
  series(e: Expr, x: Sym, x0?: ExprLike, n?: number): Expr;
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

/** An item of fromiter's argument: an expression, or a number sympified. */
function fromiterItem(v: unknown): Expr {
  if (v instanceof Expr) return v;
  if (typeof v === 'number' || typeof v === 'bigint') return impl.sympify(v);
  throw new TypeError(`fromiter: cannot sympify ${String(v)}`);
}

export abstract class Expr {
  /**
   * SymPy `fromiter(args)`: the class applied to the items of args
   * (`Add.fromiter([x, y])` is x + y). Classes whose constructor SymPy calls
   * this way (Add, Mul, Pow, MatAdd, MatMul, ...) register it; others throw
   * NotImplementedError (SymPy's bare `Expr(x, y)` has no JavaScript counterpart).
   */
  static fromiter(this: abstract new (...args: never[]) => Expr, args: Iterable<unknown>): Expr {
    const build = fromiterBuilders.get(this);
    if (build === undefined) throw new NotImplementedError(`${this.name}.fromiter is not supported`);
    return build([...args].map(fromiterItem));
  }
  abstract readonly kind: ExprKind;
  abstract readonly args: readonly Expr[];
  #key: string | undefined;

  /** Structural key: two expressions are equal iff their keys are equal. */
  get key(): string {
    return (this.#key ??= this.computeKey());
  }

  protected abstract computeKey(): string;

  equals(other: ExprLike): boolean {
    const o = impl.sympify(other);
    return this === o || this.key === o.key;
  }

  get isNumber(): boolean {
    return false;
  }

  get isAtom(): boolean {
    return this.args.length === 0;
  }

  private _commutative?: boolean;
  /** False when the expression contains a non-commutative symbol in a product-like position. */
  get isCommutative(): boolean {
    this._commutative ??= this.computeCommutative();
    return this._commutative;
  }
  protected computeCommutative(): boolean {
    return this.args.every((a) => a.isCommutative);
  }

  // ---- fluent arithmetic -------------------------------------------------
  add(o: ExprLike): Expr {
    return impl.add(this, o);
  }
  sub(o: ExprLike): Expr {
    return impl.arithmetic?.('sub', [this, impl.sympify(o)]) ?? impl.add(this, impl.mul(-1, o));
  }
  mul(o: ExprLike): Expr {
    return impl.mul(this, o);
  }
  div(o: ExprLike): Expr {
    return impl.mul(this, impl.pow(o, -1));
  }
  pow(o: ExprLike): Expr {
    return impl.pow(this, o);
  }
  neg(): Expr {
    return impl.mul(-1, this);
  }

  // ---- manipulation --------------------------------------------------------
  subs(s: Substitution): Expr;
  subs(from: Expr, to: ExprLike): Expr;
  subs(a: Substitution | Expr, b?: ExprLike): Expr {
    if (a instanceof Expr) {
      if (b === undefined) throw new TypeError('subs(from, to) requires a replacement');
      return impl.subs(this, [[a, b]]);
    }
    return impl.subs(this, a);
  }
  diff(x: Expr, n = 1): Expr {
    return impl.diff(this, x, n);
  }
  /** Limit as z -> z0 (dir '+' by default, like SymPy). */
  limit(z: Sym, z0: ExprLike, dir: '+' | '-' | '+-' = '+'): Expr {
    return impl.limit(this, z, z0, dir);
  }
  /** Series expansion about x0 up to O((x - x0)**n). */
  series(x: Sym, x0: ExprLike = 0, n = 6): Expr {
    return impl.series(this, x, x0, n);
  }
  /** Indefinite integral w.r.t. x, or definite over [a, b] when limits are given. */
  integrate(x: Sym, limits?: [ExprLike, ExprLike]): Expr {
    return impl.integrate(this, x, limits);
  }
  expand(): Expr {
    return impl.expand(this);
  }
  simplify(): Expr {
    return impl.simplify(this);
  }
  conjugate(): Expr {
    return impl.conjugate(this);
  }
  /**
   * Numerically evaluate to `n` significant digits (default 15); symbols
   * without values stay symbolic. Passing values as the first argument is
   * shorthand for `evalf(15, { subs: values })`.
   */
  evalf(n?: number | NumericValues, opts?: EvalfOptions): Expr {
    return impl.evalf(this, n, opts);
  }
  /** Rewrite in terms of another function (SymPy `rewrite`), e.g. `sin(x).rewrite('exp')`. */
  rewrite(target: string, opts?: { pattern?: readonly string[]; deep?: boolean }): Expr {
    if (!impl.rewrite) notLoaded('rewrite', 'simplify');
    return impl.rewrite(this, target, opts);
  }
  /** Alias of evalf (SymPy `.n()`). */
  n(n?: number | NumericValues, opts?: EvalfOptions): Expr {
    return impl.evalf(this, n, opts);
  }
  /** Numerically evaluate to a complex value. All symbols must have values. */
  toComplex(values?: NumericValues): ComplexValue {
    return impl.toComplex(this, values);
  }
  /** Numerically evaluate to a real number (throws if the result is not real). */
  toNumber(values?: NumericValues, tol = 1e-12): number {
    const c = impl.toComplex(this, values);
    if (Math.abs(c.im) > tol * Math.max(1, Math.abs(c.re))) {
      throw new RangeError(`toNumber: value is not real (${c.re} + ${c.im}i)`);
    }
    return c.re;
  }
  freeSymbols(): Set<Sym> {
    return impl.freeSymbols(this);
  }
  has(sub: Expr): boolean {
    if (this.key === sub.key) return true;
    return this.args.some((a) => a.has(sub));
  }

  toString(): string {
    return impl.str(this);
  }
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

/** e as a Rational; throws InvariantError when it is not one (what names the value in the message). */
export function asRational(e: Expr, what = 'value'): Rational {
  if (!(e instanceof Rational)) throw new InvariantError(`${what} is not a Rational`);
  return e;
}

/** Exact rational number p/q (q > 0, gcd(p, q) = 1). Integers have q = 1. */
export class Rational extends Expr {
  readonly kind = 'Rational' as const;
  readonly args: readonly Expr[] = [];
  readonly p: bigint;
  readonly q: bigint;

  private constructor(p: bigint, q: bigint) {
    super();
    this.p = p;
    this.q = q;
  }

  static of(p: bigint | number, q: bigint | number = 1n): Rational {
    let P = BigInt(p);
    let Q = BigInt(q);
    if (Q === 0n) throw new RangeError('Rational: division by zero');
    if (Q < 0n) {
      P = -P;
      Q = -Q;
    }
    const g = gcd(P, Q);
    if (g > 1n) {
      P /= g;
      Q /= g;
    }
    return new Rational(P, Q);
  }

  get isNumber(): boolean {
    return true;
  }
  get isInteger(): boolean {
    return this.q === 1n;
  }
  get isZero(): boolean {
    return this.p === 0n;
  }
  get isOne(): boolean {
    return this.p === 1n && this.q === 1n;
  }
  get isNegative(): boolean {
    return this.p < 0n;
  }
  get isPositive(): boolean {
    return this.p > 0n;
  }
  get value(): number {
    return Number(this.p) / Number(this.q);
  }
  protected computeKey(): string {
    return this.q === 1n ? `${this.p}` : `${this.p}/${this.q}`;
  }
}

/** Floating-point number. */
export class Float extends Expr {
  readonly kind = 'Float' as const;
  readonly args: readonly Expr[] = [];
  /** Exact binary value man * 2**exp. */
  readonly mpf: Mpf;
  /** Binary precision in bits (53 for the default 15 digits). */
  readonly prec: number;
  /**
   * A float from a JS number (rounded to `prec` bits) or a raw mpf value.
   * @param prec binary precision; defaults to 53 (15 decimal digits).
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
  /** Nearest JS double. */
  get value(): number {
    return mpfToNumber(this.mpf);
  }
  get isNumber(): boolean {
    return true;
  }
  get isZero(): boolean {
    return this.mpf.man === 0n;
  }
  get isNegative(): boolean {
    return this.mpf.man < 0n;
  }
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

export type Num = Rational | Float;

export function isNum(e: Expr): e is Num {
  return e instanceof Rational || e instanceof Float;
}

/** A symbolic variable. */
export class Sym extends Expr {
  readonly kind = 'Symbol' as const;
  readonly args: readonly Expr[] = [];
  readonly assumptions: Assumptions;

  constructor(readonly name: string, assumptions: Assumptions = {}) {
    super();
    // like SymPy, any non-empty string is a valid name (e.g. symbols(':3') gives 0, 1, 2)
    if (typeof name !== 'string' || name.length === 0) {
      throw new SyntaxError(`Invalid symbol name: ${JSON.stringify(name)}`);
    }
    const positive = assumptions.positive === true;
    const negative = assumptions.negative === true;
    // SymPy: zero implies integer, real, nonnegative and nonpositive
    const zero = assumptions.zero === true && !positive && !negative;
    const integer = zero || assumptions.integer === true;
    const nonnegative = zero || positive || assumptions.nonnegative === true;
    const nonpositive = zero || negative || assumptions.nonpositive === true;
    const real = positive || negative || nonnegative || nonpositive || integer || assumptions.real === true;
    const a: { -readonly [K in keyof Assumptions]: Assumptions[K] } = {};
    if (real) a.real = true;
    if (positive) a.positive = true;
    if (nonnegative) a.nonnegative = true;
    if (negative) a.negative = true;
    if (nonpositive) a.nonpositive = true;
    if (integer) a.integer = true;
    // SymPy integer=False: is_integer is False, and so is is_zero (zero implies integer)
    else if (assumptions.integer === false) a.integer = false;
    if (assumptions.commutative === false) a.commutative = false;
    if (assumptions.polar === true) a.polar = true;
    if (zero) a.zero = true;
    else if (positive || negative || a.integer === false || assumptions.zero === false) a.zero = false;
    this.assumptions = Object.freeze(a);
  }

  protected computeCommutative(): boolean {
    return this.assumptions.commutative !== false;
  }

  /** The name as printed (Wild adds a trailing underscore, Dummy a leading one). */
  get printName(): string {
    return this.name;
  }

  /** SymPy class name in the sort key (a coordinate symbol, SymPy BaseScalar, sorts as its own class). */
  get sortClass(): string {
    return 'Symbol';
  }

  /** SymPy class_key priority in the sort key: 2 for an Atom, 5 for a Basic such as SymPy RandomSymbol. */
  get sortPriority(): number {
    return 2;
  }

  /**
   * subs and xreplace inside a symbol-like node that carries arguments
   * (SymPy RandomSymbol(symbol, pspace) substitutes in its probability
   * space), given the substitution of a subexpression; undefined for a plain
   * symbol, which has nothing inside.
   */
  substituteInner(_f: (e: Expr) => Expr): Expr | undefined {
    return undefined;
  }

  /**
   * Free symbols of a symbol-like node besides itself (SymPy
   * RandomIndexedSymbol X(t) also has t free); none for a plain symbol.
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
    return flags ? `$${this.name}[${flags}]` : `$${this.name}`;
  }
}

/** SymPy Dummy: a symbol that is distinct from every other symbol, printed with a leading underscore. */
export class Dummy extends Sym {
  private static counter = 0;
  readonly dummyIndex: number;
  constructor(name = 'Dummy', assumptions: Assumptions = {}, index?: number) {
    super(name, assumptions);
    this.dummyIndex = index ?? ++Dummy.counter;
  }
  get printName(): string {
    return `_${this.name}`;
  }
  protected computeKey(): string {
    return `${super.computeKey()}#${this.dummyIndex}`;
  }
}

/** Pattern symbol for match/replace; matches any expression not containing an excluded one. */
export class Wild extends Sym {
  readonly exclude: readonly Expr[];
  readonly properties: readonly ((e: Expr) => boolean)[];
  constructor(
    name: string,
    opts: { exclude?: readonly ExprLike[]; properties?: readonly ((e: Expr) => boolean)[] } & Assumptions = {},
  ) {
    const { exclude = [], properties = [], ...assumptions } = opts;
    super(name, assumptions);
    this.exclude = exclude.map((e) => impl.sympify(e));
    this.properties = properties;
  }
  get printName(): string {
    return `${this.name}_`;
  }
  protected computeKey(): string {
    return `?${super.computeKey()}[${this.exclude.map((e) => e.key).join(',')}]${this.properties.length ? `{${this.properties.length}}` : ''}`;
  }
}

/** Pattern matching an applied function (optionally with a given number of arguments). */
export class WildFunction extends Wild {
  constructor(name: string, readonly nargs?: readonly number[]) {
    super(name);
  }
  protected computeKey(): string {
    return `?F${this.name}[${this.nargs?.join(',') ?? ''}]`;
  }
}

export type ConstantName = 'pi' | 'E' | 'I' | 'EulerGamma' | 'Catalan' | 'GoldenRatio' | 'TribonacciConstant';

/** Mathematical constants: pi, E (Euler's number) and I (imaginary unit). */
export class Constant extends Expr {
  readonly kind = 'Constant' as const;
  readonly args: readonly Expr[] = [];
  constructor(readonly name: ConstantName) {
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
  readonly kind = 'Add' as const;
  constructor(readonly args: readonly Expr[]) {
    super();
  }
  protected computeKey(): string {
    return `+(${this.args.map((a) => a.key).join(',')})`;
  }
}

/** Product. Canonical: numeric coefficient first (if not 1), remaining factors sorted. @internal ctor */
export class Mul extends Expr {
  readonly kind = 'Mul' as const;
  constructor(readonly args: readonly Expr[]) {
    super();
  }
  protected computeKey(): string {
    return `*(${this.args.map((a) => a.key).join(',')})`;
  }
}

/** Power base^exp. `exp(x)` is represented as Pow(E, x). @internal ctor */
export class Pow extends Expr {
  readonly kind = 'Pow' as const;
  readonly args: readonly [Expr, Expr];
  constructor(base: Expr, exp: Expr) {
    super();
    this.args = [base, exp];
  }
  get base(): Expr {
    return this.args[0];
  }
  get exp(): Expr {
    return this.args[1];
  }
  protected computeKey(): string {
    return `^(${this.args[0].key},${this.args[1].key})`;
  }
}

/**
 * Application of a named function. @internal ctor
 *
 * @experimental May change in a minor release.
 */
export class Fn extends Expr {
  readonly kind = 'Fn' as const;
  constructor(readonly name: FnName, readonly args: readonly Expr[]) {
    super();
  }
  protected computeKey(): string {
    return `${this.name}(${this.args.map((a) => a.key).join(',')})`;
  }
}

export type SpecialName = 'oo' | '-oo' | 'zoo' | 'nan';

/** Extended values: oo, -oo, zoo (complex infinity) and nan. */
export class Special extends Expr {
  readonly kind = 'Special' as const;
  readonly args: readonly Expr[] = [];
  constructor(readonly name: SpecialName) {
    super();
  }
  get isInfinite(): boolean {
    return this.name !== 'nan';
  }
  protected computeKey(): string {
    return `%${this.name}`;
  }
}

/** Boolean constant (SymPy `true` / `false`). */
export class BoolAtom extends Expr {
  readonly kind = 'Bool' as const;
  readonly args: readonly Expr[] = [];
  constructor(readonly value: boolean) {
    super();
  }
  protected computeKey(): string {
    return this.value ? '!true' : '!false';
  }
}

export type RelOp = 'Eq' | 'Ne' | 'Lt' | 'Le' | 'Gt' | 'Ge';

/** Relation such as Ne(a, 0). Construct with `rel()` in `logic.ts`. @internal ctor */
export class Rel extends Expr {
  readonly kind = 'Rel' as const;
  readonly args: readonly [Expr, Expr];
  constructor(readonly op: RelOp, lhs: Expr, rhs: Expr) {
    super();
    this.args = [lhs, rhs];
  }
  get lhs(): Expr {
    return this.args[0];
  }
  get rhs(): Expr {
    return this.args[1];
  }
  protected computeKey(): string {
    return `${this.op}(${this.args[0].key},${this.args[1].key})`;
  }
}

/** Piecewise((expr, cond), ...). Args are stored flat: [e1, c1, e2, c2, ...]. @internal ctor */
export class Piecewise extends Expr {
  readonly kind = 'Piecewise' as const;
  constructor(readonly args: readonly Expr[]) {
    super();
  }
  get pairs(): [Expr, Expr][] {
    const out: [Expr, Expr][] = [];
    for (let i = 0; i < this.args.length; i += 2) out.push([at(this.args, i), at(this.args, i + 1)]);
    return out;
  }
  protected computeKey(): string {
    return `Piecewise(${this.args.map((a) => a.key).join(',')})`;
  }
}

/** Unevaluated integral: [f, x] (indefinite) or [f, x, a, b] (definite). @internal ctor */
export class Integral extends Expr {
  readonly kind = 'Integral' as const;
  constructor(readonly args: readonly Expr[]) {
    super();
  }
  get integrand(): Expr {
    return at(this.args, 0);
  }
  get variable(): Expr {
    return at(this.args, 1);
  }
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

/** Application of an undefined function, e.g. f(x). Create with `Function('f')`. */
export class UndefFn extends Expr {
  readonly kind = 'Undef' as const;
  constructor(readonly name: string, readonly args: readonly Expr[]) {
    super();
  }
  protected computeKey(): string {
    return `@${this.name}(${this.args.map((a) => a.key).join(',')})`;
  }
}

/**
 * Unevaluated derivative. args: [expr, v1, n1, v2, n2, ...] where ni are
 * positive integer counts (SymPy `variable_count`). @internal ctor
 */
export class Derivative extends Expr {
  readonly kind = 'Derivative' as const;
  constructor(readonly args: readonly Expr[]) {
    super();
  }
  get expr(): Expr {
    return at(this.args, 0);
  }
  get variableCount(): [Expr, number][] {
    const out: [Expr, number][] = [];
    for (let i = 1; i < this.args.length; i += 2) {
      out.push([at(this.args, i), Number(asRational(at(this.args, i + 1), 'derivative count').p)]);
    }
    return out;
  }
  protected computeKey(): string {
    return `D(${this.args.map((a) => a.key).join(',')})`;
  }
}

/** Unevaluated limit: args [e, z, z0]; dir is '+', '-' or '+-'. @internal ctor */
export class Limit extends Expr {
  readonly kind = 'Limit' as const;
  constructor(readonly args: readonly Expr[], readonly dir: '+' | '-' | '+-' = '+') {
    super();
  }
  /** The expression whose limit is taken. */
  get expr(): Expr {
    return at(this.args, 0);
  }
  /** The limit variable. */
  get variable(): Expr {
    return at(this.args, 1);
  }
  /** The point the variable approaches. */
  get point(): Expr {
    return at(this.args, 2);
  }
  protected computeKey(): string {
    return `Limit(${this.args.map((a) => a.key).join(',')},${this.dir})`;
  }
}

/**
 * Order term O(expr) as variable -> point. args: [expr, variable, point];
 * expr is a power of the variable (or of variable - point). @internal ctor
 */
export class Order extends Expr {
  readonly kind = 'Order' as const;
  constructor(readonly args: readonly Expr[]) {
    super();
  }
  get expr(): Expr {
    return at(this.args, 0);
  }
  get variable(): Expr | undefined {
    return this.args[1];
  }
  get point(): Expr | undefined {
    return this.args[2];
  }
  protected computeKey(): string {
    return `O(${this.args.map((a) => a.key).join(',')})`;
  }
}

// ---------------------------------------------------------------------------
// Singletons
// ---------------------------------------------------------------------------

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

export const pi = S.Pi;
export const E = S.E;
export const I = S.I;
export const oo = S.Infinity;
export const zoo = S.ComplexInfinity;
export const nan = S.NaN;

/** Canonical ordering of arguments: numbers first, then by structural key. */
export function compareExpr(a: Expr, b: Expr): number {
  const an = a.isNumber ? 0 : 1;
  const bn = b.isNumber ? 0 : 1;
  if (an !== bn) return an - bn;
  return a.key < b.key ? -1 : a.key > b.key ? 1 : 0;
}

// ---------------------------------------------------------------------------
// Type guards
// ---------------------------------------------------------------------------

export const isRational = (e: Expr): e is Rational => e instanceof Rational;
export const isFloat = (e: Expr): e is Float => e instanceof Float;
export const isSymbol = (e: Expr): e is Sym => e instanceof Sym;
export const isAdd = (e: Expr): e is Add => e instanceof Add;
export const isMul = (e: Expr): e is Mul => e instanceof Mul;
export const isPow = (e: Expr): e is Pow => e instanceof Pow;
export const isFn = (e: Expr, name?: FnName): e is Fn =>
  e instanceof Fn && (name === undefined || e.name === name);
export const isInteger = (e: Expr): e is Rational => e instanceof Rational && e.q === 1n;

/** SymPy is_Add: a sum, or a node whose SymPy class derives from Add (MatAdd). */
export const isAddLike = (e: Expr): boolean => e instanceof Add || (e instanceof ExtensionExpr && e.assocOp === 'Add');
/** SymPy is_Mul: a product, or a node whose SymPy class derives from Mul (MatMul). */
export const isMulLike = (e: Expr): boolean => e instanceof Mul || (e instanceof ExtensionExpr && e.assocOp === 'Mul');

/**
 * Base class for expression nodes defined outside the base module (extend
 * packages). Subclasses describe themselves through the methods below; the
 * base module calls them from rebuild/subs/xreplace, the str and LaTeX
 * printers, diff and adjoint/conjugate/transpose.
 */
export abstract class ExtensionExpr extends Expr {
  readonly kind = 'Extension' as const;
  constructor(
    /** Class name used in the structural key and the default printers. */
    readonly name: string,
    readonly args: readonly Expr[],
  ) {
    super();
  }
  /** A node of the same class with new arguments (required for traversals). */
  abstract withArgs(args: readonly Expr[]): Expr;
  /**
   * SymPy is_Add / is_Mul: 'Add' or 'Mul' for a node whose SymPy class derives from Add or Mul
   * (MatAdd, MatMul), whose arguments the structural methods (as_coeff_add, as_coeff_mul,
   * as_powers_dict, could_extract_minus_sign, count_ops, ...) then treat as terms or factors;
   * 'none' for other nodes.
   */
  get assocOp(): 'Add' | 'Mul' | 'none' {
    return 'none';
  }
  /**
   * True for a node whose SymPy class derives from Atom (Str, Permutation): it sorts with the
   * class key (2, 0, name) and by its printed form, like SymPy Atom.class_key and Atom.sort_key.
   */
  get atomClass(): boolean {
    return false;
  }
  /** str() form; defaults to Name(arg1, arg2, ...). */
  printStr(print: (e: Expr) => string): string {
    return `${this.name}(${this.args.map(print).join(', ')})`;
  }
  /** LaTeX form; defaults to \operatorname{Name}\left(...\right). */
  printLatex(print: (e: Expr) => string): string {
    return `\\operatorname{${this.name}}\\left(${this.args.map(print).join(', ')}\\right)`;
  }
  /** Derivative with respect to x, or undefined when unknown (diff then fails). */
  /**
   * A numeric value with at least `dps` correct digits as an expression of
   * Floats (and I), used by evalf; undefined when the node has no value.
   */
  numericValue(_dps: number): Expr | undefined {
    return undefined;
  }
  diffSelf(_x: Expr, _d: (e: Expr, x: Expr) => Expr): Expr | undefined {
    return undefined;
  }
  /**
   * SymPy _eval_evalf: this node evaluated to `dps` digits, given `evalfArg`
   * that evaluates a subexpression; undefined for the generic rule (the
   * arguments evaluated, then withArgs).
   */
  evalfSelf(_evalfArg: (e: Expr) => Expr, _dps: number): Expr | undefined {
    return undefined;
  }
  /**
   * SymPy _eval_trigsimp: trigsimp of this node, given `trigsimp` for a
   * subexpression (vectors simplify their components); undefined for the
   * generic rule.
   */
  trigsimpSelf(_trigsimp: (e: Expr) => Expr): Expr | undefined {
    return undefined;
  }
  /** SymPy as_real_imag of this node (MatrixExpr: (M + conj(M))/2, (M - conj(M))/(2*I)); undefined for the generic rule. */
  asRealImagSelf(): [Expr, Expr] | undefined {
    return undefined;
  }
  /** SymPy kind of this node (VectorKind of a vector, ...); undefined for the generic rule. */
  kindSelf(): Kind | undefined {
    return undefined;
  }
  /** Hermitian adjoint, conjugate and transpose; undefined keeps the generic unevaluated form. */
  adjointSelf(): Expr | undefined {
    return undefined;
  }
  conjugateSelf(): Expr | undefined {
    return undefined;
  }
  transposeSelf(): Expr | undefined {
    return undefined;
  }
  /**
   * Bound variables (SymPy bound_symbols): the argument positions holding
   * the variables and the positions of the arguments in which they are
   * bound. Bound variables are not free, and substituting one only changes
   * the other arguments. Undefined when the node binds nothing.
   */
  bindings(): { variables: readonly number[]; scope: readonly number[] } | undefined {
    return undefined;
  }
  /**
   * doit evaluates the arguments before the node (SymPy Basic.doit); false
   * for a node whose doit is not deep (SymPy Cross, Dot, Gradient, ...).
   */
  get doitDeep(): boolean {
    return true;
  }
  /** SymPy doit for this node, given its arguments already evaluated (unless doitDeep is false); undefined keeps it. */
  doitSelf(): Expr | undefined {
    return undefined;
  }
  /**
   * SymPy _eval_subs: this node with old replaced by nw, given `subs` that
   * substitutes in a subexpression; undefined for the generic rule
   * (substitution in the arguments, then withArgs).
   */
  subsSelf(_old: Expr, _nw: Expr, _subs: (e: Expr) => Expr): Expr | undefined {
    return undefined;
  }
  /**
   * SymPy _eval_Integral: the integral of this node over x (between the
   * limits when given), given `integrate` for a subexpression; undefined for
   * the generic integrator.
   */
  integrateSelf(_x: Sym, _limits: readonly [Expr, Expr] | undefined, _integrate: (e: Expr) => Expr): Expr | undefined {
    return undefined;
  }
  /**
   * SymPy simplify of this node, given `simplify` for a subexpression
   * (SymPy simplifies the arguments of a node that is not an Add, Mul or
   * Pow); undefined for the generic simplification.
   */
  simplifySelf(_simplify: (e: Expr) => Expr): Expr | undefined {
    return undefined;
  }
  /**
   * SymPy is_scalar. Differentiating a node with respect to itself gives 1
   * for a scalar and stays an unevaluated Derivative otherwise.
   */
  get isScalar(): boolean {
    return true;
  }
  /** SymPy is_extended_real of this node: true, false, or undefined when unknown. */
  isRealSelf(): boolean | undefined {
    return undefined;
  }
  /**
   * SymPy _eval_rewrite(rule, args): this node rewritten in terms of
   * `target` (a function or class name such as 'cos'), given its arguments
   * already rewritten; undefined keeps the node.
   */
  rewriteSelf(_target: string, _args: readonly Expr[]): Expr | undefined {
    return undefined;
  }
  /**
   * SymPy expand overridden by the node's class (Expectation.expand,
   * Variance.expand): the expansion of this node when it is the expression
   * being expanded; undefined for the generic expansion.
   */
  expandTop(_hints: Readonly<Record<string, unknown>>): Expr | undefined {
    return undefined;
  }
  /**
   * SymPy _eval_expand_<hint>: this node expanded by a hint the base module
   * does not know (expand(e, { double: true }) calls it with 'double'). The
   * arguments are already expanded when the expansion is deep; `hints`
   * holds every hint of the call (force, deep, ...). Undefined keeps the node.
   */
  expandSelf(_hint: string, _hints: Readonly<Record<string, unknown>>): Expr | undefined {
    return undefined;
  }
  protected computeKey(): string {
    return `${this.name}(${this.args.map((a) => a.key).join(',')})`;
  }
}

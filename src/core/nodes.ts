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

import { gcd } from './numbers';
import { type Mpf, fromNumber as mpfFromNumber, normalize as mpfNormalize, toNumber as mpfToNumber } from '../numeric/mpf';

export type Kind =
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
  | 'Set';

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
  readonly integer?: boolean;
}

/** Function names known to the library. */
export type FnName =
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
  | SpecialFnName;

/** Special and combinatorial functions (see functions/special.ts). */
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
  | 'Max';

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
  sign?(e: Expr): Expr;
  isReal?(e: Expr): boolean | undefined;
  rationalFromFloat?(f: Float): Rational;
  couldExtractMinusSign?(e: Expr): boolean;
  /** SymPy collect (registered by simplify/radsimp). */
  collect?(e: Expr, syms: readonly Expr[]): Expr;
  /** SymPy fraction (registered by simplify/rational). */
  fraction?(e: Expr): [Expr, Expr];
  conjugate(e: Expr): Expr;
  abs(e: Expr): Expr;
  freeSymbols(e: Expr): Set<Sym>;
  integrate(e: Expr, x: Sym, limits?: [ExprLike, ExprLike]): Expr;
  limit(e: Expr, z: Sym, z0: ExprLike, dir?: '+' | '-' | '+-'): Expr;
  series(e: Expr, x: Sym, x0?: ExprLike, n?: number): Expr;
}

export const impl: Impl = {} as Impl;

export abstract class Expr {
  abstract readonly kind: Kind;
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

  // ---- fluent arithmetic -------------------------------------------------
  add(o: ExprLike): Expr {
    return impl.add(this, o);
  }
  sub(o: ExprLike): Expr {
    return impl.add(this, impl.mul(-1, o));
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
    if (a instanceof Expr) return impl.subs(this, [[a, b as ExprLike]]);
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
    if (!impl.rewrite) throw new Error('rewrite is not available');
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
  constructor(value: number | Mpf, prec = 53) {
    super();
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
    if (!/^[A-Za-z_Ͱ-Ͽ][A-Za-z0-9_Ͱ-Ͽ']*$/.test(name)) {
      throw new SyntaxError(`Invalid symbol name: ${JSON.stringify(name)}`);
    }
    const positive = assumptions.positive === true;
    const integer = assumptions.integer === true;
    const nonnegative = positive || assumptions.nonnegative === true;
    const real = positive || nonnegative || integer || assumptions.real === true;
    const a: { -readonly [K in keyof Assumptions]: Assumptions[K] } = {};
    if (real) a.real = true;
    if (positive) a.positive = true;
    if (nonnegative) a.nonnegative = true;
    if (integer) a.integer = true;
    this.assumptions = Object.freeze(a);
  }

  /** The name as printed (Wild adds a trailing underscore, Dummy a leading one). */
  get printName(): string {
    return this.name;
  }

  protected computeKey(): string {
    const a = this.assumptions;
    const flags = `${a.real ? 'r' : ''}${a.nonnegative ? 'n' : ''}${a.positive ? 'p' : ''}${a.integer ? 'i' : ''}`;
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

/** Application of a named function. @internal ctor */
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

export const isSpecial = (e: Expr, name?: SpecialName): e is Special =>
  e instanceof Special && (name === undefined || e.name === name);

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
    for (let i = 0; i < this.args.length; i += 2) out.push([this.args[i]!, this.args[i + 1]!]);
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
    return this.args[0]!;
  }
  get variable(): Expr {
    return this.args[1]!;
  }
  get limits(): [Expr, Expr] | undefined {
    return this.args.length === 4 ? [this.args[2]!, this.args[3]!] : undefined;
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
    return this.args[0]!;
  }
  get variableCount(): [Expr, number][] {
    const out: [Expr, number][] = [];
    for (let i = 1; i < this.args.length; i += 2) {
      out.push([this.args[i]!, Number((this.args[i + 1] as Rational).p)]);
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
    return this.args[0]!;
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

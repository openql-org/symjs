// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Fourier series (SymPy sympy/series/fourier.py: fourier_series and
 * FourierSeries).
 */

import type { Expr, ExprLike } from '../core/nodes';
import { Dummy, Piecewise, Rational, Rel, S, Sym } from '../core/nodes';
import { add, mul, pow, sub, sympify } from '../core/ops';
import { and } from '../core/boolalg';
import { piecewise } from '../core/logic';
import { asIndependent } from '../core/methods';
import { SeqFormula } from './sequences';
import { piecewiseFold, subs } from '../core/traverse';
import { cos, fn, sin } from '../functions/elementary/elementary';
import { integrate } from '../integrals/integrate';
import { simplify } from '../simplify/simplify';
import { str } from '../printing/str';
import { at, cast } from '../core/guard';
import { interval, type SetExpr } from '../sets/sets';
import { SeriesBase } from './series_class';

const isZeroExpr = (e: Expr): boolean => e instanceof Rational && e.isZero;

/**
 * A0/2 + sum(an cos(n pi x / L) + bn sin(n pi x / L))
 * on the interval (a, b) with L = (b - a)/2. A series made by shift, scale,
 * shiftx or scalex keeps the coefficients of the original function and
 * transforms its terms.
 *
 * @see SymPy `sympy.series.fourier.FourierSeries`
 * @example
 * ```ts
 * import { ex, fourierSeries, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * const s = fourierSeries(ex`x**2`, x);
 * s.truncate(2); // => -4*cos(x) + pi**2/3
 * ```
 */
export class FourierSeries extends SeriesBase {
  /** The expression class name used when printing the series. */
  override readonly name = 'FourierSeries';
  private readonly L: Expr;
  /** The function whose coefficients are computed (fn itself unless transformed). */
  private readonly source: Expr;
  /** What x is replaced with in the terms (shiftx, scalex). */
  private readonly xmap: Expr;
  /** The factor of every term (scale). */
  private readonly factor: Expr;
  /** The constant added to the series (shift). */
  private readonly offset: Expr;
  /**
   * Constructs a new `FourierSeries`.
   *
   * @param fn - Function represented by the series.
   * @param x - Variable of the expansion.
   * @param a - Left endpoint of the period.
   * @param b - Right endpoint of the period.
   * @param transform - Source function and the accumulated change of argument, scale and offset.
   */
  constructor(
    /**
     * The function represented by the series.
     *
     * @see SymPy `sympy.series.fourier.FourierSeries.function`
     */
    readonly fn: Expr,
    /**
     * The independent variable of the series.
     *
     * @see SymPy `sympy.series.fourier.FourierSeries.x`
     */
    readonly x: Sym,
    /** The left endpoint of the Fourier interval. */
    readonly a: Expr,
    /** The right endpoint of the Fourier interval. */
    readonly b: Expr,
    transform?: { source: Expr; xmap: Expr; factor: Expr; offset: Expr },
  ) {
    super(fn, x, a, b, transform?.source ?? fn, transform?.xmap ?? x, transform?.factor ?? S.One, transform?.offset ?? S.Zero);
    this.L = mul(sub(b, a), Rational.of(1n, 2n));
    this.source = transform?.source ?? fn;
    this.xmap = transform?.xmap ?? x;
    this.factor = transform?.factor ?? S.One;
    this.offset = transform?.offset ?? S.Zero;
  }
  /**
   * Rebuilds this expression with the supplied operands.
   *
   * @param args - Replacement operands in the original order.
   * @returns The rebuilt expression.
   */
  override withArgs(args: readonly Expr[]): Expr {
    return new FourierSeries(at(args, 0), cast(at(args, 1), Sym), at(args, 2), at(args, 3), {
      source: at(args, 4), xmap: at(args, 5), factor: at(args, 6), offset: at(args, 7),
    });
  }
  /**
   * Formats the expression using the supplied expression printer.
   *
   * @param print - Printer used for the component expressions.
   * @returns A plain-text representation.
   */
  override printStr(print: (e: Expr) => string): string {
    const n = new Dummy('n');
    const [constant, dependent] = asIndependent(this.source, [this.x], { asAdd: false });
    const sequence = (trig: (e: Expr) => Expr): Expr => {
      const harmonic = trig(mul(n, S.Pi, this.x, pow(this.L, -1)));
      let integral = piecewiseFold(integrate(mul(dependent, harmonic), this.x, [this.a, this.b]));
      if (integral instanceof Piecewise) {
        const finite = and(new Rel('Gt', n, S.NegativeInfinity), new Rel('Lt', n, S.Infinity));
        integral = piecewise(...integral.pairs.map(([value, cond]) => [value, cond === S.true ? cond : and(finite, cond)] as const));
      }
      const term = mul(this.factor, constant, integral, trig(this.arg(n)), pow(this.L, -1));
      return SeqFormula(term, [term.equals(0) ? new Dummy('k') : n, S.One, S.Infinity]);
    };
    return `FourierSeries(${print(this.fn)}, (${print(this.x)}, ${print(this.a)}, ${print(this.b)}), (${print(this.a0())}, ${print(sequence(cos))}, ${print(sequence(sin))}))`;
  }
  /**
   * Specifies the range over which the Fourier expansion repeats.
   *
   * @returns The period endpoints.
   * @see SymPy `sympy.series.fourier.FourierSeries.period`
   */
  get period(): readonly [Expr, Expr] { return [this.a, this.b]; }
  /**
   * Extracts the first term of the represented function's expansion.
   *
   * @returns The first nonzero asymptotic term.
   * @see SymPy `sympy.series.fourier.FourierSeries.as_leading_term`
   */
  asLeadingTerm(): Expr { return this.truncate(1); }
  /**
   * Applies substitution rules specific to this series.
   *
   * @param old - Expression being replaced.
   * @returns The replacement expression when this hook supplies one.
   */
  override subsSelf(old: Expr): Expr | undefined {
    return old.has(this.x) ? this : undefined;
  }
  /**
   * Adds the series to the other operand.
   *
   * @param other - Other operand.
   * @returns The sum.
   * @throws RangeError when the two Fourier periods differ.
   */
  override add(other: ExprLike): Expr {
    if (!(other instanceof FourierSeries)) return super.add(other);
    if (!this.a.equals(other.a) || !this.b.equals(other.b)) throw new RangeError('Both series should have the same period');
    const rename = (e: Expr) => subs(e, [[other.x, this.x]]);
    if (!this.xmap.equals(rename(other.xmap))) return super.add(other);
    const source = add(mul(this.factor, this.source), rename(mul(other.factor, other.source)));
    const offset = add(this.offset, rename(other.offset));
    if (!source.has(this.x)) return add(source, offset);
    return new FourierSeries(add(this.fn, rename(other.fn)), this.x, this.a, this.b, {
      source, xmap: this.xmap, factor: S.One, offset,
    });
  }
  /**
   * Subtracts the supplied operand from the series.
   *
   * @param other - Other operand.
   * @returns The difference.
   */
  override sub(other: ExprLike): Expr {
    return other instanceof FourierSeries ? this.add(other.neg()) : super.sub(other);
  }
  /**
   * Negates the Fourier series.
   *
   * @returns The additive inverse.
   */
  override neg(): FourierSeries { return this.scale(-1); }
  /**
   * Specifies the index range of the terms, including both endpoints.
   *
   * @returns The index interval.
   * @see SymPy `sympy.series.fourier.FourierSeries.interval`
   */
  override get interval(): SetExpr { return interval(0, S.Infinity); }
  /**
   * Identifies the first index at which a term is defined.
   *
   * @returns The starting index.
   * @see SymPy `sympy.series.fourier.FourierSeries.start`
   */
  override get start(): Expr { return S.Zero; }
  /**
   * Identifies the final index in the series or sequence.
   *
   * @returns The ending index.
   * @see SymPy `sympy.series.fourier.FourierSeries.stop`
   */
  override get stop(): Expr { return S.Infinity; }
  /**
   * Counts the terms in the index interval, allowing an infinite range.
   *
   * @returns The term count or infinity.
   * @see SymPy `sympy.series.fourier.FourierSeries.length`
   */
  override get length(): Expr { return S.Infinity; }

  private arg(k: ExprLike): Expr {
    return mul(k, S.Pi, this.xmap, pow(this.L, -1));
  }
  private coefficient(k: ExprLike, trig: (e: Expr) => Expr): Expr {
    const v = integrate(mul(this.source, trig(mul(k, S.Pi, this.x, pow(this.L, -1)))), this.x, [this.a, this.b]);
    return simplify(mul(v, pow(this.L, -1)));
  }
  /**
   * Computes the contribution of the zero-frequency Fourier mode.
   *
   * @returns The constant coefficient `a0/2`.
   * @see SymPy `sympy.series.fourier.FourierSeries.a0`
   */
  a0(): Expr {
    const c = simplify(mul(integrate(this.source, this.x, [this.a, this.b]), Rational.of(1n, 2n), pow(this.L, -1)));
    return add(mul(c, this.factor), this.offset);
  }
  /**
   * Obtains the cosine coefficient for a positive harmonic index.
   *
   * @param k - Coefficient index.
   * @returns The coefficient at order `k`.
   * @see SymPy `sympy.series.fourier.FourierSeries.an`
   */
  an(k: ExprLike): Expr {
    return mul(this.coefficient(k, cos), this.factor);
  }
  /**
   * Obtains the sine coefficient for a positive harmonic index.
   *
   * @param k - Coefficient index.
   * @returns The coefficient at order `k`.
   * @see SymPy `sympy.series.fourier.FourierSeries.bn`
   */
  bn(k: ExprLike): Expr {
    return mul(this.coefficient(k, sin), this.factor);
  }
  /** The terms of order k (k = 0 is the constant term). */
  protected override evalTerm(k: Expr): Expr {
    if (isZeroExpr(k)) return this.a0();
    return add(mul(this.an(k), cos(this.arg(k))), mul(this.bn(k), sin(this.arg(k))));
  }
  /**
   * Adds the first requested nonzero terms of the Fourier series.
   *
   * @param n - Number of nonzero terms to retain.
   * @returns The truncated Fourier sum.
   * @see SymPy `sympy.series.fourier.FourierSeries.truncate`
   * @example
   * ```ts
   * import { fourierSeries, symbols } from '@symjs/symjs';
   *
   * const [x] = symbols('x');
   * const s = fourierSeries(x, x);
   * s.truncate(4); // => 2*sin(x) - sin(2*x) + 2*sin(3*x)/3 - sin(4*x)/2
   * ```
   */
  truncate(n = 3): Expr {
    const out: Expr[] = [];
    for (let k = 0; out.length < n && k < 64 + n * 4; k++) {
      const t = this.term(k);
      if (!isZeroExpr(t)) out.push(t);
    }
    return add(...out);
  }
  private transformed(fnew: Expr, change: Partial<{ xmap: Expr; factor: Expr; offset: Expr }>): FourierSeries {
    return new FourierSeries(fnew, this.x, this.a, this.b, {
      source: this.source,
      xmap: change.xmap ?? this.xmap,
      factor: change.factor ?? this.factor,
      offset: change.offset ?? this.offset,
    });
  }
  private independent(s: ExprLike): Expr {
    const v = sympify(s);
    if (v.has(this.x)) throw new RangeError(`'${str(v)}' should be independent of ${str(this.x)}`);
    return v;
  }
  /**
   * Adds a constant to the function represented by the Fourier series.
   *
   * @param s - Shift or scale factor.
   * @returns The Fourier series with the added constant.
   * @see SymPy `sympy.series.fourier.FourierSeries.shift`
   */
  shift(s: ExprLike): FourierSeries {
    const v = this.independent(s);
    return this.transformed(add(this.fn, v), { offset: add(this.offset, v) });
  }
  /**
   * Multiplies the function represented by the Fourier series by a scalar.
   *
   * @param s - Shift or scale factor.
   * @returns The scaled Fourier series.
   * @see SymPy `sympy.series.fourier.FourierSeries.scale`
   */
  scale(s: ExprLike): FourierSeries {
    const v = this.independent(s);
    return this.transformed(mul(this.fn, v), { factor: mul(this.factor, v), offset: mul(this.offset, v) });
  }
  /**
   * Translates the argument of the function represented by the Fourier series.
   *
   * @param s - Shift or scale factor.
   * @returns The Fourier series of the translated argument.
   * @see SymPy `sympy.series.fourier.FourierSeries.shiftx`
   */
  shiftx(s: ExprLike): FourierSeries {
    const v = this.independent(s);
    return this.transformed(subs(this.fn, [[this.x, add(this.x, v)]]), { xmap: subs(this.xmap, [[this.x, add(this.x, v)]]) });
  }
  /**
   * Scales the argument of the function represented by the Fourier series.
   *
   * @param s - Shift or scale factor.
   * @returns The Fourier series of the scaled argument.
   * @see SymPy `sympy.series.fourier.FourierSeries.scalex`
   */
  scalex(s: ExprLike): FourierSeries {
    const v = this.independent(s);
    return this.transformed(subs(this.fn, [[this.x, mul(this.x, v)]]), { xmap: subs(this.xmap, [[this.x, mul(this.x, v)]]) });
  }
  /**
   * Computes the order-`n` sigma approximation by weighting harmonics below `n` with the Lanczos factor.
   *
   * @param n - Harmonic cutoff (exclusive).
   * @returns The sigma approximation of order n.
   * @see SymPy `sympy.series.fourier.FourierSeries.sigma_approximation`
   * @example
   * ```ts
   * import { fourierSeries, symbols } from '@symjs/symjs';
   *
   * const [x] = symbols('x');
   * const s = fourierSeries(x, x);
   * s.sigmaApproximation(4); // => 2*sin(x)*sinc(pi/4) - 2*sin(2*x)/pi + 2*sin(3*x)*sinc(3*pi/4)/3
   * ```
   */
  sigmaApproximation(n = 3): Expr {
    const out: Expr[] = [];
    for (let k = 0; k < n; k++) {
      const t = this.term(k);
      if (!isZeroExpr(t)) out.push(mul(fn('sinc', [mul(S.Pi, Rational.of(k, n))]), t));
    }
    return add(...out);
  }
}

/**
 * Constructs the Fourier series on the specified interval, defaulting to the interval from minus pi to
 * pi.
 *
 * @param ex - Expression to expand or evaluate.
 * @param x - Variable of the expansion.
 * @param limits - Lower and upper endpoints of the interval.
 * @returns The Fourier series, or the constant expression itself.
 * @throws RangeError when the variable is ambiguous or invalid, or an endpoint is infinite.
 * @see SymPy `sympy.series.fourier.fourier_series`
 * @example
 * ```ts
 * import { ex, fourierSeries, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * fourierSeries(ex`x**2`, x).truncate(3); // => -4*cos(x) + cos(2*x) + pi**2/3
 * ```
 */
export function fourierSeries(ex: ExprLike, x: Sym, limits?: readonly [ExprLike, ExprLike]): FourierSeries;
export function fourierSeries(ex: ExprLike, x: undefined, limits?: readonly [ExprLike, ExprLike]): Expr;
export function fourierSeries(ex: ExprLike, variable: Sym | undefined, limits: readonly [ExprLike, ExprLike] = [S.Pi.neg(), S.Pi]): Expr {
  const e = sympify(ex);
  const free = [...e.freeSymbols()];
  if (!variable && free.length > 1) throw new RangeError('Specify the Fourier series variable');
  const x = variable ?? free[0];
  if (variable !== undefined && !(variable instanceof Sym)) throw new RangeError('Fourier series variable must be a symbol');
  if (limits.some((end) => sympify(end) === S.Infinity || sympify(end) === S.NegativeInfinity)) throw new RangeError('Fourier series requires finite bounds');
  if (!(x instanceof Sym)) return e;
  return new FourierSeries(e, x, sympify(limits[0]), sympify(limits[1]));
}

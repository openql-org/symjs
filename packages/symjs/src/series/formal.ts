// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Formal power series (SymPy sympy/series/formal.py: fps and
 * FormalPowerSeries).
 */

import type { Expr, ExprLike } from '../core/nodes';
import { Add, Derivative, Dummy, Fn, Mul, Order, Pow, Rational, S, Special, Sym, UndefFn } from '../core/nodes';
import { add, couldExtractMinusSign, exp, mul, pow, sub, sympify } from '../core/ops';
import { asIndependent, asNumerDenom, isMeromorphic, isPolynomial, isRationalFunction } from '../core/methods';
import { NotImplementedError } from '../core/errors';
import { at, cast, expectType, first, getOrThrow } from '../core/guard';
import type { UndefinedFunction } from '../core/undef';
import { cancel, fraction } from '../simplify/rational';
import { freeSymbols, some, subs, xreplace } from '../core/traverse';
import { diff } from '../calculus/diff';
import { fn } from '../functions/elementary/elementary';
import { expand } from '../simplify/expand';
import { factorTerms } from '../simplify/exprtools';
import { powsimp } from '../simplify/powsimp';
import { integrate } from '../integrals/integrate';
import { polyCoefficients } from '../polys/poly';
import { str } from '../printing/str';
import { O, series, asLeadingTerm } from './series';
import { lseries, seriesTerms } from './lseries';

import { Matrix } from '../matrices/matrix';
import { nullspace } from '../matrices/linalg';
import { Poly } from '../polys/sympoly';
import { rootsDict } from '../polys/poly';
import { SymFunction } from '../core/undef';
import { NoMatch, isNoMatch } from '../core/truth';
import type { NoMatchResult } from '../core/truth';
import { Eq, piecewise } from '../core/logic';
import { Mod } from '../functions/mod';
import { interval, type SetExpr } from '../sets/sets';
import { Concrete } from '../core/concrete';
import { SeriesBase } from './series_class';
import { apart } from '../polys/partfrac';
import { AccumBoundsNode } from '../core/accumbounds';
import { limit } from './limits';
import { doit } from '../calculus/doit';

/**
 * Coefficients of a rational function, or of a function with a rational derivative.
 *
 * @param f - Function to expand.
 * @param x - Variable of the expansion.
 * @param k - Coefficient index.
 * @param order - Maximum differential order to consider.
 * @param full - Use full partial-fraction decomposition.
 * @returns The coefficient formula, independent part and starting index, or `NoMatch`.
 * @see SymPy `sympy.series.formal.rational_algorithm`
 * @example
 * ```ts
 * import { ex, rationalAlgorithm, symbols } from '@symjs/symjs';
 *
 * const [x, k] = symbols('x k');
 * rationalAlgorithm(ex`1/(1-x)`, x, k); // => [1, 0, 0]
 * ```
 */
export function rationalAlgorithm(f: ExprLike, x: Sym, k: Sym, order = 4, full = false): [Expr, Expr, number] | NoMatchResult {
  let derivative = sympify(f);
  const derivatives: Expr[] = [];
  for (let i = 0; i <= order; i++) {
    if (i) derivative = diff(derivative, x);
    if (!isRationalFunction(derivative, [x])) {
      derivatives.push(derivative);
      continue;
    }
    const decomposition = doit(apart(derivative, x, { full }));
    let coefficient: Expr = S.Zero;
    let independent: Expr = S.Zero;
    for (const term of decomposition instanceof Add ? decomposition.args : [decomposition]) {
      let [numerator, denominator] = asNumerDenom(term);
      if (!denominator.has(x)) {
        independent = add(independent, term);
        continue;
      }
      const [constant, dependent] = asIndependent(denominator, [x], { asAdd: false });
      numerator = mul(numerator, pow(constant, -1));
      denominator = dependent;
      const [base, multiplicity] = denominator instanceof Pow ? [denominator.base, denominator.exp] : [denominator, S.One];
      const polynomial = Poly.from(base, [x]);
      if (polynomial.degree() > 1) return NoMatch;
      const a = polynomial.nth(0);
      if (isZeroExpr(a)) {
        independent = add(independent, term);
        continue;
      }
      const slope = polynomial.nth(1);
      const root = mul(-1, a, pow(slope, -1));
      const j = expectType(multiplicity, (value): value is Rational => value instanceof Rational);
      let binomial: Expr = S.One;
      for (let n = 1; n < Number(j.p); n++) binomial = mul(binomial, add(k, n), Rational.of(1, n));
      coefficient = add(coefficient, mul(pow(-1, j), numerator, pow(slope, mul(-1, j)), binomial, pow(root, mul(-1, add(j, k)))));
    }
    if (isZeroExpr(coefficient)) return NoMatch;
    for (let j = 0; j < i; j++) {
      coefficient = mul(coefficient, pow(add(k, j + 1), -1));
      independent = integrate(independent, x);
      independent = add(independent, limit(sub(at(derivatives, i - j - 1), independent), x, 0));
    }
    return [subs(coefficient, [[k, add(k, -i)]]), independent, i];
  }
  return NoMatch;
}

const isZeroExpr = (e: Expr): boolean => e instanceof Rational && e.isZero;

/**
 * Group terms whose quotients are rational functions of x.
 *
 * @param terms - Terms to group by rational dependence.
 * @param x - Variable of the expansion.
 * @returns One sum per group of rationally dependent terms.
 * @see SymPy `sympy.series.formal.rational_independent`
 * @example
 * ```ts
 * import { ex, rationalIndependent, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * rationalIndependent([ex`cos(x)`, ex`sin(x)`], x); // => [cos(x), sin(x)]
 * ```
 */
export function rationalIndependent(terms: readonly ExprLike[], x: Sym): Expr[] {
  const independent: Expr[] = [];
  for (const term of terms.map(sympify)) {
    const n = asIndependent(term, [x])[1];
    const i = independent.findIndex((d) => isRationalFunction(cancel(mul(n, pow(asIndependent(d, [x])[1], -1))), [x]));
    if (i < 0) independent.push(term);
    else independent[i] = add(at(independent, i), term);
  }
  return independent;
}

function differentialRecurrence(DE: ExprLike, r: UndefinedFunction, k: Sym, ordinary: boolean): Expr {
  const e = expand(sympify(DE));
  const terms = e instanceof Add ? e.args : [e];
  const parts: { c: Expr; order: number; power: number }[] = [];
  for (const term of terms) {
    const factors = term instanceof Mul ? term.args : [term];
    const dependent = factors.filter((f) => f instanceof UndefFn || f instanceof Derivative);
    if (dependent.length !== 1) throw new TypeError('recurrence: a linear homogeneous differential equation is required');
    const d = at(dependent, 0);
    const f = cast(d instanceof Derivative ? d.expr : d, UndefFn);
    const x = cast(at(f.args, 0), Sym);
    const order = d instanceof Derivative ? d.variableCount.reduce((a, [, j]) => a + j, 0) : 0;
    const coefficient = mul(...factors.filter((a) => a !== d));
    if (ordinary) {
      const powers = polyCoefficients(coefficient, x);
      if (powers === undefined) throw new TypeError('hyperRe: polynomial differential coefficients required');
      for (const [power, c] of powers) parts.push({ c, order, power });
    } else {
      if (coefficient.has(x)) throw new TypeError('expRe: constant differential coefficients required');
      parts.push({ c: coefficient, order, power: 0 });
    }
  }
  const shift = Math.min(...parts.map((p) => p.order - p.power));
  return add(...parts.map(({ c, order, power }) => mul(c,
    ...(ordinary ? Array.from({ length: order }, (_, j) => add(k, 1 - power - shift + j)) : []),
    r(add(k, order - power - shift)))));
}

/**
 * Convert a constant-coefficient differential equation to an exponential-series recurrence.
 *
 * @param DE - Linear differential equation, written as an expression equal to zero.
 * @param r - Function representing the sequence of coefficients.
 * @param k - Coefficient index.
 * @returns The recurrence for the exponential-series coefficients.
 * @throws TypeError when the equation is not linear and homogeneous with constant coefficients.
 * @see SymPy `sympy.series.formal.exp_re`
 * @example
 * ```ts
 * import { Derivative, SymFunction, expRe, symbols } from '@symjs/symjs';
 *
 * const [x, k] = symbols('x k');
 * const f = SymFunction('f'), r = SymFunction('r');
 * expRe(Derivative(f(x), x).sub(f(x)), r, k); // => -r(k) + r(k + 1)
 * ```
 */
export function expRe(DE: ExprLike, r: UndefinedFunction, k: Sym): Expr {
  return differentialRecurrence(DE, r, k, false);
}

/**
 * Convert a polynomial-coefficient differential equation to an ordinary-series recurrence.
 *
 * @param DE - Linear differential equation, written as an expression equal to zero.
 * @param r - Function representing the sequence of coefficients.
 * @param k - Coefficient index.
 * @returns The recurrence for ordinary power-series coefficients.
 * @throws TypeError when the equation is not linear and homogeneous with polynomial coefficients.
 * @see SymPy `sympy.series.formal.hyper_re`
 * @example
 * ```ts
 * import { Derivative, SymFunction, hyperRe, symbols } from '@symjs/symjs';
 *
 * const [x, k] = symbols('x k');
 * const f = SymFunction('f'), r = SymFunction('r');
 * hyperRe(Derivative(f(x), x).sub(f(x)), r, k); // => (k + 1)*r(k + 1) - r(k)
 * ```
 */
export function hyperRe(DE: ExprLike, r: UndefinedFunction, k: Sym): Expr {
  return differentialRecurrence(DE, r, k, true);
}

/**
 * The power series of a function, truncated on request.
 *
 * @see SymPy `sympy.series.formal.FormalPowerSeries`
 * @example
 * ```ts
 * import { ex, fps, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * const f = fps(ex`log(1 + x)`, x);
 * f.coeff(3); // => 1/3
 * ```
 */
export class FormalPowerSeries extends SeriesBase {
  /** The expression class name used when printing the series. */
  override readonly name = 'FormalPowerSeries';
  /** The factor of the function free of x but with other symbols (x**n), kept out of the expansion (SymPy symb). */
  private readonly symb: Expr;
  /** The function without that factor. */
  private readonly core: Expr;
  /**
   * Constructs a new `FormalPowerSeries`.
   *
   * @param fn - Function represented by the series.
   * @param x - Variable of the expansion.
   * @param x0 - Point about which to expand.
   * @param direction - Side from which the variable approaches the point.
   */
  constructor(
    /**
     * The function represented by the series.
     *
     * @see SymPy `sympy.series.formal.FormalPowerSeries.function`
     */
    readonly fn: Expr,
    /**
     * The independent variable of the series.
     *
     * @see SymPy `sympy.series.formal.FormalPowerSeries.x`
     */
    readonly x: Sym,
    /**
     * The expansion point.
     *
     * @see SymPy `sympy.series.formal.FormalPowerSeries.x0`
     */
    readonly x0: Expr,
    /**
     * The direction of approach to the expansion point.
     *
     * @see SymPy `sympy.series.formal.FormalPowerSeries.dir`
     */
    readonly direction: '+' | '-',
  ) {
    super(fn, x, x0, direction === '+' ? 1 : -1);
    // SymPy _compute_fps: (f, symb) = expand(f).as_independent(*syms) for the symbols other than x
    const others = [...freeSymbols(fn)].filter((s) => s instanceof Sym).filter((s) => s.key !== x.key);
    const [core, symb] = others.length && !(fn instanceof Add) ? asIndependent(expand(fn), others) : [fn, S.One];
    // A sum can share a symbolic power even when its integer offsets differ.
    const base = x0 instanceof Special ? x : sub(x, x0);
    const powers = fn instanceof Add ? fn.args.map((term) => (term instanceof Mul ? term.args : [term])
      .find((f): f is Pow => f instanceof Pow && f.base.equals(base) && f.exp.freeSymbols().size > 0 && !f.exp.has(x))) : [];
    const firstPower = powers[0];
    if (fn instanceof Add && firstPower && powers.every((p): p is Pow => p !== undefined)) {
      const offsets = powers.map((p) => sub(p.exp, firstPower.exp));
      if (offsets.every((v): v is Rational => v instanceof Rational && v.isInteger)) {
        const offset = Math.max(...offsets.map((v) => v.value));
        this.symb = pow(base, add(firstPower.exp, offset));
        this.core = add(...fn.args.map((term, i) => mul(...(term instanceof Mul ? term.args : [term]).filter((f) => f !== powers[i]), pow(base, sub(at(offsets, i), offset)))));
        return;
      }
    }
    this.core = core;
    this.symb = symb;
  }
  /**
   * Rebuilds this expression with the supplied operands.
   *
   * @param args - Replacement operands in the original order.
   * @returns The rebuilt expression.
   */
  override withArgs(args: readonly Expr[]): Expr {
    return new FormalPowerSeries(at(args, 0), cast(at(args, 1), Sym), at(args, 2), at(args, 3).key === S.One.key ? '+' : '-');
  }
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
   * Extracts the first term of the represented function's expansion.
   *
   * @returns The first nonzero asymptotic term.
   * @see SymPy `sympy.series.formal.FormalPowerSeries.as_leading_term`
   */
  asLeadingTerm(): Expr { return asLeadingTerm(this.fn, this.x); }
  /**
   * Specifies the index range of the terms, including both endpoints.
   *
   * @returns The index interval.
   * @see SymPy `sympy.series.formal.FormalPowerSeries.interval`
   */
  override get interval(): SetExpr { return interval(0, S.Infinity); }
  /**
   * Identifies the first index at which a term is defined.
   *
   * @returns The starting index.
   * @see SymPy `sympy.series.formal.FormalPowerSeries.start`
   */
  override get start(): Expr { return S.Zero; }
  /**
   * Identifies the final index in the series or sequence.
   *
   * @returns The ending index.
   * @see SymPy `sympy.series.formal.FormalPowerSeries.stop`
   */
  override get stop(): Expr { return S.Infinity; }
  /**
   * Counts the terms in the index interval, allowing an infinite range.
   *
   * @returns The term count or infinity.
   * @see SymPy `sympy.series.formal.FormalPowerSeries.length`
   */
  override get length(): Expr { return S.Infinity; }

  /** The term of order k, retaining zero terms and the independent part at zero. */
  protected override evalTerm(pt: Expr): Expr {
    if (!(pt instanceof Rational) || !pt.isInteger || !Number.isSafeInteger(Number(pt.p))) {
      throw new TypeError('formal power series term index must be a safe integer');
    }
    const k = Number(pt.p);
    const lower = new Set(k === 0 ? [] : seriesTerms(this.core, this.x, this.x0, k, this.direction).terms.map((t) => t.key));
    return add(...seriesTerms(this.core, this.x, this.x0, k + 1, this.direction).terms.filter((t) => !lower.has(t.key)).map((t) => this.withSymb(t)));
  }

  /**
   * Formats the infinite power-series representation in LaTeX.
   *
   * @param print - Printer used for the component expressions.
   * @returns The LaTeX representation.
   */
  printLatex(print: (e: Expr) => string): string {
    return print(this.infinite);
  }
  /**
   * Combines the recurrent coefficient sum with the terms preceding the recurrence.
   *
   * @returns The full series expression.
   * @throws NotImplementedError when no coefficient formula is available.
   * @see SymPy `sympy.series.formal.FormalPowerSeries.infinite`
   */
  get infinite(): Expr {
    const k = new Dummy('k');
    const step = this.direction === '+' ? 1 : -1;
    const shift = mul(step, sub(this.x, this.x0));
    const local = subs(this.core, [[this.x, add(this.x0, mul(step, this.x))]]);
    let recurrence = rationalAlgorithm(local, this.x, k);
    if (isNoMatch(recurrence)) recurrence = hyperAlgorithm(local, this.x, k);
    if (isNoMatch(recurrence)) throw new NotImplementedError('No coefficient formula for this formal series');
    const [ak, independent, start] = recurrence;
    const term = this.withSymb(mul(ak, pow(shift, k)));
    return add(this.withSymb(subs(independent, [[this.x, shift]])), new Concrete('Sum', [term, k, Rational.of(start), S.Infinity]));
  }
  /**
   * Truncates the series at the requested order about the expansion point.
   *
   * @param n - Truncation order.
   * @returns The truncated expansion.
   * @see SymPy `sympy.series.formal.FormalPowerSeries.truncate`
   */
  truncate(n = 6): Expr {
    if (this.symb.key === S.One.key) {
      const s = series(this.fn, this.x, this.x0, n, this.direction, { algebraic: true });
      if (this.x0 === S.NegativeInfinity) {
        return xreplace(s, [[S.NegativeInfinity, S.Infinity]]);
      }
      if (isPolynomial(this.fn, [this.x])) return add(s, O(pow(sub(this.x, this.x0), n), this.x, this.x0));
      return s;
    }
    if (this.x0 === S.Infinity) {
      const body = series(this.core, this.x, this.x0, n, this.direction, { algebraic: true });
      const terms = body instanceof Add ? body.args : [body];
      const t = new Dummy('t', { positive: true });
      const local = subs(this.core, [[this.x, pow(t, -1)]]);
      const recurrence = hyperAlgorithm(local, t, new Dummy('k'));
      const initial = isNoMatch(recurrence) ? [] : seriesTerms(recurrence[1], t, S.Zero, n, '+').terms.map((u) => subs(u, [[t, pow(this.x, -1)]]));
      const remaining = terms.filter((u) => !initial.some((v) => v.equals(u)));
      return add(this.withSymb(add(...initial)), ...remaining.map((u) => u instanceof Order ? new Order([this.withSymb(u.expr), this.x, this.x0]) : this.withSymb(u)));
    }
    // the Order term carries the symbolic factor too: O(x**(n + m)) for the factor x**m
    const xk = isZeroExpr(this.x0) ? this.x : sub(this.x, this.x0);
    return add(this.polynomial(n), O(this.withSymb(pow(xk, n)), this.x, this.x0));
  }
  /**
   * Truncates the series and drops the asymptotic order term.
   *
   * @param n - Truncation order.
   * @returns The truncated polynomial.
   * @see SymPy `sympy.series.formal.FormalPowerSeries.polynomial`
   */
  polynomial(n = 6): Expr {
    return add(...seriesTerms(this.core, this.x, this.x0, n, this.direction).terms.map((t) => this.withSymb(t)));
  }
  /** A term times the symbolic factor, with the powers of x combined (x**2*x**n = x**(n + 2)). */
  private withSymb(t: Expr): Expr {
    return this.symb.key === S.One.key ? t : powsimp(mul(factorTerms(t), this.symb));
  }
  /**
   * Extracts the coefficient of the specified power about the expansion point.
   *
   * @param k - Coefficient index.
   * @returns The coefficient of the specified power.
   * @see SymPy `sympy.series.formal.FormalPowerSeries.coeff`
   */
  coeff(k: number): Expr {
    const poly = add(...seriesTerms(this.core, this.x, this.x0, k + 1, this.direction).terms);
    const c = subs(diff(poly, this.x, k), [[this.x, this.x0]]);
    let f = 1n;
    for (let i = 2n; i <= BigInt(k); i++) f *= i;
    return this.withSymb(mul(c, Rational.of(1n, f)));
  }
  /**
   * Collects the first requested nonzero terms of the series.
   *
   * @param n - Number of terms to use.
   * @returns The leading terms.
   */
  terms(n: number): Expr[] {
    const out: Expr[] = [];
    for (const t of lseries(this.core, this.x, this.x0, this.direction)) {
      out.push(this.withSymb(t));
      if (out.length >= n) break;
    }
    return out;
  }
  /** The series of another function about the same point in the same variable. */
  private check(other: FormalPowerSeries, x: Sym | undefined): void {
    if ((x ?? this.x).key !== this.x.key || other.x.key !== this.x.key) throw new RangeError('Both series should have the same symbol.');
    this.checkPoint(other);
  }
  private checkPoint(other: FormalPowerSeries): void {
    if (this.direction !== other.direction) throw new RangeError('Both series should be calculated from the same direction.');
    if (this.x0.key !== other.x0.key) throw new RangeError('Both series should be calculated about the same point.');
  }
  /**
   * Adds the series to the other operand.
   *
   * @param other - Other operand.
   * @returns The sum.
   * @throws RangeError when the expansion points or directions differ.
   */
  override add(other: ExprLike): Expr {
    if (!(other instanceof FormalPowerSeries)) return super.add(other);
    this.checkPoint(other);
    const sum = add(this.fn, subs(other.fn, [[other.x, this.x]]));
    return sum.has(this.x) ? new FormalPowerSeries(sum, this.x, this.x0, this.direction) : sum;
  }
  /**
   * Forms the formal power series of the product of the underlying functions.
   *
   * @param other - Other operand.
   * @param x - Variable of the expansion.
   * @returns The product series.
   * @throws RangeError when the expansion variables, points or directions differ.
   * @see SymPy `sympy.series.formal.FormalPowerSeries.product`
   * @example
   * ```ts
   * import { exp, fps, sin, symbols } from '@symjs/symjs';
   *
   * const [x] = symbols('x');
   * const f = fps(exp(x), x);
   * f.product(fps(sin(x), x), x).truncate(4); // => x + x**2 + x**3/3 + O(x**4)
   * ```
   */
  product(other: FormalPowerSeries, x?: Sym): FormalPowerSeries {
    this.check(other, x);
    return new FormalPowerSeries(mul(this.fn, other.fn), this.x, this.x0, this.direction);
  }
  /**
   * Substitutes an inner series with zero constant term into the outer series.
   *
   * @param other - Other operand.
   * @param x - Variable of the expansion.
   * @returns The composite series.
   * @throws RangeError when the expansions have incompatible variables, points or directions, or the inner series has a nonzero constant term.
   * @see SymPy `sympy.series.formal.FormalPowerSeries.compose`
   * @example
   * ```ts
   * import { exp, fps, sin, symbols } from '@symjs/symjs';
   *
   * const [x] = symbols('x');
   * const f = fps(exp(x), x);
   * f.compose(fps(sin(x), x), x).truncate(); // => 1 + x + x**2/2 - x**4/8 - x**5/15 + O(x**6)
   * ```
   */
  compose(other: FormalPowerSeries, x?: Sym): FormalPowerSeries {
    this.check(other, x);
    if (!isZeroExpr(other.coeff(0))) throw new RangeError('The formal power series of the inner function should not have any constant coefficient term.');
    return new FormalPowerSeries(subs(this.fn, [[this.x, other.fn]]), this.x, this.x0, this.direction);
  }
  /**
   * Inverts a formal power series with a nonzero constant term.
   *
   * @returns The series of 1/f, for a series with a constant term.
   * @throws RangeError when the constant term is zero.
   * @see SymPy `sympy.series.formal.FormalPowerSeries.inverse`
   * @example
   * ```ts
   * import { exp, fps, symbols } from '@symjs/symjs';
   *
   * const [x] = symbols('x');
   * const f = fps(exp(x), x);
   * f.inverse().truncate(); // => 1 - x + x**2/2 - x**3/6 + x**4/24 - x**5/120 + O(x**6)
   * ```
   */
  inverse(): FormalPowerSeries {
    if (isZeroExpr(this.coeff(0))) throw new RangeError('Constant coefficient should exist for an inverse of a formal power series to exist.');
    return new FormalPowerSeries(pow(this.fn, -1), this.x, this.x0, this.direction);
  }
  /**
   * Integrates the series term by term or evaluates the integral over supplied limits.
   *
   * @param x - Variable of the expansion.
   * @param limits - Lower and upper endpoints of the interval.
   * @returns The antiderivative series or definite integral.
   * @see SymPy `sympy.series.formal.FormalPowerSeries.integrate`
   */
  override integrate(x?: Sym): FormalPowerSeries;
  override integrate(x: Sym, limits: readonly [ExprLike, ExprLike]): Expr;
  override integrate(x?: Sym, limits?: readonly [ExprLike, ExprLike]): FormalPowerSeries | Expr {
    const v = x ?? this.x;
    if (limits) return integrate(this.fn, v, [sympify(limits[0]), sympify(limits[1])]);
    return new FormalPowerSeries(integrate(this.fn, v), this.x, this.x0, this.direction);
  }
  /**
   * Formats the series as a string.
   *
   * @returns The formatted expression.
   */
  override toString(): string {
    const k = new Dummy('k');
    const direction = this.direction === '+' ? 1 : -1;
    const xk = pow(mul(direction, sub(this.x, this.x0)), k);
    const description = this.coefficientDescription(k, direction);
    if (description === undefined) return str(this.fn);
    const seq = `SeqFormula(${description.formula}, (${str(k)}, ${description.start}, oo))`;
    return `FormalPowerSeries(${str(this.fn)}, ${str(this.x)}, ${str(this.x0)}, ${direction}, (${seq}, SeqFormula(${str(xk)}, (${str(k)}, 0, oo)), ${str(description.independent)}))`;
  }

  /**
   * Formats the expression using the supplied expression printer.
   *
   * @returns A plain-text representation.
   */
  override printStr(): string {
    return this.toString();
  }

  /** A hypergeometric coefficient formula when available, otherwise the defining Taylor derivative. */
  private coefficientDescription(k: Expr, direction: number): { formula: string; start: number; independent: Expr } | undefined {
    const f = this.core;
    if (isPolynomial(f, [this.x])) {
      const local = subs(f, [[this.x, add(this.x0, mul(direction, this.x))]]);
      return { formula: `Coeff(${str(this.withSymb(local))}, ${str(this.x)}, ${str(k)})`, start: 1, independent: this.withSymb(subs(f, [[this.x, this.x0]])) };
    }
    const arg = f instanceof Fn ? first(f.args) : f instanceof Pow ? (f.base.key === S.E.key ? f.exp : f.base) : f;
    const a = diff(arg, this.x);
    const b = subs(arg, [[this.x, this.x0]]);
    const factorial = (n: Expr): Expr => fn('factorial', [n]);
    const piece = (coefficient: Expr, step: number, residue: number): string =>
      `Piecewise((${str(this.withSymb(coefficient))}, Eq(Mod(${str(k)}, ${step}), ${residue})), (0, True))`;
    if (f instanceof Pow && f.base.key === S.E.key) {
      const polynomial = polyCoefficients(subs(f.exp, [[this.x, add(this.x0, mul(direction, this.x))]]), this.x);
      const terms = polynomial && [...polynomial].filter(([degree, coefficient]) => degree > 0 && !isZeroExpr(coefficient));
      if (terms?.length === 1) {
        const [degree, coefficient] = first(terms);
        const j = mul(k, Rational.of(1, degree));
        return { formula: piece(mul(exp(b), pow(coefficient, j), pow(factorial(j), -1)), degree, 0), start: 1, independent: this.withSymb(exp(b)) };
      }
    }
    if (!a.has(this.x)) {
      const slope = mul(direction, a);
      if (f instanceof Fn && (f.name === 'sin' || f.name === 'cos') && isZeroExpr(b)) {
        const odd = f.name === 'sin' ? 1 : 0;
        const j = mul(S.Half, sub(k, odd));
        const negative = couldExtractMinusSign(slope);
        const c = mul(negative && odd ? -1 : 1, pow(negative ? mul(-1, slope) : slope, k), pow(Rational.of(-1, 4), j), pow(mul(fn('rf', [Rational.of(2 * odd + 1, 2), j]), factorial(j)), -1));
        return { formula: piece(c, 2, odd), start: odd + 1, independent: this.withSymb(odd ? mul(a, sub(this.x, this.x0)) : S.One) };
      }
      if (f instanceof Fn && f.name === 'log' && !isZeroExpr(b)) {
        const c = mul(-1, pow(mul(-1, b, pow(slope, -1)), mul(-1, k)), pow(k, -1));
        return { formula: str(this.withSymb(c)), start: 1, independent: this.withSymb(fn('log', [b])) };
      }
      if (f instanceof Pow && !f.exp.has(this.x) && !isZeroExpr(b)) {
        const c = f.exp.key === S.NegOne.key ? mul(pow(b, -1), pow(mul(-1, slope, pow(b, -1)), k))
          : mul(fn('binomial', [f.exp, k]), pow(slope, k), pow(b, sub(f.exp, k)));
        return { formula: str(this.withSymb(c)), start: 0, independent: S.Zero };
      }
    }
    // The unevaluated kth derivative is an exact coefficient definition; printing it must not
    // trigger a fixed truncation or pretend that a general closed coefficient formula is known.
    // At a singular or undecidable point there is no justified Taylor coefficient to print.
    if (isMeromorphic(f, this.x, this.x0) !== true || some(subs(f, [[this.x, this.x0]]), (e) => e instanceof Special)) return undefined;
    const derivative = `Subs(Derivative(${str(f)}, (${str(this.x)}, ${str(k)})), ${str(this.x)}, ${str(this.x0)})`;
    const scale = mul(this.symb, pow(direction, k));
    return { formula: `${scale.key === S.One.key ? '' : `${str(scale)}*`}${derivative}/factorial(${str(k)})`, start: 0, independent: S.Zero };
  }
}

/**
 * Expands the function about the given point, inferring a sole free variable when omitted and
 * preserving constant inputs.
 *
 * @param ex - Expression to expand or evaluate.
 * @param x - Variable of the expansion.
 * @param x0 - Point about which to expand.
 * @param direction - Side from which the variable approaches the point.
 * @param options - Enable rational-function or hypergeometric coefficient searches with `rational` and `hyper`.
 * @returns The formal series, or the expression itself when it is independent of the variable or no expansion is found.
 * @throws NotImplementedError when the expression has several free variables and no expansion variable is specified.
 * @see SymPy `sympy.series.formal.fps`
 * @example
 * ```ts
 * import { ex, fps, symbols } from '@symjs/symjs';
 *
 * const [x] = symbols('x');
 * fps(ex`log(1 + x)`, x).truncate(); // => x - x**2/2 + x**3/3 - x**4/4 + x**5/5 + O(x**6)
 * ```
 */
export function fps(ex: number | bigint | Rational, x: Sym, x0?: ExprLike, direction?: '+' | '-'): Expr;
export function fps(ex: ExprLike, x: Sym, x0?: ExprLike, direction?: '+' | '-'): FormalPowerSeries;
export function fps(ex: ExprLike): FormalPowerSeries | Expr;
export function fps(ex: ExprLike, x: Sym | undefined, x0: ExprLike, direction: '+' | '-', options: { rational?: boolean; hyper?: boolean }): Expr;
export function fps(ex: ExprLike, x?: Sym, x0: ExprLike = 0, direction: '+' | '-' = '+', options: { rational?: boolean; hyper?: boolean } = {}): Expr {
  const f = sympify(ex);
  const free = [...freeSymbols(f)].filter((s) => s instanceof Sym);
  if (!x && free.length > 1) throw new NotImplementedError('multivariate formal power series');
  const variable = x ?? free[0];
  if (!variable || !f.has(variable)) return f;
  const point = sympify(x0);
  if (point instanceof Special && f instanceof Pow && f.base === S.E && limit(f.exp, variable, point) === S.Infinity) return f;
  if (!isPolynomial(f, [variable]) && (options.hyper === false || options.rational === false)) {
    const local = subs(f, [[variable, add(point, mul(direction === '+' ? 1 : -1, variable))]]);
    const k = new Dummy('k');
    const rational = options.rational !== false && !isNoMatch(rationalAlgorithm(local, variable, k));
    if (!rational && (options.hyper === false || isNoMatch(hyperAlgorithm(local, variable, k)))) return f;
  }
  return new FormalPowerSeries(f, variable, point, direction);
}


/**
 * Discover linear differential equations over the rational functions in x.
 *
 * @param fIn - Function to expand.
 * @param x - Variable of the expansion.
 * @param g - Unknown function in the differential equation.
 * @param order - Maximum differential order to consider.
 * @returns An iterator of differential equations paired with their orders.
 * @see SymPy `sympy.series.formal.simpleDE`
 */
export function* simpleDE(fIn: ExprLike, x: Sym, g: UndefinedFunction, order = 4): Generator<[Expr, number]> {
  const f = sympify(fIn);
  const derivatives: Expr[] = [f];
  for (let n = 1; n <= order; n++) {
    derivatives.push(diff(at(derivatives, n - 1), x));
    const basis: Expr[] = [];
    const columns = derivatives.map((d) => {
      const coefficients = new Map<number, Expr>();
      const expanded = expand(d);
      for (const term of expanded instanceof Add ? expanded.args : [expanded]) {
        if (isZeroExpr(term)) continue;
        let i = basis.findIndex((b) => isRationalFunction(cancel(mul(term, pow(b, -1))), [x]));
        if (i < 0) { i = basis.length; basis.push(term); }
        const ratio = cancel(mul(term, pow(at(basis, i), -1)));
        coefficients.set(i, add(coefficients.get(i) ?? S.Zero, ratio));
      }
      return coefficients;
    });
    const matrix = Matrix.fromFunction(basis.length, n + 1, (i, j) => at(columns, j).get(i) ?? S.Zero);
    const relation = nullspace(matrix).find((v) => !isZeroExpr(v.get(n, 0)));
    if (relation === undefined) continue;
    const denominator = mul(...relation.data.map((c) => fraction(cancel(c))[1]));
    const equation = add(...relation.data.map((c, i) => mul(cancel(mul(c, denominator)), diff(g(x), x, i))));
    yield [equation, n];
  }
}

/** A coefficient formula, the initial terms outside the formula, and the first index it covers. */
export type HyperSeriesResult = [Expr, Expr, number];

/**
 * Solve a two-term ordinary-series recurrence obtained from a linear DE.
 *
 * @param fIn - Function to expand.
 * @param x - Variable of the expansion.
 * @param DE - Linear differential equation, written as an expression equal to zero.
 * @param order - Order of the differential equation.
 * @param g - Unknown function in the differential equation.
 * @param k - Coefficient index.
 * @returns The coefficient formula, initial terms and starting index, or `NoMatch`.
 * @throws RangeError when the differential order is not a positive integer.
 * @see SymPy `sympy.series.formal.solve_de`
 * @example
 * ```ts
 * import { Derivative, SymFunction, exp, solveDe, symbols } from '@symjs/symjs';
 *
 * const [x, k] = symbols('x k');
 * const f = SymFunction('f');
 * solveDe(exp(x), x, Derivative(f(x), x).sub(f(x)), 1, f, k); // => [Piecewise((1/factorial(k), Eq(Mod(k, 1), 0)), (0, True)), 1, 1]
 * ```
 */
export function solveDe(fIn: ExprLike, x: Sym, DE: ExprLike, order: number, g: UndefinedFunction, k: Sym): HyperSeriesResult | NoMatchResult {
  if (!Number.isInteger(order) || order < 1) throw new RangeError('positive differential order required');
  const f = sympify(fIn);
  const recurrence = expand(hyperRe(DE, g, k));
  const coefficients = new Map<number, Expr>();
  for (const term of recurrence instanceof Add ? recurrence.args : [recurrence]) {
    const factors = term instanceof Mul ? term.args : [term];
    const call = cast(factors.find((a) => a instanceof UndefFn), UndefFn);
    // hyperRe constructs integer shifts and exactly one coefficient function per term.
    const offset = expectType(sub(first(call.args), k), (e): e is Rational => e instanceof Rational, 'integer shift');
    const index = Number(offset.p);
    coefficients.set(index, add(coefficients.get(index) ?? S.Zero, mul(...factors.filter((a) => a !== call))));
  }
  const shifts = [...coefficients.keys()].sort((a, b) => a - b);
  if (shifts.length !== 2) return NoMatch;
  const step = at(shifts, 1);
  const P = Poly.from(getOrThrow(coefficients, 0), [k]);
  const Q = Poly.from(getOrThrow(coefficients, step), [k]);
  const pRoots = rootsDict(P.asExpr(), k, { skipQuintic: true }), qRoots = rootsDict(Q.asExpr(), k, { skipQuintic: true });
  if ([...pRoots.values()].reduce((a, b) => a + b, 0) !== P.degree() || [...qRoots.values()].reduce((a, b) => a + b, 0) !== Q.degree()) return NoMatch;
  const integerRoots = [...qRoots.keys()];
  if (integerRoots.some((r) => !(r instanceof Rational) || !r.isInteger)) return NoMatch;
  const maxRoot = integerRoots.length ? Math.max(...integerRoots.map((r) => Number(r))) : -1;
  const initial = Math.max(0, maxRoot + 1);
  const branches: [Expr, Expr | boolean][] = [];
  let independent: Expr = S.Zero;
  let lastInitial = -1;
  const coefficient = (i: number): Expr => {
    const derivative = diff(f, x, i);
    const value = subs(derivative, [[x, S.Zero]]);
    const c = some(value, (v) => v instanceof Special || v instanceof AccumBoundsNode) ? limit(derivative, x, S.Zero) : value;
    return mul(c, pow(fn('factorial', [sympify(i)]), -1));
  };
  for (let i = 0; i < initial + step; i++) {
    const c = coefficient(i);
    if (some(c, (e) => e instanceof Special) || c.has(x)) return NoMatch;
    if (!isZeroExpr(c)) { independent = add(independent, mul(c, pow(x, i))); lastInitial = i; }
    if (i < initial || isZeroExpr(c)) continue;
    const t = mul(sub(k, i), Rational.of(1, step));
    const scale = mul(-1, P.LC(), pow(Q.LC(), -1), pow(step, P.degree() - Q.degree()));
    const rising = (r: Expr, multiplicity: number): Expr => pow(fn('rf', [mul(sub(i, r), Rational.of(1, step)), t]), multiplicity);
    const formula = mul(c, pow(scale, t), ...[...pRoots].map(([r, m]) => rising(r, m)), ...[...qRoots].map(([r, m]) => pow(rising(r, m), -1)));
    branches.push([formula, Eq(Mod(k, step), i % step)]);
  }
  if (!branches.length) return NoMatch;
  return [piecewise(...branches, [S.Zero, true]), independent, lastInitial + 1];
}

/**
 * Discover a differential equation and solve its hypergeometric coefficient recurrence.
 *
 * @param f - Function to expand.
 * @param x - Variable of the expansion.
 * @param k - Coefficient index.
 * @param order - Maximum differential order to consider.
 * @returns The coefficient formula, initial terms and starting index, or `NoMatch`.
 * @see SymPy `sympy.series.formal.hyper_algorithm`
 * @example
 * ```ts
 * import { exp, hyperAlgorithm, symbols } from '@symjs/symjs';
 *
 * const [x, k] = symbols('x k');
 * hyperAlgorithm(exp(x), x, k); // => [Piecewise((1/factorial(k), Eq(Mod(k, 1), 0)), (0, True)), 1, 1]
 * ```
 */
export function hyperAlgorithm(f: ExprLike, x: Sym, k: Sym, order = 4): HyperSeriesResult | NoMatchResult {
  const g = SymFunction('g');
  for (const [equation, n] of simpleDE(f, x, g, order)) {
    const solution = solveDe(f, x, equation, n, g, k);
    if (!isNoMatch(solution)) return solution;
  }
  return NoMatch;
}

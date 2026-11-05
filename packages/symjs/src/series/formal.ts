// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Formal power series (SymPy sympy/series/formal.py: fps and
 * FormalPowerSeries).
 */

import type { Expr, ExprLike, Sym } from '../core/nodes';
import { Add, Dummy, Fn, Pow, Rational, S, Special } from '../core/nodes';
import { add, couldExtractMinusSign, exp, mul, pow, sub, sympify } from '../core/ops';
import { asIndependent, isMeromorphic, isPolynomial } from '../core/methods';
import { NotImplementedError } from '../core/errors';
import { first } from '../core/guard';
import { freeSymbols, some, subs } from '../core/traverse';
import { diff } from '../calculus/diff';
import { fn } from '../functions/elementary/elementary';
import { expand } from '../simplify/expand';
import { powsimp } from '../simplify/powsimp';
import { integrate } from '../integrals/integrate';
import { polyCoefficients } from '../polys/poly';
import { str } from '../printing/str';
import { O, series } from './series';
import { lseries, seriesTerms } from './lseries';

const isZeroExpr = (e: Expr): boolean => e instanceof Rational && e.isZero;

/** SymPy FormalPowerSeries: the power series of a function, truncated on request. */
export class FormalPowerSeries {
  /** The factor of the function free of x but with other symbols (x**n), kept out of the expansion (SymPy symb). */
  private readonly symb: Expr;
  /** The function without that factor. */
  private readonly core: Expr;
  constructor(
    readonly fn: Expr,
    readonly x: Sym,
    readonly x0: Expr,
    readonly direction: '+' | '-',
  ) {
    // SymPy _compute_fps: (f, symb) = expand(f).as_independent(*syms) for the symbols other than x
    const others = [...freeSymbols(fn)].filter((s) => s.key !== x.key);
    const [core, symb] = others.length && !(fn instanceof Add) ? asIndependent(expand(fn), others) : [fn, S.One];
    this.core = core;
    this.symb = symb;
  }
  /** The series up to O((x - x0)**n) (SymPy truncate). */
  truncate(n = 6): Expr {
    if (this.symb.key === S.One.key) return series(this.fn, this.x, this.x0, n, this.direction);
    // the Order term carries the symbolic factor too: O(x**(n + m)) for the factor x**m
    const xk = isZeroExpr(this.x0) ? this.x : sub(this.x, this.x0);
    return add(this.polynomial(n), O(this.withSymb(pow(xk, n)), this.x, this.x0));
  }
  /** The truncated series without the Order term (SymPy polynomial). */
  polynomial(n = 6): Expr {
    return add(...seriesTerms(this.core, this.x, this.x0, n, this.direction).terms.map((t) => this.withSymb(t)));
  }
  /** A term times the symbolic factor, with the powers of x combined (x**2*x**n = x**(n + 2)). */
  private withSymb(t: Expr): Expr {
    return this.symb.key === S.One.key ? t : powsimp(mul(t, this.symb));
  }
  /** The coefficient of (x - x0)**k. */
  coeff(k: number): Expr {
    const poly = add(...seriesTerms(this.core, this.x, this.x0, k + 1, this.direction).terms);
    const c = subs(diff(poly, this.x, k), [[this.x, this.x0]]);
    let f = 1n;
    for (let i = 2n; i <= BigInt(k); i++) f *= i;
    return this.withSymb(mul(c, Rational.of(1n, f)));
  }
  /** The first n nonzero terms. */
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
    if (this.x0.key !== other.x0.key) throw new RangeError('Both series should be calculated about the same point.');
  }
  /** The series of the product of the functions (SymPy FormalPowerSeries.product). */
  product(other: FormalPowerSeries, x?: Sym): FormalPowerSeries {
    this.check(other, x);
    return new FormalPowerSeries(mul(this.fn, other.fn), this.x, this.x0, this.direction);
  }
  /** The series of the composition f(g(x)) with the inner series g without constant term (SymPy FormalPowerSeries.compose). */
  compose(other: FormalPowerSeries, x?: Sym): FormalPowerSeries {
    this.check(other, x);
    if (!isZeroExpr(other.coeff(0))) throw new RangeError('The formal power series of the inner function should not have any constant coefficient term.');
    return new FormalPowerSeries(subs(this.fn, [[this.x, other.fn]]), this.x, this.x0, this.direction);
  }
  /** The series of 1/f, for a series with a constant term (SymPy FormalPowerSeries.inverse; its symbol argument is not used). */
  inverse(): FormalPowerSeries {
    if (isZeroExpr(this.coeff(0))) throw new RangeError('Constant coefficient should exist for an inverse of a formal power series to exist.');
    return new FormalPowerSeries(pow(this.fn, -1), this.x, this.x0, this.direction);
  }
  /**
   * The series of the antiderivative (SymPy FormalPowerSeries.integrate), or
   * with limits the definite integral of the function.
   */
  integrate(x?: Sym): FormalPowerSeries;
  integrate(x: Sym, limits: readonly [ExprLike, ExprLike]): Expr;
  integrate(x?: Sym, limits?: readonly [ExprLike, ExprLike]): FormalPowerSeries | Expr {
    const v = x ?? this.x;
    if (limits) return integrate(this.fn, v, [sympify(limits[0]), sympify(limits[1])]);
    return new FormalPowerSeries(integrate(this.fn, v), this.x, this.x0, this.direction);
  }
  toString(): string {
    const k = new Dummy('k');
    const direction = this.direction === '+' ? 1 : -1;
    const xk = pow(mul(direction, sub(this.x, this.x0)), k);
    const description = this.coefficientDescription(k, direction);
    if (description === undefined) return str(this.fn);
    const seq = `SeqFormula(${description.formula}, (${str(k)}, ${description.start}, oo))`;
    return `FormalPowerSeries(${str(this.fn)}, ${str(this.x)}, ${str(this.x0)}, ${direction}, (${seq}, SeqFormula(${str(xk)}, (${str(k)}, 0, oo)), ${str(description.independent)}))`;
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
        const c = mul(-1, pow(mul(-1, slope, pow(b, -1)), k), pow(k, -1));
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
 * SymPy fps(f, x, x0, dir): the formal power series of f about x0. Without x, the
 * only free symbol of f is the variable, and f without free symbols is returned as it is.
 */
export function fps(ex: ExprLike, x: Sym, x0?: ExprLike, direction?: '+' | '-'): FormalPowerSeries;
export function fps(ex: ExprLike): FormalPowerSeries | Expr;
export function fps(ex: ExprLike, x?: Sym, x0: ExprLike = 0, direction: '+' | '-' = '+'): FormalPowerSeries | Expr {
  const f = sympify(ex);
  if (x !== undefined) return new FormalPowerSeries(f, x, sympify(x0), direction);
  // (a MatrixSymbol is not a free symbol here: SymPy fps(A) builds FormalPowerSeries(A, A, 0, ...),
  // whose terms cannot be computed, while A is constant)
  const free = [...freeSymbols(f)];
  if (free.length === 0) return f;
  if (free.length > 1) throw new NotImplementedError('multivariate formal power series');
  return new FormalPowerSeries(f, first(free), sympify(x0), direction);
}


// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Fourier series (SymPy sympy/series/fourier.py: fourier_series and
 * FourierSeries).
 */

import type { Expr, ExprLike, Sym } from '../core/nodes';
import { Rational, S } from '../core/nodes';
import { add, mul, pow, sub, sympify } from '../core/ops';
import { subs } from '../core/traverse';
import { cos, fn, sin } from '../functions/elementary/elementary';
import { integrate } from '../integrals/integrate';
import { simplify } from '../simplify/simplify';
import { str } from '../printing/str';

const isZeroExpr = (e: Expr): boolean => e instanceof Rational && e.isZero;

/**
 * SymPy FourierSeries: a0/2 + sum(an cos(n pi x / L) + bn sin(n pi x / L))
 * on the interval (a, b) with L = (b - a)/2. A series made by shift, scale,
 * shiftx or scalex keeps the coefficients of the original function and
 * transforms its terms.
 */
export class FourierSeries {
  private readonly L: Expr;
  /** The function whose coefficients are computed (fn itself unless transformed). */
  private readonly source: Expr;
  /** What x is replaced with in the terms (shiftx, scalex). */
  private readonly xmap: Expr;
  /** The factor of every term (scale). */
  private readonly factor: Expr;
  /** The constant added to the series (shift). */
  private readonly offset: Expr;
  constructor(
    readonly fn: Expr,
    readonly x: Sym,
    readonly a: Expr,
    readonly b: Expr,
    transform?: { source: Expr; xmap: Expr; factor: Expr; offset: Expr },
  ) {
    this.L = mul(sub(b, a), Rational.of(1n, 2n));
    this.source = transform?.source ?? fn;
    this.xmap = transform?.xmap ?? x;
    this.factor = transform?.factor ?? S.One;
    this.offset = transform?.offset ?? S.Zero;
  }
  private arg(k: number): Expr {
    return mul(k, S.Pi, this.xmap, pow(this.L, -1));
  }
  private coefficient(k: number, trig: (e: Expr) => Expr): Expr {
    const v = integrate(mul(this.source, trig(mul(k, S.Pi, this.x, pow(this.L, -1)))), this.x, [this.a, this.b]);
    return simplify(mul(v, pow(this.L, -1)));
  }
  /** The constant term a0/2. */
  a0(): Expr {
    const c = simplify(mul(integrate(this.source, this.x, [this.a, this.b]), Rational.of(1n, 2n), pow(this.L, -1)));
    return add(mul(c, this.factor), this.offset);
  }
  /** The cosine coefficient of order k >= 1. */
  an(k: number): Expr {
    return mul(this.coefficient(k, cos), this.factor);
  }
  /** The sine coefficient of order k >= 1. */
  bn(k: number): Expr {
    return mul(this.coefficient(k, sin), this.factor);
  }
  /** The terms of order k (k = 0 is the constant term). */
  term(k: number): Expr {
    if (k === 0) return this.a0();
    return add(mul(this.an(k), cos(this.arg(k))), mul(this.bn(k), sin(this.arg(k))));
  }
  /** The first n nonzero terms (SymPy truncate). */
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
  /** The series of f(x) + s (SymPy shift). */
  shift(s: ExprLike): FourierSeries {
    const v = this.independent(s);
    return this.transformed(add(this.fn, v), { offset: add(this.offset, v) });
  }
  /** The series of s*f(x) (SymPy scale). */
  scale(s: ExprLike): FourierSeries {
    const v = this.independent(s);
    return this.transformed(mul(this.fn, v), { factor: mul(this.factor, v), offset: mul(this.offset, v) });
  }
  /** The series of f(x + s) (SymPy shiftx). */
  shiftx(s: ExprLike): FourierSeries {
    const v = this.independent(s);
    return this.transformed(subs(this.fn, [[this.x, add(this.x, v)]]), { xmap: subs(this.xmap, [[this.x, add(this.x, v)]]) });
  }
  /** The series of f(s*x) (SymPy scalex). */
  scalex(s: ExprLike): FourierSeries {
    const v = this.independent(s);
    return this.transformed(subs(this.fn, [[this.x, mul(this.x, v)]]), { xmap: subs(this.xmap, [[this.x, mul(this.x, v)]]) });
  }
  /**
   * The sigma approximation of order n (SymPy sigma_approximation): the
   * terms of order k < n weighted by the Lanczos factor sinc(pi*k/n).
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

/** SymPy fourier_series(f, (x, a, b)): the Fourier series of f on (a, b); (-pi, pi) by default. */
export function fourierSeries(ex: ExprLike, x: Sym, limits: readonly [ExprLike, ExprLike] = [S.Pi.neg(), S.Pi]): FourierSeries {
  return new FourierSeries(sympify(ex), x, sympify(limits[0]), sympify(limits[1]));
}

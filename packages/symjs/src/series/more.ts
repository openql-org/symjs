// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Lazy series (lseries), formal power series (fps) and Fourier series
 * (fourier_series), and Expr.dir (the direction of approach).
 */

import type { Expr, ExprLike, Sym } from '../core/nodes';
import { Add, Dummy, Mul, Order, Pow, Rational, S, Special } from '../core/nodes';
import { add, mul, neg, pow, sub, sympify } from '../core/ops';
import { asIndependent } from '../core/methods';
import { freeSymbols, subs } from '../core/traverse';
import { diff } from '../calculus/diff';
import { cos, fn, log, sin } from '../functions/elementary';
import { expand } from '../simplify/expand';
import { powsimp } from '../simplify/powsimp';
import { integrate } from '../integrals/integrate';
import { simplify } from '../simplify/simplify';
import { str } from '../printing/str';
import { O, leadterm, series } from './series';
import { limit } from './limits';

const isZeroExpr = (e: Expr): boolean => e instanceof Rational && e.isZero;
const isOrder = (e: Expr): boolean => e instanceof Order;

/**
 * The terms of the series of e about x0 up to order n, lowest order first:
 * computed in t = x - x0 and written back in x - x0.
 */
function seriesTerms(e: Expr, x: Sym, x0: Expr, n: number, dir: '+' | '-'): { terms: Expr[]; exact: boolean } {
  const t = new Dummy('t');
  const atZero = isZeroExpr(x0);
  const et = atZero ? subs(e, [[x, t]]) : subs(e, [[x, add(x0, t)]]);
  const s = series(et, t, 0, n, dir);
  const parts = s instanceof Add ? s.args : [s];
  const terms = parts.filter((p) => !isOrder(p));
  // each term is c*t**e or c*(-t)**e (from the left) with c free of t but for log(t) or log(-t)
  // (leadterm would search the leading term of t**2000/2 to too small an order)
  const deg = (p: Expr): number => {
    for (const f of p instanceof Mul ? p.args : [p]) {
      if (f.key === t.key) return 1;
      if (f instanceof Pow && f.exp instanceof Rational && (f.base.key === t.key || f.base.key === neg(t).key)) return f.exp.value;
    }
    return 0;
  };
  const back = (p: Expr): Expr => subs(p, [[t, atZero ? x : sub(x, x0)]]);
  return { terms: [...terms].sort((a, b) => deg(a) - deg(b)).map(back), exact: !parts.some(isOrder) };
}

/**
 * SymPy Expr.lseries: the terms of the series of e about x0, lazily (an
 * iterator that computes more terms as they are requested).
 */
export function* lseries(ex: ExprLike, x: Sym, x0: ExprLike = 0, dir: '+' | '-' = '+'): Generator<Expr, void, undefined> {
  const e = sympify(ex);
  const p = sympify(x0);
  let n = 6;
  let done = 0;
  for (;;) {
    const { terms, exact } = seriesTerms(e, x, p, n, dir);
    for (const t of terms.slice(done)) yield t;
    done = Math.max(done, terms.length);
    if (exact || n > 4096) return;
    n *= 2;
  }
}

/**
 * SymPy Expr.dir(x, cdir): the direction in which e approaches its value at
 * x = 0 when x approaches 0 from the direction cdir.
 */
export function dir(ex: ExprLike, x: Sym, cdir: ExprLike): Expr {
  let arg = sympify(ex);
  if (isZeroExpr(arg)) return S.Zero;
  let minexp = 0;
  let coeff: Expr = S.Zero;
  while (!isZeroExpr(arg)) {
    minexp++;
    arg = diff(arg, x);
    coeff = subs(arg, [[x, 0]]);
    if (coeff instanceof Special && coeff.name === 'nan') coeff = limit(arg, x, 0);
    if (coeff instanceof Special && coeff.name === 'zoo') {
      try {
        coeff = leadterm(arg, x)[0];
        // a leading coefficient with log(x) is not a direction (SymPy raises and takes the limit)
        if (coeff.has(log(x))) coeff = limit(arg, x, 0);
      } catch {
        coeff = limit(arg, x, 0);
      }
    }
    if (!isZeroExpr(coeff)) break;
  }
  return mul(coeff, pow(sympify(cdir), minexp));
}

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
    return `FormalPowerSeries(${str(this.fn)}, ${str(this.x)}, ${str(this.x0)})`;
  }
}

/** SymPy fps(f, x, x0, dir): the formal power series of f about x0. */
export function fps(ex: ExprLike, x: Sym, x0: ExprLike = 0, direction: '+' | '-' = '+'): FormalPowerSeries {
  return new FormalPowerSeries(sympify(ex), x, sympify(x0), direction);
}

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

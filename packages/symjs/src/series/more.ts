// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Lazy series (lseries), formal power series (fps) and Fourier series
 * (fourier_series), and Expr.dir (the direction of approach).
 */

import type { Expr, ExprLike, Sym } from '../core/nodes';
import { Add, Dummy, Order, Rational, S, Special } from '../core/nodes';
import { add, mul, pow, sub, sympify } from '../core/ops';
import { subs } from '../core/traverse';
import { diff } from '../calculus/diff';
import { cos, sin } from '../functions/elementary';
import { integrate } from '../integrals/integrate';
import { simplify } from '../simplify/simplify';
import { str } from '../printing/str';
import { leadterm, series } from './series';
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
  const deg = (p: Expr): number => {
    try {
      return leadterm(p, t)[1].toNumber();
    } catch {
      return 0;
    }
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
  constructor(
    readonly fn: Expr,
    readonly x: Sym,
    readonly x0: Expr,
    readonly direction: '+' | '-',
  ) {}
  /** The series up to O((x - x0)**n) (SymPy truncate). */
  truncate(n = 6): Expr {
    return series(this.fn, this.x, this.x0, n, this.direction);
  }
  /** The truncated series without the Order term (SymPy polynomial). */
  polynomial(n = 6): Expr {
    return add(...seriesTerms(this.fn, this.x, this.x0, n, this.direction).terms);
  }
  /** The coefficient of (x - x0)**k. */
  coeff(k: number): Expr {
    const poly = this.polynomial(k + 1);
    const c = subs(diff(poly, this.x, k), [[this.x, this.x0]]);
    let f = 1n;
    for (let i = 2n; i <= BigInt(k); i++) f *= i;
    return mul(c, Rational.of(1n, f));
  }
  /** The first n nonzero terms. */
  terms(n: number): Expr[] {
    const out: Expr[] = [];
    for (const t of lseries(this.fn, this.x, this.x0, this.direction)) {
      out.push(t);
      if (out.length >= n) break;
    }
    return out;
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
 * on the interval (a, b) with L = (b - a)/2.
 */
export class FourierSeries {
  private readonly L: Expr;
  constructor(
    readonly fn: Expr,
    readonly x: Sym,
    readonly a: Expr,
    readonly b: Expr,
  ) {
    this.L = mul(sub(b, a), Rational.of(1n, 2n));
  }
  private arg(k: number): Expr {
    return mul(k, S.Pi, this.x, pow(this.L, -1));
  }
  private coefficient(k: number, trig: (e: Expr) => Expr): Expr {
    const v = integrate(mul(this.fn, trig(this.arg(k))), this.x, [this.a, this.b]);
    return simplify(mul(v, pow(this.L, -1)));
  }
  /** The constant term a0/2. */
  a0(): Expr {
    return simplify(mul(integrate(this.fn, this.x, [this.a, this.b]), Rational.of(1n, 2n), pow(this.L, -1)));
  }
  /** The cosine coefficient of order k >= 1. */
  an(k: number): Expr {
    return this.coefficient(k, cos);
  }
  /** The sine coefficient of order k >= 1. */
  bn(k: number): Expr {
    return this.coefficient(k, sin);
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
}

/** SymPy fourier_series(f, (x, a, b)): the Fourier series of f on (a, b); (-pi, pi) by default. */
export function fourierSeries(ex: ExprLike, x: Sym, limits: readonly [ExprLike, ExprLike] = [S.Pi.neg(), S.Pi]): FourierSeries {
  return new FourierSeries(sympify(ex), x, sympify(limits[0]), sympify(limits[1]));
}

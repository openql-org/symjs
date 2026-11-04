// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Formal power series (SymPy sympy/series/formal.py: fps and
 * FormalPowerSeries).
 */

import type { Expr, ExprLike, Sym } from '../core/nodes';
import { Add, Rational, S } from '../core/nodes';
import { add, mul, pow, sub, sympify } from '../core/ops';
import { asIndependent } from '../core/methods';
import { freeSymbols, subs } from '../core/traverse';
import { diff } from '../calculus/diff';
import { expand } from '../simplify/expand';
import { powsimp } from '../simplify/powsimp';
import { integrate } from '../integrals/integrate';
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
    return `FormalPowerSeries(${str(this.fn)}, ${str(this.x)}, ${str(this.x0)})`;
  }
}

/** SymPy fps(f, x, x0, dir): the formal power series of f about x0. */
export function fps(ex: ExprLike, x: Sym, x0: ExprLike = 0, direction: '+' | '-' = '+'): FormalPowerSeries {
  return new FormalPowerSeries(sympify(ex), x, sympify(x0), direction);
}


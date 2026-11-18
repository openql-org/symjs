// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Lazy series (SymPy Expr.lseries) and Expr.dir (the direction of
 * approach). SymPy has them as Expr methods (sympy/core/expr.py); they are
 * here because they build on series and limits.
 */

import type { Expr, ExprLike, Fn, Sym } from '../core/nodes';
import { Add, Dummy, Mul, Order, Pow, Rational, S, Special, impl } from '../core/nodes';
import { add, mul, neg, pow, sub, sympify } from '../core/ops';
import { subs } from '../core/traverse';
import { diff } from '../calculus/diff';
import { im, log, re } from '../functions/elementary/elementary';
import { rewrite } from '../simplify/rewrite';
import { expandMul } from '../simplify/expand';
import { asLeadingTerm, leadingTermRules, leadterm, series } from './series';
import { isNegative, isPositive } from '../core/assumptions';
import { AccumBounds } from '../core/accumbounds';
import { NotImplementedError } from '../core/errors';
import { defined, first } from '../core/guard';
import { fn } from '../functions/elementary/elementary';
import { limit } from './limits';

const isZeroExpr = (e: Expr): boolean => e instanceof Rational && e.isZero;
const isOrder = (e: Expr): boolean => e instanceof Order;

/**
 * The terms of the series of e about x0 up to order n, lowest order first:
 * computed in t = x - x0 and written back in x - x0.
 */
export function seriesTerms(e: Expr, x: Sym, x0: Expr, n: number, dir: '+' | '-'): { terms: Expr[]; exact: boolean } {
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

/** The value at x = 0 of an argument, or its limit from the side of cdir where it has none (nan or an interval). */
function valueAtZero(arg: Expr, x: Sym, cdir: Expr): Expr {
  const v = subs(arg, [[x, 0]]);
  if (!((v instanceof Special && v.name === 'nan') || defined(impl.accumBounds, 'accumBounds').is(v))) return v;
  return limit(arg, x, 0, isNegative(cdir) === true ? '-' : '+');
}

const isFiniteNumber = (v: Expr): boolean => !(v instanceof Special) && v.freeSymbols().size === 0;

/**
 * SymPy floor and ceiling _eval_as_leading_term: the integer value at 0, or the one next to it
 * on the side the argument moves to when its value at 0 is an integer.
 */
function roundLeadingTerm(e: Fn, x: Sym, cdir: Expr): Expr | undefined {
  const arg = first(e.args);
  const arg0 = valueAtZero(arg, x, cdir);
  if (!isFiniteNumber(arg0)) return undefined;
  const r = fn(e.name, [arg0]);
  if (r.key !== arg0.key) return r;
  const ndir = dir(arg, x, cdir instanceof Rational && cdir.isZero ? 1 : cdir);
  const down = isNegative(ndir) === true;
  if (!down && isPositive(ndir) !== true) throw new NotImplementedError(`Not sure of sign of ${ndir.toString()}`);
  if (e.name === 'floor') return down ? add(r, -1) : r;
  return down ? r : add(r, 1);
}
leadingTermRules.floor = roundLeadingTerm;
leadingTermRules.ceiling = roundLeadingTerm;

/** SymPy frac._eval_as_leading_term. */
leadingTermRules.frac = (e, x, cdir) => {
  const arg = first(e.args);
  const arg0 = subs(arg, [[x, 0]]);
  if (arg0 instanceof Special) return arg0.name === 'nan' ? undefined : AccumBounds(0, 1);
  if (arg0.freeSymbols().size > 0) return undefined;
  const r = fn('frac', [arg0]);
  if (!(r instanceof Rational && r.isZero)) return r;
  if (isNegative(dir(arg, x, cdir)) === true) return S.One;
  return asLeadingTerm(sub(arg, arg0), x, { cdir });
};

/** The infinite value (oo, -oo or zoo) an argument tends to as x -> 0 from the side of cdir, or undefined. */
function infiniteAtZero(arg: Expr, x: Sym, cdir: Expr): Special | undefined {
  let v = subs(arg, [[x, 0]]);
  if (v instanceof Special && v.name === 'zoo') v = limit(arg, x, 0, isNegative(cdir) === true ? '-' : '+');
  return v instanceof Special && v.name !== 'nan' ? v : undefined;
}

// SymPy trigonometric _eval_as_leading_term: the values accumulate on an interval at an infinite argument
for (const [name, lo, hi] of [['sin', -1, 1], ['cos', -1, 1], ['tan', S.NegativeInfinity, S.Infinity], ['cot', S.NegativeInfinity, S.Infinity], ['sec', S.NegativeInfinity, S.Infinity], ['csc', S.NegativeInfinity, S.Infinity]] as const) {
  leadingTermRules[name] = (e, x, cdir) => (infiniteAtZero(first(e.args), x, cdir) === undefined ? undefined : AccumBounds(lo, hi));
}
// SymPy hyperbolic _eval_as_leading_term: a function of an infinite argument is its own leading term
for (const name of ['sinh', 'cosh', 'tanh', 'coth']) leadingTermRules[name] = (e, x, cdir) => (infiniteAtZero(first(e.args), x, cdir) === undefined ? undefined : e);
/** Leading term of the logarithmic rewrite on the ray selected by cdir (SymPy inverse functions). */
function logarithmicLeadingTerm(e: Fn, x: Sym, cdir: Expr): Expr {
  return expandMul(asLeadingTerm(rewrite(e, 'log'), x, { cdir }));
}

// The branch-cut corrections below follow SymPy's _eval_as_leading_term methods. At a branch
// point, expand the logarithmic identity instead of differentiating a singular inverse function.
for (const name of ['asin', 'acos', 'atan', 'acot', 'asec', 'acsc', 'asinh', 'acosh', 'atanh', 'acoth', 'asech', 'acsch']) {
  leadingTermRules[name] = (e, x, cdir) => {
    const arg = first(e.args);
    if (!arg.has(x)) return e;
    const x0 = subs(arg, [[x, 0]]);
    if (x0 instanceof Special && x0.name === 'nan') {
      const value = fn(e.name, [asLeadingTerm(arg, x, { cdir })]);
      if (isZeroExpr(value)) return logarithmicLeadingTerm(e, x, cdir);
      return value instanceof Special ? e : value;
    }
    if (x0 instanceof Special) return logarithmicLeadingTerm(e, x, cdir);
    const zero = isZeroExpr(x0);
    const one = x0.key === S.One.key;
    const minusOne = x0.key === S.NegOne.key;
    const imaginaryUnit = x0.key === S.I.key || x0.key === neg(S.I).key;
    if ((name === 'asin' || name === 'atan' || name === 'asinh' || name === 'atanh') && zero) return asLeadingTerm(arg, x, { cdir });
    if ((name === 'acos' || name === 'asec') && one) {
      return mul(pow(2, S.Half), pow(asLeadingTerm(name === 'acos' ? sub(1, arg) : sub(arg, 1), x, { cdir }), S.Half));
    }
    const branchPoint = name === 'asin' || name === 'atanh' ? one || minusOne
      : name === 'acos' ? minusOne
      : name === 'atan' || name === 'asinh' ? imaginaryUnit
      : name === 'acot' || name === 'acsch' ? imaginaryUnit || zero
      : name === 'asec' ? minusOne || zero
      : one || minusOne || zero;
    if (branchPoint) return logarithmicLeadingTerm(e, x, cdir);
    const value = fn(e.name, [x0]);
    const square = pow(x0, 2);
    const realOutside = isNegative(sub(1, square)) === true;
    const imaginaryOutside = isNegative(add(1, square)) === true;
    const realInside = isNegative(neg(sub(1, square))) === true && isZeroExpr(im(x0));
    const imaginaryInside = isNegative(neg(add(1, square))) === true && isZeroExpr(re(x0));
    const onCut = name === 'asin' || name === 'acos' || name === 'atanh' ? realOutside
      : name === 'atan' || name === 'asinh' ? imaginaryOutside
      : name === 'acot' || name === 'acsch' ? imaginaryInside
      : name === 'acosh' ? isNegative(sub(x0, 1)) === true
      : name === 'asech' ? isNegative(x0) === true || isNegative(sub(1, x0)) === true
      : realInside;
    if (!onCut) return value;
    const ndir = dir(arg, x, isZeroExpr(cdir) ? S.One : cdir);
    const horizontal = name === 'atan' || name === 'acot' || name === 'asinh' || name === 'acsch';
    const component = horizontal ? re(ndir) : im(ndir);
    const positive = isPositive(component) === true;
    const negative = isNegative(component) === true;
    if (!positive && !negative) return logarithmicLeadingTerm(e, x, cdir);
    const pos = isPositive(horizontal ? im(x0) : x0) === true;
    const ipi = mul(S.I, S.Pi);
    switch (name) {
      case 'asin': return positive && pos ? sub(S.Pi, value) : negative && !pos ? sub(neg(S.Pi), value) : value;
      case 'acos': return positive && pos ? neg(value) : negative && !pos ? sub(mul(2, S.Pi), value) : value;
      case 'atan': return negative && pos ? sub(value, S.Pi) : positive && !pos ? add(value, S.Pi) : value;
      case 'acot': return positive && pos ? add(value, S.Pi) : negative && !pos ? sub(value, S.Pi) : value;
      case 'asec': return negative && pos ? neg(value) : positive && !pos ? sub(mul(2, S.Pi), value) : value;
      case 'acsc': return negative && pos ? sub(S.Pi, value) : positive && !pos ? sub(neg(S.Pi), value) : value;
      case 'asinh': return positive && !pos ? sub(neg(value), ipi) : negative && pos ? add(neg(value), ipi) : value;
      case 'atanh': return negative && !pos ? sub(value, ipi) : positive && pos ? add(value, ipi) : value;
      case 'acoth': return negative && pos ? add(value, ipi) : positive && !pos ? sub(value, ipi) : value;
      case 'acsch': return positive && pos ? sub(neg(value), ipi) : negative && !pos ? add(neg(value), ipi) : value;
      case 'acosh': return negative ? isNegative(add(x0, 1)) === true ? sub(value, mul(2, ipi)) : neg(value) : value;
      default: return positive ? pos || isNegative(add(x0, 1)) === true ? neg(value) : sub(value, mul(2, ipi)) : value;
    }
  };
}

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Algorithms that help identify numbers and sequences (SymPy
 * sympy.concrete.guess): recurrence relations of a sequence of rational
 * numbers, rationals from floating-point values by continued fractions,
 * generating functions and closed formulas (products of rising factorials)
 * of sequences.
 *
 * Ported from SymPy 1.14 (sympy/concrete/guess.py, BSD-3-Clause, Copyright
 * (c) SymPy Development Team).
 */

import type { Expr, ExprLike } from '../core/nodes';
import { Rational, S, Sym } from '../core/nodes';
import { add, div, exp, mul, neg, pow, sub, sympify } from '../core/ops';
import { isNegative, isZero } from '../core/assumptions';
import { at } from '../core/guard';
import { Product } from '../core/concrete';
import type { NoMatchResult } from '../core/truth';
import { NoMatch, isNoMatch } from '../core/truth';
import { subs } from '../core/traverse';
import type { UndefinedFunction } from '../core/undef';
import { SymFunction } from '../core/undef';
import { ceiling, floor } from '../functions/special/special';
import { polyLcm } from '../polys/sympoly';
import { rationalInterpolate } from '../polys/polyfuncs';
import { denom } from '../simplify/rational';
import { product } from './summations';

// default arguments (module constants keep the parameter lists free of calls)
const defaultA: UndefinedFunction = /* @__PURE__ */ SymFunction('a');
const defaultN: Sym = /* @__PURE__ */ new Sym('n');
const defaultX: Sym = /* @__PURE__ */ new Sym('x');

/** Python's x == 0 for a SymPy number: zero (an exact or floating-point zero). */
const isZeroValue = (e: Expr): boolean => isZero(e) === true;

/** Python int(x): x truncated toward zero. */
function truncate(e: Expr): Expr {
  if (e instanceof Rational) return Rational.of(e.p / e.q);
  return isNegative(e) === true ? ceiling(e) : floor(e);
}

/**
 * The vector of a recurrence relation of order n found in the sequence of
 * rational numbers l (SymPy find_simple_recurrence_vector): the
 * coefficients [c0, ..., cn] (integers, c0 > 0) of
 * c0*a(n + k) + c1*a(n + k - 1) + ... = 0, or [0] when no relation is
 * found.
 *
 * Example: findSimpleRecurrenceVector(fibonacci(0..11)) is [1, -1, -1].
 */
export function findSimpleRecurrenceVector(lIn: readonly ExprLike[]): Expr[] {
  let l = lIn.map(sympify);
  let q1: Expr[] = [S.Zero];
  let q2: Expr[] = [S.One];
  let b = 0;
  const z = l.length >> 1;
  while (q2.length <= z) {
    while (isZeroValue(at(l, b))) {
      b++;
      if (b === l.length) {
        let c: Expr = S.One;
        for (const x of q2) c = polyLcm(c, denom(x));
        if (isNegative(mul(at(q2, 0), c)) === true) c = neg(c);
        return q2.map((x) => truncate(mul(x, c)));
      }
    }
    const a = div(S.One, at(l, b));
    const m: Expr[] = [a];
    for (let k = b + 1; k < l.length; k++) {
      // SymPy indexes m[b - j - 1] from the end of m
      const terms: Expr[] = [];
      for (let j = b; j < k; j++) terms.push(mul(at(l, j + 1), at(m, k - j - 1)));
      m.push(mul(neg(add(...terms)), a));
    }
    l = m;
    const next: Expr[] = Array.from({ length: Math.max(q2.length, b + q1.length) }, () => S.Zero);
    q2.forEach((q, k) => (next[k] = mul(a, q)));
    q1.forEach((q, k) => (next[k + b] = add(at(next, k + b), q)));
    // trailing zeros can occur
    while (isZeroValue(at(next, next.length - 1))) next.pop();
    q1 = q2;
    q2 = next;
    b = 1;
  }
  return [S.Zero];
}

/**
 * A recurrence relation of the sequence v of integers or rationals (SymPy
 * find_simple_recurrence), as an expression in A(N), A(N + 1), ... that
 * vanishes; 0 when no relation is found.
 *
 * Example: findSimpleRecurrence(fibonacci(0..11)) is
 * -a(n) - a(n + 1) + a(n + 2).
 */
export function findSimpleRecurrence(v: readonly ExprLike[], A: UndefinedFunction = defaultA, N: Expr = defaultN): Expr {
  const p = findSimpleRecurrenceVector(v);
  const n = p.length;
  if (n <= 1) return S.Zero;
  return add(...p.map((pk, k) => mul(A(add(N, n - 1 - k)), pk)));
}

/**
 * A rational number identified from a real number x by its continued
 * fraction (SymPy rationalize): the expansion stops at the first partial
 * quotient that is not smaller than maxcoeff.
 *
 * Example: rationalize(Float(0.333333333333333)) is 1/3; with maxcoeff 250,
 * pi gives 355/113.
 */
export function rationalize(xIn: ExprLike, maxcoeff: ExprLike = 10000): Expr {
  let x = sympify(xIn);
  const maxc = sympify(maxcoeff);
  let [p0, p1, q0, q1]: [Expr, Expr, Expr, Expr] = [S.Zero, S.One, S.One, S.Zero];
  let a = floor(x);
  while (isNegative(sub(a, maxc)) === true || isZeroValue(q1)) {
    const p = add(mul(a, p1), p0);
    const q = add(mul(a, q1), q0);
    [p0, p1] = [p1, p];
    [q0, q1] = [q1, q];
    if (isZeroValue(sub(x, a))) break;
    x = div(S.One, sub(x, a));
    a = floor(x);
  }
  return div(p1, q1);
}

/**
 * A rational generating function guessed for the sequence v of rational
 * numbers (SymPy guess_generating_function_rational), or NoMatch.
 *
 * Example: for fibonacci(5..14) it is (3*x + 5)/(-x**2 - x + 1).
 */
export function guessGeneratingFunctionRational(vIn: readonly ExprLike[], X: Expr = defaultX): Expr | NoMatchResult {
  const v = vIn.map(sympify);
  // the denominator from the recurrence relation
  const q = findSimpleRecurrenceVector(v);
  const n = q.length;
  if (n <= 1) return NoMatch;
  // the numerator
  const p = Array.from({ length: v.length >> 1 }, (_, i) => add(...Array.from({ length: Math.min(i + 1, n) }, (_u, k) => mul(at(v, i - k), at(q, k)))));
  return div(add(...p.map((pk, k) => mul(pk, pow(X, k)))), add(...q.map((qk, k) => mul(qk, pow(X, k)))));
}

/** Options of guessGeneratingFunction. */
export interface GuessGeneratingFunctionOptions {
  /**
   * The types of generating functions to look for: 'ogf', 'egf', 'lgf',
   * 'hlgf', 'lgdogf', 'lgdegf' or 'all' (the default). As in SymPy, a
   * single string is searched as a substring.
   */
  types?: readonly string[] | string;
  /** The greatest n-th root of a rational function that is tested (default 2). */
  maxsqrtn?: number;
}

/**
 * The self-convolutions t, t*w, t*w*w, ... of the sequence w, until one has
 * a rational generating function g: g**(1/d) for the d-th convolution, or
 * NoMatch.
 */
function rationalRoot(w: readonly Expr[], X: Expr, maxsqrtn: number): Expr | NoMatchResult {
  let t: Expr[] = [S.One, ...Array.from({ length: w.length - 1 }, () => S.Zero)];
  for (let d = 0; d < Math.max(1, maxsqrtn); d++) {
    const prev = t;
    t = Array.from({ length: w.length }, (_, n) => add(...Array.from({ length: n + 1 }, (_u, i) => mul(at(prev, n - i), at(w, i)))));
    const g = guessGeneratingFunctionRational(t, X);
    if (!isNoMatch(g) && !isZeroValue(g)) return pow(g, Rational.of(1n, BigInt(d + 1)));
  }
  return NoMatch;
}

/** The sequence divided by the factorials: v[i]/i!. */
function divideByFactorials(v: readonly Expr[]): Expr[] {
  let f: Expr = S.One;
  return v.map((k, i) => {
    f = mul(f, i === 0 ? 1 : i);
    return div(k, f);
  });
}

/** The coefficients of f'(x)/f(x) for the power series f with coefficients z. */
function logarithmicDerivative(z: readonly Expr[]): Expr[] {
  const a = at(z, 0);
  const w: Expr[] = [];
  for (let n = 0; n < z.length - 1; n++) {
    const terms = Array.from({ length: n }, (_, i) => mul(at(w, w.length - i - 1), at(z, i + 1)));
    w.push(div(sub(mul(at(z, n + 1), n + 1), add(...terms)), a));
  }
  return w;
}

/**
 * Generating functions guessed for the sequence v of rational numbers
 * (SymPy guess_generating_function), by type: 'ogf' (ordinary), 'egf'
 * (exponential), 'lgf' (logarithmic), 'hlgf' (hyperbolic logarithmic),
 * 'lgdogf' and 'lgdegf' (logarithmic derivatives of the ordinary and the
 * exponential ones). N-th roots of rational functions are detected up to
 * maxsqrtn.
 *
 * Example: for 1, 2, 3, ... with types ['ogf', 'lgf', 'hlgf'] it is
 * Map { ogf: 1/(x**2 - 2*x + 1), lgf: 1/(x + 1), hlgf: 1/(1 - x) }.
 */
export function guessGeneratingFunction(vIn: readonly ExprLike[], X: Expr = defaultX, opts: GuessGeneratingFunctionOptions = {}): Map<string, Expr> {
  const v = vIn.map(sympify);
  const t0 = opts.types ?? ['all'];
  const types: readonly string[] | string = t0.includes('all') ? ['ogf', 'egf', 'lgf', 'hlgf', 'lgdogf', 'lgdegf'] : t0;
  const maxsqrtn = opts.maxsqrtn ?? 2;
  const result = new Map<string, Expr>();
  const tryType = (name: string, w: readonly Expr[]): Expr | NoMatchResult => {
    const g = rationalRoot(w, X, maxsqrtn);
    if (!isNoMatch(g)) result.set(name, g);
    return g;
  };

  // ordinary generating function
  if (types.includes('ogf')) tryType('ogf', v);
  // exponential generating function: division by the factorials
  if (types.includes('egf')) tryType('egf', divideByFactorials(v));
  // logarithmic generating function: multiplication by (-1)**(n + 1)/n
  if (types.includes('lgf')) tryType('lgf', v.map((k, i) => div(mul(i % 2 === 0 ? 1 : -1, k), i + 1)));
  // hyperbolic logarithmic generating function: division by n + 1
  if (types.includes('hlgf')) tryType('hlgf', v.map((k, i) => div(k, i + 1)));
  const v0Nonzero = !isZeroValue(at(v, 0));
  // logarithmic derivative of the ordinary generating function; log(f(x)) is the integral of f'(x)/f(x)
  if (v0Nonzero && (types.includes('lgdogf') || (types.includes('ogf') && !result.has('ogf')))) {
    const g = tryType('lgdogf', logarithmicDerivative(v));
    if (!isNoMatch(g) && !result.has('ogf')) result.set('ogf', exp(g.integrate(asSym(X))));
  }
  // logarithmic derivative of the exponential generating function
  if (v0Nonzero && (types.includes('lgdegf') || (types.includes('egf') && !result.has('egf')))) {
    const g = tryType('lgdegf', logarithmicDerivative(divideByFactorials(v)));
    if (!isNoMatch(g) && !result.has('egf')) result.set('egf', exp(g.integrate(asSym(X))));
  }
  return result;
}

/** The variable of integration X (SymPy integrates with respect to any symbol). */
function asSym(X: Expr): Sym {
  if (X instanceof Sym) return X;
  throw new TypeError('guess_generating_function: X must be a symbol');
}

/** Options of guess. */
export interface GuessOptions {
  /** true: go on with the next iterations after formulas are found (default false). */
  all?: boolean;
  /** false: leave the products unevaluated (default true). */
  evaluate?: boolean;
  /** The number of iterations (default 2, at most the length of the sequence minus 1). */
  niter?: number;
  /** The symbols to use (the first is the main variable); default i0, i1, .... */
  variables?: readonly Sym[];
}

/**
 * Formulas guessed for the sequence l of rational numbers (SymPy guess,
 * adapted from Christian Krattenthaler's Rate.m): rational functions of the
 * main variable i0 at the first iteration, products of rising factorials
 * at the second, products of such products at the third, and so on.
 *
 * Example: guess([1, 2, 6, 24, 120], { evaluate: false }) is
 * [Product(i1 + 1, (i1, 1, i0 - 1))].
 */
export function guess(lIn: readonly ExprLike[], opts: GuessOptions = {}): Expr[] {
  let l = lIn.map(sympify);
  if (l.slice(0, -1).some(isZeroValue)) return [];
  const N = l.length;
  const niter = Math.min(N - 1, opts.niter ?? 2);
  const myprod = opts.evaluate === false ? Product : product;
  const g: Expr[][] = [];
  const res: Expr[] = [];
  const symb = opts.variables ?? Array.from({ length: niter }, (_, i) => new Sym(`i${i}`));
  for (const [k, s] of symb.entries()) {
    g.push(l);
    const n = l.length;
    let r: Expr[] = [];
    const gk = at(g, k);
    const data = gk.slice(0, -1).map((y, i): [Expr, Expr] => [Rational.of(BigInt(i + 1)), y]);
    for (let i = n - 3; i >= 0; i--) {
      const ri = rationalInterpolate(data, i, s);
      const atN = subs(ri, [[s, n]]);
      if (!isZeroValue(subs(denom(ri), [[s, n]])) && isZeroValue(sub(atN, at(gk, gk.length - 1))) && !r.some((x) => x.key === ri.key)) r.push(ri);
    }
    if (r.length) {
      for (let i = k - 1; i >= 0; i--) {
        const lim: [Sym, Expr, Expr] = [at(symb, i + 1), S.One, sub(at(symb, i), 1)];
        r = r.map((x) => mul(at(at(g, i), 0), myprod(x, lim)));
      }
      if (opts.all !== true) return r;
      res.push(...r);
    }
    const prev = l;
    l = Array.from({ length: N - k - 1 }, (_, i) => div(at(prev, i + 1), at(prev, i)));
  }
  return res;
}

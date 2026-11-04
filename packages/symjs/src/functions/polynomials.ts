// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (functions/special/polynomials.py and the dense
// generators of polys/orthopolys.py), Copyright (c) 2006-2023 SymPy
// Development Team, BSD 3-Clause License (see LICENSE).

/**
 * @file Orthogonal polynomials (SymPy functions/special/polynomials.py):
 * jacobi, gegenbauer, chebyshevt, chebyshevu, legendre, assoc_legendre,
 * hermite, hermite_prob, laguerre and assoc_laguerre with SymPy's evaluation
 * rules, derivatives, conjugates and rewrites, chebyshevt_root,
 * chebyshevu_root and jacobi_normalized, and the coefficient generators that
 * polys/orthopolys.ts builds its Poly results from.
 */

import { at, defined, first, pair } from '../core/guard';
import { isIntegerQ, isNegative, isPositive, isZero } from '../core/assumptions';
import type { ComplexValue as C, Expr, ExprLike } from '../core/nodes';
import { Dummy, Float, Rational, S, Special, Sym } from '../core/nodes';
import { Sum } from '../core/concrete';
import { add, couldExtractMinusSign, exp, mul, neg, pow, sqrt, sympify } from '../core/ops';
import { derivative } from '../core/undef';
import { SubsNode } from '../core/subsnode';
import { fnPartials } from '../calculus/diff';
import { numericFns } from '../numeric/evalf';
import { mpFns } from '../numeric/mpeval';
import * as MF from '../numeric/mpf';
import '../numeric/mpspecialfns';
import { chermite, claguerre } from '../numeric/mporthopoly';
import { expand } from '../simplify/expand';
import { registerRewrite } from '../simplify/rewrite';
import { conjugate, conjugateRules, cos, evaluators, fn, re } from './elementary';
import { binomial, factorial, gamma, rf } from './special';
import { hyper } from './hyper';

// ---- coefficient generators (SymPy polys/orthopolys.py) -----------------------------

/** Coefficients, lowest power first. */
export type Coeffs = Expr[];

const big = (cs: readonly bigint[]): Coeffs => cs.map((c) => Rational.of(c));

/** p(x) from its coefficients (lowest power first). */
export function coeffsExpr(cs: readonly Expr[], x: Expr): Expr {
  return add(...cs.map((c, k) => mul(c, pow(x, k))));
}

const shift = (p: readonly bigint[]): bigint[] => [0n, ...p];
/** p - q for a p at least as long as q (the recurrences subtract a lower-degree polynomial). */
const sub = (p: readonly bigint[], q: readonly bigint[]): bigint[] => p.map((v, i) => v - (q[i] ?? 0n));
const scale = (p: readonly bigint[], c: bigint): bigint[] => p.map((v) => v * c);

/** m1 <- next(m1, m2, i) for i = 2..n from m2 = 1 and m1 (SymPy's three-term recurrences). */
function recurrence(n: number, m1Start: bigint[], next: (m1: bigint[], m2: bigint[], i: number) => bigint[]): bigint[] {
  if (n < 1) return [1n];
  let m2: bigint[] = [1n];
  let m1 = m1Start;
  for (let i = 2; i <= n; i++) [m2, m1] = [m1, next(m1, m2, i)];
  return m1;
}

/** T_n (SymPy dup_chebyshevt). */
export const chebyshevtCoeffs = (n: number): Coeffs => big(recurrence(n, [0n, 1n], (m1, m2) => sub(scale(shift(m1), 2n), m2)));
/** U_n (SymPy dup_chebyshevu). */
export const chebyshevuCoeffs = (n: number): Coeffs => big(recurrence(n, [0n, 2n], (m1, m2) => sub(scale(shift(m1), 2n), m2)));
/** H_n (SymPy dup_hermite). */
export const hermiteCoeffs = (n: number): Coeffs =>
  big(recurrence(n, [0n, 2n], (m1, m2, i) => scale(sub(shift(m1), scale(m2, BigInt(i - 1))), 2n)));
/** He_n (SymPy dup_hermite_prob). */
export const hermiteProbCoeffs = (n: number): Coeffs => big(recurrence(n, [0n, 1n], (m1, m2, i) => sub(shift(m1), scale(m2, BigInt(i - 1)))));

function binom(n: number, k: number): bigint {
  let r = 1n;
  for (let i = 0; i < k; i++) r = (r * BigInt(n - i)) / BigInt(i + 1);
  return r;
}
function fact(n: number): bigint {
  let r = 1n;
  for (let i = 2; i <= n; i++) r *= BigInt(i);
  return r;
}

/** P_n = 2^-n sum_k (-1)^k C(n, k) C(2n - 2k, n) x^(n - 2k) (the coefficients of SymPy dup_legendre). */
export function legendreCoeffs(n: number): Coeffs {
  const cs: Coeffs = Array.from({ length: n + 1 }, () => S.Zero);
  for (let k = 0; 2 * k <= n; k++) cs[n - 2 * k] = Rational.of((k % 2 ? -1n : 1n) * binom(n, k) * binom(2 * n - 2 * k, n), 2n ** BigInt(n));
  return cs;
}

/** (a)_k as a product of k linear factors. */
const rising = (a: Expr, k: number): Expr => mul(...Array.from({ length: k }, (_, i) => add(a, i)));

/**
 * P_n^(a,b) = 1/n! sum_k C(n, k) (a + b + n + 1)_k (a + k + 1)_(n - k) ((x - 1)/2)^k, the
 * polynomial of SymPy dup_jacobi with coefficients expanded in a and b.
 */
export function jacobiCoeffs(n: number, a: Expr, b: Expr): Coeffs {
  const terms: Expr[][] = Array.from({ length: n + 1 }, () => []);
  for (let k = 0; k <= n; k++) {
    const r = mul(Rational.of(binom(n, k), fact(n) * 2n ** BigInt(k)), rising(add(a, b, n + 1), k), rising(add(a, k + 1), n - k));
    for (let j = 0; j <= k; j++) at(terms, j).push(mul(Rational.of(((k - j) % 2 ? -1n : 1n) * binom(k, j)), r));
  }
  return terms.map((t) => expand(add(...t)));
}

/** C_n^(a) = sum_k (-1)^k (a)_(n - k) (2x)^(n - 2k)/(k! (n - 2k)!) (SymPy dup_gegenbauer). */
export function gegenbauerCoeffs(n: number, a: Expr): Coeffs {
  const cs: Coeffs = Array.from({ length: n + 1 }, () => S.Zero);
  for (let k = 0; 2 * k <= n; k++) {
    const c = Rational.of((k % 2 ? -1n : 1n) * 2n ** BigInt(n - 2 * k), fact(k) * fact(n - 2 * k));
    cs[n - 2 * k] = expand(mul(c, rising(a, n - k)));
  }
  return cs;
}

/** L_n^(a) = sum_k (-1)^k (a + k + 1)_(n - k) x^k/(k! (n - k)!) (SymPy dup_laguerre). */
export function laguerreCoeffs(n: number, alpha: Expr): Coeffs {
  return Array.from({ length: n + 1 }, (_, k) => expand(mul(Rational.of(k % 2 ? -1n : 1n, fact(k) * fact(n - k)), rising(add(alpha, k + 1), n - k))));
}

// ---- evaluation (SymPy eval classmethods) ----------------------------------------------

const ValueError = RangeError;
const isNumber = (e: Expr): e is Rational | Float => e instanceof Rational || e instanceof Float;
/** A nonnegative integer that fits a JS number (the orders the generators take). */
/**
 * SymPy n.is_integer, where a Float is an integer only when it is zero (an
 * integral nonzero Float is undecided, a non-integral one is not an integer).
 */
function isIntegerSympy(n: Expr): boolean | undefined {
  if (n instanceof Float) return n.value === 0 ? true : Number.isInteger(n.value) ? undefined : false;
  return isIntegerQ(n);
}
const MAX_ORDER = 100000n;
/** The order of SymPy _eval_at_order: n when n.is_integer and n >= 0 (a nonnegative integer, or the Float 0). */
const order = (n: Expr): number | undefined => {
  if (n instanceof Float) return n.value === 0 ? 0 : undefined;
  return n instanceof Rational && n.q === 1n && n.p >= 0n && n.p <= MAX_ORDER ? Number(n.p) : undefined;
};
/** Python int(n) of a nonnegative number n (truncation, as jacobi, gegenbauer and assoc_laguerre call their generators). */
const truncated = (n: Rational | Float): number | undefined => {
  const t = n instanceof Rational ? n.p / n.q : BigInt(Math.trunc(n.value));
  return t <= MAX_ORDER ? Number(t) : undefined;
};
const same = (a: Expr, b: Expr): boolean => a.key === b.key;
const isOo = (e: Expr): boolean => e instanceof Special && e.name === 'oo';
const isNegOo = (e: Expr): boolean => e instanceof Special && e.name === '-oo';
const isOne = (e: Expr): boolean => e instanceof Rational && e.isOne;
const minusOneTo = (n: Expr): Expr => pow(S.NegOne, n);

export const jacobi = (n: ExprLike, a: ExprLike, b: ExprLike, x: ExprLike): Expr => fn('jacobi', [n, a, b, x]);
export const gegenbauer = (n: ExprLike, a: ExprLike, x: ExprLike): Expr => fn('gegenbauer', [n, a, x]);
export const chebyshevt = (n: ExprLike, x: ExprLike): Expr => fn('chebyshevt', [n, x]);
export const chebyshevu = (n: ExprLike, x: ExprLike): Expr => fn('chebyshevu', [n, x]);
export const legendre = (n: ExprLike, x: ExprLike): Expr => fn('legendre', [n, x]);
export const assocLegendre = (n: ExprLike, m: ExprLike, x: ExprLike): Expr => fn('assoc_legendre', [n, m, x]);
export const hermite = (n: ExprLike, x: ExprLike): Expr => fn('hermite', [n, x]);
export const hermiteProb = (n: ExprLike, x: ExprLike): Expr => fn('hermite_prob', [n, x]);
export const laguerre = (n: ExprLike, x: ExprLike): Expr => fn('laguerre', [n, x]);
export const assocLaguerre = (n: ExprLike, alpha: ExprLike, x: ExprLike): Expr => fn('assoc_laguerre', [n, alpha, x]);

/**
 * SymPy jacobi.eval; a numeric non-integer n is truncated with int(n) as in
 * SymPy (degrees above 100000 stay unevaluated).
 */
function evalJacobi(n: Expr, a: Expr, b: Expr, x: Expr): Expr | undefined {
  if (same(a, b)) {
    if (same(a, S.NegHalf)) return mul(rf(S.Half, n), pow(factorial(n), -1), chebyshevt(n, x));
    if (isZero(a) === true) return legendre(n, x);
    if (same(a, S.Half)) return mul(rf(Rational.of(3, 2), n), pow(factorial(add(n, 1)), -1), chebyshevu(n, x));
    return mul(rf(add(a, 1), n), pow(rf(add(mul(2, a), 1), n), -1), gegenbauer(n, add(a, S.Half), x));
  }
  if (same(b, neg(a))) {
    const h = mul(a, S.Half);
    return mul(gamma(add(n, a, 1)), pow(gamma(add(n, 1)), -1), pow(add(1, x), h), pow(pow(add(1, neg(x)), h), -1), assocLegendre(n, neg(a), x));
  }
  if (!isNumber(n)) {
    if (couldExtractMinusSign(x)) return mul(minusOneTo(n), jacobi(n, b, a, neg(x)));
    if (isZero(x) === true) {
      return mul(pow(2, neg(n)), gamma(add(a, n, 1)), pow(mul(gamma(add(a, 1)), factorial(n)), -1), hyper([neg(n), add(neg(b), neg(n))], [add(a, 1)], -1));
    }
    if (isOne(x)) return mul(rf(add(a, 1), n), pow(factorial(n), -1));
    if (isOo(x) && isPositive(n) === true) {
      if (isIntegerQ(add(a, b, mul(2, n))) === true) throw new ValueError('Error. a + b + 2*n should not be an integer.');
      return mul(rf(add(a, b, n, 1), n), S.Infinity);
    }
    return undefined;
  }
  if (isNegative(n) === true) throw new ValueError(`Cannot generate Jacobi polynomial of index ${n.toString()}`);
  // SymPy jacobi_poly(n, ...) truncates a non-integer degree with int(n)
  const k = truncated(n);
  return k === undefined ? undefined : coeffsExpr(jacobiCoeffs(k, a, b), x);
}

/** SymPy gegenbauer.eval: zero for a negative n, int(n) for a numeric non-integer n. */
function evalGegenbauer(n: Expr, a: Expr, x: Expr): Expr | undefined {
  if (isNegative(n) === true) return S.Zero;
  if (same(a, S.Half)) return legendre(n, x);
  if (isOne(a)) return chebyshevu(n, x);
  if (same(a, S.NegOne)) return S.Zero;
  if (!isNumber(n)) {
    if (same(x, S.NegOne)) {
      if (isPositive(add(re(a), S.NegHalf)) === true) return S.ComplexInfinity;
      const g = mul(gamma(add(mul(2, a), n)), pow(mul(gamma(mul(2, a)), gamma(add(n, 1))), -1));
      return mul(cos(mul(S.Pi, add(a, n))), fn('sec', [mul(S.Pi, a)]), g);
    }
    if (couldExtractMinusSign(x)) return mul(minusOneTo(n), gegenbauer(n, a, neg(x)));
    if (isZero(x) === true) {
      const den = mul(gamma(mul(add(1, neg(n)), S.Half)), gamma(add(n, 1)), gamma(a));
      return mul(pow(2, n), sqrt(S.Pi), gamma(add(a, mul(S.Half, n))), pow(den, -1));
    }
    if (isOne(x)) return mul(gamma(add(mul(2, a), n)), pow(mul(gamma(mul(2, a)), gamma(add(n, 1))), -1));
    if (isOo(x) && isPositive(n) === true) return mul(rf(a, n), S.Infinity);
    return undefined;
  }
  // SymPy gegenbauer_poly(n, ...) truncates a non-integer degree with int(n)
  const k = truncated(n);
  return k === undefined ? undefined : coeffsExpr(gegenbauerCoeffs(k, a), x);
}

/** The polynomial of a nonnegative integer order (SymPy OrthogonalPolynomial._eval_at_order). */
const atOrder = (gen: (n: number) => Coeffs, n: Expr, x: Expr): Expr | undefined => {
  const k = order(n);
  return k === undefined ? undefined : coeffsExpr(gen(k), x);
};

function evalChebyshevt(n: Expr, x: Expr): Expr | undefined {
  if (isNumber(n)) return atOrder(chebyshevtCoeffs, isNegative(n) === true ? neg(n) : n, x);
  if (couldExtractMinusSign(x)) return mul(minusOneTo(n), chebyshevt(n, neg(x)));
  if (couldExtractMinusSign(n)) return chebyshevt(neg(n), x);
  if (isZero(x) === true) return cos(mul(S.Half, S.Pi, n));
  if (isOne(x)) return S.One;
  return isOo(x) ? S.Infinity : undefined;
}

function evalChebyshevu(n: Expr, x: Expr): Expr | undefined {
  if (isNumber(n)) {
    if (isNegative(n) !== true) return atOrder(chebyshevuCoeffs, n, x);
    if (same(n, S.NegOne)) return S.Zero;
    const p = atOrder(chebyshevuCoeffs, add(neg(n), -2), x);
    // SymPy negates the None of _eval_at_order for a non-integer -n - 2
    if (p === undefined) throw new TypeError("bad operand type for unary -: 'NoneType'");
    return neg(p);
  }
  if (couldExtractMinusSign(x)) return mul(minusOneTo(n), chebyshevu(n, neg(x)));
  if (couldExtractMinusSign(n)) {
    // (SymPy's n == -1 test here never holds: a number n is handled above)
    const m = add(neg(n), -2);
    if (!couldExtractMinusSign(m)) return neg(chebyshevu(m, x));
  }
  if (isZero(x) === true) return cos(mul(S.Half, S.Pi, n));
  if (isOne(x)) return add(1, n);
  return isOo(x) ? S.Infinity : undefined;
}

function evalLegendre(n: Expr, x: Expr): Expr | undefined {
  if (isNumber(n)) return atOrder(legendreCoeffs, isNegative(n) === true ? add(neg(n), -1) : n, x);
  if (couldExtractMinusSign(x)) return mul(minusOneTo(n), legendre(n, neg(x)));
  if (couldExtractMinusSign(n) && !couldExtractMinusSign(add(neg(n), -1))) return legendre(add(neg(n), -1), x);
  if (isZero(x) === true) return mul(sqrt(S.Pi), pow(mul(gamma(add(S.Half, mul(S.NegHalf, n))), gamma(add(1, mul(S.Half, n)))), -1));
  if (isOne(x)) return S.One;
  return isOo(x) ? S.Infinity : undefined;
}

/** (-1)^m (1 - x^2)^(m/2) d^m/dx^m P_n(x) (SymPy assoc_legendre._eval_at_order). */
function assocLegendreAt(n: number, m: number, x: Expr): Expr {
  let cs = legendreCoeffs(n);
  for (let i = 0; i < m; i++) cs = cs.slice(1).map((c, k) => mul(c, k + 1));
  return mul(m % 2 ? -1 : 1, pow(add(1, neg(pow(x, 2))), Rational.of(m, 2)), coeffsExpr(cs, x));
}

function evalAssocLegendre(n: Expr, m: Expr, x: Expr): Expr | undefined {
  if (couldExtractMinusSign(m)) {
    return mul(minusOneTo(neg(m)), factorial(add(m, n)), pow(factorial(add(n, neg(m))), -1), assocLegendre(n, neg(m), x));
  }
  if (same(m, S.Zero)) return legendre(n, x);
  if (same(x, S.Zero)) {
    const den = mul(gamma(mul(add(1, neg(m), neg(n)), S.Half)), gamma(add(1, mul(S.NegHalf, add(m, neg(n))))));
    return mul(pow(2, m), sqrt(S.Pi), pow(den, -1));
  }
  if (n instanceof Rational && m instanceof Rational && n.q === 1n && m.q === 1n) {
    if (n.p < 0n) throw new ValueError(`assoc_legendre: 1st index must be nonnegative integer (got ${n.toString()})`);
    if (m.p > n.p) throw new ValueError(`assoc_legendre: abs('2nd index') must be <= '1st index' (got ${n.toString()}, ${m.toString()})`);
    return assocLegendreAt(Number(n.p), Number(m.p), x);
  }
  return undefined;
}

function evalHermite(n: Expr, x: Expr, prob: boolean): Expr | undefined {
  const self = prob ? hermiteProb : hermite;
  if (isNumber(n)) {
    if (isNegative(n) === true) {
      // SymPy hermite_prob builds the ValueError without raising it
      if (prob) return undefined;
      throw new ValueError(`The index n must be nonnegative integer (got ${n.toString()})`);
    }
    return atOrder(prob ? hermiteProbCoeffs : hermiteCoeffs, n, x);
  }
  if (couldExtractMinusSign(x)) return mul(minusOneTo(n), self(n, neg(x)));
  if (isZero(x) === true) {
    const v = mul(sqrt(S.Pi), pow(gamma(mul(add(1, neg(n)), S.Half)), -1));
    return prob ? v : mul(pow(2, n), v);
  }
  return isOo(x) ? S.Infinity : undefined;
}

function evalLaguerre(n: Expr, x: Expr): Expr | undefined {
  if (isIntegerSympy(n) === false) throw new ValueError('Error: n should be an integer.');
  if (isNumber(n)) {
    if (isNegative(n) === true) return mul(exp(x), laguerre(add(neg(n), -1), neg(x)));
    return atOrder((k) => laguerreCoeffs(k, S.Zero), n, x);
  }
  if (couldExtractMinusSign(n) && !couldExtractMinusSign(add(neg(n), -1))) return mul(exp(x), laguerre(add(neg(n), -1), neg(x)));
  if (isZero(x) === true) return S.One;
  if (isNegOo(x)) return S.Infinity;
  return isOo(x) ? mul(minusOneTo(n), S.Infinity) : undefined;
}

function evalAssocLaguerre(n: Expr, alpha: Expr, x: Expr): Expr | undefined {
  if (isZero(alpha) === true) return laguerre(n, x);
  if (isNumber(n)) {
    if (isNegative(n) === true) throw new ValueError(`The index n must be nonnegative integer (got ${n.toString()})`);
    // SymPy laguerre_poly(n, x, alpha) truncates a non-integer degree with int(n)
    const k = truncated(n);
    return k === undefined ? undefined : coeffsExpr(laguerreCoeffs(k, alpha), x);
  }
  if (isZero(x) === true) return binomial(add(n, alpha), alpha);
  if (!isOo(x) && !isNegOo(x)) return undefined;
  // SymPy tests `n > 0` with Python's bool, a TypeError when it is undecided
  const pos = isPositive(n);
  if (pos === undefined) throw new TypeError(`cannot determine truth value of Relational: ${n.toString()} > 0`);
  if (!pos) return undefined;
  return isOo(x) ? mul(minusOneTo(n), S.Infinity) : S.Infinity;
}

/** An evaluator of a fixed number of arguments. */
const args4 = (f: (a: Expr, b: Expr, c: Expr, d: Expr) => Expr | undefined) => (...xs: Expr[]) => f(at(xs, 0), at(xs, 1), at(xs, 2), at(xs, 3));
const args3 = (f: (a: Expr, b: Expr, c: Expr) => Expr | undefined) => (...xs: Expr[]) => f(at(xs, 0), at(xs, 1), at(xs, 2));
const args2 = (f: (a: Expr, b: Expr) => Expr | undefined) => (...xs: Expr[]) => f(at(xs, 0), at(xs, 1));

evaluators.jacobi = args4(evalJacobi);
evaluators.gegenbauer = args3(evalGegenbauer);
evaluators.chebyshevt = args2(evalChebyshevt);
evaluators.chebyshevu = args2(evalChebyshevu);
evaluators.legendre = args2(evalLegendre);
evaluators.assoc_legendre = args3(evalAssocLegendre);
evaluators.hermite = args2((n, x) => evalHermite(n, x, false));
evaluators.hermite_prob = args2((n, x) => evalHermite(n, x, true));
evaluators.laguerre = args2(evalLaguerre);
evaluators.assoc_laguerre = args3(evalAssocLaguerre);

/** SymPy chebyshevt_root(n, k) = cos(pi (2k + 1)/(2n)), the k-th root of T_n. */
export function chebyshevtRoot(nIn: ExprLike, kIn: ExprLike): Expr {
  const [n, k] = rootIndices(nIn, kIn);
  return cos(mul(S.Pi, add(mul(2, k), 1), pow(mul(2, n), -1)));
}

/** SymPy chebyshevu_root(n, k) = cos(pi (k + 1)/(n + 1)), the k-th root of U_n. */
export function chebyshevuRoot(nIn: ExprLike, kIn: ExprLike): Expr {
  const [n, k] = rootIndices(nIn, kIn);
  return cos(mul(S.Pi, add(k, 1), pow(add(n, 1), -1)));
}

function rootIndices(nIn: ExprLike, kIn: ExprLike): [Expr, Expr] {
  const n = sympify(nIn);
  const k = sympify(kIn);
  if (!(n instanceof Rational && k instanceof Rational && k.value >= 0 && k.value < n.value)) {
    throw new ValueError(`must have 0 <= k < n, got k = ${k.toString()} and n = ${n.toString()}`);
  }
  return [n, k];
}

/** SymPy jacobi_normalized: P_n^(a,b)(x) divided by the square root of its norm. */
export function jacobiNormalized(n: ExprLike, a: ExprLike, b: ExprLike, x: ExprLike): Expr {
  const nfactor = mul(
    pow(2, add(a, b, 1)),
    gamma(add(n, a, 1)),
    gamma(add(n, b, 1)),
    pow(add(mul(2, n), a, b, 1), -1),
    pow(mul(factorial(n), gamma(add(n, a, b, 1))), -1),
  );
  return mul(jacobi(n, a, b, x), pow(sqrt(nfactor), -1));
}

// ---- derivatives (SymPy fdiff) ----------------------------------------------------------

/** d f/d args[i] for an index SymPy has no formula for: Derivative(f, args[i]) for a symbol, else NotImplementedError. */
function noPartial(name: Parameters<typeof fn>[0], args: readonly Expr[], i: number): Expr {
  // SymPy Function.fdiff: Derivative(f, v) for a symbol v not in the other arguments, else Subs(Derivative(f(xi), xi), xi, v)
  const v = at(args, i);
  if (v instanceof Sym && !args.some((b, j) => j !== i && b.has(v))) return derivative(fn(name, args), [[v, 1]]);
  const xi = new Dummy(`xi_${i + 1}`);
  return new SubsNode([derivative(fn(name, args.map((b, j) => (j === i ? xi : b))), [[xi, 1]]), xi, v]);
}

fnPartials.jacobi = (args, i) => {
  const [n, a, b, x] = [at(args, 0), at(args, 1), at(args, 2), at(args, 3)];
  if (i === 3) return mul(mul(S.Half, add(a, b, n, 1)), jacobi(add(n, -1), add(a, 1), add(b, 1), x));
  if (i === 0) return noPartial('jacobi', args, i);
  const k = new Dummy('k');
  const f1 = pow(add(a, b, n, k, 1), -1);
  const ra = i === 1 ? add(b, k, 1) : add(a, k, 1);
  const sign = i === 1 ? S.One : minusOneTo(add(n, neg(k)));
  const f2 = mul(sign, add(a, b, mul(2, k), 1), rf(ra, add(n, neg(k))), pow(mul(add(n, neg(k)), rf(add(a, b, k, 1), add(n, neg(k)))), -1));
  return Sum(mul(f1, add(jacobi(n, a, b, x), mul(f2, jacobi(k, a, b, x)))), [k, 0, add(n, -1)]);
};
fnPartials.gegenbauer = (args, i) => {
  const [n, a, x] = [at(args, 0), at(args, 1), at(args, 2)];
  if (i === 2) return mul(2, a, gegenbauer(add(n, -1), add(a, 1), x));
  if (i === 0) return noPartial('gegenbauer', args, i);
  const k = new Dummy('k');
  // Python's left-to-right products: 2*(1 + (-1)**(n - k)) distributes first
  const factor1 = mul(mul(2, add(1, minusOneTo(add(n, neg(k))))), add(k, a), pow(mul(add(k, n, mul(2, a)), add(n, neg(k))), -1));
  const factor2 = add(
    mul(mul(2, add(k, 1)), pow(mul(add(k, mul(2, a)), add(mul(2, k), mul(2, a), 1)), -1)),
    mul(2, pow(add(k, n, mul(2, a)), -1)),
  );
  return Sum(add(mul(factor1, gegenbauer(k, a, x)), mul(factor2, gegenbauer(n, a, x))), [k, 0, add(n, -1)]);
};
/** The partial derivatives of f(n, x) with the formula `dx` for d/dx. */
const inX = (name: Parameters<typeof fn>[0], dx: (n: Expr, x: Expr) => Expr) => (args: readonly Expr[], i: number) =>
  i === 1 ? dx(...pair(args)) : noPartial(name, args, i);
fnPartials.chebyshevt = inX('chebyshevt', (n, x) => mul(n, chebyshevu(add(n, -1), x)));
fnPartials.chebyshevu = inX('chebyshevu', (n, x) =>
  mul(add(mul(add(n, 1), chebyshevt(add(n, 1), x)), neg(mul(x, chebyshevu(n, x)))), pow(add(pow(x, 2), -1), -1)),
);
fnPartials.legendre = inX('legendre', (n, x) => mul(n, pow(add(pow(x, 2), -1), -1), add(mul(x, legendre(n, x)), neg(legendre(add(n, -1), x)))));
fnPartials.hermite = inX('hermite', (n, x) => mul(2, n, hermite(add(n, -1), x)));
fnPartials.hermite_prob = inX('hermite_prob', (n, x) => mul(n, hermiteProb(add(n, -1), x)));
fnPartials.laguerre = inX('laguerre', (n, x) => neg(assocLaguerre(add(n, -1), 1, x)));
fnPartials.assoc_legendre = (args, i) => {
  const [n, m, x] = [at(args, 0), at(args, 1), at(args, 2)];
  if (i !== 2) return noPartial('assoc_legendre', args, i);
  return mul(pow(add(pow(x, 2), -1), -1), add(mul(x, n, assocLegendre(n, m, x)), neg(mul(add(m, n), assocLegendre(add(n, -1), m, x)))));
};
fnPartials.assoc_laguerre = (args, i) => {
  const [n, alpha, x] = [at(args, 0), at(args, 1), at(args, 2)];
  if (i === 2) return neg(assocLaguerre(add(n, -1), add(alpha, 1), x));
  if (i === 0) return noPartial('assoc_laguerre', args, i);
  const k = new Dummy('k');
  return Sum(mul(assocLaguerre(k, alpha, x), pow(add(n, neg(alpha)), -1)), [k, 0, add(n, -1)]);
};

// ---- conjugates (SymPy _eval_conjugate) -------------------------------------------------

// OrthogonalPolynomial: f(n, conjugate(x)); the subclasses with parameters conjugate them too
for (const name of ['chebyshevt', 'chebyshevu', 'legendre', 'hermite', 'hermite_prob', 'laguerre'] as const) {
  conjugateRules[name] = (args) => fn(name, [first(args), conjugate(at(args, 1))]);
}
for (const name of ['jacobi', 'gegenbauer', 'assoc_legendre', 'assoc_laguerre'] as const) {
  conjugateRules[name] = (args) => fn(name, [first(args), ...args.slice(1).map(conjugate)]);
}

// ---- rewrites as sums (SymPy _eval_rewrite_as_Sum / _as_polynomial) -----------------------

const notNonnegativeInteger = (n: Expr): boolean => isNegative(n) === true || isIntegerQ(n) === false;
const floorHalf = (n: Expr): Expr => fn('floor', [mul(S.Half, n)]);

const SUMS: Partial<Record<Parameters<typeof fn>[0], (args: readonly Expr[]) => Expr | undefined>> = {
  jacobi: (args) => {
    const [n, a, b, x] = [at(args, 0), at(args, 1), at(args, 2), at(args, 3)];
    if (notNonnegativeInteger(n)) throw new ValueError('Error: n should be a non-negative integer.');
    const k = new Dummy('k');
    const kern = mul(rf(neg(n), k), rf(add(a, b, n, 1), k), rf(add(a, k, 1), add(n, neg(k))), pow(factorial(k), -1), pow(mul(add(1, neg(x)), S.Half), k));
    return mul(pow(factorial(n), -1), Sum(kern, [k, 0, n]));
  },
  gegenbauer: (args) => {
    const [n, a, x] = [at(args, 0), at(args, 1), at(args, 2)];
    const k = new Dummy('k');
    const kern = mul(minusOneTo(k), rf(a, add(n, neg(k))), pow(mul(2, x), add(n, mul(-2, k))), pow(mul(factorial(k), factorial(add(n, mul(-2, k)))), -1));
    return Sum(kern, [k, 0, floorHalf(n)]);
  },
  chebyshevt: (args) => {
    const [n, x] = pair(args);
    const k = new Dummy('k');
    return Sum(mul(binomial(n, mul(2, k)), pow(add(pow(x, 2), -1), k), pow(x, add(n, mul(-2, k)))), [k, 0, floorHalf(n)]);
  },
  chebyshevu: (args) => {
    const [n, x] = pair(args);
    const k = new Dummy('k');
    const kern = mul(minusOneTo(k), factorial(add(n, neg(k))), pow(mul(2, x), add(n, mul(-2, k))), pow(mul(factorial(k), factorial(add(n, mul(-2, k)))), -1));
    return Sum(kern, [k, 0, floorHalf(n)]);
  },
  legendre: (args) => {
    const [n, x] = pair(args);
    const k = new Dummy('k');
    const kern = mul(minusOneTo(k), pow(binomial(n, k), 2), pow(mul(add(1, x), S.Half), add(n, neg(k))), pow(mul(add(1, neg(x)), S.Half), k));
    return Sum(kern, [k, 0, n]);
  },
  assoc_legendre: (args) => {
    const [n, m, x] = [at(args, 0), at(args, 1), at(args, 2)];
    const k = new Dummy('k');
    const den = mul(pow(2, n), factorial(add(n, neg(k))), factorial(k), factorial(add(n, mul(-2, k), neg(m))));
    const kern = mul(factorial(add(mul(2, n), mul(-2, k))), pow(den, -1), minusOneTo(k), pow(x, add(n, neg(m), mul(-2, k))));
    return mul(pow(add(1, neg(pow(x, 2))), mul(m, S.Half)), Sum(kern, [k, 0, fn('floor', [mul(add(n, neg(m)), S.Half)])]));
  },
  hermite: (args) => {
    const [n, x] = pair(args);
    const k = new Dummy('k');
    const kern = mul(minusOneTo(k), pow(mul(factorial(k), factorial(add(n, mul(-2, k)))), -1), pow(mul(2, x), add(n, mul(-2, k))));
    return mul(factorial(n), Sum(kern, [k, 0, floorHalf(n)]));
  },
  hermite_prob: (args) => {
    const [n, x] = pair(args);
    const k = new Dummy('k');
    const kern = mul(pow(S.NegHalf, k), pow(x, add(n, mul(-2, k))), pow(mul(factorial(k), factorial(add(n, mul(-2, k)))), -1));
    return mul(factorial(n), Sum(kern, [k, 0, floorHalf(n)]));
  },
  laguerre: (args) => laguerreSum(...pair(args)),
  assoc_laguerre: (args) => {
    const [n, alpha, x] = [at(args, 0), at(args, 1), at(args, 2)];
    if (notNonnegativeInteger(n)) throw new ValueError('Error: n should be a non-negative integer.');
    const k = new Dummy('k');
    const kern = mul(rf(neg(n), k), pow(mul(gamma(add(k, alpha, 1)), factorial(k)), -1), pow(x, k));
    return mul(gamma(add(n, alpha, 1)), pow(factorial(n), -1), Sum(kern, [k, 0, n]));
  },
};

function laguerreSum(n: Expr, x: Expr): Expr {
  if (isNegative(n) === true) return mul(exp(x), laguerreSum(add(neg(n), -1), neg(x)));
  if (isIntegerQ(n) === false) throw new ValueError('Error: n should be an integer.');
  const k = new Dummy('k');
  return Sum(mul(rf(neg(n), k), pow(factorial(k), -2), pow(x, k)), [k, 0, n]);
}

for (const [name, rule] of Object.entries(SUMS)) {
  registerRewrite(name, 'Sum', rule);
  registerRewrite(name, 'polynomial', rule);
}
registerRewrite('hermite', 'hermite_prob', (args) => {
  const [n, x] = pair(args);
  return mul(pow(sqrt(2), n), hermiteProb(n, mul(x, sqrt(2))));
});
registerRewrite('hermite_prob', 'hermite', (args) => {
  const [n, x] = pair(args);
  return mul(pow(sqrt(2), neg(n)), hermite(n, mul(x, pow(sqrt(2), -1))));
});

// ---- numerics (mpmath legendre, legenp, jacobi, gegenbauer, chebyt, chebyu, hermite, laguerre) ----

mpFns['hermite'] = (args, p) => chermite(at(args, 0), at(args, 1), p);
mpFns['laguerre'] = (args, p) => claguerre(at(args, 0), [MF.ZERO, MF.ZERO], at(args, 1), p);
mpFns['assoc_laguerre'] = (args, p) => claguerre(at(args, 0), at(args, 1), at(args, 2), p);

const toMp = (z: C): [MF.Mpf, MF.Mpf] => [MF.fromNumber(z.re), MF.fromNumber(z.im)];
for (const name of ['jacobi', 'gegenbauer', 'chebyshevt', 'chebyshevu', 'legendre', 'assoc_legendre', 'hermite', 'laguerre', 'assoc_laguerre'] as const) {
  const f = defined(mpFns[name], name);
  numericFns[name] = (args) => {
    const [r, i] = f(args.map(toMp), 53);
    return { re: MF.toNumber(r), im: MF.toNumber(i) };
  };
}

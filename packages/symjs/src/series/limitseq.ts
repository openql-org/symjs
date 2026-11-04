// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy (sympy/series/limitseq.py), Copyright (c) SymPy Development Team, BSD-3-Clause.

/**
 * @file Limits of sequences (SymPy limit_seq, after M. Kauers, "Computing
 * Limits of Sequences") and the difference operator difference_delta.
 */

import type { Expr, ExprLike, Sym } from '../core/nodes';
import { Add, Dummy, Fn, Limit, Mul, Pow, Rational, S, Special } from '../core/nodes';
import { Concrete } from '../core/concrete';
import { at, last } from '../core/guard';
import { asNumerDenom, coeff } from '../core/methods';
import { add, mul, neg, pow, sub, sympify } from '../core/ops';
import { freeSymbols, rebuild, subs, xreplace } from '../core/traverse';
import { type UnsolvedResult, orUnsolved } from '../core/truth';
import { fn } from '../functions/elementary';
import { expand } from '../simplify/expand';
import { sympyArgs } from '../simplify/cse';
import { gammasimp } from '../simplify/gammasimp';
import { rewrite } from '../simplify/rewrite';
import { factor } from '../polys/sympoly';
import { doitConcrete } from '../concrete/summations';
import { accumBounds } from '../core/accumbounds';
import { isNegative, isReal } from '../core/assumptions';
import { limit } from './limits';

/** The depth of nested limit_seq computations of dominant terms. */
const MAX_DEPTH = 2;

const isSum = (e: Expr): boolean => e instanceof Concrete && e.kind2 === 'Sum';
const hasSum = (e: Expr): boolean => isSum(e) || e.args.some(hasSum);

/**
 * SymPy difference_delta(expr, n, step): the difference x[n + step] - x[n] of
 * the sequence x[n] = expr (n is the free symbol of expr when omitted).
 */
export function differenceDelta(ex: ExprLike, n?: Sym, step: ExprLike = 1): Expr {
  const e = sympify(ex);
  let v = n;
  if (v === undefined) {
    const f = [...freeSymbols(e)];
    if (f.length === 0) return S.Zero;
    if (f.length > 1) throw new RangeError(`Since there is more than one variable in the expression, a variable must be supplied to take the difference of ${e.toString()}`);
    v = at(f, 0);
  }
  const h = sympify(step);
  if (!h.isNumber || h instanceof Special) throw new RangeError('Step should be a finite number.');
  return delta(e, v, h);
}

/** difference_delta with the variable and the step given (SymPy _eval_difference_delta of Add, Mul, Pow and Sum). */
function delta(e: Expr, n: Sym, h: Expr): Expr {
  const shift = (a: Expr): Expr => subs(a, [[n, add(n, h)]]);
  let r: Expr | undefined;
  if (e instanceof Add) r = add(...e.args.map((a) => delta(a, n, h)));
  else if (e instanceof Mul) {
    const args = sympyArgs(e);
    const arg0 = at(args, 0);
    const rest = mul(...args.slice(1));
    r = add(mul(shift(arg0), delta(rest, n, h)), mul(delta(arg0, n, h), rest));
  } else if (e instanceof Pow && e.exp.has(n) && !e.base.has(n)) r = mul(sub(pow(e.base, sub(shift(e.exp), e.exp)), 1), e);
  else if (e instanceof Concrete && e.kind2 === 'Sum') {
    // the terms from upper + 1 to the shifted upper bound
    const limits = e.limits;
    const [k, , upper] = last(limits);
    const f = limits.length === 1 ? e.function : new Concrete('Sum', e.args.slice(0, -3));
    r = doitSums(new Concrete('Sum', [f, k, add(upper, 1), shift(upper)]));
  }
  // a zero result is recomputed from the definition (SymPy tests the truth of the result)
  if (r !== undefined && !(r instanceof Rational && r.isZero)) return r;
  return sub(shift(e), e);
}

/** The sums and products of e evaluated, innermost first (SymPy doit for them). */
function doitSums(e: Expr): Expr {
  const r = e.args.length ? rebuild(e, e.args.map(doitSums)) : e;
  return r instanceof Concrete ? doitConcrete(r) : r;
}

/** The terms of an Add (the expression itself otherwise). */
const terms = (e: Expr): readonly Expr[] => (e instanceof Add ? sympyArgs(e) : [e]);

const isInfinite = (e: Expr): boolean => e instanceof Special && (e.name === 'oo' || e.name === '-oo');

/**
 * SymPy dominant(expr, n): the term of the sum expr that dominates every
 * other one as n -> oo, or undefined when there is no unique such term.
 */
export function dominant(ex: ExprLike, n: Sym, depth = 0): Expr | undefined {
  // the algorithm recurses through dominant and limit_seq (SymPy until its recursion limit)
  if (depth > MAX_DEPTH) return undefined;
  const ts = terms(expand(sympify(ex), { func: true }));
  let term0 = last(ts);
  let comp = [term0];
  for (const t of ts.slice(0, -1)) {
    const r = mul(term0, pow(t, -1));
    let e = gammasimp(r);
    if (e.key === r.key) e = factor(r);
    const l = limitSeqImpl(e, n, 5, depth + 1);
    if (l === undefined) return undefined;
    if (l instanceof Rational && l.isZero) {
      term0 = t;
      comp = [term0];
    } else if (!isInfinite(l)) comp.push(t);
  }
  return comp.length > 1 ? undefined : term0;
}

/** A limit, or undefined for an unevaluated Limit and nan (SymPy Limit.doit raises PoleError for nan). */
const asLimit = (r: Expr): Expr | undefined => (r instanceof Limit || (r instanceof Special && r.name === 'nan') ? undefined : r);

/**
 * The limit at oo, or undefined when it cannot be computed (SymPy
 * _limit_inf; an unevaluated Limit is not a result here, so that the
 * algorithm goes on where SymPy returns the Limit; a failure of the limit
 * computation is no result either).
 */
function limitInf(e: Expr, n: Sym): Expr | undefined {
  try {
    return asLimit(limit(e, n, S.Infinity));
  } catch (ex) {
    // SymPy catches NotImplementedError and PoleError only: a ValueError (RangeError here) propagates
    // (limit_seq(laguerre(n, 1), n) raises "n should be an integer." from laguerre(oo, 1))
    if (ex instanceof RangeError) throw ex;
    return undefined;
  }
}

/** A computed limit (an unevaluated Limit counts as one, like in SymPy). */
const known = (e: Expr | undefined): e is Expr => e !== undefined;

function limitSeqTrials(ex: Expr, n: Sym, trials: number, depth: number): Expr | undefined {
  let e = ex;
  for (let i = 0; i < trials; i++) {
    if (!hasSum(e)) {
      const r = limitInf(e, n);
      if (known(r)) return r;
    }
    let [num, den] = asNumerDenom(e);
    if (!den.has(n) || !num.has(n)) return limitInf(doitSums(e), n);
    [num, den] = [differenceDelta(expand(num), n), differenceDelta(expand(den), n)];
    e = gammasimp(mul(num, pow(den, -1)));
    if (!hasSum(e)) {
      const r = limitInf(e, n);
      if (known(r)) return r;
    }
    [num, den] = asNumerDenom(e);
    const dn = dominant(num, n, depth);
    if (dn === undefined) return undefined;
    const dd = dominant(den, n, depth);
    if (dd === undefined) return undefined;
    e = gammasimp(mul(dn, pow(dd, -1)));
  }
  return undefined;
}

/** fibonacci(n) in terms of the golden ratio (SymPy fibonacci._eval_rewrite_as_GoldenRatio). */
function fibonacciToGoldenRatio(e: Expr): Expr {
  const args = e.args.map(fibonacciToGoldenRatio);
  if (e instanceof Fn && e.name === 'fibonacci' && args.length === 1) {
    const k = at(args, 0);
    const phi = S.GoldenRatio;
    return mul(sub(pow(phi, k), pow(neg(phi), neg(k))), pow(sub(mul(2, phi), 1), -1));
  }
  return args.length ? rebuild(e, args) : e;
}

/**
 * Powers of a negative b to an exponent a*m + c with an even
 * integer a and an integer c (m an integer): (-1)**c * (-b)**(a*m + c); and
 * sines and cosines of pi*(a*m + c) with an even integer a.
 */
function fixParity(e: Expr, m: Sym): Expr {
  const args = e.args.map((a) => fixParity(a, m));
  const r = args.length ? rebuild(e, args) : e;
  // sin(pi*(a*m + c)) = sin(pi*c) and cos(pi*(a*m + c)) = cos(pi*c) for an even integer a
  if (r instanceof Fn && (r.name === 'sin' || r.name === 'cos')) {
    const t = expand(mul(at(r.args, 0), pow(S.Pi, -1)));
    const a = coeff(t, m);
    if (a instanceof Rational && a.isInteger && a.p % 2n === 0n && !a.isZero) {
      const c = sub(t, mul(a, m));
      return fn(r.name, [mul(S.Pi, c)]);
    }
  }
  if (r instanceof Pow && isNegative(r.base) === true) {
    const ex = expand(r.exp);
    const a = coeff(ex, m);
    const c = sub(ex, mul(a, m));
    if (a instanceof Rational && a.isInteger && a.p % 2n === 0n && c instanceof Rational && c.isInteger) return mul(c.p % 2n === 0n ? 1 : -1, pow(neg(r.base), r.exp));
  }
  return r;
}

/** A real number (SymPy is_comparable). */
const isComparable = (e: Expr): boolean => isInfinite(e) || (e.isNumber && isReal(e) === true);

function limitSeqImpl(ex: Expr, n: Sym, trials: number, depth: number): Expr | undefined {
  if (!ex.has(n)) return ex;
  let e = fibonacciToGoldenRatio(ex);
  e = rewrite(e, 'gamma', { pattern: ['factorial', 'subfactorial'] });
  const n0 = new Dummy('n', { integer: true, positive: true });
  const pows: Expr[] = [];
  const collectPows = (a: Expr): void => {
    if (a instanceof Pow) pows.push(a);
    a.args.forEach(collectPows);
  };
  collectPows(e);
  const oscillates = pows.some((p) => p instanceof Pow && isNegative(p.base) === true && p.exp.has(n)) || hasTrig(e);
  let L1: Expr | undefined;
  if (oscillates) {
    // odd and even n apart, as n = 2*m - 1 and n = 2*m with a positive integer m (SymPy uses odd and even dummies)
    L1 = limitSeqTrials(fixParity(xreplace(e, [[n, sub(mul(2, n0), 1)]]), n0), n0, trials, depth);
    if (L1 !== undefined) {
      const L2 = limitSeqTrials(fixParity(xreplace(e, [[n, mul(2, n0)]]), n0), n0, trials, depth);
      if (L2 === undefined) return undefined;
      if (L1.key !== L2.key) {
        if (isComparable(L1) && isComparable(L2)) return accumBounds(fn('Min', [L1, L2]), fn('Max', [L1, L2]));
        return undefined;
      }
    }
  } else L1 = limitSeqTrials(xreplace(e, [[n, n0]]), n0, trials, depth);
  if (L1 !== undefined) return L1;
  if (e instanceof Add) {
    const ls = e.args.map((t) => limitSeqImpl(t, n, trials, depth));
    const found = ls.filter((l): l is Expr => l !== undefined);
    if (found.length < ls.length) return undefined;
    // oo - oo is no limit (SymPy returns nan)
    return asLimit(add(...found));
  }
  if (!hasSum(e)) {
    const lim = limitSeqTrials(fn('abs', [xreplace(e, [[n, n0]])]), n0, trials, depth);
    if (lim instanceof Rational && lim.isZero) return S.Zero;
  }
  return undefined;
}

const hasTrig = (e: Expr): boolean => (e instanceof Fn && (e.name === 'sin' || e.name === 'cos')) || e.args.some(hasTrig);

/**
 * SymPy limit_seq(expr, n, trials): the limit of the sequence expr as the
 * integer n tends to oo, for sequences built from rational functions,
 * indefinite sums and products; Unsolved when the algorithm finds none.
 */
export function limitSeq(ex: ExprLike, n?: Sym, trials = 5): Expr | UnsolvedResult {
  const e = sympify(ex);
  let v = n;
  if (v === undefined) {
    const free = [...freeSymbols(e)];
    if (free.length === 0) return e;
    if (free.length > 1) throw new RangeError('Expression has more than one variable. Please specify a variable.');
    v = at(free, 0);
  }
  return orUnsolved(limitSeqImpl(e, v, trials, 0));
}

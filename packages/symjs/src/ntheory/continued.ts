// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Continued fractions (SymPy sympy.ntheory.continued_fraction):
 * continued_fraction, continued_fraction_periodic,
 * continued_fraction_iterator, continued_fraction_convergents and
 * continued_fraction_reduce. Periodic continued fractions are arrays whose
 * last element is the array of the repeating terms.
 */

import type { Expr, ExprLike } from '../core/nodes';
import { Add, Float, Mul, Pow, Rational, S } from '../core/nodes';
import { add, div, mul, sqrt, sub, sympify } from '../core/ops';
import { asNumerDenom } from '../core/methods';
import { gcd, lcm } from '../core/numbers';
import { NotImplementedError } from '../core/errors';
import { expectType, getOrThrow, pair } from '../core/guard';
import { floor as floorFn } from '../functions/special';
import { factorintInt } from './factor';
import type { IntLike } from './intutil';
import { asInt, fdiv, isqrt, sqrtrem } from './intutil';

/** A continued fraction: terms, the last one possibly the list of periodic terms. */
export type ContinuedFraction = (bigint | bigint[])[];

const sgn = (x: bigint): bigint => (x < 0n ? -1n : x > 0n ? 1n : 0n);

/** floor((P + S*sqrt(d)) / q) for a non-square d > 0, S != 0 and q != 0. */
function floorQuad(P: bigint, Sc: bigint, d: bigint, q: bigint): bigint {
  const t = isqrt(Sc * Sc * d);
  const L = Sc > 0n ? P + t : P - t - 1n;
  return q > 0n ? fdiv(L, q) : fdiv(L + 1n, q);
}

/** The sign of P + S*sqrt(d) for d > 0 not a square and S != 0. */
function signQuad(P: bigint, Sc: bigint, d: bigint): bigint {
  if (sgn(P) === sgn(Sc) || P === 0n) return sgn(Sc);
  return Sc * Sc * d > P * P ? sgn(Sc) : sgn(P);
}

/**
 * The continued fraction of (p + s*sqrt(d))/q (SymPy
 * continued_fraction_periodic): a list of terms whose last element is the
 * list of the repeating terms for a quadratic irrational.
 */
export function continuedFractionPeriodic(pIn: IntLike, qIn: IntLike, dIn: IntLike = 0, sIn: IntLike = 1): ContinuedFraction {
  let p = asInt(pIn);
  let q = asInt(qIn);
  let d = asInt(dIn);
  let s = asInt(sIn);
  if (d < 0n) throw new RangeError(`expected non-negative for \`d\` but got ${d}`);
  if (q === 0n) throw new RangeError('The denominator cannot be 0.');
  if (s === 0n) d = 0n;
  const [sd0, rem] = sqrtrem(d);
  if (rem === 0n) return [...continuedFractionIterator(Rational.of(p + s * sd0, q))];
  if (q < 0n) [p, q, s] = [-p, -q, -s];
  if (signQuad(p, s, d) < 0n) {
    const w = floorQuad(-p, -s, d, q);
    const oneF = continuedFractionPeriodic((w + 1n) * q + p, q, d, s);
    oneF[0] = expectType(oneF[0], isBigint, 'integer part of a continued fraction') - (w + 1n);
    return oneF;
  }
  let sigma = sgn(s);
  d *= s * s;
  if ((d - p * p) % q !== 0n) {
    d *= q * q;
    sigma *= sgn(q);
    p *= q;
    q *= q;
  }
  const terms: bigint[] = [];
  const pq = new Map<string, number>();
  while (!pq.has(`${p},${q}`)) {
    pq.set(`${p},${q}`, terms.length);
    const t = floorQuad(p, sigma, d, q);
    terms.push(t);
    p = t * q - p;
    q = fdiv(d - p * p, q);
  }
  const i = getOrThrow(pq, `${p},${q}`);
  return [...terms.slice(0, i), terms.slice(i)];
}

function allRationalAtoms(e: Expr): boolean {
  if (e instanceof Rational) return true;
  if (e instanceof Add || e instanceof Mul || e instanceof Pow) return e.args.every(allRationalAtoms);
  return false;
}

const isInt = (e: Expr): e is Rational => e instanceof Rational && e.q === 1n;
const isHalf = (e: Expr): boolean => e instanceof Rational && e.p === 1n && e.q === 2n;
/** sqrt(n) for an integer n. */
type SqrtOfInt = Pow & { readonly base: Rational };
const isSqrtOfInt = (e: Expr): e is SqrtOfInt => e instanceof Pow && isHalf(e.exp) && isInt(e.base);
const isBigint = (x: unknown): x is bigint => typeof x === 'bigint';

/** A term of a continued fraction given as a list: a number or (last) the periodic part. */
type CfTerm = ExprLike | readonly ExprLike[];
const isPeriod = (t: CfTerm): t is readonly ExprLike[] => Array.isArray(t);
const isTermList = (cf: Iterable<CfTerm>): cf is readonly CfTerm[] => Array.isArray(cf);

/** The continued fraction of a rational number or a quadratic irrational (SymPy continued_fraction). */
export function continuedFraction(a: ExprLike): ContinuedFraction {
  const e = sympify(a);
  if (allRationalAtoms(e)) {
    if (e instanceof Rational) return e.q === 1n ? continuedFractionPeriodic(e.p, 1n, 0n) : continuedFractionPeriodic(e.p, e.q, 0n);
    if (isSqrtOfInt(e)) return continuedFractionPeriodic(0n, 1n, e.base.p);
    if (e instanceof Mul && e.args.length === 2) {
      const [r, sq] = pair(e.args);
      if (r instanceof Rational && isSqrtOfInt(sq)) return continuedFractionPeriodic(0n, r.q, sq.base.p, r.p);
    }
    const [p, dd] = asNumerDenom(e.expand());
    if (isInt(dd)) {
      if (p instanceof Rational) return continuedFractionPeriodic(p.p, dd.p * p.q);
      let a0: Expr = S.Zero;
      let bc: Expr = p;
      if (p instanceof Add && p.args.length === 2) [a0, bc] = pair(p.args);
      if (isInt(a0)) {
        let b: Expr | undefined;
        let c: Expr | undefined;
        if (bc instanceof Mul && bc.args.length === 2) [b, c] = pair(bc.args);
        else if (bc instanceof Pow) [b, c] = [S.One, bc];
        if (b !== undefined && c !== undefined && isInt(b) && isSqrtOfInt(c)) return continuedFractionPeriodic(a0.p, dd.p, c.base.p, b.p);
      }
    }
  }
  throw new RangeError(`expecting a rational or quadratic irrational, not ${e.toString()}`);
}

/** SymPy Integer(int(floor(x))): floor(x) as a bigint, also when floor leaves an integral Float. */
function floorInt(x: Expr): bigint {
  const i = floorFn(x);
  if (isInt(i)) return i.p;
  // an integral Float is normalized to an odd mantissa (or 0) with exp >= 0
  if (i instanceof Float) return i.mpf.man << BigInt(i.mpf.exp);
  throw new NotImplementedError(`cannot compute floor(${x.toString()})`);
}

/** The terms of the continued fraction of x (SymPy continued_fraction_iterator); infinite for irrational x. */
export function* continuedFractionIterator(xIn: ExprLike): Generator<bigint, void, undefined> {
  const x0 = sympify(xIn);
  if (x0 instanceof Rational) {
    let p = x0.p;
    let q = x0.q;
    for (;;) {
      const i = fdiv(p, q);
      yield i;
      p -= i * q;
      if (p === 0n) return;
      [p, q] = [q, p];
    }
  }
  let x: Expr = x0;
  for (;;) {
    const i = floorInt(x);
    yield i;
    x = sub(x, i);
    if ((x instanceof Rational || x instanceof Float) && x.isZero) return;
    x = div(1, x);
  }
}

/**
 * The convergents of a continued fraction given as terms (a finite or
 * infinite iterable, or an array whose last element is the periodic part)
 * (SymPy continued_fraction_convergents).
 */
export function* continuedFractionConvergents(cf: Iterable<ExprLike | bigint | readonly (ExprLike | bigint)[]>): Generator<Expr, void, undefined> {
  let terms: Iterable<ExprLike | bigint | readonly (ExprLike | bigint)[]> = cf;
  const period = isTermList(cf) ? cf.at(-1) : undefined;
  if (isTermList(cf) && period !== undefined && isPeriod(period)) {
    const arr = cf;
    terms = (function* () {
      yield* arr.slice(0, -1);
      for (;;) yield* period;
    })();
  }
  let [p2, q2]: [Expr, Expr] = [S.Zero, S.One];
  let [p1, q1]: [Expr, Expr] = [S.One, S.Zero];
  for (const t of terms) {
    if (isPeriod(t)) throw new TypeError('the periodic part must be the last element');
    const a = sympify(t);
    const p = add(mul(a, p1), p2);
    const q = add(mul(a, q1), q2);
    [p2, q2] = [p1, q1];
    [p1, q1] = [p, q];
    yield div(p, q);
  }
}

// arithmetic in Q(sqrt(D)): [a, b] means a + b*sqrt(D) with Rational a, b
type Quad = [Rational, Rational];
const R = (p: bigint, q: bigint = 1n): Rational => Rational.of(p, q);
const radd = (x: Rational, y: Rational): Rational => R(x.p * y.q + y.p * x.q, x.q * y.q);
const rmul = (x: Rational, y: Rational): Rational => R(x.p * y.p, x.q * y.q);
const rneg = (x: Rational): Rational => R(-x.p, x.q);
const rdiv = (x: Rational, y: Rational): Rational => R(x.p * y.q, x.q * y.p);
const qadd = (x: Quad, y: Quad): Quad => [radd(x[0], y[0]), radd(x[1], y[1])];
const qmul = (x: Quad, y: Quad, D: bigint): Quad => [radd(rmul(x[0], y[0]), rmul(rmul(x[1], y[1]), R(D))), radd(rmul(x[0], y[1]), rmul(x[1], y[0]))];
function qdiv(x: Quad, y: Quad, D: bigint): Quad {
  const conj: Quad = [y[0], rneg(y[1])];
  const num = qmul(x, conj, D);
  const den = radd(rmul(y[0], y[0]), rneg(rmul(rmul(y[1], y[1]), R(D))));
  return [rdiv(num[0], den), rdiv(num[1], den)];
}

const asRational = (t: ExprLike | bigint): Rational => {
  const e = typeof t === 'bigint' ? R(t) : sympify(t);
  if (!(e instanceof Rational)) throw new NotImplementedError('continued_fraction_reduce: the terms of a periodic continued fraction must be rational');
  return e;
};

/** The recurrences [p1, q1, p2, q2] after the given terms. */
function convergentState(terms: readonly Rational[]): [Rational, Rational, Rational, Rational] {
  let [p2, q2] = [R(0n), R(1n)];
  let [p1, q1] = [R(1n), R(0n)];
  for (const a of terms) {
    const p = radd(rmul(a, p1), p2);
    const q = radd(rmul(a, q1), q2);
    [p2, q2] = [p1, q1];
    [p1, q1] = [p, q];
  }
  return [p1, q1, p2, q2];
}

/**
 * The value of a continued fraction (SymPy continued_fraction_reduce): a
 * Rational for finite lists, a quadratic irrational (A + B*sqrt(D))/C for
 * periodic ones.
 */
export function continuedFractionReduce(cf: readonly (ExprLike | bigint | readonly (ExprLike | bigint)[])[]): Expr {
  const prefix: (ExprLike | bigint)[] = [];
  let period: (ExprLike | bigint)[] | undefined;
  for (const t of cf) {
    if (isPeriod(t)) {
      period = [...t];
      break;
    }
    prefix.push(t);
  }
  if (period === undefined) {
    let a: Expr = S.Zero;
    for (const c of continuedFractionConvergents(prefix)) a = c;
    return a;
  }
  // the purely periodic part y = [period..., y]: Q y**2 + (Q' - P) y - P' = 0
  const [P, Q, P2, Q2] = convergentState(period.map(asRational));
  if (Q.p === 0n) throw new NotImplementedError('continued_fraction_reduce: degenerate period');
  const bq = radd(Q2, rneg(P));
  const disc = radd(rmul(bq, bq), rmul(R(4n), rmul(Q, P2)));
  // complex roots: no real value (SymPy raises TypeError comparing them)
  if (disc.p < 0n) throw new RangeError('continued_fraction_reduce: the periodic continued fraction has no real value');
  // sqrt(disc) = k/m * sqrt(D) with D squarefree
  const nm = disc.p * disc.q;
  let k = 1n;
  let D = 1n;
  for (const [pr, e] of factorintInt(nm, {})) {
    k *= pr ** (e / 2n);
    if (e % 2n === 1n) D *= pr;
  }
  const sqrtCoeff = R(k, disc.q);
  const sign = Q.p > 0n ? 1n : -1n;
  const twoQ = rmul(R(2n), Q);
  let pure: Quad = [rdiv(rneg(bq), twoQ), rdiv(rmul(R(sign), sqrtCoeff), twoQ)];
  if (D === 1n) pure = [radd(pure[0], pure[1]), R(0n)];
  const [p1, q1, p2, q2] = convergentState(prefix.map(asRational));
  const num = qadd(qmul([p1, R(0n)], pure, D), [p2, R(0n)]);
  const den = qadd(qmul([q1, R(0n)], pure, D), [q2, R(0n)]);
  const [r, s] = qdiv(num, den, D);
  if (s.p === 0n) return r;
  const C = lcm(r.q, s.q);
  const A = (r.p * C) / r.q;
  const B = (s.p * C) / s.q;
  const g = gcd(gcd(A, B), C);
  const [A1, B1, C1] = [A / g, B / g, C / g];
  const rad = sqrt(D);
  if (A1 === 0n) return mul(R(B1, C1), rad);
  const numer = add(A1, mul(B1, rad));
  if (C1 === 1n) return numer;
  return new Mul([R(1n, C1), numer]);
}

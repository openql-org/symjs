// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0, polys/appellseqs.py, Copyright (c) 2006-2023
// SymPy Development Team, BSD 3-Clause License (see LICENSE).

import type { Expr, ExprLike } from '../core/nodes';
import { Dummy, Rational, Float } from '../core/nodes';
import { add, mul, pow, sympify } from '../core/ops';
import type { IntLike } from '../ntheory/intutil';
import type { NamedPolyOptions, NamedPolyResult } from './orthopolys';
import { Poly } from './sympoly';
import { domainArith, domainNeg, QQ, ZZ, type Domain } from './domains';
import { dupMulGround, dupSubGround, dupQuoGround } from './densearith';
import { dupEval, dupIntegrate } from './densetools';

/** Dense Bernoulli polynomial over K, with coefficients in descending order. */
export function dupBernoulli(n: number, K: Domain): unknown[] {
  if (n < 1) return [K.convert(1)];
  let p: unknown[] = [K.convert(1), K.convert(Rational.of(-1, 2))];
  for (let i = 2; i <= n; i++) {
    p = dupIntegrate(dupMulGround(p, K.convert(i), K), 1, K);
    if (i % 2 === 0) p = dupSubGround(p, domainArith(K, 'mul', dupEval(p, K.convert(Rational.of(1, 2)), K), K.convert(Rational.of(2n ** BigInt(i - 1), 2n ** BigInt(i) - 1n))), K);
  }
  return p;
}

/** Dense central Bernoulli polynomial over K. */
export function dupBernoulliC(n: number, K: Domain): unknown[] {
  let p: unknown[] = [K.convert(1)];
  for (let i = 1; i <= n; i++) {
    p = dupIntegrate(dupMulGround(p, K.convert(i), K), 1, K);
    if (i % 2 === 0) p = dupSubGround(p, domainArith(K, 'mul', dupEval(p, K.one, K), K.convert(Rational.of(2n ** BigInt(i - 1) - 1n, 2n ** BigInt(i) - 1n))), K);
  }
  return p;
}

/** Dense Genocchi polynomial over K; G_0 is represented by a single zero. */
export function dupGenocchi(n: number, K: Domain): unknown[] {
  if (n < 1) return [K.convert(0)];
  let p: unknown[] = [domainNeg(K, K.one)];
  for (let i = 2; i <= n; i++) {
    p = dupIntegrate(dupMulGround(p, K.convert(i), K), 1, K);
    if (i % 2 === 0) p = dupSubGround(p, domainArith(K, 'quo', dupEval(p, K.one, K), K.convert(2)), K);
  }
  return p;
}

/** Dense Euler polynomial over K, computed from the integer Genocchi polynomial. */
export function dupEuler(n: number, K: Domain): unknown[] {
  return dupQuoGround(dupGenocchi(n + 1, ZZ), K.convert(-n - 1), K);
}

/** Dense Andre polynomial over K. */
export function dupAndre(n: number, K: Domain): unknown[] {
  let p: unknown[] = [K.convert(1)];
  for (let i = 1; i <= n; i++) {
    p = dupIntegrate(dupMulGround(p, K.convert(i), K), 1, K);
    if (i % 2 === 0) p = dupSubGround(p, dupEval(p, K.one, K), K);
  }
  return p;
}

type Kind = 'bernoulli' | 'central' | 'genocchi' | 'euler' | 'andre';
const denseCoefficients = { bernoulli: dupBernoulli, central: dupBernoulliC, genocchi: dupGenocchi, euler: dupEuler, andre: dupAndre };

function appell(n: IntLike, x: ExprLike | undefined, opts: NamedPolyOptions, kind: Kind): Expr | Poly {
  const index = sympify(n);
  if (!(index instanceof Rational || index instanceof Float)) throw new TypeError('polynomial index must be numeric');
  const value = index.toNumber(), degree = Math.trunc(value);
  if (!Number.isSafeInteger(degree) || value < 0) throw new RangeError('polynomial index must be nonnegative');
  const v = x === undefined ? new Dummy('x') : sympify(x);
  const K = kind === 'andre' || kind === 'genocchi' ? ZZ : QQ;
  const e = add(...denseCoefficients[kind](degree, K).reverse().map((c,k) => mul(K.toSympy(c), pow(v,k))));
  return opts.polys ? Poly.from(e, [v], { domain: String(K), pure: x === undefined }) : e;
}

/** Bernoulli polynomial B_n(x), with B_1(x) = x - 1/2. */
export function bernoulliPoly<O extends NamedPolyOptions = Record<string, never>>(n: IntLike, x?: ExprLike, opts?: O): NamedPolyResult<O>;
export function bernoulliPoly(n: IntLike, x?: ExprLike, opts: NamedPolyOptions = {}): Expr | Poly { return appell(n,x,opts,'bernoulli'); }
/** Central Bernoulli polynomial 2^n B_n((x+1)/2). */
export function bernoulliCPoly<O extends NamedPolyOptions = Record<string, never>>(n: IntLike, x?: ExprLike, opts?: O): NamedPolyResult<O>;
export function bernoulliCPoly(n: IntLike, x?: ExprLike, opts: NamedPolyOptions = {}): Expr | Poly { return appell(n,x,opts,'central'); }
/** Genocchi polynomial G_n(x). */
export function genocchiPoly<O extends NamedPolyOptions = Record<string, never>>(n: IntLike, x?: ExprLike, opts?: O): NamedPolyResult<O>;
export function genocchiPoly(n: IntLike, x?: ExprLike, opts: NamedPolyOptions = {}): Expr | Poly { return appell(n,x,opts,'genocchi'); }
/** Euler polynomial E_n(x). */
export function eulerPoly<O extends NamedPolyOptions = Record<string, never>>(n: IntLike, x?: ExprLike, opts?: O): NamedPolyResult<O>;
export function eulerPoly(n: IntLike, x?: ExprLike, opts: NamedPolyOptions = {}): Expr | Poly { return appell(n,x,opts,'euler'); }
/** Andre polynomial, the Appell sequence of Euler numbers. */
export function andrePoly<O extends NamedPolyOptions = Record<string, never>>(n: IntLike, x?: ExprLike, opts?: O): NamedPolyResult<O>;
export function andrePoly(n: IntLike, x?: ExprLike, opts: NamedPolyOptions = {}): Expr | Poly { return appell(n,x,opts,'andre'); }

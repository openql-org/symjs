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

type Kind = 'bernoulli' | 'central' | 'genocchi' | 'euler' | 'andre';
const scale = (c: Rational, p: bigint, q = 1n): Rational => Rational.of(c.p * p, c.q * q);

/** Coefficients in ascending order, using the Appell integral recurrence. */
function coefficients(n: number, kind: Kind): Rational[] {
  if (kind === 'euler') return coefficients(n + 1, 'genocchi').map((c) => scale(c, -1n, BigInt(n + 1)));
  if (kind === 'genocchi' && n === 0) return [Rational.of(0)];
  const shifted = kind === 'bernoulli' || kind === 'genocchi';
  let cs = kind === 'genocchi' ? [Rational.of(-1)] : kind === 'bernoulli' && n > 0 ? [Rational.of(-1, 2), Rational.of(1)] : [Rational.of(1)];
  for (let i = shifted ? 2 : 1; i <= n; i++) {
    cs = [Rational.of(0), ...cs.map((c,k) => scale(c, BigInt(i), BigInt(k + 1)))];
    if (i % 2 !== 0) continue;
    let value = Rational.of(0);
    cs.forEach((c,k) => {
      const v = kind === 'bernoulli' ? scale(c, 1n, 2n ** BigInt(k)) : c;
      value = Rational.of(value.p * v.q + v.p * value.q, value.q * v.q);
    });
    const power = 2n ** BigInt(i);
    if (kind === 'bernoulli') value = scale(value, power / 2n, power - 1n);
    else if (kind === 'central') value = scale(value, power / 2n - 1n, power - 1n);
    else if (kind === 'genocchi') value = scale(value, 1n, 2n);
    cs[0] = scale(value, -1n);
  }
  return cs;
}

function appell(n: IntLike, x: ExprLike | undefined, opts: NamedPolyOptions, kind: Kind): Expr | Poly {
  const index = sympify(n);
  if (!(index instanceof Rational || index instanceof Float)) throw new TypeError('polynomial index must be numeric');
  const value = index.toNumber(), degree = Math.trunc(value);
  if (!Number.isSafeInteger(degree) || value < 0) throw new RangeError('polynomial index must be nonnegative');
  const v = x === undefined ? new Dummy('x') : sympify(x);
  const e = add(...coefficients(degree, kind).map((c,k) => mul(c, pow(v,k))));
  return opts.polys ? Poly.from(e, [v], { domain: kind === 'andre' || kind === 'genocchi' ? 'ZZ' : 'QQ', pure: x === undefined }) : e;
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

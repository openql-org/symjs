// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Rounding of numeric expressions to decimal places (SymPy Expr.round).
 */

import type { Expr, ExprLike } from '../core/nodes';
import { Float, Rational, S, Special } from '../core/nodes';
import { add, mul, sympify } from '../core/ops';
import { atoms } from '../core/methods';
import { im, re } from '../functions/elementary';
import * as F from './mpf';
import { evalAdaptive } from './mpeval';
import { float } from './floatctor';

/** Python round(n, k) for an integer and k < 0 (half to even). */
function roundInt(n: bigint, k: number): bigint {
  if (k >= 0) return n;
  const m = 10n ** BigInt(-k);
  const neg = n < 0n;
  const a = neg ? -n : n;
  let q = a / m;
  const r = a % m;
  if (2n * r > m || (2n * r === m && q % 2n === 1n)) q += 1n;
  return (neg ? -q : q) * m;
}

/** Position of the first significant digit: _mag(12) = 2, _mag(.012) = -1. */
function decimalMag(v: F.Mpf): number {
  const x = Math.abs(F.toNumber(v));
  let m = Math.ceil(Math.log10(x));
  // correct for off-by-one using exact comparison with 10**m
  const p = m >= 0 ? F.fromInt(10n ** BigInt(m)) : F.fromRational(1n, 10n ** BigInt(-m), 200);
  if (F.cmp(F.abs(v), p) >= 0) m += 1;
  return m;
}

/**
 * Round a numeric expression to n decimal places (SymPy `round`). Without
 * `n` the result is an Integer; complex values round both parts.
 */
export function round(xIn: ExprLike, n?: number): Expr {
  const x = sympify(xIn);
  if (x.freeSymbols().size) throw new TypeError('Cannot round symbolic expression');
  if (x instanceof Special) return x;
  const v = evalAdaptive(x, 60);
  if (!F.isZero(v[1])) {
    return add(round(re(x), n), mul(S.I, round(im(x), n)));
  }
  if (F.isZero(v[0])) return n === undefined ? S.Zero : x;
  const p = n ?? 0;
  if (x instanceof Rational && x.isInteger) return Rational.of(roundInt(x.p, p));
  const digitsToDecimal = decimalMag(v[0]);
  let allow = digitsToDecimal + p;
  const precs = atoms(x)
    .filter((a): a is Float => a instanceof Float)
    .map((f) => f.prec);
  let dps: number;
  if (precs.length) {
    dps = F.precToDps(Math.max(...precs));
    allow = Math.min(allow, dps);
  } else dps = Math.max(15, allow);
  const shift = -digitsToDecimal + dps;
  const extra = 1;
  const P = F.dpsToPrec(dps + extra);
  const xn = evalAdaptive(x, P)[0];
  const scaleF = shift >= 0 ? F.fromInt(10n ** BigInt(shift)) : F.fromRational(1n, 10n ** BigInt(-shift), P);
  const xf = F.mul(xn, scaleF, P);
  // Integer(xf) truncates toward zero
  let xi = xf.man < 0n ? -F.floor(F.neg(xf)) : F.floor(xf);
  const sign = F.sign(xn) > 0 ? 1n : -1n;
  const dif = F.round(F.mulInt(F.sub(xf, F.fromInt(xi)), sign), F.dpsToPrec(extra));
  const half = { man: 1n, exp: -1n };
  const c = F.cmp(dif, half);
  // a tie goes to the even neighbour (SymPy: xi += sign if xi % 2 else -xi % 2)
  if (c > 0 || (c === 0 && xi % 2n !== 0n)) xi += sign;
  const ip = p - shift;
  const xr = roundInt(xi, ip);
  const rv = shift >= 0 ? Rational.of(xr, 10n ** BigInt(shift)) : Rational.of(xr * 10n ** BigInt(-shift));
  if (rv.isInteger) {
    if (n === undefined) return rv;
    return float(String(rv.p), dps);
  }
  if (!allow) {
    const [rp, rq] = F.toRational(F.round(xn, P));
    if (rv.p * rq > rp * rv.q) allow += 1;
  }
  return float(rv, allow);
}

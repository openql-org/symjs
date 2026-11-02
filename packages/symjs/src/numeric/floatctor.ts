// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file The SymPy `Float(num, dps)` constructor: precision inference from
 * decimal strings, rounding of doubles, integers and exact numbers.
 */

import type { Expr } from '../core/nodes';
import { Float, Rational, S, Special } from '../core/nodes';
import * as F from './mpf';
import { evalAdaptive } from './mpeval';

/** Decimal digit count as Python's Decimal(...).as_tuple() reports it. */
function decimalDigits(s: string): number {
  const mant = s.split('e')[0]!.replace(/^[+-]/, '').replace(/[._]/g, '');
  const d = mant.replace(/^0+/, '');
  return d.length === 0 ? 1 : d.length;
}

/** True when a decimal literal denotes an integer (exponent >= 0 in Decimal terms). */
function decimalIsInteger(s: string): boolean {
  const [mant, e] = s.split('e') as [string, string | undefined];
  const frac = (mant.split('.')[1] ?? '').replace(/_/g, '');
  return Number(e ?? '0') - frac.length >= 0;
}

/**
 * Create a Float like SymPy's `Float(num, dps)`.
 *
 * - `num` may be a JS number (a Python float), a bigint or integer Rational
 *   (a Python int), a decimal string, or any exact numeric expression.
 * - `dps` is the decimal precision; `''` infers it from the digits of a
 *   string. Without `dps`, strings get max(15, their digit count).
 * - `precision` gives the binary precision instead of `dps`.
 */
export function float(num: number | bigint | string | Expr, dpsIn?: number | '', precision?: number): Expr {
  let dps = dpsIn;
  let n: number | string | Expr = typeof num === 'bigint' ? String(num) : num;
  if (n instanceof Rational && n.isInteger) n = String(n.p);
  if (n instanceof Float && dps === undefined && precision === undefined) return n;
  if (typeof n === 'string') {
    let t = n.trim().replace(/ /g, '_').toLowerCase();
    if (t.startsWith('.') && t.length > 1) t = '0' + t;
    else if (t.startsWith('-.') && t.length > 2) t = '-0.' + t.slice(2);
    else if (t === 'inf' || t === '+inf') return S.Infinity;
    else if (t === '-inf') return S.NegativeInfinity;
    else if (t === 'nan') return S.NaN;
    if (!/^[+-]?(\d[\d_]*)?(\.(\d[\d_]*)?)?(e[+-]?\d+)?$/.test(t) || !/\d/.test(t)) {
      throw new SyntaxError(`string-float not recognized: ${n}`);
    }
    n = t;
  } else if (typeof n === 'number') {
    if (Number.isNaN(n)) return S.NaN;
    if (n === Infinity) return S.Infinity;
    if (n === -Infinity) return S.NegativeInfinity;
    if (n === 0) n = '0';
  } else if (n instanceof Special) {
    return n;
  }
  if (dps === undefined && precision === undefined) {
    dps = 15;
    if (typeof n === 'string') {
      let d = decimalDigits(n);
      if (!n.includes('.') && decimalIsInteger(n)) {
        const intDigits = F.floor(F.fromStr(n, 100000)).toString().replace('-', '').length;
        d = Math.max(d, intDigits);
      }
      dps = Math.max(15, d);
    }
  } else if (dps === '') {
    if (typeof n !== 'string') throw new TypeError('The null string can only be used when the number to Float is passed as a string or an integer.');
    let d = decimalDigits(n);
    if (!n.includes('.') && decimalIsInteger(n)) {
      const intDigits = F.floor(F.fromStr(n, 100000)).toString().replace('-', '').length;
      d = Math.max(d, intDigits);
    }
    dps = d;
  }
  const prec = precision ?? F.dpsToPrec(dps as number);
  let mpf: F.Mpf;
  if (typeof n === 'number') mpf = F.round(F.fromNumber(n), prec);
  else if (typeof n === 'string') mpf = F.fromStr(n, prec);
  else if (n instanceof Rational) mpf = F.fromRational(n.p, n.q, prec);
  else if (n instanceof Float) mpf = F.round(n.mpf, prec);
  else {
    const v = evalAdaptive(n, prec, () => undefined);
    if (!F.isZero(v[1])) throw new TypeError('Float: the value is not real');
    mpf = v[0];
  }
  return new Float(mpf, prec);
}

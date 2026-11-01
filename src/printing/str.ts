// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Plain-text printer compatible with SymPy's `StrPrinter`
 * (e.g. `x**2 + 2*x*y - sqrt(2)/2`).
 */

import { Add, Constant, Expr, Float, Fn, Mul, Pow, Rational, Sym, impl, isNum } from '../core/nodes';
import { mul, pow, splitCoeff } from '../core/ops';
import { asOrderedFactors, asOrderedTerms, sympyFunctionName } from './sortkey';

/** SymPy precedence values. */
export const PREC = { ADD: 40, MUL: 50, POW: 60, FUNC: 70, ATOM: 1000 } as const;

const isExp = (e: Expr): boolean => e instanceof Pow && e.base instanceof Constant && e.base.name === 'E';

/** SymPy `could_extract_minus_sign` for printing purposes. */
export function startsNegative(e: Expr): boolean {
  if (isNum(e)) return e.isNegative;
  if (e instanceof Mul) {
    const c = e.args[0]!;
    return isNum(c) && c.isNegative;
  }
  return false;
}

/** SymPy `precedence()`. */
export function precedence(e: Expr): number {
  if (e instanceof Rational) {
    if (e.isInteger) return e.p < 0n ? PREC.ADD : PREC.ATOM;
    return e.p < 0n ? PREC.ADD : PREC.MUL;
  }
  if (e instanceof Float) return e.value < 0 ? PREC.ADD : PREC.ATOM;
  if (e instanceof Add) return PREC.ADD;
  if (e instanceof Mul) return startsNegative(e) ? PREC.ADD : PREC.MUL;
  if (isExp(e)) return PREC.FUNC;
  if (e instanceof Pow) return PREC.POW;
  if (e instanceof Fn) return PREC.FUNC;
  return PREC.ATOM;
}

/** Format a float like SymPy's default 15-digit Float. */
export function floatString(v: number): string {
  if (v === 0) return '0.0';
  const exp = Math.floor(Math.log10(Math.abs(v)));
  if (exp >= -4 && exp < 15) {
    return v.toPrecision(15);
  }
  const [m, e] = v.toExponential(14).split('e') as [string, string];
  return `${m}e${e.startsWith('+') ? e.slice(1) : e}`;
}

/** SymPy `_keep_coeff`: c*rest without re-evaluation (no distribution over sums). */
export function keepCoeff(c: Rational | Float, rest: Expr): Expr {
  if (c instanceof Rational && c.isOne) return rest;
  if (rest instanceof Rational && rest.isOne) return c;
  return new Mul([c, ...(rest instanceof Mul ? rest.args : [rest])]);
}

function parenthesize(e: Expr, level: number): string {
  const s = str(e);
  return precedence(e) <= level ? `(${s})` : s;
}

function printMul(e: Mul): string {
  const prec = precedence(e);
  const [c, rest] = splitCoeff(e);
  let sign = '';
  let expr: Expr = e;
  if (c.isNegative) {
    sign = '-';
    expr = keepCoeff(c instanceof Rational ? Rational.of(-c.p, c.q) : new Float(-c.value), rest);
    if (!(expr instanceof Mul)) {
      // e.g. -x: after removing the sign only a single factor remains
      return sign + parenthesize(expr, prec);
    }
  }
  const a: Expr[] = [];
  const b: Expr[] = [];
  for (const item of asOrderedFactors(expr)) {
    if (item instanceof Pow && !isExp(item) && splitCoeff(item.exp)[0].isNegative) {
      const x = item.exp;
      b.push(x instanceof Rational && x.p === -1n && x.q === 1n ? item.base : pow(item.base, mul(-1, x)));
    } else if (item instanceof Rational) {
      if (item.p !== 1n) a.push(Rational.of(item.p));
      if (item.q !== 1n) b.push(Rational.of(item.q));
    } else {
      a.push(item);
    }
  }
  const aStr = (a.length > 0 ? a : [Rational.of(1n)]).map((x) => parenthesize(x, prec));
  const bStr = b.map((x) => parenthesize(x, prec));
  if (bStr.length === 0) return sign + aStr.join('*');
  if (bStr.length === 1) return `${sign}${aStr.join('*')}/${bStr[0]}`;
  return `${sign}${aStr.join('*')}/(${bStr.join('*')})`;
}

function printPow(e: Pow): string {
  const [b, x] = e.args;
  if (isExp(e)) return `exp(${str(x)})`;
  if (x instanceof Rational) {
    if (x.p === 1n && x.q === 2n) return `sqrt(${str(b)})`;
    if (x.p === -1n && x.q === 2n) return `1/sqrt(${str(b)})`;
    if (x.p === -1n && x.q === 1n) return `1/${parenthesize(b, PREC.POW)}`;
  }
  return `${parenthesize(b, PREC.POW)}**${parenthesize(x, PREC.POW)}`;
}

function printAdd(e: Add): string {
  const parts: string[] = [];
  for (const term of asOrderedTerms(e)) {
    let t = str(term);
    let sign = '+';
    if (t.startsWith('-')) {
      sign = '-';
      t = t.slice(1);
    }
    parts.push(sign, precedence(term) < PREC.ADD ? `(${t})` : t);
  }
  const first = parts.shift();
  return (first === '-' ? '-' : '') + parts.join(' ');
}

export function str(e: Expr): string {
  if (e instanceof Rational) return e.q === 1n ? `${e.p}` : `${e.p}/${e.q}`;
  if (e instanceof Float) return floatString(e.value);
  if (e instanceof Sym) return e.name;
  if (e instanceof Constant) return e.name;
  if (e instanceof Fn) return `${sympyFunctionName(e.name)}(${e.args.map(str).join(', ')})`;
  if (e instanceof Add) return printAdd(e);
  if (e instanceof Mul) return printMul(e);
  if (e instanceof Pow) return printPow(e);
  return e.key;
}

impl.str = str;

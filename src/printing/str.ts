// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Plain-text printer, e.g. `x^2 + 2*x*y - sqrt(2)/2`.
 */

import { Add, Constant, Expr, Float, Fn, Mul, Pow, Rational, Sym, impl, isNum } from '../core/nodes';
import { mul, pow, splitCoeff } from '../core/ops';
import { floatString, isNegativeTerm, printOrder, splitFraction } from './order';

export const PREC = { ADD: 10, MUL: 20, POW: 30, ATOM: 100 } as const;

export function precedence(e: Expr): number {
  if (e instanceof Rational) {
    if (e.isNegative) return PREC.ADD;
    return e.isInteger ? PREC.ATOM : PREC.MUL;
  }
  if (e instanceof Float) return e.isNegative ? PREC.ADD : PREC.ATOM;
  if (e instanceof Add) return PREC.ADD;
  if (e instanceof Mul) return isNegativeTerm(e) ? PREC.ADD : PREC.MUL;
  if (e instanceof Pow) {
    if (e.base instanceof Constant && e.base.name === 'E') return PREC.ATOM;
    if (e.exp instanceof Rational && e.exp.p === 1n && e.exp.q === 2n) return PREC.ATOM;
    if (isNegExp(e.exp)) return PREC.MUL;
    return PREC.POW;
  }
  return PREC.ATOM;
}

function isNegExp(x: Expr): boolean {
  const [c] = splitCoeff(x);
  return c.isNegative;
}

function paren(e: Expr, minPrec: number): string {
  const s = str(e);
  return precedence(e) < minPrec ? `(${s})` : s;
}

export function str(e: Expr): string {
  if (e instanceof Rational) return e.q === 1n ? `${e.p}` : `${e.p}/${e.q}`;
  if (e instanceof Float) return floatString(e);
  if (e instanceof Sym) return e.name;
  if (e instanceof Constant) return e.name;
  if (e instanceof Fn) return `${e.name}(${e.args.map(str).join(', ')})`;

  if (e instanceof Add) {
    const terms = printOrder(e.args);
    let out = str(terms[0]!);
    for (const t of terms.slice(1)) {
      if (isNegativeTerm(t)) out += ` - ${paren(mul(-1, t), PREC.MUL)}`;
      else out += ` + ${str(t)}`;
    }
    return out;
  }

  if (e instanceof Mul) {
    const f = splitFraction(e);
    const numParts: string[] = [];
    const denParts: string[] = [];
    if (f.coeff instanceof Rational) {
      if (f.coeff.p !== 1n) numParts.push(`${f.coeff.p}`);
      if (f.coeff.q !== 1n) denParts.push(`${f.coeff.q}`);
    } else if (f.coeff.value !== 1) {
      numParts.push(floatString(f.coeff));
    }
    for (const x of f.num) numParts.push(paren(x, PREC.MUL));
    for (const x of f.den) denParts.push(paren(x, PREC.MUL));
    let s = numParts.length > 0 ? numParts.join('*') : '1';
    if (denParts.length === 1) {
      const single = f.den.length === 1 ? f.den[0]! : undefined;
      const needs = single !== undefined && precedence(single) < PREC.POW;
      s += needs ? `/(${denParts[0]})` : `/${denParts[0]}`;
    } else if (denParts.length > 1) {
      s += `/(${denParts.join('*')})`;
    }
    return (f.sign ? '-' : '') + s;
  }

  if (e instanceof Pow) {
    const [b, x] = e.args;
    if (b instanceof Constant && b.name === 'E') return `exp(${str(x)})`;
    if (x instanceof Rational && x.p === 1n && x.q === 2n) return `sqrt(${str(b)})`;
    if (isNegExp(x)) {
      const inv = pow(b, mul(-1, x));
      return `1/${precedence(inv) < PREC.POW ? `(${str(inv)})` : str(inv)}`;
    }
    const bs = precedence(b) < PREC.ATOM || isNum(b) ? paren(b, PREC.ATOM) : str(b);
    const xs = paren(x, PREC.ATOM);
    return `${bs}^${xs}`;
  }
  return e.key;
}

impl.str = str;

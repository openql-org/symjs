// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Helpers shared by the printers: term ordering and numerator/denominator split.
 */

import { Add, Constant, Expr, Float, Fn, Mul, Num, Pow, Rational, S, Sym, isNum } from '../core/nodes';
import { numNeg } from '../core/num';
import { mul, pow, splitCoeff } from '../core/ops';

function degree(e: Expr): number {
  if (e instanceof Sym) return 1;
  if (e instanceof Pow && e.exp instanceof Rational && e.base instanceof Sym) return e.exp.value;
  if (e instanceof Mul) return e.args.reduce((s, a) => s + (isNum(a) ? 0 : degree(a)), 0);
  if (isNum(e)) return 0;
  if (e instanceof Constant) return 0;
  return 0.5;
}

const hasSymbol = (e: Expr): boolean => e instanceof Sym || e.args.some(hasSymbol);

/**
 * Order terms of a sum for display: terms with symbols first (higher degree
 * first), then the rational constant, then other constant terms
 * (e.g. `x^2 + 2*x + 1`, `1 - 2*I`, `1/2 + sqrt(2)/2`).
 */
export function printOrder(args: readonly Expr[]): Expr[] {
  const category = (e: Expr) => (isNum(e) ? 1 : hasSymbol(e) ? 0 : 2);
  return [...args].sort((a, b) => {
    const dc = category(a) - category(b);
    if (dc !== 0) return dc;
    const [, ra] = splitCoeff(a);
    const [, rb] = splitCoeff(b);
    const dd = degree(rb) - degree(ra);
    if (dd !== 0) return dd;
    return ra.key < rb.key ? -1 : ra.key > rb.key ? 1 : 0;
  });
}

/**
 * Order factors of a product for display (SymPy-like):
 * I, numeric radicals, constants, symbols/powers by base, then exp and functions.
 * E.g. `2*I*sqrt(2)*x^2*y*exp(x)*sin(x)`.
 */
export function factorOrder(fs: readonly Expr[]): Expr[] {
  const rank = (e: Expr): number => {
    if (e instanceof Constant) return e.name === 'I' ? 0 : 2;
    if (e instanceof Pow && isNum(e.base)) return 1;
    if (e instanceof Pow && e.base instanceof Constant && e.base.name === 'E') return 4;
    if (e instanceof Fn) return 4;
    return 3;
  };
  const k = (e: Expr) => (e instanceof Pow && !(e.base instanceof Constant) ? e.base.key : e.key);
  return [...fs].sort((a, b) => {
    const d = rank(a) - rank(b);
    if (d !== 0) return d;
    return k(a) < k(b) ? -1 : k(a) > k(b) ? 1 : 0;
  });
}

/** Does this term print with a leading minus sign? */
export function isNegativeTerm(e: Expr): boolean {
  const [c] = splitCoeff(e);
  return c.isNegative;
}

export interface Fraction {
  sign: boolean; // true if negative
  coeff: Num; // positive numeric coefficient
  num: Expr[];
  den: Expr[];
}

/** Split a product into sign, coefficient, numerator and denominator factors. */
export function splitFraction(e: Expr): Fraction {
  const factors = e instanceof Mul ? e.args : [e];
  let coeff: Num = S.One;
  const num: Expr[] = [];
  const den: Expr[] = [];
  for (const f of factors) {
    if (isNum(f)) {
      coeff = f;
      continue;
    }
    if (f instanceof Pow) {
      const x = f.exp;
      const negExp = (isNum(x) && x.isNegative) || (x instanceof Mul && isNum(x.args[0]!) && (x.args[0] as Num).isNegative);
      if (negExp && !(f.base instanceof Constant && f.base.name === 'E')) {
        den.push(pow(f.base, mul(-1, x)));
        continue;
      }
    }
    num.push(f);
  }
  const sign = coeff.isNegative;
  if (sign) coeff = numNeg(coeff);
  return { sign, coeff, num: factorOrder(num), den: factorOrder(den) };
}

export function isAdd(e: Expr): e is Add {
  return e instanceof Add;
}

export function floatString(f: Float): string {
  const v = f.value;
  if (Number.isInteger(v) && Math.abs(v) < 1e21) return `${v}.0`;
  return `${v}`;
}

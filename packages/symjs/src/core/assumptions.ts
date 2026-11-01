// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Three-valued assumption queries (true / false / undefined = unknown).
 */

import { Add, Constant, Expr, Fn, Float, Mul, Pow, Rational, Special, Sym, impl } from './nodes';

export type Tri = boolean | undefined;

const all = (xs: readonly Expr[], f: (e: Expr) => Tri): Tri => {
  let unknown = false;
  for (const x of xs) {
    const r = f(x);
    if (r === false) return false;
    if (r === undefined) unknown = true;
  }
  return unknown ? undefined : true;
};

export function isZero(e: Expr): Tri {
  if (e instanceof Rational || e instanceof Float) return e.isZero;
  if (e instanceof Special) return e.name === 'nan' ? undefined : false;
  if (e instanceof Constant) return false;
  if (e instanceof Sym) return e.assumptions.positive ? false : undefined;
  if (e instanceof Pow && e.base instanceof Constant && e.base.name === 'E') return false;
  return undefined;
}

export function isReal(e: Expr): Tri {
  if (e instanceof Rational || e instanceof Float) return true;
  // extended reals: oo and -oo behave as real for simplification purposes
  if (e instanceof Special) return e.name === 'oo' || e.name === '-oo' ? true : undefined;
  if (e instanceof Constant) return e.name !== 'I';
  if (e instanceof Sym) return e.assumptions.real ? true : undefined;
  if (e instanceof Add) return all(e.args, isReal) ? true : undefined;
  if (e instanceof Mul) {
    // a product of reals is real; exactly one imaginary-unit factor makes it non-real
    let nonReal = 0;
    for (const a of e.args) {
      const r = isReal(a);
      if (r === undefined) return undefined;
      if (r === false) {
        if (a instanceof Constant && a.name === 'I') nonReal++;
        else return undefined;
      }
    }
    if (nonReal === 0) return true;
    return all(e.args.filter((a) => !(a instanceof Constant)), isNonZero) ? false : undefined;
  }
  if (e instanceof Pow) {
    const [b, x] = e.args;
    if (isReal(b) && isIntegerQ(x)) return isZero(b) && isNegative(x) ? undefined : true;
    if (isPositive(b) && isReal(x)) return true;
    if (isNonNegative(b) && isPositive(x)) return true;
    return undefined;
  }
  if (e instanceof Fn) {
    const a = e.args[0]!;
    switch (e.name) {
      case 'abs':
      case 're':
      case 'im':
      case 'arg':
        return true;
      case 'sin':
      case 'cos':
      case 'tan':
      case 'atan':
      case 'sinh':
      case 'cosh':
      case 'tanh':
      case 'conjugate':
      case 'asinh':
      case 'acot':
      case 'sech':
      case 'sinc':
        return isReal(a) ? true : undefined;
      case 'log':
        return isPositive(a) ? true : undefined;
      default:
        return undefined;
    }
  }
  return undefined;
}

export function isNonZero(e: Expr): Tri {
  const z = isZero(e);
  if (z !== undefined) return !z;
  if (isPositive(e) || isNegative(e)) return true;
  if (e instanceof Mul) return all(e.args, isNonZero);
  if (e instanceof Pow) return isNonZero(e.base);
  return undefined;
}

export function isPositive(e: Expr): Tri {
  if (e instanceof Rational || e instanceof Float) return e.isPositive;
  if (e instanceof Special) return e.name === 'oo' ? true : e.name === '-oo' ? false : undefined;
  if (e instanceof Constant) return e.name === 'I' ? false : true;
  if (e instanceof Sym) return e.assumptions.positive ? true : e.assumptions.nonpositive ? false : undefined;
  if (e instanceof Add) return all(e.args, isPositive) ? true : undefined;
  if (e instanceof Mul) {
    let neg = 0;
    for (const a of e.args) {
      if (isPositive(a)) continue;
      if (isNegative(a)) neg++;
      else return undefined;
    }
    return neg % 2 === 0;
  }
  if (e instanceof Pow) {
    const [b, x] = e.args;
    if (isPositive(b) && isReal(x)) return true;
    if (isReal(b) && isNonZero(b) && x instanceof Rational && x.isInteger && x.p % 2n === 0n) return true;
    return undefined;
  }
  if (e instanceof Fn) {
    if (e.name === 'abs') return isNonZero(e.args[0]!) ? true : undefined;
  }
  return undefined;
}

export function isNegative(e: Expr): Tri {
  if (e instanceof Rational || e instanceof Float) return e.isNegative;
  if (e instanceof Special) return e.name === '-oo' ? true : e.name === 'oo' ? false : undefined;
  if (e instanceof Constant) return false;
  if (e instanceof Sym) return e.assumptions.negative ? true : e.assumptions.nonnegative ? false : undefined;
  if (e instanceof Add) return all(e.args, isNegative) ? true : undefined;
  if (e instanceof Mul) {
    let neg = 0;
    for (const a of e.args) {
      if (isPositive(a)) continue;
      if (isNegative(a)) neg++;
      else return undefined;
    }
    return neg % 2 === 1;
  }
  return undefined;
}

export function isNonNegative(e: Expr): Tri {
  if (isPositive(e) || isZero(e)) return true;
  if (e instanceof Sym && e.assumptions.nonnegative) return true;
  if (e instanceof Sym && e.assumptions.negative) return false;
  if (e instanceof Fn && e.name === 'abs') return true;
  if (e instanceof Add) return all(e.args, isNonNegative) ? true : undefined;
  if (e instanceof Mul) return all(e.args, isNonNegative) ? true : undefined;
  if (e instanceof Pow && isNonNegative(e.base) && isReal(e.exp)) return true;
  if (e instanceof Pow && isReal(e.base) && e.exp instanceof Rational && e.exp.isInteger && e.exp.p % 2n === 0n) {
    return true;
  }
  const n = isNegative(e);
  return n === true ? false : undefined;
}

export function isIntegerQ(e: Expr): Tri {
  if (e instanceof Rational) return e.isInteger;
  if (e instanceof Special) return false;
  if (e instanceof Float) return false;
  if (e instanceof Constant) return false;
  if (e instanceof Sym) return e.assumptions.integer ? true : undefined;
  if (e instanceof Add || e instanceof Mul) return all(e.args, isIntegerQ) ? true : undefined;
  if (e instanceof Pow) {
    if (isIntegerQ(e.base) && isIntegerQ(e.exp) && isNonNegative(e.exp)) return true;
  }
  return undefined;
}
impl.isReal = isReal;

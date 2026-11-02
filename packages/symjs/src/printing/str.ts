// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Plain-text printer compatible with SymPy's `StrPrinter`
 * (e.g. `x**2 + 2*x*y - sqrt(2)/2`).
 */

import type { Expr } from '../core/nodes';
import { Add, ExtensionExpr, BoolAtom, Constant, Derivative, Float, Fn, Integral, Limit, Mul, Order, Piecewise, Pow, Rational, Rel, Special, Sym, UndefFn, impl, isNum } from '../core/nodes';
import { mul, pow, splitCoeff } from '../core/ops';
import { numNeg } from '../core/num';
import { floatToString } from '../numeric/mpf';
import { asOrderedFactors, asOrderedTerms, sympyFunctionName } from './sortkey';
import { Concrete } from '../core/concrete';
import { at } from '../core/guard';

/** SymPy precedence values. */
export const PREC = { REL: 35, ADD: 40, MUL: 50, POW: 60, FUNC: 70, ATOM: 1000 } as const;

export const REL_SYMBOL = { Lt: '<', Le: '<=', Gt: '>', Ge: '>=' } as const;

const isExp = (e: Expr): boolean => e instanceof Pow && e.base instanceof Constant && e.base.name === 'E';

/** SymPy `could_extract_minus_sign` for printing purposes. */
export function startsNegative(e: Expr): boolean {
  if (isNum(e)) return e.isNegative;
  if (e instanceof Special) return e.name === '-oo';
  if (e instanceof Mul) {
    const c = at(e.args, 0);
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
  if (e instanceof Special) return e.name === '-oo' ? PREC.ADD : PREC.ATOM;
  if (e instanceof Add) return PREC.ADD;
  if (e instanceof Mul) return startsNegative(e) ? PREC.ADD : PREC.MUL;
  if (isExp(e)) return PREC.FUNC;
  if (e instanceof Pow) return PREC.POW;
  if (e instanceof Fn || e instanceof Piecewise || e instanceof UndefFn) return PREC.FUNC;
  if (e instanceof Rel) return PREC.REL;
  return PREC.ATOM;
}

/** Format a float like SymPy's StrPrinter (full precision at top level, trailing zeros stripped inside). */
export function floatString(v: number | Float, stripZeros = false): string {
  const f = typeof v === 'number' ? new Float(v) : v;
  return floatToString(f.mpf, f.prec, stripZeros);
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
    expr = keepCoeff(numNeg(c), rest);
  }
  const a: Expr[] = [];
  const b: Expr[] = [];
  for (const item of expr instanceof Mul ? asOrderedFactors(expr) : [expr]) {
    if (item instanceof Pow && item.isCommutative && !isExp(item) && splitCoeff(item.exp)[0].isNegative) {
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
    if (x.p === -1n && x.q === 2n && e.isCommutative) return `1/sqrt(${str(b)})`;
    if (x.p === -1n && x.q === 1n && e.isCommutative) return `1/${parenthesize(b, PREC.POW)}`;
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

let printLevel = 0;

export function str(e: Expr): string {
  printLevel++;
  try {
    return strInner(e);
  } finally {
    printLevel--;
  }
}

/** Print as a sub-expression (e.g. a matrix entry): floats drop trailing zeros. */
export function strNested(e: Expr): string {
  printLevel++;
  try {
    return str(e);
  } finally {
    printLevel--;
  }
}

function strInner(e: Expr): string {
  if (e instanceof Rational) return e.q === 1n ? `${e.p}` : `${e.p}/${e.q}`;
  if (e instanceof Float) return floatString(e, printLevel > 1);
  if (e instanceof Sym) return e.printName;
  if (e instanceof Constant) return e.name;
  if (e instanceof Special) return e.name;
  if (e instanceof Fn) return `${sympyFunctionName(e.name)}(${e.args.map(str).join(', ')})`;
  if (e instanceof Add) return printAdd(e);
  if (e instanceof Mul) {
    // an unevaluated product of several numbers (Mul(1, 2, evaluate=False)) prints as written
    if (e.args.filter((a) => a instanceof Rational).length > 1) return e.args.map((a) => parenthesize(a, PREC.MUL)).join('*');
    return printMul(e);
  }
  if (e instanceof Pow) return printPow(e);
  if (e instanceof BoolAtom) return e.value ? 'True' : 'False';
  if (e instanceof Rel) {
    if (e.op === 'Eq' || e.op === 'Ne') return `${e.op}(${str(e.lhs)}, ${str(e.rhs)})`;
    return `${parenthesize(e.lhs, PREC.REL)} ${REL_SYMBOL[e.op]} ${parenthesize(e.rhs, PREC.REL)}`;
  }
  if (e instanceof Piecewise) return `Piecewise(${e.pairs.map(([x, c]) => `(${str(x)}, ${str(c)})`).join(', ')})`;
  if (e instanceof UndefFn) return `${e.name}(${e.args.map(str).join(', ')})`;
  if (e instanceof Concrete) {
    return `${e.kind2}(${str(e.function)}, ${e.limits.map(([k, a, b]) => `(${str(k)}, ${str(a)}, ${str(b)})`).join(', ')})`;
  }
  if (e instanceof Derivative) {
    const vs = e.variableCount.map(([v, n]) => (n === 1 ? str(v) : `(${str(v)}, ${n})`));
    return `Derivative(${str(e.expr)}, ${vs.join(', ')})`;
  }
  if (e instanceof Limit) {
    return `Limit(${str(e.expr)}, ${str(e.variable)}, ${str(e.point)}, dir='${e.dir}')`;
  }
  if (e instanceof Order) {
    if (e.args.length > 3) {
      // several variables: O(e, x, y) at 0, O(e, (x, p), (y, p)) elsewhere
      const vs = e.args.slice(1, -1);
      const pt = at(e.args, e.args.length - 1);
      const at0 = pt instanceof Rational && pt.isZero;
      return `O(${str(at(e.args, 0))}, ${vs.map((v) => (at0 ? str(v) : `(${str(v)}, ${str(pt)})`)).join(', ')})`;
    }
    const v = e.variable;
    const p = e.point;
    if (!v || !p || (p instanceof Rational && p.isZero)) return `O(${str(e.expr)})`;
    return `O(${str(e.expr)}, (${str(v)}, ${str(p)}))`;
  }
  if (e instanceof ExtensionExpr) return e.printStr(str);
  if ('printStr' in e && typeof e.printStr === 'function') return String(e.printStr(str));
  if (e instanceof Integral) {
    // nested integrals print as one multiple integral, innermost limits first (SymPy)
    const lims: string[] = [];
    let cur: Expr = e;
    while (cur instanceof Integral) {
      const [, , a, b] = cur.args;
      const v = cur.variable;
      lims.unshift(a === undefined ? str(v) : b === undefined ? `(${str(v)}, ${str(a)})` : `(${str(v)}, ${str(a)}, ${str(b)})`);
      cur = cur.integrand;
    }
    return `Integral(${str(cur)}, ${lims.join(', ')})`;
  }
  return e.key;
}

impl.str = str;

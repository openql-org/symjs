// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Port of SymPy's `sort_key`, `as_ordered_factors` and `as_ordered_terms`.
 *
 * The printers use these to reproduce SymPy's term and factor ordering exactly
 * (e.g. `x**2*y`, `1 - 2*I`, `-sqrt(2)/4 + sqrt(6)/4`, `I*sin(x) + cos(x)`).
 */

import { Add, ComplexValue, Constant, Expr, Float, Fn, Mul, Order, Pow, Rational, S, Special, Sym, impl, isNum } from '../core/nodes';
import { pow, splitCoeff } from '../core/ops';

/** A SymPy-style sort key: nested tuples of numbers and strings. */
export type Key = number | string | Key[];

export function compareKeys(a: Key, b: Key): number {
  if (Array.isArray(a) && Array.isArray(b)) {
    const n = Math.min(a.length, b.length);
    for (let i = 0; i < n; i++) {
      const c = compareKeys(a[i]!, b[i]!);
      if (c !== 0) return c;
    }
    return a.length - b.length;
  }
  if (typeof a === 'number' && typeof b === 'number') return a < b ? -1 : a > b ? 1 : 0;
  if (typeof a === 'string' && typeof b === 'string') return a < b ? -1 : a > b ? 1 : 0;
  // heterogeneous comparison does not occur for well-formed keys; order by type for determinism
  const rank = (k: Key) => (typeof k === 'number' ? 0 : typeof k === 'string' ? 1 : 2);
  return rank(a) - rank(b);
}

/** SymPy class names used in class keys. */
const CONSTANT_CLASS: Record<string, string> = { I: 'ImaginaryUnit', pi: 'Pi', E: 'Exp1' };

/** SymPy FunctionClass.class_key priorities. */
const FUNCTION_PRIORITY: Record<string, number> = {
  exp: 10,
  log: 11,
  sin: 20,
  cos: 21,
  tan: 22,
  cot: 23,
  sinh: 30,
  cosh: 31,
  tanh: 32,
  coth: 33,
  conjugate: 40,
  re: 41,
  im: 42,
  arg: 43,
};

/** SymPy class name of a function node (e.g. abs -> Abs). */
export function sympyFunctionName(name: string): string {
  return name === 'abs' ? 'Abs' : name;
}

const isExp = (e: Expr): e is Pow => e instanceof Pow && e.base instanceof Constant && e.base.name === 'E';

function classKey(e: Expr): Key {
  if (isNum(e) || e instanceof Special) return [1, 0, 'Number'];
  if (e instanceof Sym) return [2, 0, 'Symbol'];
  if (e instanceof Constant) return [2, 0, CONSTANT_CLASS[e.name]!];
  if (e instanceof Mul) return [3, 0, 'Mul'];
  if (e instanceof Add) return [3, 1, 'Add'];
  if (isExp(e)) return [4, 10, 'exp'];
  if (e instanceof Pow) return [3, 2, 'Pow'];
  if (e instanceof Fn) {
    const name = sympyFunctionName(e.name);
    return [4, FUNCTION_PRIORITY[name] ?? 10000, name];
  }
  return [5, 0, e.kind];
}

const numValue = (e: Expr): number => (e instanceof Rational || e instanceof Float ? e.value : NaN);

const ONE_KEY: Key = [[1, 0, 'Number'], [0, []], [], 1];

/** SymPy `Basic.sort_key()` / `default_sort_key`. */
const SPECIAL_VALUE: Record<string, number> = { oo: Infinity, '-oo': -Infinity, zoo: Infinity, nan: NaN };

export function sortKey(e: Expr): Key {
  if (isNum(e)) return [[1, 0, 'Number'], [0, []], [], numValue(e)];
  if (e instanceof Special) return [[1, 0, 'Number'], [0, []], [], SPECIAL_VALUE[e.name]!];
  if (e instanceof Sym) return [[2, 0, 'Symbol'], [1, [e.name]], ONE_KEY, 1];
  if (e instanceof Constant) return [classKey(e), [1, [impl.str(e)]], ONE_KEY, 1];

  // Expr.sort_key
  const [coeff, rest] = splitCoeff(e);
  let expr: Expr = rest;
  let exp: Expr = S.One;
  let ck: Key;
  let args: Key[];
  if (isExp(expr)) {
    // exp(x) is a Function in SymPy
    ck = [4, 10, 'exp'];
    args = [sortKey(expr.exp)];
  } else {
    if (expr instanceof Pow) {
      exp = expr.exp;
      expr = expr.base;
    }
    ck = classKey(expr);
    if (expr.isAtom) args = [impl.str(expr)];
    else if (expr instanceof Add) args = asOrderedTerms(expr).map(sortKey);
    else if (expr instanceof Mul) args = asOrderedFactors(expr).map(sortKey);
    else args = expr.args.map(sortKey);
  }
  return [ck, [args.length, args], sortKey(exp), numValue(coeff)];
}

/** SymPy `Mul.as_ordered_factors()` (all factors are commutative here). */
export function asOrderedFactors(e: Expr): Expr[] {
  const fs = e instanceof Mul ? [...e.args] : [e];
  return fs
    .map((f) => ({ f, k: sortKey(f) }))
    .sort((a, b) => compareKeys(a.k, b.k))
    .map((x) => x.f);
}

const hasFreeSymbols = (e: Expr): boolean => e instanceof Sym || e.args.some(hasFreeSymbols);

/** SymPy `decompose_power`: x**(p/q) -> (x**(1/q), p), x**(2*y) -> (x**y, 2). */
function decomposePower(f: Expr): [Expr, number] {
  if (!(f instanceof Pow)) return [f, 1];
  const [b, x] = f.args;
  if (x instanceof Rational) {
    if (!x.isInteger) return [pow(b, Rational.of(1n, x.q)), Number(x.p)];
    return [b, Number(x.p)];
  }
  if (x instanceof Float) return [f, 1];
  const [c, tail] = splitCoeff(x);
  if (!(c instanceof Rational)) return [f, 1];
  if (c.p === -1n && c.q === 1n) return [pow(b, tail), -1];
  if (!c.isOne) return [pow(b, impl.mul(Rational.of(1n, c.q), tail)), Number(c.p)];
  return [f, 1];
}

/** SymPy `Expr.as_ordered_terms()` with the default (lex) ordering. */
export function asOrderedTerms(e: Expr): Expr[] {
  const all = e instanceof Add ? e.args : [e];
  const orders = all.filter((t) => t instanceof Order);
  if (orders.length > 0) {
    // SymPy: with Order terms, the other terms are sorted in reverse (ascending degree) and O comes last
    const rest = all.filter((t) => !(t instanceof Order));
    return [...lexOrder(rest).reverse(), ...orders];
  }
  const terms = all;
  // Special case: Add(positive Number, Mul(negative Number, expr)) keeps the number first (1 - x**2)
  if (terms.length === 2) {
    const isNumberLike = (t: Expr) => isNum(t) || (t instanceof Constant && t.name !== 'I');
    const sorted = [...terms].sort((a, b) => (isNumberLike(a) ? 0 : 1) - (isNumberLike(b) ? 0 : 1));
    const [n, m] = sorted as [Expr, Expr];
    if (isNumberLike(n) && m instanceof Mul && m.args.length === 2) {
      const c = m.args[0]!;
      const positive = isNum(n) ? n.isPositive : true;
      if (positive && isNum(c) && c.isNegative) return sorted;
    }
  }
  return lexOrder(terms);
}

/** Sort terms by SymPy's lex key on the monomials of the generators. */
function lexOrder(terms: readonly Expr[]): Expr[] {
  const gens = new Map<string, Expr>();
  const parsed = terms.map((term) => {
    const [c, rest] = splitCoeff(term);
    let coeff: ComplexValue = { re: numValue(c), im: 0 };
    const cpart = new Map<string, number>();
    if (!(rest instanceof Rational && rest.isOne)) {
      for (const factor of rest instanceof Mul ? rest.args : [rest]) {
        if (!hasFreeSymbols(factor)) {
          try {
            const v = impl.toComplex(factor);
            coeff = { re: coeff.re * v.re - coeff.im * v.im, im: coeff.re * v.im + coeff.im * v.re };
            continue;
          } catch {
            // fall through: treat as a generator
          }
        }
        const [base, exp] = decomposePower(factor);
        cpart.set(base.key, (cpart.get(base.key) ?? 0) + exp);
        gens.set(base.key, base);
      }
    }
    return { term, coeff, cpart };
  });
  const genList = [...gens.values()].map((g) => ({ g, k: sortKey(g) })).sort((a, b) => compareKeys(a.k, b.k));
  const keyed = parsed.map(({ term, coeff, cpart }) => {
    const monom: Key[] = genList.map(({ g }) => -(cpart.get(g.key) ?? 0));
    const ck: Key = [
      [coeff.im !== 0 ? 1 : 0, coeff.im],
      [coeff.re, coeff.im],
    ];
    return { term, k: [monom, [], ck] as Key };
  });
  return keyed.sort((a, b) => compareKeys(a.k, b.k)).map((x) => x.term);
}

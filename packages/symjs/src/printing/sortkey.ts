// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Port of SymPy's `sort_key`, `as_ordered_factors` and `as_ordered_terms`.
 *
 * The printers use these to reproduce SymPy's term and factor ordering exactly
 * (e.g. `x**2*y`, `1 - 2*I`, `-sqrt(2)/4 + sqrt(6)/4`, `I*sin(x) + cos(x)`).
 */

import type { ComplexValue, ConstantName, Expr, RelOp, SpecialName } from '../core/nodes';
import { Add, BoolAtom, Constant, Derivative, Dummy, ExtensionExpr, Float, Fn, Mul, Order, Pow, Rational, Rel, S, Special, Sym, UndefFn, Wild, WildFunction, impl, isNum } from '../core/nodes';
import { pow, splitCoeff } from '../core/ops';
import { Concrete } from '../core/concrete';
import { at, pair } from '../core/guard';

/** A SymPy-style sort key: nested tuples of numbers and strings. */
export type Key = number | string | Key[];

export function compareKeys(a: Key, b: Key): number {
  if (Array.isArray(a) && Array.isArray(b)) {
    const n = Math.min(a.length, b.length);
    for (let i = 0; i < n; i++) {
      const c = compareKeys(at(a, i), at(b, i));
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
const CONSTANT_CLASS: Record<ConstantName, string> = {
  I: 'ImaginaryUnit',
  pi: 'Pi',
  E: 'Exp1',
  EulerGamma: 'EulerGamma',
  Catalan: 'Catalan',
  GoldenRatio: 'GoldenRatio',
  TribonacciConstant: 'TribonacciConstant',
};

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
  // functions whose nargs is Naturals0 in SymPy (class_key (4, 0, name))
  exp_polar: 0,
  lerchphi: 0,
  meijerg: 0,
  LeviCivita: 0,
  carmichael: 0,
};

/** SymPy class name of a function node (e.g. abs -> Abs). */
const SYMPY_FN_NAMES: Record<string, string> = { abs: 'Abs', ff: 'FallingFactorial', rf: 'RisingFactorial' };

export function sympyFunctionName(name: string): string {
  return SYMPY_FN_NAMES[name] ?? name;
}

const isExp = (e: Expr): e is Pow => e instanceof Pow && e.base instanceof Constant && e.base.name === 'E';

const REL_CLASS: Record<RelOp, string> = { Eq: 'Equality', Ne: 'Unequality', Lt: 'StrictLessThan', Le: 'LessThan', Gt: 'StrictGreaterThan', Ge: 'GreaterThan' };

// a WildFunction is a Function in SymPy (class key (4, 0, 'WildFunction'))
const symClass = (e: Sym): Key => (e instanceof WildFunction ? [4, 0, 'WildFunction'] : [e.sortPriority, 0, e instanceof Wild ? 'Wild' : e instanceof Dummy ? 'Dummy' : e.sortClass]);

/** SymPy class_key: (priority, sub-priority, class name) used to order expressions. */
export function classKey(e: Expr): Key {
  if (isNum(e) || e instanceof Special) return [1, 0, 'Number'];
  if (e instanceof BoolAtom) return [5, 0, e.value ? 'BooleanTrue' : 'BooleanFalse'];
  if (e instanceof Sym) return symClass(e);
  if (e instanceof Constant) return [2, 0, CONSTANT_CLASS[e.name]];
  if (e instanceof Mul) return [3, 0, 'Mul'];
  if (e instanceof Add) return [3, 1, 'Add'];
  if (isExp(e)) return [4, 10, 'exp'];
  if (e instanceof Pow) return [3, 2, 'Pow'];
  if (e instanceof Fn) {
    const name = sympyFunctionName(e.name);
    return [4, FUNCTION_PRIORITY[name] ?? 10000, name];
  }
  if (e instanceof UndefFn) return [4, 0, e.name];
  if (e instanceof Derivative) return [5, 0, 'Derivative'];
  if (e instanceof Rel) return [5, 0, REL_CLASS[e.op]];
  // SymPy MatAdd and MatMul sort like Add and Mul
  if (e instanceof ExtensionExpr) return e.name === 'MatAdd' ? [3, 1, 'MatAdd'] : e.name === 'MatMul' ? [3, 0, 'MatMul'] : [5, 0, e.name];
  // a Sum or Product sorts by its class name
  if (e instanceof Concrete) return [5, 0, e.kind2];
  if ('className' in e && typeof e.className === 'string' && e.className) return [5, 0, e.className];
  return [5, 0, e.kind];
}

const ONE_KEY: Key = [[1, 0, 'Number'], [0, []], [], 1];

const SPECIAL_VALUE: Record<SpecialName, number> = { oo: Infinity, '-oo': -Infinity, zoo: Infinity, nan: NaN };

/**
 * SymPy `as_coeff_Mul()` as the value of the coefficient (the last entry of a
 * sort key) and the rest, where oo, -oo, zoo and nan are coefficients too
 * (they are Numbers in SymPy).
 */
function coeffMul(e: Expr): [number, Expr] {
  const [c, rest] = splitCoeff(e);
  const special = rest instanceof Mul ? rest.args.find((a) => a instanceof Special) : undefined;
  if (special instanceof Special) return [c.value * SPECIAL_VALUE[special.name], impl.mul(...rest.args.filter((a) => a !== special))];
  return [c.value, rest];
}

/** SymPy `Basic.sort_key()` / `default_sort_key`. */

export function sortKey(e: Expr): Key {
  if (isNum(e)) return [[1, 0, 'Number'], [0, []], [], e.value];
  if (e instanceof Special) return [[1, 0, 'Number'], [0, []], [], SPECIAL_VALUE[e.name]];
  if (e instanceof Dummy) return [[2, 0, 'Dummy'], [2, [e.name, e.dummyIndex]], ONE_KEY, 1];
  if (e instanceof Sym) return [symClass(e), [1, [e.printName]], ONE_KEY, 1];
  if (e instanceof Constant) return [classKey(e), [1, [impl.str(e)]], ONE_KEY, 1];
  if (e instanceof BoolAtom) return [classKey(e), [0, []], ONE_KEY, 1];

  // Expr.sort_key
  const [coeff, rest] = coeffMul(e);
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
    // an Indexed is an Atom in SymPy (is_Atom = True): it sorts by its printed form
    if (expr.isAtom || (expr instanceof ExtensionExpr && expr.name === 'Indexed')) args = [impl.str(expr)];
    else if (expr instanceof Add) args = asOrderedTerms(expr).map(sortKey);
    else if (expr instanceof Mul) args = asOrderedFactors(expr).map(sortKey);
    else args = expr.args.map(sortKey);
  }
  return [ck, [args.length, args], sortKey(exp), coeff];
}

/** SymPy `Mul.as_ordered_factors()` (all factors are commutative here). */
export function asOrderedFactors(e: Expr): Expr[] {
  const fs = e instanceof Mul ? [...e.args] : [e];
  // commutative factors are sorted; non-commutative ones keep their order
  const c = fs.filter((f) => f.isCommutative);
  const nc = fs.filter((f) => !f.isCommutative);
  return [
    ...c
      .map((f) => ({ f, k: sortKey(f) }))
      .sort((a, b) => compareKeys(a.k, b.k))
      .map((x) => x.f),
    ...nc,
  ];
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

/** A monomial ordering for SymPy `as_ordered_terms(order)`: lex, grlex, grevlex, ilex, igrlex or igrevlex, optionally prefixed by 'rev-'. */
export type TermOrder = 'lex' | 'grlex' | 'grevlex' | 'ilex' | 'igrlex' | 'igrevlex' | `rev-${'lex' | 'grlex' | 'grevlex' | 'ilex' | 'igrlex' | 'igrevlex'}`;

/** A monomial key: nested tuples of numbers. */
type NumKey = number | NumKey[];

/** -key, elementwise and recursively (SymPy InverseOrder and _parse_order's neg). */
const negKey = (k: NumKey): NumKey => (typeof k === 'number' ? -k : k.map(negKey));

/** SymPy monomial_key(order) for an exponent vector. */
function monomialKey(order: string, m: number[]): NumKey {
  const sum = m.reduce((a, b) => a + b, 0);
  switch (order) {
    case 'lex':
      return m;
    case 'grlex':
      return [sum, m];
    case 'grevlex':
      return [sum, [...m].reverse().map((v) => -v)];
    case 'ilex':
    case 'igrlex':
    case 'igrevlex':
      return negKey(monomialKey(order.slice(1), m));
    default:
      throw new RangeError(`supported monomial orderings are 'lex', 'grlex' and 'grevlex' (or i-, rev- prefixed), got ${order}`);
  }
}

/**
 * SymPy `Expr.as_ordered_terms(order)`: without an order the printers'
 * default (lex, with SymPy's special case 1 - x**2); with a monomial
 * ordering the terms sorted by it (reversed for a 'rev-' prefix).
 */
export function asOrderedTerms(e: Expr, order?: TermOrder): Expr[] {
  if (order !== undefined) {
    const reverse = order.startsWith('rev-');
    const sorted = lexOrder(e instanceof Add ? e.args : [e], reverse ? order.slice(4) : order);
    return reverse ? sorted.reverse() : sorted;
  }
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
    const [n, m] = pair(sorted);
    if (isNumberLike(n) && m instanceof Mul && m.args.length === 2) {
      const c = at(m.args, 0);
      const positive = isNum(n) ? n.isPositive : true;
      if (positive && isNum(c) && c.isNegative) return sorted;
    }
  }
  return lexOrder(terms);
}

/** Sort terms by SymPy's key on the monomials of the generators (lex by default). */
function lexOrder(terms: readonly Expr[], order = 'lex'): Expr[] {
  const gens = new Map<string, Expr>();
  const parsed = terms.map((term) => {
    const [c, rest] = splitCoeff(term);
    let coeff: ComplexValue = { re: c.value, im: 0 };
    const cpart = new Map<string, number>();
    const ncpart: Expr[] = [];
    if (!(rest instanceof Rational && rest.isOne)) {
      for (const factor of rest instanceof Mul ? rest.args : [rest]) {
        if (!factor.isCommutative) {
          ncpart.push(factor);
          continue;
        }
        if (!hasFreeSymbols(factor)) {
          try {
            const v = impl.toComplex(factor);
            // avoid 0*oo = nan for real infinite factors
            coeff =
              v.im === 0
                ? { re: coeff.re * v.re, im: coeff.im === 0 ? 0 : coeff.im * v.re }
                : { re: coeff.re * v.re - coeff.im * v.im, im: coeff.re * v.im + coeff.im * v.re };
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
    return { term, coeff, cpart, ncpart };
  });
  const genList = [...gens.values()].map((g) => ({ g, k: sortKey(g) })).sort((a, b) => compareKeys(a.k, b.k));
  const keyed = parsed.map(({ term, coeff, cpart, ncpart }) => {
    const monom = negKey(monomialKey(order, genList.map(({ g }) => cpart.get(g.key) ?? 0)));
    const ck: Key = [
      [coeff.im !== 0 ? 1 : 0, coeff.im],
      [coeff.re, coeff.im],
    ];
    return { term, k: [monom, ncpart.map(sortKey), ck] };
  });
  return keyed.sort((a, b) => compareKeys(a.k, b.k)).map((x) => x.term);
}

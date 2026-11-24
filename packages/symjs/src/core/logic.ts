// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Relations, boolean constants and Piecewise.
 */

import { Special } from './nodes';
import type { ExprLike, RelOp } from './nodes';
import { Expr } from './nodes';
import { Add, BoolAtom, ExtensionExpr, Float, Fn, Mul, Piecewise, Pow, Rational, Rel, S, Sym, impl, isNum, registerHeadResolver } from './nodes';
import { numCmp } from './num';
import { add, couldExtractMinusSign, knownNonreal, mul, sympify } from './ops';
import { BoolOp, and, or } from './boolalg';
import { compareKeys, sortKey } from '../printing/sortkey';
import { at } from './guard';
import { isIntegerQ, isKnownExtendedReal, isNegative, isNonNegative, isNonZero, isPositive, isReal, isZero } from './assumptions';

const isBoolean = (e: Expr): boolean => e instanceof Rel || e instanceof BoolAtom || e instanceof BoolOp;
const isSpecial = (name: string) => (x: Expr): boolean => x instanceof Special && x.name === name;

/** A real value that is finite: a real polynomial in real symbols (a real symbol is finite in SymPy; 1/x may be infinite). */
function isFiniteReal(e: Expr): boolean {
  const finite = (x: Expr): boolean =>
    !(x instanceof Special) && !(x instanceof Pow && !(x.exp instanceof Rational && x.exp.isInteger && !x.exp.isNegative)) && x.args.every(finite);
  return finite(e) && isReal(e) === true;
}

/** Create a relation, evaluating it to True/False when the difference is a number. */
/** Lower bound on factorial(n) when n is a nonnegative integer. */
export function factorialLowerBound(e: Expr): Rational | undefined {
  if (!(e instanceof Fn) || e.name !== 'factorial') return undefined;
  const n = at(e.args, 0);
  if (isIntegerQ(n) !== true || isNonNegative(n) !== true) return undefined;
  return isNonNegative(add(n, -2)) === true ? Rational.of(2) : S.One;
}

export function rel(op: RelOp, a: ExprLike, b: ExprLike): Expr {
  const lhs = sympify(a);
  const rhs = sympify(b);
  const equality = op === 'Eq' || op === 'Ne';
  const bounds = impl.accumBounds;
  if (!equality && bounds !== undefined && (bounds.is(lhs) || bounds.is(rhs))) {
    if ([lhs, rhs].some((e) => !isKnownExtendedReal(e))) throw new TypeError('AccumBounds comparisons require extended real operands');
    const [a, b] = bounds.is(lhs) ? bounds.bounds(lhs) : [lhs, lhs];
    const [c, d] = bounds.is(rhs) ? bounds.bounds(rhs) : [rhs, rhs];
    const lower = op === 'Lt' || op === 'Le';
    if (rel(op, lower ? b : a, lower ? c : d) === S.true) return S.true;
    if (rel(op, lower ? a : b, lower ? d : c) === S.false) return S.false;
    return new Rel(op, lhs, rhs);
  }
  // nan is not equal to anything (SymPy Eq(nan, nan) is False) and cannot be ordered
  if ([lhs, rhs].some(isSpecial('nan'))) {
    if (!equality) throw new TypeError('Invalid NaN comparison');
    return op === 'Eq' ? S.false : S.true;
  }
  if (!equality) {
    for (const operand of [lhs, rhs]) {
      if (isBoolean(operand)) throw new TypeError('Can only compare inequalities with expressions');
      if (isSpecial('zoo')(operand) || knownNonreal(operand)) {
        throw new TypeError(`Invalid comparison of non-real ${String(operand)}`);
      }
    }
  }
  if (equality && lhs instanceof BoolAtom && rhs instanceof BoolAtom) return (lhs.value === rhs.value) === (op === 'Eq') ? S.true : S.false;
  if (equality) {
    const symbol = lhs instanceof Sym ? lhs : rhs;
    const number = lhs instanceof Float ? lhs : rhs;
    if (symbol instanceof Sym && number instanceof Float) {
      const integer = number.isZero || number.mpf.exp >= 0n;
      if (symbol.assumptions0.get('rational') === false || symbol.assumptions.integer === false && integer) return op === 'Eq' ? S.false : S.true;
      if (symbol.assumptions.integer === true && integer) return new Rel(op, lhs, rhs);
    }
  }
  const decided = impl.relational?.(op, lhs, rhs);
  if (decided !== undefined) return decided;
  const byCmp = (c: number): Expr => ({ Eq: c === 0, Ne: c !== 0, Lt: c < 0, Le: c <= 0, Gt: c > 0, Ge: c >= 0 }[op] ? S.true : S.false);
  // a real (finite) value against oo or -oo (SymPy: a real symbol is finite)
  for (const [inf, other, sgn] of [[rhs, lhs, -1], [lhs, rhs, 1]] as const) {
    if (inf instanceof Special && (inf.name === 'oo' || inf.name === '-oo') && isFiniteReal(other)) {
      // the sign of lhs - rhs
      return byCmp((inf.name === 'oo' ? 1 : -1) * sgn);
    }
  }
  if (!equality && isNum(lhs) && isNum(rhs)) return byCmp(numCmp(lhs, rhs));
  if (!equality && (lhs instanceof Rational || rhs instanceof Rational)) {
    const reverse = lhs instanceof Rational;
    const numeric = reverse ? lhs : rhs;
    const bound = factorialLowerBound(reverse ? rhs : lhs);
    if (numeric instanceof Rational && bound !== undefined) {
      const compared = numCmp(bound, numeric);
      const test = reverse ? REVERSED[op] : op;
      if (compared > 0 || compared === 0 && (test === 'Ge' || test === 'Lt')) return test === 'Gt' || test === 'Ge' ? S.true : S.false;
    }
  }
  // equal sides (such as oo and oo, whose difference is nan)
  if (lhs.key === rhs.key) {
    if (equality || (lhs instanceof Sym ? lhs.assumptions0.get('extended_real') === true : isReal(lhs) === true)) return byCmp(0);
    return new Rel(op, lhs, rhs);
  }
  // SymPy compares bounded integer indices through the extrema of their ranges.
  if (!equality) {
    const interval = (e: Expr): readonly [Expr, Expr] => e instanceof Sym && 'lower' in e && 'upper' in e && e.lower instanceof Expr && e.upper instanceof Expr ? [e.lower, e.upper] : [e, e];
    const [lo, hi] = interval(lhs), [rlo, rhi] = interval(rhs);
    if (lo !== lhs || rlo !== rhs) {
      const lower = op === 'Lt' || op === 'Le';
      if (rel(op, lower ? hi : lo, lower ? rlo : rhi) === S.true) return S.true;
      if (rel(op, lower ? lo : hi, lower ? rhi : rlo) === S.false) return S.false;
    }
  }
  // a relation is not a number: Eq(Eq(F, G), C1) of the exact ODE solution stays unevaluated (SymPy)
  if (equality && (isBoolean(lhs) || isBoolean(rhs))) return new Rel(op, lhs, rhs);
  const d = add(lhs, mul(-1, rhs));
  if (d instanceof Rational) return byCmp(numCmp(d, S.Zero));
  if (d instanceof Float) return byCmp(numCmp(d, S.Zero));
  // the difference is oo or -oo for oo against a finite number (SymPy Lt(-oo, oo) is True)
  if (isSpecial('oo')(d) || isSpecial('-oo')(d)) return byCmp(isSpecial('oo')(d) ? 1 : -1);
  // zoo differs from every finite number and from oo (the difference is zoo or nan)
  if (equality && d instanceof Special) return op === 'Eq' ? S.false : S.true;
  // numeric expressions that are clearly different
  if (equality && d.freeSymbols().size === 0) {
    try {
      const v = d.toComplex();
      if ((v.im === 0 || !hasUnevaluatedComplexPower(d)) && Math.hypot(v.re, v.im) > 1e-9) return op === 'Eq' ? S.false : S.true;
    } catch {
      // not numerically evaluable
    }
    if (lhs.isNumber && rhs.isNumber) {
      for (const [real, other] of [[lhs, rhs], [rhs, lhs]] as const) {
        if (isReal(real) !== true || isReal(other) === true || hasUnevaluatedComplexPower(other)) continue;
        try {
          if (Math.abs(other.toComplex().im) > 1e-9) return op === 'Eq' ? S.false : S.true;
        } catch { /* The complex part is unknown. */ }
      }
    }
  }
  // SymPy is_eq: a difference whose is_zero is known decides the equality (Eq(a, 0) is False for a positive a)
  if (equality) {
    const z = isZero(d) ?? (isNonZero(d) === true ? false : undefined);
    if (z === true || (z === false && d.isCommutative)) return (op === 'Eq') === z ? S.true : S.false;
  }
  if (!equality) {
    const decided = orderTruth(op, d);
    if (decided !== undefined) return decided ? S.true : S.false;
    if ((lhs instanceof Float || rhs instanceof Float) && d.isComparable) {
      const numeric = impl.evalf(d, 15);
      if (isNum(numeric) && !numeric.isZero) return byCmp(numCmp(numeric, S.Zero));
    }
    if (d instanceof Add && isRadicalExpression(d) && impl.equalsZero?.(d)) return byCmp(0);
  }
  return new Rel(op, lhs, rhs);
}

/** Exact arithmetic expressions over rationals and their radicals. */
function isRadicalExpression(e: Expr): boolean {
  return e instanceof Rational || (e instanceof Add || e instanceof Mul || e instanceof Pow && e.exp instanceof Rational) && e.args.every(isRadicalExpression);
}

/** A branch-bearing power that has not been reduced to real and imaginary parts. */
function hasUnevaluatedComplexPower(e: Expr): boolean {
  return e instanceof Pow && e.base instanceof Add && knownNonreal(e.base)
    || e.args.some(hasUnevaluatedComplexPower);
}

/**
 * SymPy is_lt/is_le/is_gt/is_ge of lhs - rhs = d: decided by the sign the
 * assumptions give d (which evaluate real numbers numerically); undefined
 * when it cannot be decided.
 */
function orderTruth(op: 'Lt' | 'Le' | 'Gt' | 'Ge', d: Expr): boolean | undefined {
  const lower = op === 'Lt' || op === 'Le';
  // Lt and Le ask about -d > 0 and -d >= 0
  const v = lower ? mul(-1, d) : d;
  const strict = op === 'Lt' || op === 'Gt';
  if ((strict ? isPositive(v) : isNonNegative(v)) === true) return true;
  if ((strict ? isNonNegative(mul(-1, v)) : isNegative(v)) === true) return false;
  // a real value known not to be positive (a nonpositive symbol) is not > 0
  if (strict && isPositive(v) === false && isReal(v) === true) return false;
  return undefined;
}

/**
 * The equation `a = b`. It evaluates to `true` or `false` when the two sides
 * are known to be equal or different, and stays unevaluated otherwise.
 *
 * @param a - The left-hand side.
 * @param b - The right-hand side.
 * @returns The equation, or a Boolean.
 * @see SymPy `sympy.core.relational.Equality`
 * @example
 * ```ts
 * import { Eq, ex, simplify } from '@symjs/symjs';
 *
 * Eq(ex`y`, ex`x + x**2`); // => Eq(y, x**2 + x)
 * Eq(2, 5); // => False
 * simplify(Eq(ex`exp(x)`, ex`sinh(x) + cosh(x)`)); // => True
 * ```
 */
export const Eq = (a: ExprLike, b: ExprLike): Expr => rel('Eq', a, b);
/**
 * The relation `a != b`, the negation of {@link Eq}.
 *
 * @param a - The left-hand side.
 * @param b - The right-hand side.
 * @returns The relation, or a Boolean.
 * @see SymPy `sympy.core.relational.Unequality`
 * @example
 * ```ts
 * import { ex, Ne } from '@symjs/symjs';
 *
 * Ne(ex`y`, ex`x + x**2`); // => Ne(y, x**2 + x)
 * Ne(2, 5); // => True
 * ```
 */
export const Ne = (a: ExprLike, b: ExprLike): Expr => rel('Ne', a, b);
export const Lt = (a: ExprLike, b: ExprLike): Expr => rel('Lt', a, b);
export const Le = (a: ExprLike, b: ExprLike): Expr => rel('Le', a, b);
export const Gt = (a: ExprLike, b: ExprLike): Expr => rel('Gt', a, b);
export const Ge = (a: ExprLike, b: ExprLike): Expr => rel('Ge', a, b);

const relationHeads = { Eq, Ne, Lt, Le, Gt, Ge } as const;
registerHeadResolver(Rel, (e) => relationHeads[e.op]);

/** SymPy is_number: an expression without symbols (pi/2, sqrt(2)). */
const isNumber = (e: Expr): boolean => e.kind !== 'Set' && e.freeSymbols().size === 0;

const REVERSED: Record<RelOp, RelOp> = { Lt: 'Gt', Le: 'Ge', Gt: 'Lt', Ge: 'Le', Eq: 'Eq', Ne: 'Ne' };

/**
 * SymPy Relational.canonical: a number on the right, otherwise the sides in
 * default_sort_key order, and no minus sign that can be extracted on the
 * left (-x < y is y > -x).
 */
export function canonicalRelation(r: Rel): Expr {
  let [op, lhs, rhs] = [r.op, r.lhs instanceof Rel ? canonicalRelation(r.lhs) : r.lhs, r.rhs instanceof Rel ? canonicalRelation(r.rhs) : r.rhs];
  const reversed = (): void => {
    [op, lhs, rhs] = [REVERSED[op], rhs, lhs];
  };
  // (two numbers are compared by rel: an unevaluated relation has a side with symbols)
  if (!isNumber(rhs) && (isNumber(lhs) || compareKeys(sortKey(lhs), sortKey(rhs)) > 0)) reversed();
  if (couldExtractMinusSign(lhs)) return rel(REVERSED[op], mul(-1, lhs), mul(-1, rhs));
  // (SymPy also negates both sides when -rhs sorts before lhs; the sort key ignores the sign of the
  // coefficient, so with lhs sorted before rhs that cannot happen: Eq(x, -y) and Eq(-x, y) are Eq(x, -y))
  return rel(op, lhs, rhs);
}

/** SymPy _canonical_coeff: the canonical relation with the rational term and coefficient of the left side moved right (-2*x + 1 < 0 is x > 1/2). */
function canonicalCoeff(r0: Rel): Expr {
  const r = canonicalRelation(r0);
  if (!(r instanceof Rel) || isBoolean(r.lhs) || isBoolean(r.rhs)) return r;
  const terms = r.lhs instanceof Add ? r.lhs.args : [r.lhs];
  const b = terms.find((t): t is Rational => t instanceof Rational) ?? S.Zero;
  const l = add(r.lhs, mul(-1, b));
  const [m0, rest] = l instanceof Mul ? [at(l.args, 0), l] : [S.One, l];
  const m = m0 instanceof Rational ? m0 : S.One;
  const lhs = mul(rest, m.pow(-1));
  const rhs = mul(add(r.rhs, mul(-1, b)), m.pow(-1));
  // a negative coefficient left after the rational term is taken out reverses the relation
  // (Ne(1 - 1/(4*a), 0) is Ne(1/a, 4))
  return rel(m.isNegative ? REVERSED[r.op] : r.op, lhs, rhs);
}

const NEGATED: Record<RelOp, RelOp> = { Lt: 'Ge', Le: 'Gt', Gt: 'Le', Ge: 'Lt', Eq: 'Ne', Ne: 'Eq' };

/** The key of the canonical negation of a relation (SymPy c.negated.canonical). */
function negatedKey(r: Rel): string {
  return canonicalRelation(new Rel(NEGATED[r.op], r.lhs, r.rhs)).key;
}

/** The relations of a condition made canonical (SymPy Piecewise.eval: cond.replace(is_Relational, _canonical_coeff)). */
function canonicalCondition(c: Expr): Expr {
  if (c instanceof Rel) return canonicalCoeff(c);
  if (c instanceof BoolOp && (c.op === 'And' || c.op === 'Or')) {
    const args = c.args.map(canonicalCondition);
    return args.every((a, i) => a.key === at(c.args, i).key) ? c : c.op === 'And' ? and(...args) : or(...args);
  }
  return c;
}

const isTrue = (c: Expr) => c instanceof BoolAtom && c.value;
const isFalse = (c: Expr) => c instanceof BoolAtom && !c.value;

/**
 * Piecewise((e1, c1), (e2, c2), ...). Pairs with a False condition are dropped,
 * pairs after a True condition are unreachable, and Piecewise((e, True)) is e.
 */
type PiecewisePair = readonly [ExprLike, ExprLike | boolean];
type PiecewiseOptions = { evaluate?: boolean };
const isPiecewisePair = (value: PiecewisePair | PiecewiseOptions): value is PiecewisePair => Array.isArray(value);

export function piecewise(...args: (PiecewisePair | PiecewiseOptions)[]): Expr {
  const last = args.at(-1);
  const evaluate = last === undefined || isPiecewisePair(last) || last.evaluate !== false;
  const out: Expr[] = [];
  const seen = new Set<string>();
  for (const pair of args.filter(isPiecewisePair)) {
    const [e, c0] = pair;
    let c = typeof c0 === 'boolean' ? (c0 ? S.true : S.false) : sympify(c0);
    if (c instanceof Rational && (c.isOne || c.isZero)) c = c.isOne ? S.true : S.false;
    if (c instanceof Rel && c.args.some((operand) => operand instanceof Piecewise)) {
      c = impl.piecewiseFold?.(c) ?? c;
    }
    // a boolean Piecewise as a condition is the if-then-else ITE(c1, a, b) (SymPy rewrite(ITE))
    if (c instanceof Piecewise && c.args.length === 4 && isTrue(at(c.args, 3)) && isBoolean(at(c.args, 0)) && isBoolean(at(c.args, 2))) {
      // the relations are canonical (a number on the right: 2 < y -> y > 2)
      const flip: Record<RelOp, RelOp> = { Lt: 'Gt', Le: 'Ge', Gt: 'Lt', Ge: 'Le', Eq: 'Eq', Ne: 'Ne' };
      const canon = (r: Expr): Expr => (r instanceof Rel && isNum(r.lhs) && !isNum(r.rhs) ? new Rel(flip[r.op], r.rhs, r.lhs) : r);
      c = new BoolOp('ITE', [canon(at(c.args, 1)), canon(at(c.args, 0)), canon(at(c.args, 2))]);
    }
    if (!(isBoolean(c) || c instanceof Sym || c instanceof ExtensionExpr)) {
      throw new TypeError('Piecewise condition must be Boolean');
    }
    if (!evaluate) {
      if (!isFalse(c)) out.push(sympify(e), c);
      if (isTrue(c)) break;
      continue;
    }
    c = canonicalCondition(c);
    // SymPy _piecewise_collapse_arguments: repeated and redundant conditions
    const parts = c instanceof BoolOp && c.op === 'And' ? [c, ...c.args] : [c];
    if (parts.some((p) => seen.has(p.key))) continue;
    if (c instanceof BoolOp && c.op === 'And') {
      const kept: Expr[] = [];
      let none = false;
      for (const a of c.args) {
        if (a instanceof Rel) {
          if (seen.has(negatedKey(a))) continue;
          // a strict inequality after the non-strict one cannot hold
          if ((a.op === 'Lt' || a.op === 'Gt') && seen.has(rel(a.op === 'Lt' ? 'Le' : 'Ge', a.lhs, a.rhs).key)) none = true;
        }
        kept.push(a);
      }
      c = none ? S.false : and(...kept);
    } else if (c instanceof Rel && seen.has(negatedKey(c))) c = S.true;
    if (isFalse(c)) continue;
    let ex = sympify(e);
    if (ex instanceof Piecewise) {
      const inner = ex.pairs;
      const firstReachable = inner.findIndex(([, test]) => !seen.has(test.key));
      if (firstReachable < 0) ex = S.NaN;
      else if (firstReachable > 0) ex = piecewise(...inner.slice(firstReachable));
    }
    seen.add(c.key);
    if (out.length && at(out, -2).key === ex.key) {
      // successive pairs with the same expression: one pair with the conditions or-ed
      out[out.length - 1] = or(c, at(out, -1));
    } else if (out.length && at(out, -1).key === c.key) continue;
    else out.push(ex, c);
    if (isTrue(at(out, -1))) break;
  }
  // SymPy: no condition can hold, so the value is undefined (nan)
  if (out.length === 0) return S.NaN;
  if (out.length === 2 && isTrue(at(out, 1))) return at(out, 0);
  return new Piecewise(out);
}

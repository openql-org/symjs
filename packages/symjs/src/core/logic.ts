// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Relations, boolean constants and Piecewise.
 */

import { Special } from './nodes';
import type { Expr, ExprLike, RelOp } from './nodes';
import { Add, BoolAtom, Float, Mul, Piecewise, Pow, Rational, Rel, S, isNum } from './nodes';
import { numCmp } from './num';
import { add, couldExtractMinusSign, mul, sympify } from './ops';
import { BoolOp, and, or } from './boolalg';
import { compareKeys, sortKey } from '../printing/sortkey';
import { at, cast } from './guard';
import { isNegative, isNonNegative, isNonZero, isPositive, isReal, isZero } from './assumptions';

const isBoolean = (e: Expr): boolean => e instanceof Rel || e instanceof BoolAtom || e instanceof BoolOp;
const isSpecial = (name: string) => (x: Expr): boolean => x instanceof Special && x.name === name;

/** A real value that is finite: a real polynomial in real symbols (a real symbol is finite in SymPy; 1/x may be infinite). */
function isFiniteReal(e: Expr): boolean {
  const finite = (x: Expr): boolean =>
    !(x instanceof Special) && !(x instanceof Pow && !(x.exp instanceof Rational && x.exp.isInteger && !x.exp.isNegative)) && x.args.every(finite);
  return finite(e) && isReal(e) === true;
}

/** Create a relation, evaluating it to True/False when the difference is a number. */
export function rel(op: RelOp, a: ExprLike, b: ExprLike): Expr {
  const lhs = sympify(a);
  const rhs = sympify(b);
  const equality = op === 'Eq' || op === 'Ne';
  // nan is not equal to anything (SymPy Eq(nan, nan) is False) and cannot be ordered
  if ([lhs, rhs].some(isSpecial('nan'))) {
    if (!equality) throw new TypeError('Invalid NaN comparison');
    return op === 'Eq' ? S.false : S.true;
  }
  if (!equality && [lhs, rhs].some(isSpecial('zoo'))) throw new TypeError('Invalid comparison of non-real zoo');
  const byCmp = (c: number): Expr => ({ Eq: c === 0, Ne: c !== 0, Lt: c < 0, Le: c <= 0, Gt: c > 0, Ge: c >= 0 }[op] ? S.true : S.false);
  // a real (finite) value against oo or -oo (SymPy: a real symbol is finite)
  for (const [inf, other, sgn] of [[rhs, lhs, -1], [lhs, rhs, 1]] as const) {
    if (inf instanceof Special && (inf.name === 'oo' || inf.name === '-oo') && isFiniteReal(other)) {
      // the sign of lhs - rhs
      return byCmp((inf.name === 'oo' ? 1 : -1) * sgn);
    }
  }
  // equal sides (such as oo and oo, whose difference is nan)
  if (lhs.key === rhs.key) return byCmp(0);
  const d = add(lhs, mul(-1, rhs));
  if (d instanceof Rational) return byCmp(numCmp(d, S.Zero));
  if (d instanceof Float) return byCmp(Math.sign(d.value));
  // the difference is oo or -oo for oo against a finite number (SymPy Lt(-oo, oo) is True)
  if (isSpecial('oo')(d) || isSpecial('-oo')(d)) return byCmp(isSpecial('oo')(d) ? 1 : -1);
  // zoo differs from every finite number and from oo (the difference is zoo or nan)
  if (equality && d instanceof Special) return op === 'Eq' ? S.false : S.true;
  // numeric expressions that are clearly different
  if (equality && d.freeSymbols().size === 0) {
    try {
      const v = d.toComplex();
      if (Math.hypot(v.re, v.im) > 1e-9) return op === 'Eq' ? S.false : S.true;
    } catch {
      // not numerically evaluable
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
  }
  return new Rel(op, lhs, rhs);
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

export const Eq = (a: ExprLike, b: ExprLike): Expr => rel('Eq', a, b);
export const Ne = (a: ExprLike, b: ExprLike): Expr => rel('Ne', a, b);
export const Lt = (a: ExprLike, b: ExprLike): Expr => rel('Lt', a, b);
export const Le = (a: ExprLike, b: ExprLike): Expr => rel('Le', a, b);
export const Gt = (a: ExprLike, b: ExprLike): Expr => rel('Gt', a, b);
export const Ge = (a: ExprLike, b: ExprLike): Expr => rel('Ge', a, b);

/** SymPy is_number: an expression without symbols (pi/2, sqrt(2)). */
const isNumber = (e: Expr): boolean => e.freeSymbols().size === 0;

const REVERSED: Record<RelOp, RelOp> = { Lt: 'Gt', Le: 'Ge', Gt: 'Lt', Ge: 'Le', Eq: 'Eq', Ne: 'Ne' };

/**
 * SymPy Relational.canonical: a number on the right, otherwise the sides in
 * default_sort_key order, and no minus sign that can be extracted on the
 * left (-x < y is y > -x).
 */
export function canonicalRelation(r: Rel): Expr {
  let [op, lhs, rhs] = [r.op, r.lhs, r.rhs];
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
  // reordering or negating the sides keeps a relation undecided
  const r = cast(canonicalRelation(r0), Rel, 'canonical relation');
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
  return canonicalRelation(cast(rel(NEGATED[r.op], r.lhs, r.rhs), Rel, 'negated relation')).key;
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
export function piecewise(...pairs: readonly (readonly [ExprLike, ExprLike | boolean])[]): Expr {
  const out: Expr[] = [];
  const seen = new Set<string>();
  for (const [e, c0] of pairs) {
    let c = typeof c0 === 'boolean' ? (c0 ? S.true : S.false) : sympify(c0);
    // a boolean Piecewise as a condition is the if-then-else ITE(c1, a, b) (SymPy rewrite(ITE))
    if (c instanceof Piecewise && c.args.length === 4 && isTrue(at(c.args, 3)) && isBoolean(at(c.args, 0)) && isBoolean(at(c.args, 2))) {
      // the relations are canonical (a number on the right: 2 < y -> y > 2)
      const flip: Record<RelOp, RelOp> = { Lt: 'Gt', Le: 'Ge', Gt: 'Lt', Ge: 'Le', Eq: 'Eq', Ne: 'Ne' };
      const canon = (r: Expr): Expr => (r instanceof Rel && isNum(r.lhs) && !isNum(r.rhs) ? new Rel(flip[r.op], r.rhs, r.lhs) : r);
      c = new BoolOp('ITE', [canon(at(c.args, 1)), canon(at(c.args, 0)), canon(at(c.args, 2))]);
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
    seen.add(c.key);
    if (isFalse(c)) continue;
    const ex = sympify(e);
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

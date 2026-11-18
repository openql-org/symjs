// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/** SymPy relational predicates: three-valued comparisons under assumptions. */
import type { Expr, ExprLike, RelOp } from './nodes';
import { Add, BoolAtom, Mul, Rational, Rel, S, Sym, impl } from './nodes';
import { add, mul, pow, splitCoeff, sympify } from './ops';
import { BasicNode } from './basic';
import { canonicalRelation, rel } from './logic';
import type { Assumption } from './refine';
import { ask, Q } from './refine';
import type { Truth } from './truth';
import { truthNot } from './truth';
import { isPositive } from './assumptions';
import { isPolynomial } from './methods';
import { gcd, lcm } from './numbers';
import { first } from './guard';
import { compareKeys, sortKey } from '../printing/sortkey';

/** SymPy Relational(lhs, rhs, rop). */
export function Relational(lhs: ExprLike, rhs: ExprLike, rop = '==', options: { evaluate?: boolean } = {}): Expr {
  const construct = (op: RelOp): Expr => options.evaluate === false ? new Rel(op, sympify(lhs), sympify(rhs)) : rel(op, lhs, rhs);
  switch (rop) {
    case '==': case 'eq': return construct('Eq');
    case '!=': case '<>': case 'ne': return construct('Ne');
    case '>': case 'gt': return construct('Gt');
    case '<': case 'lt': return construct('Lt');
    case '>=': case 'ge': return construct('Ge');
    case '<=': case 'le': return construct('Le');
    default: throw new RangeError(`Invalid relational operator: ${rop}`);
  }
}

const REVERSED: Readonly<Record<RelOp, RelOp>> = { Eq: 'Eq', Ne: 'Ne', Lt: 'Gt', Le: 'Ge', Gt: 'Lt', Ge: 'Le' };
const NEGATED: Readonly<Record<RelOp, RelOp>> = { Eq: 'Ne', Ne: 'Eq', Lt: 'Ge', Le: 'Gt', Gt: 'Le', Ge: 'Lt' };

/** Exchange the sides and reverse the comparison, preserving unevaluated relations. */
export function reversed(relation: Rel): Rel {
  return new Rel(REVERSED[relation.op], relation.rhs, relation.lhs);
}

/** Negate both sides and reverse the comparison. Boolean sides retain their signs. */
export function reversedSign(relation: Rel): Rel {
  if (relation.lhs instanceof BoolAtom || relation.rhs instanceof BoolAtom) return relation;
  return new Rel(REVERSED[relation.op], mul(-1, relation.lhs), mul(-1, relation.rhs));
}

/** Complement a comparison without evaluating its sides. */
export function negated(relation: Rel): Rel {
  return new Rel(NEGATED[relation.op], relation.lhs, relation.rhs);
}

/** SymPy is_eq. */
export function isEq(lhs: ExprLike, rhs: ExprLike, assumptions: Assumption = true): Truth {
  const a = sympify(lhs), b = sympify(rhs);
  if (a.key !== b.key && ask(Q.infinite(a), assumptions) === true && ask(Q.infinite(b), assumptions) === true) {
    const realA = ask(Q.extended_real(a), assumptions), realB = ask(Q.extended_real(b), assumptions);
    if (realA !== 'unknown' && realB !== 'unknown' && realA !== realB) return false;
    if (realA === true && realB === true) {
      const positiveA = ask(Q.extended_positive(a), assumptions), positiveB = ask(Q.extended_positive(b), assumptions);
      if (positiveA !== 'unknown' && positiveB !== 'unknown') return positiveA === positiveB;
    }
  }
  return ask(Q.eq(a, b), assumptions);
}
/** SymPy is_neq. */
export const isNeq = (lhs: ExprLike, rhs: ExprLike, assumptions: Assumption = true): Truth => truthNot(isEq(lhs, rhs, assumptions));
/** SymPy is_ge. */
export const isGe = (lhs: ExprLike, rhs: ExprLike, assumptions: Assumption = true): Truth => {
  if ([lhs, rhs].some((e) => e instanceof BasicNode && e.name === 'Basic')) throw new TypeError('inequalities require expressions');
  return ask(Q.ge(lhs, rhs), assumptions);
};
/** SymPy is_le. */
export const isLe = (lhs: ExprLike, rhs: ExprLike, assumptions: Assumption = true): Truth => isGe(rhs, lhs, assumptions);
/** SymPy is_gt. */
export const isGt = (lhs: ExprLike, rhs: ExprLike, assumptions: Assumption = true): Truth => truthNot(isLe(lhs, rhs, assumptions));
/** SymPy is_lt. */
export const isLt = (lhs: ExprLike, rhs: ExprLike, assumptions: Assumption = true): Truth => truthNot(isGe(lhs, rhs, assumptions));

/** Simplify both sides and normalize a linear relation, as in Relational._eval_simplify. */
export function simplifyRelation(relation: Rel, simplify: (e: Expr) => Expr): Expr {
  const r = rel(relation.op, simplify(relation.lhs), simplify(relation.rhs));
  if (!(r instanceof Rel)) return r;
  const canonical = canonicalRelation(r);
  if (r.args.some((a) => a instanceof BoolAtom)) return canonical;
  let difference = add(r.lhs, mul(-1, r.rhs));
  if (difference instanceof Mul) {
    const factors = difference.args.filter((f) => !f.isNumber || isPositive(f) !== true);
    difference = mul(...factors);
  }
  difference = impl.expand(difference);
  if (difference instanceof Rational) return rel(r.op, difference, S.Zero);
  const terms = difference instanceof Add ? difference.args : [difference];
  let constant: Expr = S.Zero;
  const linear: [Rational, Sym][] = [];
  for (const term of terms) {
    if (term instanceof Rational) constant = add(constant, term);
    else {
      const [coefficient, symbol] = splitCoeff(term);
      if (!(coefficient instanceof Rational) || !(symbol instanceof Sym) || symbol.assumptions.real === false) return canonical;
      linear.push([coefficient, symbol]);
    }
  }
  linear.sort((a, b) => compareKeys(sortKey(a[1]), sortKey(b[1])));
  let numerator = 0n, denominator = 1n;
  for (const [c] of linear) {
    numerator = gcd(numerator, c.p);
    denominator = lcm(denominator, c.q);
  }
  const scale = Rational.of(numerator, denominator);
  const normalized = linear.map(([c, x]) => mul(c, pow(scale, -1), x));
  const rhs = mul(-1, constant, pow(scale, -1));
  const result = constant.key === S.Zero.key
    ? new Rel(r.op, first(normalized), mul(-1, add(...normalized.slice(1))))
    : new Rel(r.op, add(...normalized), rhs);
  return canonicalRelation(result);
}

/** Mathematical equality of relational sides, including reversed comparisons. */
export function relationalEquals(a: Rel, other: Expr, failingExpression = false): Truth | Expr {
  if (!(other instanceof Rel)) return 'unknown';
  if (a.key === other.key || a.key === reversed(other).key) return true;
  const equals = (x: Expr, y: Expr): Truth | Expr => {
    const d = impl.simplify(add(x, mul(-1, y)));
    return d.key === S.Zero.key ? true : d.isNumber || d.freeSymbols().size > 0 && isPolynomial(d) ? false : failingExpression ? d : 'unknown';
  };
  if (a.op === 'Eq' || a.op === 'Ne' || other.op === 'Eq' || other.op === 'Ne') {
    if (a.op !== other.op) return false;
    const left = equals(a.lhs, other.lhs), right = equals(a.rhs, other.rhs);
    if (left === true) return right;
    if (right === true) return left;
    const lr = equals(a.lhs, other.rhs), rl = equals(a.rhs, other.lhs);
    if (lr === true) return rl;
    if (rl === true) return lr;
    const results = [left, right, lr, rl];
    return results.find((v) => v !== false) ?? false;
  }
  const b = other.op === a.op ? other : reversed(other);
  if (a.op !== b.op) return false;
  const left = equals(a.lhs, b.lhs);
  if (left === false) return false;
  const right = equals(a.rhs, b.rhs);
  if (right === false) return false;
  return left === true ? right : left;
}

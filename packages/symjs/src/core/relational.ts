// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/** SymPy relational predicates: three-valued comparisons under assumptions. */
import type { Expr, ExprLike, RelOp } from './nodes';
import { BoolAtom, Rel } from './nodes';
import { mul, sympify } from './ops';
import { rel } from './logic';
import type { Assumption } from './refine';
import { ask, Q } from './refine';
import type { Truth } from './truth';
import { truthNot } from './truth';

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
export const isEq = (lhs: ExprLike, rhs: ExprLike, assumptions: Assumption = true): Truth => ask(Q.eq(lhs, rhs), assumptions);
/** SymPy is_neq. */
export const isNeq = (lhs: ExprLike, rhs: ExprLike, assumptions: Assumption = true): Truth => truthNot(isEq(lhs, rhs, assumptions));
/** SymPy is_ge. */
export const isGe = (lhs: ExprLike, rhs: ExprLike, assumptions: Assumption = true): Truth => ask(Q.ge(lhs, rhs), assumptions);
/** SymPy is_le. */
export const isLe = (lhs: ExprLike, rhs: ExprLike, assumptions: Assumption = true): Truth => isGe(rhs, lhs, assumptions);
/** SymPy is_gt. */
export const isGt = (lhs: ExprLike, rhs: ExprLike, assumptions: Assumption = true): Truth => truthNot(isLe(lhs, rhs, assumptions));
/** SymPy is_lt. */
export const isLt = (lhs: ExprLike, rhs: ExprLike, assumptions: Assumption = true): Truth => truthNot(isGe(lhs, rhs, assumptions));

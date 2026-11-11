// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/** SymPy relational predicates: three-valued comparisons under assumptions. */
import type { Expr, ExprLike } from './nodes';
import { rel } from './logic';
import type { Assumption } from './refine';
import { ask, Q } from './refine';
import type { Truth } from './truth';
import { truthNot } from './truth';

/** SymPy Relational(lhs, rhs, rop). */
export function Relational(lhs: ExprLike, rhs: ExprLike, rop = '=='): Expr {
  switch (rop) {
    case '==': case 'eq': return rel('Eq', lhs, rhs);
    case '!=': case '<>': case 'ne': return rel('Ne', lhs, rhs);
    case '>': case 'gt': return rel('Gt', lhs, rhs);
    case '<': case 'lt': return rel('Lt', lhs, rhs);
    case '>=': case 'ge': return rel('Ge', lhs, rhs);
    case '<=': case 'le': return rel('Le', lhs, rhs);
    default: throw new RangeError(`Invalid relational operator: ${rop}`);
  }
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

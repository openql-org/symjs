// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Assumptions for the linear real arithmetic solver (SymPy
 * sympy.assumptions.lra_satask): the predicates that the old assumptions of
 * the expressions give, and satisfiability queries in linear real arithmetic.
 *
 * Ported from SymPy 1.14 (BSD 3-Clause, see LICENSE).
 */

import { BoolAtom, Rational, Rel, S, Expr, type ExprLike } from '../core/nodes';
import { and, not, BoolOp } from '../core/boolalg';
import type { Truth } from '../core/truth';
import { at } from '../core/guard';
import { sympify } from '../core/ops';
import { freeSymbols } from '../core/traverse';
import { isIntegerQ, isNegative, isPositive, isReal, isZero } from '../core/assumptions';
import type { Assumption } from '../core/refine';
import { AppliedPredicate, globalAssumptions, registerPropositionHandler, Q } from '../core/refine';
import { UnhandledInput, combineLinear, linearForm, linearFeasible, type LinearConstraint } from '../logic/algorithms/lratheory';

/**
 * SymPy extract_pred_from_old_assum: the predicate (Q.zero, Q.positive,
 * Q.negative, Q.nonzero, Q.nonpositive or Q.nonnegative) that the old
 * assumptions of each non-constant expression give. Throws UnhandledInput
 * for an expression that is not known to be real, is an integer (other
 * than zero), cannot be an integer or is irrational.
 */
export function extractPredFromOldAssum(allExprs: Iterable<ExprLike>): AppliedPredicate[] {
  const ret: AppliedPredicate[] = [];
  for (const e of allExprs) {
    const expr = sympify(e);
    if (freeSymbols(expr).size === 0) continue;
    // SymPy also rejects a real product of a non-real factor (I times an imaginary variable) and an
    // irrational expression; the old assumptions of symjs report neither (such a product is not known to be
    // real, and an expression known to be irrational is not known to be real), so the checks are not repeated
    if (isReal(expr) !== true) throw new UnhandledInput(`LRASolver: ${String(expr)} must be real`);
    const integer = isIntegerQ(expr);
    if (integer === true && isZero(expr) !== true) throw new UnhandledInput(`LRASolver: ${String(expr)} is an integer`);
    if (integer === false) throw new UnhandledInput(`LRASolver: ${String(expr)} can't be an integer`);
    // expr is real: nonzero, nonpositive and nonnegative are the negations of zero, positive and negative
    const [zero, positive, negative] = [isZero(expr), isPositive(expr), isNegative(expr)];
    if (zero === true) ret.push(Q.zero(expr));
    else if (positive === true) ret.push(Q.positive(expr));
    else if (negative === true) ret.push(Q.negative(expr));
    else if (zero === false) ret.push(Q.nonzero(expr));
    else if (positive === false) ret.push(Q.nonpositive(expr));
    else if (negative === false) ret.push(Q.nonnegative(expr));
  }
  return ret;
}


const relationNames = { Eq: 'eq', Ne: 'ne', Lt: 'lt', Le: 'le', Gt: 'gt', Ge: 'ge' } as const;
const complement: Record<string, string> = { eq: 'ne', ne: 'eq', lt: 'ge', le: 'gt', gt: 'le', ge: 'lt' };
const signRelations: Record<string, string> = { positive: 'gt', negative: 'lt', nonpositive: 'le', nonnegative: 'ge', zero: 'eq', nonzero: 'ne', extended_positive: 'gt', extended_negative: 'lt', extended_nonpositive: 'le', extended_nonnegative: 'ge', extended_nonzero: 'ne' };

/** Translate the Boolean skeleton to conjunctions of theory constraints. */
function theoryBranches(e: Expr, negate = false): LinearConstraint[][] {
  if (e instanceof BoolAtom) return e.value !== negate ? [[]] : [];
  if (e instanceof BoolOp) {
    if (e.op === 'Not') return theoryBranches(at(e.args, 0), !negate);
    if (e.op !== 'And' && e.op !== 'Or') throw new UnhandledInput('Unsupported Boolean connective');
    const parts = e.args.map((arg) => theoryBranches(arg, negate));
    if ((e.op === 'And') === negate) return parts.flat();
    return parts.reduce<LinearConstraint[][]>((a, b) => a.flatMap((x) => b.map((y) => [...x, ...y])), [[]]);
  }
  let name: string, lhs: Expr, rhs: Expr;
  if (e instanceof Rel) {
    name = relationNames[e.op]; lhs = e.lhs; rhs = e.rhs;
  } else if (e instanceof AppliedPredicate) {
    name = e.predicate; lhs = e.arg; rhs = e.args[1] ?? S.Zero;
    if (['positive_infinite', 'negative_infinite', 'real', 'extended_real', 'finite'].includes(name)) linearForm(lhs);
    if (['positive_infinite', 'negative_infinite'].includes(name)) return negate ? [[]] : [];
    if (['real', 'extended_real', 'finite'].includes(name)) return negate ? [] : [[]];
    name = signRelations[name] ?? name;
  } else throw new UnhandledInput('Unsupported proposition');
  if (negate) name = complement[name] ?? '';
  if (!['eq', 'ne', 'lt', 'le', 'gt', 'ge'].includes(name)) throw new UnhandledInput('Unsupported predicate');
  const form = combineLinear(linearForm(lhs), linearForm(rhs), Rational.of(-1));
  const opposite = combineLinear(new Map(), form, Rational.of(-1));
  if (name === 'eq') return [[{ form, strict: false }, { form: opposite, strict: false }]];
  if (name === 'ne') return [[{ form, strict: true }], [{ form: opposite, strict: true }]];
  return [[{ form: name === 'gt' || name === 'ge' ? opposite : form, strict: name === 'gt' || name === 'lt' }]];
}

/** Decide a proposition by checking both polarities against the real theory. */
export function lraSatask(proposition: ExprLike | boolean, assumptions: Assumption = true): Truth {
  const prop = typeof proposition === 'boolean' ? (proposition ? S.true : S.false) : sympify(proposition);
  const assumed = typeof assumptions === 'boolean' ? (assumptions ? S.true : S.false) : assumptions instanceof Expr ? assumptions : and(...assumptions);
  const context = and(assumed, ...globalAssumptions);
  const symbols = new Set([...freeSymbols(prop), ...freeSymbols(context)]);
  const old = extractPredFromOldAssum(symbols);
  const base = and(context, ...old);
  const satisfiable = (e: Expr): boolean => theoryBranches(e).some(linearFeasible);
  if (!satisfiable(base)) throw new RangeError('inconsistent assumptions');
  const yes = satisfiable(and(base, prop));
  const no = satisfiable(and(base, not(prop)));
  return !yes ? false : !no ? true : 'unknown';
}

registerPropositionHandler((proposition, assumptions) => {
  try { return lraSatask(proposition, assumptions); }
  catch (error) {
    if (error instanceof UnhandledInput) return 'unknown';
    throw error;
  }
});

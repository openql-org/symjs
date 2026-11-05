// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Known facts between the unary predicates of the assumption system
 * (SymPy sympy.assumptions.facts): the decomposition of the composite
 * predicates, the facts between number and matrix predicates, and the
 * functions that derive the implied and rejected predicates of each
 * predicate (the contents of sympy.assumptions.ask_generated).
 *
 * Ported from SymPy 1.14 (BSD 3-Clause, see LICENSE).
 */

import type { Expr, ExprLike } from '../core/nodes';
import { Sym } from '../core/nodes';
import { BoolOp, and, not, or } from '../core/boolalg';
import { sympify } from '../core/ops';
import type { Predicate } from '../core/refine';
import { AppliedPredicate, Predicate as makePredicate, Q } from '../core/refine';
import type { Truth } from '../core/truth';
import { at } from '../core/guard';
import { ExprMap } from '../core/exprmap';
import { Equivalent, Exclusive, Implies } from '../logic/boolalg';
import { satisfiable } from '../logic/inference';
import { toCnf } from '../logic/minimize';

let composites: Map<Predicate, readonly Predicate[]> | undefined;

/**
 * The composite predicates and their decomposition into primitive
 * predicates, which keeps the SAT problems small (SymPy
 * get_composite_predicates). Each value lists the predicates whose
 * disjunction the key is (`Q.real: Q.negative | Q.zero | Q.positive`).
 */
export function getCompositePredicates(): Map<Predicate, readonly Predicate[]> {
  composites ??= new Map<Predicate, readonly Predicate[]>([
    [Q.real, [Q.negative, Q.zero, Q.positive]],
    [Q.integer, [Q.even, Q.odd]],
    [Q.nonpositive, [Q.negative, Q.zero]],
    [Q.nonzero, [Q.negative, Q.positive]],
    [Q.nonnegative, [Q.zero, Q.positive]],
    [Q.extended_real, [Q.negative_infinite, Q.negative, Q.zero, Q.positive, Q.positive_infinite]],
    [Q.extended_positive, [Q.positive, Q.positive_infinite]],
    [Q.extended_negative, [Q.negative, Q.negative_infinite]],
    [Q.extended_nonzero, [Q.negative_infinite, Q.negative, Q.positive, Q.positive_infinite]],
    [Q.extended_nonpositive, [Q.negative_infinite, Q.negative, Q.zero]],
    [Q.extended_nonnegative, [Q.zero, Q.positive, Q.positive_infinite]],
    [Q.complex, [Q.algebraic, Q.transcendental]],
  ]);
  return new Map(composites);
}

const placeholder = (x: ExprLike | undefined): Expr => (x === undefined ? new Sym('x') : sympify(x));

/** The facts between unary number and matrix predicates of x (default the symbol x) (SymPy get_known_facts). */
export function getKnownFacts(x?: ExprLike): Expr {
  const s = placeholder(x);
  return and(getNumberFacts(s), getMatrixFacts(s));
}

/** The facts between unary number predicates of x (default the symbol x) (SymPy get_number_facts). */
export function getNumberFacts(x?: ExprLike): Expr {
  const s = placeholder(x);
  return and(
    // primitive predicates for extended real exclude each other
    Exclusive(Q.negative_infinite(s), Q.negative(s), Q.zero(s), Q.positive(s), Q.positive_infinite(s)),
    // build complex plane
    Exclusive(Q.real(s), Q.imaginary(s)),
    Implies(or(Q.real(s), Q.imaginary(s)), Q.complex(s)),
    // other subsets of complex
    Exclusive(Q.transcendental(s), Q.algebraic(s)),
    Equivalent(Q.real(s), or(Q.rational(s), Q.irrational(s))),
    Exclusive(Q.irrational(s), Q.rational(s)),
    Implies(Q.rational(s), Q.algebraic(s)),
    // integers
    Exclusive(Q.even(s), Q.odd(s)),
    Implies(Q.integer(s), Q.rational(s)),
    Implies(Q.zero(s), Q.even(s)),
    Exclusive(Q.composite(s), Q.prime(s)),
    Implies(or(Q.composite(s), Q.prime(s)), and(Q.integer(s), Q.positive(s))),
    Implies(and(Q.even(s), Q.positive(s), not(Q.prime(s))), Q.composite(s)),
    // hermitian and antihermitian
    Implies(Q.real(s), Q.hermitian(s)),
    Implies(Q.imaginary(s), Q.antihermitian(s)),
    Implies(Q.zero(s), or(Q.hermitian(s), Q.antihermitian(s))),
    // define finity and infinity, and build extended real line
    Exclusive(Q.infinite(s), Q.finite(s)),
    Implies(Q.complex(s), Q.finite(s)),
    Implies(or(Q.negative_infinite(s), Q.positive_infinite(s)), Q.infinite(s)),
    // commutativity
    Implies(or(Q.finite(s), Q.infinite(s)), Q.commutative(s)),
  );
}

/** The facts between unary matrix predicates of x (default the symbol x) (SymPy get_matrix_facts). */
export function getMatrixFacts(x?: ExprLike): Expr {
  const s = placeholder(x);
  return and(
    Implies(Q.orthogonal(s), Q.positive_definite(s)),
    Implies(Q.orthogonal(s), Q.unitary(s)),
    Implies(and(Q.unitary(s), Q.real_elements(s)), Q.orthogonal(s)),
    Implies(Q.unitary(s), Q.normal(s)),
    Implies(Q.unitary(s), Q.invertible(s)),
    Implies(Q.normal(s), Q.square(s)),
    Implies(Q.diagonal(s), Q.normal(s)),
    Implies(Q.positive_definite(s), Q.invertible(s)),
    Implies(Q.diagonal(s), Q.upper_triangular(s)),
    Implies(Q.diagonal(s), Q.lower_triangular(s)),
    Implies(Q.lower_triangular(s), Q.triangular(s)),
    Implies(Q.upper_triangular(s), Q.triangular(s)),
    Implies(Q.triangular(s), or(Q.upper_triangular(s), Q.lower_triangular(s))),
    Implies(and(Q.upper_triangular(s), Q.lower_triangular(s)), Q.diagonal(s)),
    Implies(Q.diagonal(s), Q.symmetric(s)),
    Implies(Q.unit_triangular(s), Q.triangular(s)),
    Implies(Q.invertible(s), Q.fullrank(s)),
    Implies(Q.invertible(s), Q.square(s)),
    Implies(Q.symmetric(s), Q.square(s)),
    Implies(and(Q.fullrank(s), Q.square(s)), Q.invertible(s)),
    Equivalent(Q.invertible(s), not(Q.singular(s))),
    Implies(Q.integer_elements(s), Q.real_elements(s)),
    Implies(Q.real_elements(s), Q.complex_elements(s)),
  );
}

/** The predicate Q.<name> (a predicate not in Q is made anew). */
export const predicateNamed = (name: string): Predicate => Q[name] ?? makePredicate(name);

/** The implied and rejected predicates of each predicate (the values of generate_known_facts_dict). */
export type KnownFactsDict = Map<Predicate, [Set<Predicate>, Set<Predicate>]>;

/**
 * The predicates implied and rejected by each unary predicate (SymPy
 * generate_known_facts_dict). The keys are applied predicates with the same
 * placeholder symbol; fact is a fact between them.
 */
export function generateKnownFactsDict(keys: readonly Expr[], fact: ExprLike | boolean): KnownFactsDict {
  const factCnf = toCnf(fact);
  const mapping = singleFactLookup(keys, factCnf);
  const ret: KnownFactsDict = new Map();
  for (const [key, value] of mapping) {
    const implied = new Set<Predicate>();
    const rejected = new Set<Predicate>();
    for (const e of value) {
      if (e instanceof AppliedPredicate) implied.add(predicateNamed(e.predicate));
      const negated = e instanceof BoolOp && e.op === 'Not' ? at(e.args, 0) : undefined;
      if (negated instanceof AppliedPredicate) rejected.add(predicateNamed(negated.predicate));
    }
    if (key instanceof AppliedPredicate) ret.set(predicateNamed(key.predicate), [implied, rejected]);
  }
  return ret;
}

/** Every unary predicate of Q: all but eq, ne, gt, lt, ge and le (SymPy get_known_facts_keys). */
export function getKnownFactsKeys(): Predicate[] {
  const exclude = new Set(['eq', 'ne', 'gt', 'lt', 'ge', 'le']);
  return Object.keys(Q)
    .filter((n) => !exclude.has(n))
    .map(predicateNamed);
}

/**
 * For each key, the keys and negated keys that it implies under the known
 * facts (SymPy single_fact_lookup).
 */
export function singleFactLookup(knownFactsKeys: readonly Expr[], knownFactsCnf: ExprLike | boolean): ExprMap<Expr[]> {
  const mapping = new ExprMap<Expr[]>();
  for (const key of knownFactsKeys) {
    const implied = [key];
    for (const other of knownFactsKeys) {
      if (other.key === key.key) continue;
      if (askFullInference(other, key, knownFactsCnf) === true) implied.push(other);
      if (askFullInference(not(other), key, knownFactsCnf) === true) implied.push(not(other));
    }
    mapping.set(key, implied);
  }
  return mapping;
}

/**
 * Whether the proposition holds under the assumptions and the known facts:
 * true, false or 'unknown' (SymPy ask_full_inference).
 */
export function askFullInference(proposition: ExprLike | boolean, assumptions: ExprLike | boolean, knownFactsCnf: ExprLike | boolean): Truth {
  if (satisfiable(and(knownFactsCnf, assumptions, proposition)) === false) return false;
  if (satisfiable(and(knownFactsCnf, assumptions, not(proposition))) === false) return true;
  return 'unknown';
}

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/core/assumptions.py: assumptions, common_assumptions,
// failing_assumptions, check_assumptions), Copyright (c) 2006-2023 SymPy Development Team,
// BSD 3-Clause License.

/**
 * @file The assumption facts of an expression as a whole (SymPy
 * `assumptions(expr)`, the values of its `is_<fact>` properties) and the
 * functions that compare them: `checkAssumptions`, `failingAssumptions` and
 * `commonAssumptions`.
 *
 * The facts of a symbol are the closure of the assumptions it was created
 * with. The facts of another expression are what `ask` decides for each
 * predicate, with the rules of SymPy's old assumptions that `ask` does not
 * apply (a sum with exactly one term that is not extended real is not
 * extended real; `exp` of an imaginary number is real only when it is
 * ±1), closed under the implications between the facts.
 */

import type { ExprLike } from './nodes';
import { Add, Constant, Expr, Pow, S, Sym } from './nodes';
import { mul, pow, sympify } from './ops';
import { deduceAllFacts } from './facts';
import { isPolar } from './assumptions';
import { Q, ask } from './refine';
import type { FuzzyLike, Truth } from './truth';

/** The assumption facts of SymPy (`_assume_defined`), in alphabetical order. */
export const ASSUMPTION_NAMES = [
  'algebraic', 'antihermitian', 'commutative', 'complex', 'composite', 'even', 'extended_negative', 'extended_nonnegative',
  'extended_nonpositive', 'extended_nonzero', 'extended_positive', 'extended_real', 'finite', 'hermitian', 'imaginary', 'infinite',
  'integer', 'irrational', 'negative', 'noninteger', 'nonnegative', 'nonpositive', 'nonzero', 'odd', 'polar', 'positive', 'prime',
  'rational', 'real', 'transcendental', 'zero',
] as const;

/** The name of an assumption fact (`'positive'`, `'integer'`, `'extended_real'`, ...). */
export type AssumptionName = (typeof ASSUMPTION_NAMES)[number];

/** Desired values of assumption facts (SymPy's keyword arguments `positive=True, ...`); null or 'unknown' stands for None. */
export type AssumptionValues = Readonly<Partial<Record<string, FuzzyLike>>>;

const isName = (k: string): k is AssumptionName => (ASSUMPTION_NAMES as readonly string[]).includes(k);

/** The given facts closed under their implications (the facts themselves if they contradict each other). */
function closure(given: Readonly<Record<string, boolean>>): Map<string, boolean> {
  try {
    return deduceAllFacts(given);
  } catch {
    // the deciders disagree on an expression; keep what they found
    return new Map(Object.entries(given));
  }
}

/**
 * SymPy `_fuzzy_group(args, quick_exit=True)`: true when all are true,
 * false when exactly one is false and the others true, otherwise unknown.
 */
function fuzzyGroup(vs: readonly (boolean | undefined)[]): boolean | undefined {
  let other = false;
  for (const v of vs) {
    if (v === true) continue;
    if (v === undefined || other) return undefined;
    other = true;
  }
  return !other;
}

const facts = new WeakMap<Expr, Map<string, boolean>>();

/** The known facts of an expression (the values of its `is_<fact>` that are not None). */
function factsOf(e: Expr): Map<string, boolean> {
  const cached = facts.get(e);
  if (cached) return cached;
  let rv: Map<string, boolean>;
  if (e instanceof Sym) {
    const given = Object.entries({ ...e.assumptions, commutative: e.assumptions.commutative !== false }).filter((kv): kv is [string, boolean] => typeof kv[1] === 'boolean');
    rv = closure(Object.fromEntries(given));
  } else {
    const given: Record<string, boolean> = {};
    for (const k of ASSUMPTION_NAMES) {
      const p = Q[k];
      const v: Truth = p === undefined ? (isPolar(e) ? true : 'unknown') : ask(p(e));
      if (v !== 'unknown') given[k] = v;
    }
    // SymPy Add._eval_is_extended_real: exactly one term that is not extended real makes the sum not extended real
    if (given['extended_real'] === undefined && e instanceof Add) {
      const r = fuzzyGroup(e.args.map((a) => factsOf(a).get('extended_real')));
      if (r !== undefined) given['extended_real'] = r;
    }
    // SymPy exp._eval_is_extended_real: exp(a) for an imaginary a is real when a/(I*pi) is an integer, -2*a/(I*pi) even
    if (given['extended_real'] === undefined && e instanceof Pow && e.base instanceof Constant && e.base.name === 'E' && factsOf(e.exp).get('imaginary') === true) {
      const even = ask(Q.even(mul(-2, S.I, e.exp, pow(S.Pi, -1))));
      if (even !== 'unknown') given['extended_real'] = even;
    }
    rv = closure(given);
  }
  facts.set(e, rv);
  return rv;
}

/** The value of one fact of an expression (`expr.is_<name>`); 'unknown' for SymPy's None and for a name that is not a fact. */
function factOf(e: Expr, name: string): Truth {
  return factsOf(e).get(name) ?? 'unknown';
}

const fuzzy = (v: FuzzyLike): Truth => v ?? 'unknown';

/**
 * SymPy `assumptions(expr)`: the facts of an expression that are known, as
 * a map from the fact name to its value. For a symbol these are the closure
 * of the assumptions it was created with.
 *
 * `assumptions(x + I)` for a positive x is `{finite: true, complex: true,
 * real: false, zero: false, ...}`.
 */
export function assumptions(expr: ExprLike): Map<AssumptionName, boolean> {
  const f = factsOf(sympify(expr));
  return new Map(ASSUMPTION_NAMES.flatMap((k): [AssumptionName, boolean][] => {
    const v = f.get(k);
    return v === undefined ? [] : [[k, v]];
  }));
}

/**
 * SymPy `common_assumptions(exprs, check=None)`: the facts known with the
 * same value for all the expressions (only the facts named in `check`, when
 * it is given).
 */
export function commonAssumptions(exprs: Iterable<ExprLike>, check?: Iterable<string>): Map<AssumptionName, boolean> {
  const names = check === undefined ? ASSUMPTION_NAMES : ASSUMPTION_NAMES.filter((k) => new Set(check).has(k));
  const all = [...exprs].map((x) => assumptions(x));
  const rv = new Map<AssumptionName, boolean>();
  const [first, ...rest] = all;
  if (first === undefined) return rv;
  for (const k of names) {
    const v = first.get(k);
    if (v !== undefined && rest.every((m) => m.get(k) === v)) rv.set(k, v);
  }
  return rv;
}

/**
 * SymPy `failing_assumptions(expr, **assumptions)`: the facts whose value
 * differs from the desired one, with the value the expression has
 * ('unknown' when it is not known). An empty map when all hold.
 *
 * `failingAssumptions(x**2 - 1, { positive: true })` is `{positive: 'unknown'}`.
 */
export function failingAssumptions(expr: ExprLike, desired: AssumptionValues): Map<string, Truth> {
  const e = sympify(expr);
  const failed = new Map<string, Truth>();
  for (const [k, want] of Object.entries(desired)) {
    const test = factOf(e, k);
    if (test !== fuzzy(want)) failed.set(k, test);
  }
  return failed;
}

/**
 * SymPy `check_assumptions(expr, against=None, **assume)`: whether the
 * facts of the expression agree with the desired values (`{ positive: true,
 * ... }`) or with the facts of another expression `against` (such as the
 * symbol the expression replaces). False when a fact contradicts, 'unknown'
 * when one is not known, otherwise true. Desired values that are null or
 * 'unknown' are ignored.
 */
export function checkAssumptions(expr: ExprLike, against: ExprLike | AssumptionValues = {}): Truth {
  const e = sympify(expr);
  const assume: AssumptionValues = typeof against === 'object' && !(against instanceof Expr) ? against : Object.fromEntries(assumptions(against));
  let known: Truth = true;
  for (const [k, v] of Object.entries(assume)) {
    const want = fuzzy(v);
    if (want === 'unknown') continue;
    const test = isName(k) ? factOf(e, k) : 'unknown';
    if (test === 'unknown') known = 'unknown';
    else if (test !== want) return false;
  }
  return known;
}


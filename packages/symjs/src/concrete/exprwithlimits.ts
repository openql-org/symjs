// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 concrete/expr_with_limits.py (BSD-3-Clause).

import { Concrete, concreteHooks } from '../core/concrete';
import { Integral, S, type Expr } from '../core/nodes';
import { first } from '../core/guard';
import { add, mul, pow, sub } from '../core/ops';
import { xreplace } from '../core/traverse';
import { Interval, Range, inf, sup } from '../sets/sets';
import { abs, fn } from '../functions/elementary/elementary';
import { NotImplementedError } from '../core/errors';
import { ask, Q, registerHandler } from '../core/refine';
import { fact } from '../core/exprfacts';
import { ASSUMPTION_NAMES } from '../core/checkassumptions';
import { deduceAllFacts } from '../core/facts';
import type { Truth } from '../core/truth';
import { truthAnd, truthOr } from '../core/truth';

/** SymPy _process_limits for discrete set limits, with its change of variable. */
concreteHooks.processLimit = (f, k, domain) => {
  if (domain instanceof Interval) throw new TypeError('Use Range for a discrete limit');
  if (!(domain instanceof Range)) throw new NotImplementedError('Expecting a Range limit');
  const lo = inf(domain), hi = sup(domain), step = abs(domain.step);
  if (step.key === S.One.key) return [f, lo, hi];
  const fromLeft = lo.key !== S.NegativeInfinity.key;
  const replacement = fromLeft ? add(mul(step, k), lo) : sub(hi, mul(step, k));
  const upper = fromLeft ? fn('floor', [mul(sub(hi, lo), pow(step, -1))]) : S.Infinity;
  return [xreplace(f, [[k, replacement]]), S.Zero, upper];
};

/** Limits in the order used by SymPy (innermost first). */
function limits(e: Concrete | Integral): (readonly Expr[])[] {
  if (e instanceof Concrete) return e.limits;
  return [...(e.integrand instanceof Integral ? limits(e.integrand) : []), e.args.slice(1)];
}

/** Variables of a sum, product or integral, including indefinite variables. */
export function variables(e: Concrete | Integral): Expr[] {
  return limits(e).flatMap((l) => l.slice(0, 1));
}

/** Whether every limit is finite, using assumptions on the bounds and variables. */
export function hasFiniteLimits(e: Concrete | Integral): Truth {
  return truthAnd(...limits(e).map((l): Truth => {
    const variableFinite = ask(Q.finite(first(l)));
    if (l.length !== 3) return variableFinite;
    const bounds = truthAnd(...l.slice(1).map((b) => ask(Q.finite(b))));
    return bounds === 'unknown' ? variableFinite : bounds;
  }));
}

/** Whether any definite limit runs from a larger lower bound to a smaller upper bound. */
export function hasReversedLimits(e: Concrete | Integral): Truth {
  return truthOr(...limits(e).map((l): Truth => {
    const a = l[1], b = l[2];
    if (a === undefined || b === undefined) return 'unknown';
    const d = sub(b, a);
    if (ask(Q.extended_negative(d)) === true) return true;
    return ask(Q.extended_nonnegative(d)) === true ? false : 'unknown';
  }));
}

/** SymPy Sum/Product _eval_is_* handlers, closed under the assumption rules. */
function concreteFacts(e: Concrete): Map<string, boolean> {
  const given: Record<string, boolean> = {};
  const empty = e.hasEmptySequence === true;
  if (empty) return deduceAllFacts({ [e.kind2 === 'Sum' ? 'zero' : 'positive']: true, finite: true });
  const finite = hasFiniteLimits(e) === true;
  const term = (name: string) => fact(e.function, name);
  const real = term('extended_real');
  if (real !== undefined) given['extended_real'] = real;
  if (finite && term('finite') === true) given['finite'] = true;
  const zero = term('zero');
  if (zero === true) given['zero'] = true;
  if (e.kind2 === 'Sum') {
    if (finite && hasReversedLimits(e) === false) {
      for (const name of ['positive', 'negative']) {
        const value = term(name);
        if (value !== undefined) given[name] = value;
      }
    }
  } else {
    if (finite && zero !== undefined) given['zero'] = zero;
    if (term('extended_nonnegative') === true) given['extended_nonnegative'] = true;
    if (finite) {
      if (term('positive') === true) given['positive'] = true;
      if (term('nonnegative') === true) given['nonnegative'] = true;
    }
  }
  return deduceAllFacts(given);
}

for (const name of ASSUMPTION_NAMES) {
  if (name === 'polar') continue;
  registerHandler(name, (e) => e instanceof Concrete ? concreteFacts(e).get(name) ?? 'unknown' : 'unknown');
}

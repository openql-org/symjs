// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file simplify(): try several strategies and keep the simplest result.
 */

import { Add, Expr, ExprLike, Fn, Mul, Pow, Rational, impl } from '../core/nodes';
import { splitCoeff, sympify } from '../core/ops';
import { countOps, mapBottomUp, some } from '../core/traverse';
import { fn } from '../functions/elementary';
import { expandMul as expand } from './expand';
import { powsimp } from './powsimp';
import { factorTerms } from './exprtools';
import { radsimp } from './radsimp';
import { cancel } from './rational';
import { exptotrig, expsimp, hasTrig, trigsimp } from './trigsimp';

const hasDenominator = (e: Expr): boolean =>
  some(e, (x) => x instanceof Pow && splitCoeff(x.exp)[0].isNegative && !x.base.isNumber);

/** A sum with a non-integer rational term, e.g. x - 3/2 (SymPy clears such denominators). */
function hasRationalCoeffInsideSum(e: Expr): boolean {
  if (e instanceof Add && e.args.some((a) => (a instanceof Rational && !a.isInteger) || (a instanceof Mul && a.args[0] instanceof Rational && !(a.args[0] as Rational).isInteger))) return true;
  return e.args.some(hasRationalCoeffInsideSum);
}

function simplifyCore(e: Expr): Expr {
  if (e.isAtom) return e;
  const candidates: Expr[] = [e];
  const tryPush = (f: () => Expr) => {
    try {
      candidates.push(f());
    } catch {
      // a failing strategy is simply skipped
    }
  };
  tryPush(() => expand(e));
  tryPush(() => powsimp(e));
  tryPush(() => factorTerms(e));
  if (hasTrig(e)) {
    tryPush(() => exptotrig(e));
    tryPush(() => expsimp(e));
  }
  tryPush(() => expand(radsimp(e)));
  if (hasDenominator(e)) {
    tryPush(() => cancel(e));
    if (hasTrig(e)) tryPush(() => cancel(exptotrig(e)));
  }
  let best = candidates[0]!;
  let bestCost = countOps(best);
  for (const c of candidates.slice(1)) {
    const cost = countOps(c);
    if (cost < bestCost) {
      best = c;
      bestCost = cost;
    }
  }
  // SymPy's pipeline ends in factor_terms(cancel(...)) and keeps it unless it is longer
  if (hasDenominator(e) && !(best instanceof Add)) {
    try {
      const ft = factorTerms(cancel(e));
      if (countOps(ft) <= bestCost && hasRationalCoeffInsideSum(best) && !hasRationalCoeffInsideSum(ft)) best = ft;
    } catch {
      // keep best
    }
  }
  return hasTrig(best) ? trigsimp(best) : best;
}

/**
 * Simplify an expression using a combination of expansion, trigonometric /
 * exponential rewriting and rational-function cancellation. The candidate
 * with the fewest nodes wins.
 */
export function simplify(ex: ExprLike): Expr {
  const e = mapBottomUp(sympify(ex), (x) =>
    x instanceof Fn ? fn(x.name, x.args.map(simplifyCore)) : x,
  );
  return simplifyCore(e);
}

impl.simplify = simplify;

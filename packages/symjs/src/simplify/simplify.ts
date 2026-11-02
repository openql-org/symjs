// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file simplify(): try several strategies and keep the simplest result.
 */

import { Expr, ExprLike, Fn, Pow, impl } from '../core/nodes';
import { splitCoeff, sympify } from '../core/ops';
import { countOps, mapBottomUp, some } from '../core/traverse';
import { fn } from '../functions/elementary';
import { expandMul as expand } from './expand';
import { powsimp } from './powsimp';
import { factorTerms } from './exprtools';
import { radsimp } from './radsimp';
import { cancel } from './rational';
import { exptotrig, expsimp, hasTrig } from './trigsimp';

const hasDenominator = (e: Expr): boolean =>
  some(e, (x) => x instanceof Pow && splitCoeff(x.exp)[0].isNegative && !x.base.isNumber);

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
  return best;
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

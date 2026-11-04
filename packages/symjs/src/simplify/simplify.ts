// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file simplify(): try several strategies and keep the simplest result.
 */

import type { Expr, ExprLike } from '../core/nodes';
import { Add, ExtensionExpr, Fn, Mul, Pow, Rational, S, impl } from '../core/nodes';
import { mul, pow, splitCoeff, sympify } from '../core/ops';
import { asNumerDenom } from '../core/methods';
import { countOps as opCount } from '../core/match';
import { countOps, mapBottomUp, rebuild, some } from '../core/traverse';
import { combsimp } from './gammasimp';
import { fn } from '../functions/elementary/elementary';
import { expand_log, expand_power_exp, expandMul as expand } from './expand';
import { logcombine, powsimp } from './powsimp';
import { factorTerms } from './exprtools';
import { radsimp } from './radsimp';
import { cancel } from './rational';
import { exptotrig, expsimp, exptrigsimp, hasTrig, trigsimp } from './trigsimp';
import { first } from '../core/guard';

const hasDenominator = (e: Expr): boolean =>
  some(e, (x) => x instanceof Pow && splitCoeff(x.exp)[0].isNegative && !x.base.isNumber);

/** A sum with a non-integer rational term, e.g. x - 3/2 (SymPy clears such denominators). */
function hasRationalCoeffInsideSum(e: Expr): boolean {
  if (e instanceof Add && e.args.some((a) => (a instanceof Rational && !a.isInteger) || (a instanceof Mul && a.args[0] instanceof Rational && !(a.args[0]).isInteger))) return true;
  return e.args.some(hasRationalCoeffInsideSum);
}

/** A sum with a term divided by a symbolic expression (SymPy simplify first puts such sums over a common denominator). */
function hasFractionInsideSum(e: Expr): boolean {
  const isFraction = (t: Expr): boolean =>
    (t instanceof Pow && t.exp instanceof Rational && t.exp.isNegative && !(t.base instanceof Rational)) || (t instanceof Mul && t.args.some(isFraction));
  if (e instanceof Add && e.args.some(isFraction)) return true;
  return e.args.some(hasFractionInsideSum);
}

/** An even integer power of a sum ((u - v)**2), whose base may appear with either sign. */
const isEvenPowerOfSum = (x: Expr): x is Pow => x instanceof Pow && x.base instanceof Add && x.exp instanceof Rational && x.exp.isInteger && x.exp.p % 2n === 0n;

/** (-b)**(2k) as b**(2k) with one sign of b chosen by its structural key, so that the two forms combine. */
function normalizeEvenPowers(e: Expr): Expr {
  return mapBottomUp(e, (x) => {
    if (!isEvenPowerOfSum(x)) return x;
    const nb = mul(-1, x.base);
    return nb.key < x.base.key ? new Pow(nb, x.exp) : x;
  });
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

  // combinatorial functions: Gamma ratios combined (SymPy combsimp in simplify)
  if (some(e, (x) => x instanceof Fn && ['factorial', 'binomial', 'gamma', 'rf', 'ff'].includes(x.name))) tryPush(() => combsimp(expand(e)));
  if (hasDenominator(e)) {
    tryPush(() => cancel(e));
    if (hasTrig(e)) tryPush(() => cancel(exptotrig(e)));
  }
  let best = first(candidates);
  let bestCost = countOps(best);
  for (const c of candidates.slice(1)) {
    const cost = countOps(c);
    if (cost < bestCost) {
      best = c;
      bestCost = cost;
    }
  }
  // (-u + v)**2 and (u - v)**2 in different terms (the norms of opposite vectors) combine
  if (some(best, isEvenPowerOfSum)) {
    const nb = normalizeEvenPowers(best);
    if (countOps(nb) < bestCost) {
      best = nb;
      bestCost = countOps(nb);
    }
  }
  // SymPy's pipeline ends in factor_terms(cancel(...)) and keeps it unless it is longer
  if (hasDenominator(e) && !(best instanceof Add)) {
    try {
      const ft = factorTerms(cancel(e));
      if (countOps(ft) <= bestCost && hasRationalCoeffInsideSum(best) && !hasRationalCoeffInsideSum(ft)) best = ft;
      else if (countOps(ft) <= bestCost && hasFractionInsideSum(best) && !hasFractionInsideSum(ft)) best = ft;
    } catch {
      // keep best
    }
  }
  // SymPy: expr = factor_terms(expr, sign=False) after the rational candidates, so the numeric
  // content of a quotient stays in front: 3*(5 - 21*x)/((x - 1)*(5*x - 1)), not (15 - 63*x)/...
  if (best instanceof Mul && hasDenominator(best)) {
    const ft = factorTerms(best, { sign: false });
    if (opCount(ft) <= opCount(best)) best = ft;
  }
  let r = hasTrig(best) ? trigsimp(best) : best;
  // SymPy: short = shorter(short, factor_terms(short), expand_power_exp(expand_mul(short)))
  if (r !== best) {
    const em = expand_power_exp(expand(r));
    if (opCount(em) < opCount(r)) r = em;
  }
  // SymPy simplify ends with exptrigsimp, which pairs exp(I*x) + exp(-I*x) into 2*cos(x) also inside products
  if (some(r, (x) => x instanceof Pow && x.base.key === S.E.key && x.exp.has(S.I))) {
    const t = exptrigsimp(r);
    if (countOps(t) < countOps(r)) return t;
  }
  return r;
}

/**
 * Simplify an expression using a combination of expansion, trigonometric /
 * exponential rewriting and rational-function cancellation. The candidate
 * with the fewest nodes wins.
 */
export function simplify(ex: ExprLike, opts: SimplifyOptions = {}): Expr {
  const original = sympify(ex);
  if (original instanceof ExtensionExpr) {
    const own = original.simplifySelf((x) => simplify(x, opts));
    if (own !== undefined) return own;
  }
  const e = mapBottomUp(original, (x) =>
    x instanceof Fn ? fn(x.name, x.args.map(simplifyCore)) : x,
  );
  let r = simplifyCore(e);
  const measure = opts.measure ?? countOps;
  const size = (x: Expr): number => {
    const m = measure(x);
    return typeof m === 'number' ? m : m.toNumber();
  };
  // SymPy: with a custom measure, logarithms are expanded or combined, whichever is shorter
  if (opts.measure && some(r, (x) => x instanceof Fn && x.name === 'log')) {
    const expanded = expand_log(r, true);
    const combined = logcombine(r);
    r = size(combined) < size(expanded) ? combined : expanded;
  }
  // SymPy: a sum in the denominator is rationalized when one radical term goes away
  // (1/(sqrt(2) + 2) = 1 - sqrt(2)/2)
  r = rationalizeDenominator(r);
  // SymPy's done(): doit() rebuilds the result evaluated, so unevaluated products such as the
  // (phi + theta)/2 of factor become phi/2 + theta/2 again
  r = reevaluate(r);
  // SymPy: a result longer than ratio times the input (by the measure) is rejected
  const ratio = opts.ratio ?? 1.7;
  return size(r) > ratio * size(original) ? original : r;
}

/**
 * SymPy simplify: numer, denom = expr.as_numer_denom(); for a sum denom,
 * n, d = fraction(radsimp(1/denom, symbolic=False, max_terms=1)) and the
 * result (numer*n).expand()/d when n is not 1.
 */
function rationalizeDenominator(e: Expr): Expr {
  const [numer, denom] = asNumerDenom(e);
  if (!(denom instanceof Add)) return e;
  const [n, d] = asNumerDenom(radsimp(pow(denom, -1), { symbolic: false, maxTerms: 1 }));
  if (n.key === S.One.key) return e;
  return mul(expand(mul(numer, n)), pow(d, -1));
}

/** Every node rebuilt with evaluation, bottom-up (SymPy Basic.doit on expressions without unevaluated objects). */
function reevaluate(e: Expr): Expr {
  return e.args.length ? rebuild(e, e.args.map(reevaluate)) : e;
}

/** Options of simplify (SymPy ratio and measure). */
export interface SimplifyOptions {
  /** The largest accepted measure(result)/measure(input); default 1.7. */
  ratio?: number;
  /** The size of an expression; default countOps. A number or a numeric expression. */
  measure?: (e: Expr) => number | Expr;
}

impl.simplify = simplify;

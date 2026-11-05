// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file simplify(): a port of SymPy's simplify pipeline (sympy/simplify/simplify.py).
 */

import type { Expr, ExprLike } from '../core/nodes';
import { Add, Dummy, ExtensionExpr, Fn, Mul, Pow, Rational, S, impl, isNum } from '../core/nodes';
import { minimalPolynomial } from '../polys/numberfields';
import { couldExtractMinusSign, mul, pow, sympify } from '../core/ops';
import { asContentPrimitive, asNumerDenom } from '../core/methods';
import { countOps as opCount } from '../core/match';
import { mapBottomUp, rebuild, some, xreplace } from '../core/traverse';
import { combsimp } from './gammasimp';
import { besselsimp } from './besselsimp';
import { Hyper, MeijerG, kroneckersimp } from '../functions/special/hyper';
import { expand as expandAll, expand_log, expand_power_exp, expandMul as expand } from './expand';
import { logcombine, powsimp } from './powsimp';
import { factorTerms, signsimp } from './exprtools';
import { collectAbs, radsimp } from './radsimp';
import { cancel, fraction, together } from './rational';
import { exptrigsimp, trigsimp } from './trigsimp';
import { first } from '../core/guard';

/** The names of SymPy's TrigonometricFunction and HyperbolicFunction classes. */
const TRIG_HYP = new Set(['sin', 'cos', 'tan', 'cot', 'sec', 'csc', 'sinc', 'sinh', 'cosh', 'tanh', 'coth', 'sech', 'csch']);
/** SymPy's CombinatorialFunction classes. */
const COMBINATORIAL = new Set(['factorial', 'factorial2', 'binomial', 'rf', 'ff', 'subfactorial']);
/** The CombinatorialFunction classes and gamma (the functions combsimp is applied for). */
const COMBINATORIAL_GAMMA = new Set([...COMBINATORIAL, 'gamma']);
const BESSEL = new Set(['besselj', 'bessely', 'besseli', 'besselk', 'hankel1', 'hankel2', 'jn', 'yn']);
const hasFn = (e: Expr, names: ReadonlySet<string>): boolean => some(e, (x) => x instanceof Fn && names.has(x.name));
const isExpPow = (x: Expr): boolean => x instanceof Pow && x.base.key === S.E.key;

/**
 * The hyperexpand step of simplify. simplify cannot import hyperexpand (which simplifies its
 * results), so hyperexpand.ts' importers register it here; without it the step is skipped.
 */
export const simplifyHooks: { hyperexpand?: (e: Expr) => Expr } = {};

/**
 * Simplify an expression (SymPy simplify): rational-function forms (cancel, together), the
 * special simplifications for the functions it contains (hyperexpand, besselsimp, trigsimp,
 * log expansion or combination, combsimp), power simplification and sign normalization; each
 * step keeps the shortest candidate by `measure` (count_ops), and a result longer than `ratio`
 * times the input is rejected.
 */
export function simplify(ex: ExprLike, opts: SimplifyOptions = {}): Expr {
  const sympified = sympify(ex);
  if (sympified instanceof ExtensionExpr) {
    const own = sympified.simplifySelf((x) => simplify(x, opts));
    if (own !== undefined) return own;
  }
  const measureFn = opts.measure ?? opCount;
  const measure = (x: Expr): number => {
    const m = measureFn(x);
    return typeof m === 'number' ? m : m.toNumber();
  };
  const ratio = opts.ratio ?? 1.7;
  /** SymPy shorter: the first choice of the smallest measure. */
  const shorter = (...choices: Expr[]): Expr => {
    let best = first(choices);
    let bm: number | undefined;
    for (const c of choices.slice(1)) {
      if (c.key === best.key) continue;
      bm ??= measure(best);
      const cm = measure(c);
      if (cm < bm) [best, bm] = [c, cm];
    }
    return best;
  };
  /** SymPy done: doit, and the Abs factors collected when that is shorter. */
  const done = (e: Expr): Expr => {
    const rv = reevaluate(e);
    return shorter(rv, collectAbs(rv));
  };
  // (SymPy first returns 0 for an expression known to be zero; the assumptions here decide that only
  // for expressions that evaluate to 0)
  if (sympified.isAtom) return sympified;
  // SymPy _eval_simplify of hyper, the Bessel functions and the combinatorial functions
  const hyperexpand = simplifyHooks.hyperexpand;
  if (sympified instanceof Hyper && hyperexpand) return hyperexpand(sympified);
  if (sympified instanceof Fn && BESSEL.has(sympified.name)) return besselsimp(sympified);
  if (sympified instanceof Fn && COMBINATORIAL.has(sympified.name)) {
    const c = combsimp(sympified);
    return measure(c) <= ratio * measure(sympified) ? c : sympified;
  }
  const original = collectAbs(signsimp(sympified));
  // deep simplification: the arguments of the nodes other than sums, products and powers
  let expr = mapTopDownUnhandled(original, (x) => simplify(x, opts));
  if (!(expr instanceof Add || expr instanceof Mul || expr instanceof Pow)) {
    // SymPy log._eval_simplify: the logarithm expanded when that is not longer
    if (expr instanceof Fn && expr.name === 'log') expr = shorter(expand_log(expr), expr);
    return done(expr);
  }
  // rational-function forms
  expr = mapBottomUp(expr, normal);
  const [c, p] = contentPrimitive(powsimp(expr));
  expr = mul(c, p);
  const e0 = cancel(expr);
  const expr1 = shorter(e0, cancel(mexpand(e0)));
  const expr2 = shorter(together(expr, { deep: true }), together(expr1, { deep: true }));
  expr = ratio === Infinity ? expr2 : shorter(expr2, expr1, expr);
  expr = factorTerms(expr, { sign: false });
  // the functions it contains
  if (hyperexpand && some(expr, (x) => x instanceof Hyper || x instanceof MeijerG)) expr = hyperexpand(expr);
  if (hasFn(expr, KRONECKER)) expr = kroneckersimp(expr);
  if (hasFn(expr, BESSEL)) expr = besselsimp(expr);
  if (hasFn(expr, TRIG_HYP)) expr = trigsimp(expr);
  if (hasFn(expr, LOG)) expr = shorter(expand_log(expr), logcombine(expr));
  if (hasFn(expr, COMBINATORIAL_GAMMA)) expr = combsimp(expr);
  // powers, the cancelled form and the factored or expanded form
  let short = shorter(powsimp(expr, { combine: 'exp', deep: true }), powsimp(expr), expr);
  short = shorter(short, cancel(short));
  short = shorter(short, factorTerms(short), expand_power_exp(expand(short)));
  if (hasFn(short, TRIG_HYP) || some(short, isExpPow)) short = exptrigsimp(short);
  // no hollow 2-argument products c*(a + b)
  expr = mapBottomUp(short, (x) => (x instanceof Mul && x.args.length === 2 && isNum(first(x.args)) && x.args[1] instanceof Add ? mul(...x.args) : x));
  expr = rationalizeDenominator(expr);
  if (couldExtractMinusSign(expr)) {
    // (SymPy checks d != 0; a division by zero is already zoo in the numerator)
    const [n, d] = fraction(expr);
    expr = signsimp(mul(mul(-1, n), pow(mul(-1, d), -1)));
  }
  if (measure(expr) > ratio * measure(original)) expr = original;
  const r = done(expr);
  // (a zero built from other rationals is the canonical S.Zero)
  return r instanceof Rational && r.isZero ? S.Zero : r;
}

const LOG = new Set(['log']);
const KRONECKER = new Set(['KroneckerDelta']);

/**
 * SymPy as_content_primitive, where exp(x) is not a power: its argument keeps its content
 * (Expr.as_content_primitive gives (1, exp(x))).
 */
function contentPrimitive(e: Expr): [Rational, Expr] {
  const reps: [Expr, Expr][] = [];
  const hide = (x: Expr): Expr => {
    if (isExpPow(x)) {
      const d = new Dummy('e');
      reps.push([d, x]);
      return d;
    }
    return x.args.length ? rebuild(x, x.args.map(hide)) : x;
  };
  const [c, p] = asContentPrimitive(hide(e));
  return [c, reps.length ? xreplace(p, reps) : p];
}

/** SymPy Expr.normal: n/d of as_numer_denom (sums over a common denominator). */
function normal(e: Expr): Expr {
  const [n, d] = asNumerDenom(e);
  return d instanceof Rational && d.isOne ? n : mul(n, pow(d, -1));
}

/** SymPy _mexpand: expand_mul and expand_multinomial. */
const mexpand = (e: Expr): Expr => expandAll(e, { power_exp: false, power_base: false, log: false });

/**
 * SymPy expr.replace(lambda x: x.args and not isinstance(x, (Add, Mul, Pow, ExpBase)), lambda x:
 * x.func(*[simplify(i) for i in x.args])): every node other than sums, products and powers has
 * its arguments simplified (a replaced node is not visited again).
 */
function mapTopDownUnhandled(e: Expr, simp: (x: Expr) => Expr): Expr {
  if (e.args.length === 0) return e;
  if (e instanceof Add || e instanceof Mul || e instanceof Pow) {
    const args = e.args.map((a) => mapTopDownUnhandled(a, simp));
    return args.every((a, i) => a === e.args[i]) ? e : rebuild(e, args);
  }
  return rebuild(e, e.args.map(simp));
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

/** An algebraic number: rationals and I under sums, products and rational powers. */
const isAlgebraicNumber = (e: Expr): boolean =>
  e instanceof Rational || e === S.I || ((e instanceof Add || e instanceof Mul) && e.args.every(isAlgebraicNumber)) || (e instanceof Pow && e.exp instanceof Rational && isAlgebraicNumber(e.base));

impl.equalsZero = (e) => {
  if (simplify(e).key === S.Zero.key) return true;
  const x = new Dummy('x');
  return isAlgebraicNumber(e) && minimalPolynomial(e, x).key === x.key ? true : undefined;
};

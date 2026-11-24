// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file simplify(): a port of SymPy's simplify pipeline (sympy/simplify/simplify.py).
 */

import type { Expr, ExprLike, FnName } from '../core/nodes';
import { Add, Constant, Dummy, ExtensionExpr, Float, Fn, Integral, Mul, Piecewise, Pow, Rational, Rel, S, Sym, UndefFn, impl, isNum } from '../core/nodes';
import { Concrete, Sum } from '../core/concrete';
import { AlgebraicNumber, minimalPolynomial } from '../polys/numberfields';
import { add, couldExtractMinusSign, mul, pow, sub, sympify } from '../core/ops';
import { asContentPrimitive, asIndependent, asNumerDenom, isConstantTruth, isRationalFunction } from '../core/methods';
import { countOps as opCount } from '../core/match';
import { mapBottomUp, piecewiseFold, piecewiseFoldHooks, rebuild, some, subs, xreplace } from '../core/traverse';
import { combsimp } from './gammasimp';
import { besselsimp } from './besselsimp';
import { Hyper, MeijerG, KroneckerDelta, kroneckersimp } from '../functions/special/hyper';
import { expand as expandAll, expand_log, expand_power_exp, expandMul as expand } from './expand';
import { combinePhases, logcombine, powsimp } from './powsimp';
import { factorTerms, signsimp } from './exprtools';
import { collectAbs, radsimp } from './radsimp';
import { cancel, fraction, together } from './rational';
import { exptrigsimp, trigsimp } from './trigsimp';
import { at, first } from '../core/guard';
import { nsimplify, nfloat } from '../numeric/nfloat';
import { simplifyRelation } from '../core/relational';
import { isNegative, isIntegerQ } from '../core/assumptions';
import type { Truth } from '../core/truth';
import { simplifyLogic } from '../logic/minimize';
import { toNnf } from '../logic/normalforms';
import { simplifySymbolicIntervals } from '../functions/elementary/piecewise';
import { BoolOp, and } from '../core/boolalg';
import { simplifyBoolean } from '../logic/minimize';
import { Eq, Ge, Gt, Le, Lt, canonicalRelation, piecewise } from '../core/logic';
import { ordered } from '../core/match';
import type { SetExpr } from '../sets/sets';
import { EmptySet, Interval, Reals, cmpReal, complement, intersection, interval, union } from '../sets/sets';

/**
 * Strip rational coefficients from an equation, applying the same operations to its right side.
 *
 * @remarks
 * For `clear_coefficients(expr - 2)`, SymPy displays `(y*(2*x + 1), 1/6)`.
 * @param exprIn - The input expression.
 * @param rhsIn - The right-hand side.
 * @returns The transformed left- and right-hand sides.
 * @see SymPy `sympy.simplify.simplify.clear_coefficients`
 * @example
 * ```ts
 * import { clearCoefficients, ex } from '@symjs/symjs';
 *
 * clearCoefficients(ex`4*y*(6*x + 3) - 2`); // => [y*(2*x + 1), 1/6]
 * ```
 */
export function clearCoefficients(exprIn: ExprLike, rhsIn: ExprLike = 0): [Expr, Expr] {
  let expr = sympify(exprIn);
  let rhs = sympify(rhsIn);
  if (expr instanceof Rational) return [S.Zero, add(rhs, mul(-1, expr))];
  for (;;) {
    const previous = expr.key;
    const [content, primitive] = asContentPrimitive(expr);
    rhs = mul(rhs, pow(content, -1));
    expr = primitive;
    if (expr instanceof Add && first(expr.args) instanceof Rational) {
      rhs = add(rhs, mul(-1, first(expr.args)));
      expr = add(...expr.args.slice(1));
    }
    if (expr.key === previous) break;
  }
  expr = signsimp(expr, false);
  return couldExtractMinusSign(expr) ? [mul(-1, expr), mul(-1, rhs)] : [expr, rhs];
}

/**
 * Extract constant factors from a Sum, or from a summand and its limits.
 *
 * @param expr - The input expression.
 * @param limits - The index and its inclusive lower and upper bounds.
 * @param opts - `radical` extracts common radicals, `clear` clears rational coefficients, `fraction` combines denominators and `sign` extracts a common minus sign.
 * @returns The sum with independent factors extracted.
 * @see SymPy `sympy.simplify.simplify.factor_sum`
 * @example
 * ```ts
 * import { ex, factorSum, symbols } from '@symjs/symjs';
 *
 * factorSum(ex`a*k`, [[symbols('k')[0], 1, 5]]); // => a*Sum(k, (k, 1, 5))
 * ```
 */
export function factorSum(expr: ExprLike, limits?: readonly [Sym, ExprLike, ExprLike][], opts: { radical?: boolean; clear?: boolean; fraction?: boolean; sign?: boolean } = {}): Expr {
  return factorTerms(limits === undefined ? expr : Sum(expr, ...limits), opts);
}

/**
 * Formally cancel functions with their inverses (SymPy inversecombine).
 * As in SymPy, this explicitly assumes the relevant principal branch:
 * asin(sin(x)) = x and log(exp(x)) = x are not global complex identities.
 *
 * @param expr - The input expression.
 * @returns The expression with inverse-function pairs cancelled.
 * @see SymPy `sympy.simplify.simplify.inversecombine`
 * @example
 * ```ts
 * import { ex, inversecombine } from '@symjs/symjs';
 *
 * inversecombine(ex`asin(sin(x))`); // => x
 * inversecombine(ex`2*log(exp(3*x))`); // => 6*x
 * ```
 */
export function inversecombine(expr: ExprLike): Expr {
  const inverse: Partial<Record<FnName, FnName>> = {
    asin: 'sin', acos: 'cos', atan: 'tan', acot: 'cot', asec: 'sec', acsc: 'csc',
    asinh: 'sinh', acosh: 'cosh', atanh: 'tanh', acoth: 'coth', asech: 'sech', acsch: 'csch',
    sin: 'asin', cos: 'acos', tan: 'atan', cot: 'acot', sec: 'asec', csc: 'acsc',
    sinh: 'asinh', cosh: 'acosh', tanh: 'atanh', coth: 'acoth', sech: 'asech', csch: 'acsch',
  };
  return mapBottomUp(sympify(expr), (e) => {
    if (e instanceof UndefFn && 'inverse' in e && typeof e.inverse === 'function' && e.args.length === 1) {
      const inner = first(e.args);
      if (inner.args.length === 1 && e.inverse()(first(inner.args)).equals(inner)) return first(inner.args);
    }
    if (e instanceof Fn) {
      const inner = e.args[0];
      if (e.name === 'log' && inner instanceof Pow && inner.base.key === S.E.key) {
        if (e.args.length === 1) return inner.exp;
        if (e.args.length === 2) return mul(inner.exp, pow(rebuild(e, [at(e.args, 1)]), -1));
      }
      if (e.args.length === 1 && inner instanceof Fn && inner.args.length === 1 && inverse[e.name] === inner.name) return first(inner.args);
    }
    if (e instanceof Pow && e.base.key === S.E.key && e.exp instanceof Fn && e.exp.name === 'log') return first(e.exp.args);
    return e;
  });
}

/**
 * Find a real root of a sum of surds; every numerically proposed denesting is verified exactly.
 *
 * @param exprIn - The input expression.
 * @param nIn - The root degree.
 * @param opts - `maxLen` limits the number of surds used in identifying a candidate.
 * @returns The real root, expressed in radicals when identified.
 * @see SymPy `sympy.simplify.simplify.nthroot`
 * @example
 * ```ts
 * import { ex, nthroot } from '@symjs/symjs';
 *
 * nthroot(ex`34*sqrt(7) + 90`, 3); // => sqrt(7) + 3
 * ```
 */
export function nthroot(exprIn: ExprLike, nIn: ExprLike, opts: { maxLen?: number } = {}): Expr {
  const expr = sympify(exprIn);
  const n = sympify(nIn);
  const principal = pow(expr, pow(n, -1));
  if (!(n instanceof Rational && n.isInteger) || n.isZero) return principal;
  const negative = n.p % 2n !== 0n && isNegative(expr) === true;
  const radicand = negative ? mul(-1, expr) : expr;
  const root = pow(radicand, pow(n, -1));
  const radicals = new Map<string, Expr>();
  some(radicand, (e) => {
    if (e instanceof Pow && e.exp.key === S.Half.key && e.base instanceof Rational && e.base.isInteger && e.base.isPositive) radicals.set(e.key, e);
    return false;
  });
  const candidate = nsimplify(root, { constants: [...radicals.values()].slice(0, opts.maxLen ?? 4) });
  const verified = expandAll(add(pow(candidate, n), mul(-1, radicand))).key === S.Zero.key;
  const result = verified ? candidate : root;
  return negative ? mul(-1, result) : result;
}

/**
 * Compress repeated words in noncommutative products. Dynamic programming minimizes
 * the number of factors, including factors inside powers, while preserving order.
 *
 * @param exprIn - The input expression.
 * @param opts - `deep` also simplifies arguments of compound expressions.
 * @returns The product with repeated noncommutative factors compressed.
 * @see SymPy `sympy.simplify.simplify.nc_simplify`
 * @example
 * ```ts
 * import { ex, ncSimplify } from '@symjs/symjs';
 *
 * ncSimplify(ex`x`); // => x
 * ```
 */
export function ncSimplify(exprIn: ExprLike, opts: { deep?: boolean } = {}): Expr {
  const expr = sympify(exprIn);
  if (expr.isCommutative) return expr;
  if (expr instanceof Add) return add(...expr.args.map((e) => ncSimplify(e, opts)));
  if (expr instanceof Pow) return opts.deep === false ? expr : pow(ncSimplify(expr.base), expr.exp);
  if (!(expr instanceof Mul)) return expr;
  const commuting = expr.args.filter((e) => e.isCommutative);
  const word: Expr[] = [];
  const append = (e: Expr): void => {
    if (word.length > 128) return;
    if (e instanceof Mul && opts.deep !== false) {
      e.args.forEach(append);
    } else if (e instanceof Pow && e.exp instanceof Rational && e.exp.isInteger && e.exp.p > 0n && e.exp.p <= 64n && (opts.deep !== false || !(e.base instanceof Mul))) {
      for (let i = 0n; i < e.exp.p; i++) append(e.base);
    } else word.push(e);
  };
  expr.args.filter((e) => !e.isCommutative).forEach(append);
  if (word.length > 128) return expr;
  // Cancel adjacent inverses before looking for repeated words.
  const reduced: Expr[] = [];
  for (const e of word) {
    const previous = reduced.at(-1);
    if (previous !== undefined && mul(previous, e).key === S.One.key) reduced.pop();
    else reduced.push(e);
  }
  // The word bound above keeps the dynamic program finite without approximations.
  type Candidate = { expr: Expr; score: number };
  const score = (e: Expr): number => e instanceof Pow ? score(e.base) : e instanceof Mul ? e.args.reduce((s, a) => s + score(a), 0) : 1;
  const memo = new Map<string, Candidate>();
  const best = (start: number, end: number): Candidate => {
    const key = `${start}:${end}`;
    const cached = memo.get(key);
    if (cached !== undefined) return cached;
    const original = mul(...reduced.slice(start, end));
    let result = { expr: original, score: score(original) };
    const take = (e: Expr): void => {
      const s = score(e);
      if (s < result.score) result = { expr: e, score: s };
    };
    for (let size = 1; size <= (end - start) / 2; size++) {
      if ((end - start) % size !== 0) continue;
      if (reduced.slice(start, end).every((e, i) => e.key === at(reduced, start + i % size).key)) take(pow(best(start, start + size).expr, (end - start) / size));
    }
    for (let split = start + 1; split < end; split++) take(mul(best(start, split).expr, best(split, end).expr));
    memo.set(key, result);
    return result;
  };
  const result = best(0, reduced.length).expr;
  const factors = result instanceof Mul ? result.args : [result];
  const grouped: Expr[] = [];
  let inverses: Expr[] = [];
  const flush = (): void => {
    if (inverses.length) grouped.push(pow(mul(...inverses.reverse()), -1));
    inverses = [];
  };
  for (const e of factors) {
    if (e instanceof Pow && isNegative(e.exp) === true) inverses.push(pow(e, -1));
    else { flush(); grouped.push(e); }
  }
  flush();
  return mul(...commuting, ...grouped);
}

/** The names of SymPy's TrigonometricFunction and HyperbolicFunction classes. */
const TRIG_HYP = new Set(['sin', 'cos', 'tan', 'cot', 'sec', 'csc', 'sinc', 'sinh', 'cosh', 'tanh', 'coth', 'sech', 'csch']);
/** SymPy's CombinatorialFunction classes. */
const COMBINATORIAL = new Set(['factorial', 'factorial2', 'binomial', 'rf', 'ff', 'subfactorial']);
/** The CombinatorialFunction classes and gamma (the functions combsimp is applied for). */
const COMBINATORIAL_GAMMA = new Set([...COMBINATORIAL, 'gamma']);
const BESSEL = new Set(['besselj', 'bessely', 'besseli', 'besselk', 'hankel1', 'hankel2', 'jn', 'yn']);
const hasFn = (e: Expr, names: ReadonlySet<string>): boolean => some(e, (x) => x instanceof Fn && names.has(x.name));
const isExpPow = (x: Expr): x is Pow => x instanceof Pow && x.base.key === S.E.key;

/**
 * The hyperexpand step of simplify. simplify cannot import hyperexpand (which simplifies its
 * results), so hyperexpand.ts' importers register it here; without it the step is skipped.
 */
export const simplifyHooks: { hyperexpand?: (e: Expr) => Expr } = {};

piecewiseFoldHooks.normalizeIte = (condition) => simplifyLogic(toNnf(condition), 'cnf');

function isSubstitutionEquation(e: Rel): boolean {
  const variable = (x: Expr): boolean => x instanceof Sym || x instanceof UndefFn;
  return variable(e.lhs) && (variable(e.rhs) || e.rhs instanceof Rational || e.rhs instanceof Constant);
}

/** Read a conjunction of comparisons to real constants as an interval. */
function piecewiseConditionSet(condition: Expr, x: Sym): SetExpr | undefined {
  if (condition === S.true) return Reals;
  if (condition === S.false) return EmptySet;
  if (condition instanceof BoolOp && condition.op === 'And') {
    const parts = condition.args.map((part) => piecewiseConditionSet(part, x));
    if (parts.every((part): part is SetExpr => part !== undefined)) return intersection(...parts);
    return undefined;
  }
  if (!(condition instanceof Rel) || condition.op === 'Eq' || condition.op === 'Ne') return undefined;
  if (condition.lhs instanceof Fn && condition.lhs.name === 'abs' && first(condition.lhs.args).equals(x)
      && (condition.op === 'Lt' || condition.op === 'Le') && condition.rhs instanceof Rational && condition.rhs.isPositive) {
    return interval(mul(-1, condition.rhs), condition.rhs, condition.op === 'Lt', condition.op === 'Lt');
  }
  const left = condition.lhs.key === x.key;
  if (!left && condition.rhs.key !== x.key) return undefined;
  const bound = left ? condition.rhs : condition.lhs;
  if (cmpReal(bound, S.Zero) === undefined) return undefined;
  const upper = (condition.op === 'Lt' || condition.op === 'Le') === left;
  const strict = condition.op === 'Lt' || condition.op === 'Gt';
  return upper ? interval(S.NegativeInfinity, bound, true, strict) : interval(bound, S.Infinity, strict, true);
}

function simplifyPiecewiseIntervals(e: Piecewise, opts: SimplifyOptions): [Expr, Expr][] {
  const pairs = e.pairs;
  const vars = [...new Map(pairs.flatMap(([, c]) => [...c.freeSymbols()].map((symbol) => [symbol.key, symbol] as const))).values()];
  const x = vars[0];
  if (vars.length > 1) return simplifySymbolicIntervals(pairs, (condition) => simplify(condition, { ...opts, doit: false }));
  if (!(x instanceof Sym)) return pairs;
  let covered: SetExpr = EmptySet;
  const result: [Expr, Expr][] = [];
  for (const [value, condition] of pairs) {
    const set = piecewiseConditionSet(condition, x);
    if (set === undefined) return pairs;
    const remaining = complement(set, covered);
    if (remaining === EmptySet) continue;
    const all = union(covered, set);
    let test = all === Reals ? S.true : condition;
    if (test !== S.true && remaining instanceof Interval && (!remaining.equals(set) || condition instanceof Rel && condition.lhs instanceof Fn && condition.lhs.name === 'abs')) {
      const entireLeft = interval(S.NegativeInfinity, remaining.start, true, !remaining.leftOpen);
      const lo = remaining.isLeftUnbounded || complement(entireLeft, covered) === EmptySet
        ? S.true : remaining.leftOpen ? Gt(x, remaining.start) : Ge(x, remaining.start);
      const hi = remaining.isRightUnbounded ? S.true : remaining.rightOpen ? Lt(x, remaining.end) : Le(x, remaining.end);
      test = and(lo, hi);
    }
    result.push([value, test]);
    covered = all;
  }
  if (covered !== Reals) result.push([S.NaN, S.true]);
  return result;
}

/** Apply branch equalities and merge a point value when it agrees with the next branch. */
function simplifyPiecewise(e: Piecewise, opts: SimplifyOptions): Expr {
  const pairs = simplifyPiecewiseIntervals(e, opts).map(([branch, condition]): [Expr, Expr] => {
    let value = branch;
    const parts = condition instanceof BoolOp && condition.op === 'And' ? condition.args : [condition];
    const equality = (part: Expr): part is Rel => part instanceof Rel && part.op === 'Eq';
    const equations = ordered(parts.filter(equality).map((eq) => {
      if (isExpPow(eq.lhs) && eq.lhs.exp instanceof Add) {
        return Eq(pow(S.E, signsimp(factorTerms(eq.lhs.exp))), eq.rhs);
      }
      if (isSubstitutionEquation(eq) || eq.freeSymbols().size !== 1) return eq;
      const delta = expand(add(eq.lhs, mul(-1, eq.rhs)));
      return canonicalRelation(new Rel('Eq', delta, S.Zero));
    }));
    let remaining = parts.filter((part) => !equality(part));
    for (const [i, eq] of equations.entries()) {
      if (!(eq instanceof Rel) || !isSubstitutionEquation(eq)) continue;
      const replacement = [[eq.lhs, eq.rhs]] as const;
      value = subs(value, replacement);
      equations.splice(i + 1, equations.length, ...equations.slice(i + 1).map((other) => subs(other, replacement)));
      remaining = remaining.map((other) => subs(other, replacement));
    }
    const tests = remaining.map((test) => {
      if (test instanceof BoolOp && test.op === 'Or') return simplifyLogic(simplify(test, { ...opts, doit: false }));
      return test instanceof Rel ? simplify(test, { ...opts, doit: false }) : test;
    });
    return [simplify(value, { ...opts, doit: false }), and(...equations, ...tests)];
  });
  for (let i = pairs.length - 2; i >= 0; i--) {
    const [value, condition] = at(pairs, i);
    const [next] = at(pairs, i + 1);
    const parts = condition instanceof BoolOp && condition.op === 'And' ? condition.args : [condition];
    if (!parts.every((part): part is Rel => part instanceof Rel && part.op === 'Eq')) continue;
    const replacement = ordered(parts).filter((eq): eq is Rel => eq instanceof Rel && (pairs.length === 2 || isSubstitutionEquation(eq)))
      .map((eq) => [eq.lhs, eq.rhs] as const);
    if (subs(next, replacement).key === subs(value, replacement).key) at(pairs, i)[0] = next;
  }
  return piecewise(...pairs);
}

/**
 * Simplifies an expression by trying rational-function forms (`cancel`,
 * `together`), the simplifications for the functions it contains (`hyperexpand`,
 * `besselsimp`, `trigsimp`, log expansion or combination, `combsimp`), power
 * simplification and sign normalization. Each step keeps the shortest candidate
 * by `measure` (`countOps` by default), and a result longer than `ratio` times
 * the input is rejected.
 *
 * @param ex - The expression to simplify.
 * @param opts - See {@link SimplifyOptions}.
 * @returns The simplified expression.
 * @see SymPy `sympy.simplify.simplify.simplify`
 * @example
 * ```ts
 * import { ex, simplify, trigsimp } from '@symjs/symjs';
 *
 * const a = ex`(x + x**2)/(x*sin(y)**2 + x*cos(y)**2)`;
 * a; // => (x**2 + x)/(x*sin(y)**2 + x*cos(y)**2)
 * simplify(a); // => x + 1
 * trigsimp(a); // => (x**2 + x)/x
 * ```
 */
export function simplify(ex: AlgebraicNumber, opts?: SimplifyOptions): AlgebraicNumber;
export function simplify(ex: ExprLike, opts?: SimplifyOptions): Expr;
export function simplify(ex: ExprLike | AlgebraicNumber, opts: SimplifyOptions = {}): Expr | AlgebraicNumber {
  if (ex instanceof AlgebraicNumber) {
    const measure = opts.measure ?? opCount;
    const size = (e: Expr): number => {
      const value = measure(e);
      return typeof value === 'number' ? value : value.toNumber();
    };
    const limit = (opts.ratio ?? 1.7) * size(ex.root);
    const candidate = ex.minpoly().roots().find((root) => size(root) < limit && exprEquals(root, ex.root) === true);
    return candidate === undefined || ex.root.equals(candidate) ? ex
      : new AlgebraicNumber(candidate, ex.coeffList, ex.alias === undefined ? {} : { alias: ex.alias });
  }
  const input = opts.inverse ? inversecombine(ex) : sympify(ex);
  if (input instanceof BoolOp) return simplifyBoolean(input, (arg) => simplify(arg, opts));
  if (input instanceof Piecewise) return simplifyPiecewise(input, opts);
  // (a sum with Kronecker deltas keeps its Piecewise terms apart: they become deltas below)
  if (input instanceof Add && input.args.some((term) => term instanceof Piecewise) && !some(input, (e) => e instanceof Fn && e.name === 'KroneckerDelta')) {
    const folded = piecewiseFold(input);
    if (folded instanceof Piecewise) return simplifyPiecewise(folded, opts);
  }
  if (input instanceof Rel) {
    const result = simplifyRelation(input, (e) => simplify(e, opts));
    const measure = opts.measure ?? ((e: Expr) => opCount(e) + (e instanceof Rel ? 1 : 0));
    const value = (e: Expr): number => { const n = measure(e); return typeof n === 'number' ? n : n.toNumber(); };
    return value(result) < (opts.ratio ?? 1.7) * value(input) ? result : input;
  }
  const rationalized = opts.rational !== undefined && opts.rational !== false && some(input, (e) => e instanceof Float);
  let sympified = rationalized ? nsimplify(input, { rational: true }) : input;
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
  /** Selects the first expression with the smallest value of the simplification measure. */
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
  /**
   * Evaluates the expression according to the simplification options and collects
   * absolute-value factors if that reduces the measure.
   */
  const done = (e: Expr): Expr => {
    const rv = opts.doit !== false && impl.doit ? impl.doit(e) : reevaluate(e);
    const reduced = !rv.equals(e) && some(rv, t => t instanceof Fn && t.name === 'gamma') ? shorter(rv, combsimp(rv)) : rv;
    const result = shorter(reduced, collectAbs(reduced));
    return rationalized && opts.rational === null ? nfloat(result) : result;
  };
  // (SymPy first returns 0 for an expression known to be zero; the assumptions here decide that only
  // for expressions that evaluate to 0)
  if (sympified.isAtom) return done(sympified);
  // Integral and Sum have their own _eval_simplify in SymPy: simplify the
  // bound expression without forcing evaluation of the outer operator.
  if (sympified instanceof Integral) {
    const [c, f] = asIndependent(factorTerms(sympified.integrand), [sympified.variable], { asAdd: false });
    if (c.key !== S.One.key) return simplify(mul(c, new Integral([f, ...sympified.args.slice(1)])), opts);
    return rebuild(sympified, sympified.args.map((a) => simplify(a, opts)));
  }
  if (sympified instanceof Concrete && sympified.kind2 === 'Sum') {
    return factorTerms(combineConcrete(rebuild(sympified, sympified.args.map((a) => simplify(a, opts)))));
  }
  if (sympified instanceof Fn && sympified.name === 'log' && first(sympified.args) instanceof Concrete) {
    return shorter(expand_log(sympified), sympified);
  }
  if (sympified instanceof Fn && sympified.name === 'sign') {
    const [content, primitive] = asContentPrimitive(first(sympified.args));
    if (content.isPositive && !content.isOne) return rebuild(sympified, [primitive]);
  }
  // SymPy _eval_simplify of hyper, the Bessel functions and the combinatorial functions
  const hyperexpand = simplifyHooks.hyperexpand;
  if (sympified instanceof Hyper && hyperexpand) return hyperexpand(sympified);
  if (sympified instanceof Fn && BESSEL.has(sympified.name)) return besselsimp(sympified);
  if (sympified instanceof Fn && COMBINATORIAL.has(sympified.name)) {
    const c = combsimp(sympified);
    return measure(c) <= ratio * measure(sympified) ? c : sympified;
  }
  if (some(sympified, (e) => e instanceof Piecewise)) {
    if (hasFn(sympified, KRONECKER)) {
      sympified = mapBottomUp(sympified, (p) => {
        if (!(p instanceof Piecewise) || p.pairs.length !== 2) return p;
        const [[a, cond], [b, last]] = [first(p.pairs), at(p.pairs, 1)] as const;
        if (!(cond instanceof Rel) || last.key !== S.true.key) return p;
        if ((cond.op === 'Eq' && a.key === S.One.key && b.key === S.Zero.key) ||
            (cond.op === 'Ne' && a.key === S.Zero.key && b.key === S.One.key)) return KroneckerDelta(cond.lhs, cond.rhs);
        return p;
      });
    }
    const folded = piecewiseFold(sympified);
    if (folded instanceof Piecewise) return simplifyPiecewise(folded, opts);
  }
  const leading = sympified instanceof Mul ? first(sympified.args) : undefined;
  if (leading instanceof Float && leading.mpf.man === 1n && leading.mpf.exp === 0n && !sympified.isCommutative) {
    sympified = mul(...sympified.args.slice(1));
  }
  if (sympified.has(S.I)) {
    // On the negative real axis b**(p/2) = I**p * (-b)**(p/2).
    sympified = mapBottomUp(sympified, (a) => a instanceof Pow && a.exp instanceof Rational && a.exp.q === 2n && isNegative(a.base) === true
      ? mul(pow(S.I, a.exp.p), pow(mul(-1, a.base), a.exp)) : a);
  }
  const original = collectAbs(signsimp(mapBottomUp(sympified, t => {
    if (!isExpPow(t) || !t.exp.has(S.Pi) || !t.exp.has(S.I)) return t;
    const cycles = cancel(mul(t.exp, pow(mul(2, S.Pi, S.I), -1)));
    return isIntegerQ(cycles) === true ? S.One : t;
  })));
  // deep simplification: the arguments of the nodes other than sums, products and powers
  let signed = absorbSign(original);
  if (hasFn(signed, SIGN) && hasFn(signed, ABS)) {
    const distributed = expand(signed);
    const absorbed = absorbSign(distributed);
    if (absorbed.key !== distributed.key) signed = absorbed;
  }
  let expr = mapTopDownUnhandled(signed, (x) => simplify(x, opts));
  if (!(expr instanceof Add || expr instanceof Mul || expr instanceof Pow)) {
    // SymPy log._eval_simplify: the logarithm expanded when that is not longer
    if (expr instanceof Fn && expr.name === 'log') expr = shorter(expand_log(expr), expr);
    return done(expr);
  }
  // Expose a common power of an algebraic base before rational normalization
  // distributes its denominator. The remaining polynomial coefficient may vanish.
  if (expr instanceof Add && some(expr, (e) => e instanceof Pow && e.base instanceof Add && isAlgebraicNumber(e.base) && e.exp instanceof Add)) {
    expr = shorter(expr, expand(expand_power_exp(expr)));
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
  // (Abs(z) or Abs(z**e), as Abs keeps a power of a base of unknown sign)
  const absOf = (absolute: Expr, z: Expr): boolean => {
    if (!(absolute instanceof Fn && absolute.name === 'abs')) return false;
    const a = first(absolute.args);
    return a.equals(z) || (a instanceof Pow && a.base.equals(z));
  };
  if (some(expr, (sign) => sign instanceof Fn && sign.name === 'sign' && some(expr, (absolute) => absOf(absolute, first(sign.args))))) {
    const folded = piecewiseFold(expr.rewrite('Abs', { pattern: ['sign'] }));
    if (folded instanceof Piecewise) return simplifyPiecewise(folded, opts);
  }
  expr = combineConcrete(expr);
  // the functions it contains
  if (hyperexpand && some(expr, (x) => x instanceof Hyper || x instanceof MeijerG)) expr = hyperexpand(expr);
  if (hasFn(expr, KRONECKER)) expr = kroneckersimp(expr);
  if (hasFn(expr, BESSEL)) expr = besselsimp(expr);
  if (hasFn(expr, TRIG_HYP)) expr = trigsimp(expr);
  if (hasFn(expr, LOG)) expr = shorter(expand_log(expr), logcombine(expr), expr);
  if (hasFn(expr, COMBINATORIAL_GAMMA)) expr = combsimp(expr);
  // powers, the cancelled form and the factored or expanded form
  let short = shorter(powsimp(expr, { combine: 'exp', deep: true }), powsimp(expr), expr);
  short = shorter(short, cancel(short));
  short = shorter(short, factorTerms(short), expand_power_exp(expand(short)));
  if (hasFn(short, TRIG_HYP) || some(short, isExpPow)) short = exptrigsimp(short);
  // no hollow 2-argument products c*(a + b)
  expr = mapBottomUp(short, (x) => (x instanceof Mul && x.args.length === 2 && isNum(first(x.args)) && x.args[1] instanceof Add ? mul(...x.args) : x));
  expr = rationalizeDenominator(expr);
  const phased = combinePhases(expr);
  if (phased.key !== expr.key) expr = shorter(expr, phased, expand(phased));
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

const ABS = new Set(['abs']);
const SIGN = new Set(['sign']);
const LOG = new Set(['log']);
const KRONECKER = new Set(['KroneckerDelta']);

/** Combine sums/products over the same or adjacent ranges (SymPy sum_simplify/product_simplify). */
function combineConcrete(e: Expr): Expr {
  return mapBottomUp(e, (node) => {
    if (!(node instanceof Add || node instanceof Mul)) return node;
    const sum = node instanceof Add;
    const kind = sum ? 'Sum' : 'Product';
    const terms = node.args.map((a): Expr => {
      if (!sum || !(a instanceof Mul)) return a;
      const sums = a.args.filter((b): b is Concrete => b instanceof Concrete && b.kind2 === 'Sum');
      if (sums.length !== 1) return a;
      const s = first(sums);
      const c = mul(...a.args.filter((b) => b !== s));
      return s.limits.some(([v]) => c.has(v)) ? a : new Concrete('Sum', [mul(c, s.function), ...s.args.slice(1)]);
    });
    const candidates: Concrete[] = [];
    const others: Expr[] = [];
    for (const term of terms) {
      if (term instanceof Concrete && term.kind2 === kind) candidates.push(term);
      else others.push(term);
    }
    for (let i = 0; i < candidates.length; i++) {
      let a = at(candidates, i);
      for (let j = i + 1; j < candidates.length; j++) {
        const b = at(candidates, j);
        let combined: Concrete | undefined;
        if (a.args.slice(1).map((v) => v.key).join(';') === b.args.slice(1).map((v) => v.key).join(';')) {
          combined = new Concrete(kind, [sum ? add(a.function, b.function) : mul(a.function, b.function), ...a.args.slice(1)]);
        } else if (a.limits.length === 1 && b.limits.length === 1 && a.function.key === b.function.key) {
          for (const [left, right] of [[a, b], [b, a]] as const) {
            const [v, lo, hi] = first(left.limits);
            const [w, bl, bh] = first(right.limits);
            if (v.key === w.key && add(hi, 1).key === bl.key) {
              combined = new Concrete(kind, [a.function, v, lo, bh]);
              break;
            }
          }
        }
        if (combined !== undefined) {
          a = combined;
          candidates[i] = a;
          candidates.splice(j--, 1);
        }
      }
    }
    return sum ? add(...others, ...candidates.map((a) => factorTerms(a))) : mul(...others, ...candidates);
  });
}

/** sign(z)*Abs(z) = z, including z = 0 and nonreal z. */
function absorbSign(e: Expr): Expr {
  return mapBottomUp(e, (t) => {
    if (!(t instanceof Mul)) return t;
    const factors = [...t.args];
    let changed = false;
    for (let i = 0; i < factors.length; i++) {
      const f = factors[i];
      if (!(f instanceof Fn && f.name === 'sign')) continue;
      const z = first(f.args);
      const j = factors.findIndex((a) => a instanceof Fn && a.name === 'abs' && first(a.args).key === z.key);
      if (j >= 0) { factors[i] = z; factors[j] = S.One; changed = true; }
    }
    return changed ? mul(...factors) : t;
  });
}

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
  /** Cancel inverse function pairs formally. */
  inverse?: boolean;
  /** Evaluate Integral, Sum, Product, Derivative and Limit nodes; default true. */
  doit?: boolean;
  /** Rationalize Floats; null restores Floats after simplification. Default false. */
  rational?: boolean | null;
  /** The largest accepted measure(result)/measure(input); default 1.7. */
  ratio?: number;
  /** The size of an expression; default countOps. A number or a numeric expression. */
  measure?: (e: Expr) => number | Expr;
}

impl.simplify = simplify;

/** An algebraic number: rationals and I under sums, products and rational powers. */
const isAlgebraicNumber = (e: Expr): boolean =>
  e instanceof Rational || e === S.I || ((e instanceof Add || e instanceof Mul) && e.args.every(isAlgebraicNumber)) || (e instanceof Pow && e.exp instanceof Rational && isAlgebraicNumber(e.base));

/** An exact zero test for closed algebraic expressions. */
function algebraicZero(e: Expr): boolean {
  if (!isAlgebraicNumber(e)) return false;
  if (expandAll(e).equals(S.Zero)) return true;
  const x = new Dummy('x');
  try {
    return minimalPolynomial(e, x).equals(x);
  } catch {
    return false;
  }
}

/**
 * Tests mathematical equality, returning `'unknown'` when equality cannot be decided.
 *
 * @param lhs - The left-hand side.
 * @param rhs - The right-hand side.
 * @returns The truth value, or `'unknown'` when it cannot be determined.
 * @see SymPy `sympy.core.expr.Expr.equals`
 */
export function exprEquals(lhs: ExprLike, rhs: ExprLike): Truth {
  const a = sympify(lhs), b = sympify(rhs);
  if (a.equals(b)) return true;
  const difference = factorTerms(simplify(sub(a, b)));
  if (difference.equals(S.Zero) || algebraicZero(difference)) return true;
  if (difference.isNumber) return false;
  if (!some(difference, (term) => term instanceof Add || term instanceof ExtensionExpr && term.name === 'Mod')) return false;
  if (difference instanceof Mul) {
    const factors = difference.args.map((factor) => {
      const zero = exprEquals(factor, S.Zero);
      return zero === 'unknown' && isRationalFunction(factor) && isConstantTruth(factor) === false ? false : zero;
    });
    if (factors.includes(true)) return true;
    if (factors.every((value) => value === false)) return false;
  }
  return 'unknown';
}

impl.equalsZero = (e) => algebraicZero(e) || simplify(e).equals(S.Zero) ? true : undefined;

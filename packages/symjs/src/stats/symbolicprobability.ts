// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/stats/symbolic_probability.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.stats.symbolic_probability: Probability, Expectation,
 * Variance, Covariance, Moment and CentralMoment as unevaluated expression
 * nodes. `doit` evaluates them on the probability spaces of their random
 * symbols, `expand` uses the linearity of the expectation, and `rewrite`
 * expresses them through each other, integrals or sums.
 */

import { Add, ExtensionExpr, Mul, Rel, S, Sym } from '../core/nodes';
import type { ExprLike , Expr} from '../core/nodes';
import { add, mul, pow, sub, sympify } from '../core/ops';
import { Eq } from '../core/logic';
import { BoolOp } from '../core/boolalg';
import { Sum } from '../core/concrete';
import { callableClass } from '../core/callable';
import { xreplace } from '../core/traverse';
import { compareKeys, sortKey } from '../printing/sortkey';
import { NotImplementedError } from '../core/errors';
import { at, cast as cast2, defined, first } from '../core/guard';
import { SetExpr, inf, sup } from '../sets/sets';
import { expand } from '../simplify/expand';
import { rewrite } from '../simplify/rewrite';
import { doit } from '../calculus/doit';
import { makeIntegral } from './crv';
import { PSpace, RandomSymbol, dependent, given, isRandom, pspace, randomSymbols, statsClasses } from './rv';
import { BernoulliDistribution } from './frvtypes';

/** Hints of doit (SymPy keyword arguments). */
export interface ProbabilityDoitHints {
  /** false: the argument is not evaluated first (SymPy deep=False). */
  readonly deep?: boolean;
  /** false: integrals and sums are left unevaluated (SymPy evaluate=False). */
  readonly evaluate?: boolean;
}

/** The probability space is SymPy's PSpace() of a random symbol without a space. */
const isEmptySpace = (ps: PSpace): boolean => ps.key === new PSpace().key;

/** The random factors and the other factors of a product (SymPy is_random split of Mul.args). */
function splitRandom(e: Mul): [Expr[], Expr[]] {
  return [e.args.filter((a) => isRandom(a)), e.args.filter((a) => !isRandom(a))];
}

/** A relational or boolean (SymPy isinstance(x, (Relational, Boolean))). */
const isBoolean = (e: Expr): boolean => e instanceof Rel || e instanceof BoolOp || e === S.true || e === S.false;

/** The arguments with an optional condition. */
const withCondition = (args: readonly Expr[], condition: Expr | undefined): Expr[] => (condition === undefined ? [...args] : [...args, condition]);

/** A stats node evaluated by its own doit (SymPy doit(**hints)). */
abstract class StatsNode extends ExtensionExpr {
  override get doitDeep(): boolean {
    return false;
  }
  override doitSelf(): Expr {
    return this.doit();
  }
  /** The value (SymPy doit). */
  abstract doit(hints?: ProbabilityDoitHints): Expr;
  /** The node as an integral (or sum), evaluated (SymPy evaluate_integral). */
  evaluateIntegral(): Expr {
    return doit(rewrite(this, 'Integral'));
  }
  /** SymPy evaluate_sum (the same as evaluate_integral). */
  evaluateSum(): Expr {
    return this.evaluateIntegral();
  }
}

// ---------------------------------------------------------------------------
// Probability
// ---------------------------------------------------------------------------

/** SymPy Probability(prob, condition): the unevaluated probability of a condition. */
export class ProbabilityNode extends StatsNode {
  constructor(args: readonly Expr[]) {
    super('Probability', args);
  }
  /** The given condition, if any. */
  get condition(): Expr | undefined {
    return this.args[1];
  }
  withArgs(args: readonly Expr[]): Expr {
    return new ProbabilityNode(args);
  }
  /** The probability (SymPy Probability.doit). */
  doit(hints: ProbabilityDoitHints = {}): Expr {
    const condition = at(this.args, 0);
    const givenCondition = this.condition;
    if (condition instanceof BoolOp && condition.op === 'Not') {
      return sub(1, new ProbabilityNode(withCondition([at(condition.args, 0)], givenCondition)).doit(hints));
    }
    if (givenCondition instanceof RandomSymbol) {
      const condrv = randomSymbols(condition);
      if (condrv.length === 1 && first(condrv).key === givenCondition.key) {
        return new BernoulliDistribution([new ProbabilityNode([condition]).doit(hints), S.Zero, S.One]);
      }
      if (condrv.some((rv) => dependent(rv, givenCondition))) return new ProbabilityNode([condition, givenCondition]);
      return new ProbabilityNode([condition]).doit();
    }
    if (givenCondition !== undefined && !isBoolean(givenCondition)) throw new RangeError(`${givenCondition.toString()} is not a relational or combination of relationals`);
    if (givenCondition === S.false || condition === S.false) return S.Zero;
    if (!isBoolean(condition)) throw new RangeError(`${condition.toString()} is not a relational or combination of relationals`);
    if (condition === S.true) return S.One;
    if (givenCondition !== undefined) return new ProbabilityNode([given(condition, givenCondition)]).doit(hints);
    const ps = pspace(condition);
    if (isEmptySpace(ps)) return new ProbabilityNode([condition]);
    const result = ps.probability(condition);
    return hints.evaluate ?? true ? doit(result) : result;
  }
  /** SymPy _eval_rewrite_as_Integral and _eval_rewrite_as_Sum: the unevaluated probability. */
  override rewriteSelf(target: string, args: readonly Expr[]): Expr | undefined {
    if (target === 'Integral' || target === 'Sum') return new ProbabilityNode(args).doit({ evaluate: false });
    return undefined;
  }
}

/** SymPy Probability(prob, condition=None). */
export const Probability = /* @__PURE__ */ callableClass(
  ProbabilityNode,
  (prob: ExprLike | boolean, condition?: ExprLike | boolean): ProbabilityNode =>
    new ProbabilityNode(withCondition([toExpr(prob)], condition === undefined ? undefined : toExpr(condition))),
);
export type Probability = ProbabilityNode;

/** A boolean or expression as an expression. */
const toExpr = (v: ExprLike | boolean): Expr => (typeof v === 'boolean' ? (v ? S.true : S.false) : sympify(v));

// ---------------------------------------------------------------------------
// Expectation
// ---------------------------------------------------------------------------

/** SymPy Expectation(expr, condition): the unevaluated expectation of a random expression. */
export class ExpectationNode extends StatsNode {
  constructor(args: readonly Expr[]) {
    super('Expectation', args);
  }
  /** The given condition, if any. */
  get condition(): Expr | undefined {
    return this.args[1];
  }
  withArgs(args: readonly Expr[]): Expr {
    return makeExpectation(at(args, 0), args[1]);
  }
  protected override computeCommutative(): boolean {
    return at(this.args, 0).isCommutative;
  }
  /** The expectation of each term and of the random factors of products (SymPy Expectation.expand). */
  expand(): Expr {
    const e = at(this.args, 0);
    const condition = this.condition;
    if (!isRandom(e)) return e;
    if (e instanceof Add) return add(...e.args.map((a) => expandExpectation(makeExpectation(a, condition))));
    const expandExpr = expand(e);
    if (expandExpr instanceof Add) return add(...expandExpr.args.map((a) => expandExpectation(makeExpectation(a, condition))));
    if (e instanceof Mul) {
      const [rv, nonrv] = splitRandom(e);
      return mul(...nonrv, makeExpectation(mul(...rv), condition));
    }
    return this;
  }
  override expandTop(): Expr {
    return this.expand();
  }
  /** The expected value (SymPy Expectation.doit). */
  doit(hints: ProbabilityDoitHints = {}): Expr {
    const deep = hints.deep ?? true;
    const condition = this.condition;
    const evaluate = hints.evaluate ?? true;
    let e = at(this.args, 0);
    if (deep) e = doit(e);
    if (!isRandom(e) || e instanceof ExpectationNode) return e;
    if (condition !== undefined) return doitExpectation(makeExpectation(given(e, condition)), hints);
    if (e instanceof Add) {
      return add(...e.args.map((a) => (a instanceof ExpectationNode ? makeExpectation(a, condition) : doitExpectation(makeExpectation(a, condition), hints))));
    }
    if (e instanceof Mul && hasExpectation(e)) return e;
    const ps = pspace(e);
    if (isEmptySpace(ps)) return makeExpectation(e);
    const result = ps.computeExpectation(e, undefined, { evaluate });
    return evaluate ? doit(result) : result;
  }
  /** SymPy _eval_rewrite_as_Probability, _eval_rewrite_as_Integral and _eval_rewrite_as_Sum. */
  override rewriteSelf(target: string, args: readonly Expr[]): Expr | undefined {
    const [arg, condition] = [at(args, 0), args[1]];
    if (target === 'Integral' || target === 'Sum') return doitExpectation(makeExpectation(arg, condition), { deep: false, evaluate: false });
    if (target !== 'Probability') return undefined;
    const rvs = randomSymbols(arg);
    if (rvs.length > 1) throw new NotImplementedError('rewrite(Probability) of an expectation of several random symbols');
    if (rvs.length === 0) return arg;
    const rv = first(rvs);
    const name = rv.symbol.name;
    const symbol = /^[A-Z]/.test(name) ? new Sym(name.toLowerCase()) : new Sym(`${name}_1`);
    const body = mul(xreplace(arg, [[rv, symbol]]), new ProbabilityNode(withCondition([Eq(rv, symbol)], condition)));
    if (rv.pspace.isContinuous) return makeIntegral(body, [[symbol, inf(rv.pspace.domain.set), sup(rv.pspace.domain.set)]]);
    if (rv.pspace.isFinite) throw new NotImplementedError('rewrite(Probability) of an expectation of a finite random symbol');
    return Sum(body, [symbol, inf(rv.pspace.domain.set), sup(spaceSet(rv.pspace))]);
  }
}

/** The set of a single space (SymPy pspace.set). */
function spaceSet(ps: PSpace): SetExpr {
  return cast2((ps as PSpace & { set?: unknown }).set, SetExpr, 'set of the probability space');
}

/** An Expectation expanded, or the value it already is (SymPy Expectation(a).expand() of a constant a). */
const expandExpectation = (e: Expr): Expr => (e instanceof ExpectationNode ? e.expand() : expand(e));

/** An Expectation evaluated with the hints, or the value it already is. */
const doitExpectation = (e: Expr, hints: ProbabilityDoitHints): Expr => (e instanceof ExpectationNode ? e.doit(hints) : e);

/** The expression contains an Expectation (SymPy expr.atoms(Expectation)). */
const hasExpectation = (e: Expr): boolean => e instanceof ExpectationNode || e.args.some(hasExpectation);

/** SymPy Expectation(expr, condition=None): a value that is not random is its own expectation. */
export function makeExpectation(exprIn: ExprLike, conditionIn?: ExprLike): Expr {
  const e = sympify(exprIn);
  if (conditionIn === undefined) return isRandom(e) ? new ExpectationNode([e]) : e;
  return new ExpectationNode([e, sympify(conditionIn)]);
}

/** SymPy Expectation(expr, condition=None). */
export const Expectation = /* @__PURE__ */ callableClass(ExpectationNode, makeExpectation);
export type Expectation = ExpectationNode;

// ---------------------------------------------------------------------------
// Variance and Covariance
// ---------------------------------------------------------------------------

/** The hooks of rv_interface (variance and covariance with evaluate=False). */
export const interfaceHooks: {
  variance?: (x: Expr, condition: Expr | undefined, evaluate: boolean) => Expr;
  covariance?: (x: Expr, y: Expr, condition: Expr | undefined, evaluate: boolean) => Expr;
} = {};

/** SymPy Variance(arg, condition): the unevaluated variance of a random expression. */
export class VarianceNode extends StatsNode {
  constructor(args: readonly Expr[]) {
    super('Variance', args);
  }
  /** The given condition, if any. */
  get condition(): Expr | undefined {
    return this.args[1];
  }
  withArgs(args: readonly Expr[]): Expr {
    return new VarianceNode(args);
  }
  protected override computeCommutative(): boolean {
    return at(this.args, 0).isCommutative;
  }
  /** The variances and covariances of the terms (SymPy Variance.expand). */
  expand(): Expr {
    const arg = at(this.args, 0);
    const condition = this.condition;
    if (!isRandom(arg)) return S.Zero;
    if (arg instanceof RandomSymbol) return this;
    if (arg instanceof Add) {
      const rv = arg.args.filter((a) => isRandom(a));
      const variances = add(...rv.map((xv) => new VarianceNode(withCondition([xv], condition)).expand()));
      const covariances: Expr[] = [];
      for (let i = 0; i < rv.length; i++) {
        for (let j = i + 1; j < rv.length; j++) covariances.push(mul(2, cov(at(rv, i), at(rv, j), condition).expand()));
      }
      return add(variances, ...covariances);
    }
    if (arg instanceof Mul) {
      const [rv, nonrv] = splitRandom(arg);
      return mul(...nonrv.map((a) => pow(a, 2)), new VarianceNode(withCondition([mul(...rv)], condition)));
    }
    return this;
  }
  override expandTop(): Expr {
    return this.expand();
  }
  /** SymPy Variance.doit (Basic.doit: the variance is not evaluated, only its arguments). */
  doit(): Expr {
    return new VarianceNode(this.args.map((a) => doit(a)));
  }
  override rewriteSelf(target: string, args: readonly Expr[]): Expr | undefined {
    const [arg, condition] = [at(args, 0), args[1]];
    if (target === 'Expectation') return sub(makeExpectation(pow(arg, 2), condition), pow(makeExpectation(arg, condition), 2));
    if (target === 'Probability') return rewrite(rewrite(new VarianceNode(args), 'Expectation'), 'Probability');
    if (target === 'Integral' || target === 'Sum') return defined(interfaceHooks.variance, 'rv_interface')(at(this.args, 0), this.condition, false);
    return undefined;
  }
}

/** SymPy Variance(arg, condition=None). */
export const Variance = /* @__PURE__ */ callableClass(
  VarianceNode,
  (arg: ExprLike, condition?: ExprLike): VarianceNode => new VarianceNode(withCondition([sympify(arg)], condition === undefined ? undefined : sympify(condition))),
);
export type Variance = VarianceNode;

/** The two arguments in default_sort_key order. */
const sorted2 = (a: Expr, b: Expr): [Expr, Expr] => (compareKeys(sortKey(a), sortKey(b)) <= 0 ? [a, b] : [b, a]);

/** SymPy Covariance(arg1, arg2, condition): the unevaluated covariance of two random expressions. */
export class CovarianceNode extends StatsNode {
  constructor(args: readonly Expr[]) {
    super('Covariance', args);
  }
  /** The given condition, if any. */
  get condition(): Expr | undefined {
    return this.args[2];
  }
  withArgs(args: readonly Expr[]): Expr {
    return new CovarianceNode(args);
  }
  protected override computeCommutative(): boolean {
    return at(this.args, 0).isCommutative;
  }
  /** The covariances of the random terms (SymPy Covariance.expand). */
  expand(): Expr {
    const [a1, a2] = [at(this.args, 0), at(this.args, 1)];
    const condition = this.condition;
    if (a1.key === a2.key) return new VarianceNode(withCondition([a1], condition)).expand();
    if (!isRandom(a1) || !isRandom(a2)) return S.Zero;
    const [arg1, arg2] = sorted2(a1, a2);
    if (arg1 instanceof RandomSymbol && arg2 instanceof RandomSymbol) return cov(arg1, arg2, condition);
    const list1 = expandSingleArgument(expand(arg1));
    const list2 = expandSingleArgument(expand(arg2));
    return add(...list1.flatMap(([a, r1]) => list2.map(([b, r2]) => mul(a, b, cov(r1, r2, condition)))));
  }
  override expandTop(): Expr {
    return this.expand();
  }
  /** SymPy Covariance.doit (Basic.doit: only the arguments are evaluated). */
  doit(): Expr {
    return new CovarianceNode(this.args.map((a) => doit(a)));
  }
  override rewriteSelf(target: string, args: readonly Expr[]): Expr | undefined {
    const [arg1, arg2, condition] = [at(args, 0), at(args, 1), args[2]];
    if (target === 'Expectation') return sub(makeExpectation(mul(arg1, arg2), condition), mul(makeExpectation(arg1, condition), makeExpectation(arg2, condition)));
    if (target === 'Probability') return rewrite(rewrite(new CovarianceNode(args), 'Expectation'), 'Probability');
    if (target === 'Integral' || target === 'Sum') return defined(interfaceHooks.covariance, 'rv_interface')(at(this.args, 0), at(this.args, 1), this.condition, false);
    return undefined;
  }
}

/** SymPy Covariance(*sorted(...), condition=condition). */
function cov(a: Expr, b: Expr, condition: Expr | undefined): CovarianceNode {
  return new CovarianceNode(withCondition(sorted2(a, b), condition));
}

/** The (coefficient, random part) pairs of the terms (SymPy _expand_single_argument). */
function expandSingleArgument(e: Expr): [Expr, Expr][] {
  if (e instanceof RandomSymbol) return [[S.One, e]];
  if (e instanceof Add) {
    const out: [Expr, Expr][] = [];
    for (const a of e.args) {
      if (a instanceof Mul) out.push(mulNonrvRv(a));
      else if (isRandom(a)) out.push([S.One, a]);
    }
    return out;
  }
  if (e instanceof Mul) return [mulNonrvRv(e)];
  return [[S.One, e]];
}

/** The non-random and random factors of a product (SymPy _get_mul_nonrv_rv_tuple). */
function mulNonrvRv(m: Mul): [Expr, Expr] {
  const [rv, nonrv] = splitRandom(m);
  return [mul(...nonrv), mul(...rv)];
}

/** SymPy Covariance(arg1, arg2, condition=None, evaluate=True): the arguments are sorted unless evaluate is false. */
export const Covariance = /* @__PURE__ */ callableClass(
  CovarianceNode,
  (arg1: ExprLike, arg2: ExprLike, condition?: ExprLike, opts: { evaluate?: boolean } = {}): CovarianceNode => {
    const [a, b] = [sympify(arg1), sympify(arg2)];
    const args = opts.evaluate ?? true ? sorted2(a, b) : [a, b];
    return new CovarianceNode(withCondition(args, condition === undefined ? undefined : sympify(condition)));
  },
);
export type Covariance = CovarianceNode;

// ---------------------------------------------------------------------------
// Moments
// ---------------------------------------------------------------------------

/** SymPy Moment(X, n, c=0, condition=None): the unevaluated n-th moment of X about c. */
export class MomentNode extends StatsNode {
  constructor(args: readonly Expr[]) {
    super('Moment', args);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new MomentNode(args);
  }
  /** The moment (SymPy Moment.doit: the expectation, evaluated). */
  doit(hints: ProbabilityDoitHints = {}): Expr {
    return doitExpectation(rewrite(this, 'Expectation'), hints);
  }
  override rewriteSelf(target: string, args: readonly Expr[]): Expr | undefined {
    const [X, n, c, condition] = [at(args, 0), at(args, 1), at(args, 2), args[3]];
    if (target === 'Expectation') return makeExpectation(pow(sub(X, c), n), condition);
    if (target === 'Probability' || target === 'Integral') return rewrite(rewrite(new MomentNode(args), 'Expectation'), target);
    return undefined;
  }
}

/** SymPy Moment(X, n, c=0, condition=None). */
export const Moment = /* @__PURE__ */ callableClass(
  MomentNode,
  (X: ExprLike, n: ExprLike, c: ExprLike = 0, condition?: ExprLike): MomentNode =>
    new MomentNode(withCondition([sympify(X), sympify(n), sympify(c)], condition === undefined ? undefined : sympify(condition))),
);
export type Moment = MomentNode;

/** SymPy CentralMoment(X, n, condition=None): the unevaluated n-th moment of X about its mean. */
export class CentralMomentNode extends StatsNode {
  constructor(args: readonly Expr[]) {
    super('CentralMoment', args);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new CentralMomentNode(args);
  }
  /** The central moment (SymPy CentralMoment.doit). */
  doit(hints: ProbabilityDoitHints = {}): Expr {
    return doitExpectation(rewrite(this, 'Expectation'), hints);
  }
  override rewriteSelf(target: string, args: readonly Expr[]): Expr | undefined {
    const [X, n, condition] = [at(args, 0), at(args, 1), args[2]];
    if (target === 'Expectation') {
      const mu = makeExpectation(X, condition);
      return rewrite(new MomentNode(withCondition([X, n, mu], condition)), 'Expectation');
    }
    if (target === 'Probability' || target === 'Integral') return rewrite(rewrite(new CentralMomentNode(args), 'Expectation'), target);
    return undefined;
  }
}

/** SymPy CentralMoment(X, n, condition=None). */
export const CentralMoment = /* @__PURE__ */ callableClass(
  CentralMomentNode,
  (X: ExprLike, n: ExprLike, condition?: ExprLike): CentralMomentNode =>
    new CentralMomentNode(withCondition([sympify(X), sympify(n)], condition === undefined ? undefined : sympify(condition))),
);
export type CentralMoment = CentralMomentNode;


statsClasses.expectation = (e, condition, evaluate) => {
  const node = makeExpectation(e, condition);
  return evaluate ? doitExpectation(node, {}) : node;
};
statsClasses.probability = (condition, givenCondition, evaluate) => {
  const node = new ProbabilityNode(withCondition([condition], givenCondition));
  return evaluate ? node.doit() : node;
};
statsClasses.probabilityNode = (condition) => new ProbabilityNode([condition]);

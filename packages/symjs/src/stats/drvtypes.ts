// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/stats/drv_types.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.stats.drv_types: the discrete distributions on the
 * integers and the functions that create random symbols with them
 * (`Poisson('X', lamda)`, `Geometric('X', p)`, ...).
 */

import { Dummy, S, Sym } from '../core/nodes';
import type { ExprLike , Expr} from '../core/nodes';
import { add, exp, mul, pow, sqrt, sub, sympify } from '../core/ops';
import { Eq, Ge, Gt, Lt, piecewise } from '../core/logic';
import { Lambda, LambdaNode } from '../core/lambda';
import { Sum } from '../core/concrete';
import { isNonNegative } from '../core/assumptions';
import { NotImplementedError } from '../core/errors';
import { at, cast, defined } from '../core/guard';
import { Integers, Naturals, Naturals0, SetExpr, asRelational, inf, sup } from '../sets/sets';
import { log } from '../functions/elementary/elementary';
import { beta, binomial, factorial, floor, zeta } from '../functions/special/special';
import { besseli } from '../functions/special/bessel';
import { hyper } from '../functions/special/hyper';
import { polylog } from '../functions/special/zetafunctions';
import { doit } from '../calculus/doit';
import { Fn } from '../core/nodes';
import { isPositive, isIntegerQ as isIntegerValued } from '../core/assumptions';
import { isRandom, statsClasses, valueCheck } from './rv';
import type { ComputeOptions , RandomSymbol} from './rv';
import { SingleDiscreteDistribution, SingleDiscretePSpace } from './drv';
import type { ClosedForm } from './crv';
import type { RVOptions } from './crvtypes';

const neg = (e: ExprLike): Expr => mul(-1, e);
const div = (a: ExprLike, b: ExprLike): Expr => mul(a, pow(b, -1));

/** A discrete distribution class (constructed from its parameters). */
type DistributionClass = new (args: readonly Expr[]) => SingleDiscreteDistribution;

/** A random symbol with the distribution of the parameters (SymPy rv of drv_types). */
export function rv(symbol: string | Sym, cls: DistributionClass, params: readonly ExprLike[], opts: RVOptions = {}): RandomSymbol {
  const args = params.map(sympify);
  const dist = new cls(args);
  if (opts.check ?? true) dist.check();
  if (args.some((a) => isRandom(a))) return defined(statsClasses.compound, 'compound_rv')(symbol, dist);
  return new SingleDiscretePSpace([typeof symbol === 'string' ? new Sym(symbol) : symbol, dist]).value;
}

/** SymPy DiscreteDistributionHandmade(pdf, set): a distribution given by a Lambda mass function on a set. */
export class DiscreteDistributionHandmade extends SingleDiscreteDistribution {
  constructor(args: readonly Expr[]) {
    super('DiscreteDistributionHandmade', args.length === 1 ? [at(args, 0), Integers] : args);
  }
  override get set(): SetExpr {
    return cast(this.arg(1), SetExpr);
  }
  pdf(x: ExprLike): Expr {
    return cast(this.arg(0), LambdaNode, 'pdf').call(x);
  }
  override check(): void {
    const x = new Dummy('x');
    const val = doit(Sum(this.pdf(x), [x, inf(this.set), sup(this.set)]));
    valueCheck(Eq(val, 1) !== S.false, 'The pdf is incorrect on the given set.');
  }
}

/**
 * A discrete random variable with the given mass function on a set of
 * integers (SymPy DiscreteRV(symbol, density, set)). The mass function is
 * not checked unless `check` is true.
 */
export function DiscreteRV(symbol: Sym, densityIn: ExprLike, set: SetExpr = Integers, opts: RVOptions = {}): RandomSymbol {
  const pdf = Lambda(symbol, piecewise([densityIn, asRelational(set, symbol)], [0, true]));
  return rv(symbol.name, DiscreteDistributionHandmade, [pdf, set], { check: opts.check ?? false });
}

/** SymPy FlorySchulzDistribution(a). */
export class FlorySchulzDistribution extends SingleDiscreteDistribution {
  constructor(args: readonly Expr[]) {
    super('FlorySchulzDistribution', args);
  }
  override get set(): SetExpr {
    return Naturals;
  }
  override check(): void {
    const a = this.arg(0);
    valueCheck([Lt(0, a), Lt(a, 1)], 'a must be between 0 and 1');
  }
  pdf(kIn: ExprLike): Expr {
    const k = sympify(kIn);
    const a = this.arg(0);
    return mul(pow(a, 2), k, pow(sub(1, a), sub(k, 1)));
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    const a = this.arg(0);
    return div(mul(pow(a, 2), exp(mul(S.I, t))), pow(add(1, mul(sub(a, 1), exp(mul(S.I, t)))), 2));
  }
  protected override momentGeneratingFunctionClosed(t: Expr): ClosedForm {
    const a = this.arg(0);
    return div(mul(pow(a, 2), exp(t)), pow(add(1, mul(sub(a, 1), exp(t))), 2));
  }
}

/** Flory-Schulz distribution (SymPy FlorySchulz(name, a)). */
export function FlorySchulz(name: string | Sym, a: ExprLike): RandomSymbol {
  return rv(name, FlorySchulzDistribution, [a]);
}

/** SymPy GeometricDistribution(p). */
export class GeometricDistribution extends SingleDiscreteDistribution {
  constructor(args: readonly Expr[]) {
    super('GeometricDistribution', args);
  }
  override get set(): SetExpr {
    return Naturals;
  }
  override check(): void {
    const p = this.arg(0);
    valueCheck([Lt(0, p), Ge(1, p)], 'p must be between 0 and 1');
  }
  pdf(kIn: ExprLike): Expr {
    const k = sympify(kIn);
    const p = this.arg(0);
    return mul(pow(sub(1, p), sub(k, 1)), p);
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    const p = this.arg(0);
    return div(mul(p, exp(mul(S.I, t))), sub(1, mul(sub(1, p), exp(mul(S.I, t)))));
  }
  protected override momentGeneratingFunctionClosed(t: Expr): ClosedForm {
    const p = this.arg(0);
    return div(mul(p, exp(t)), sub(1, mul(sub(1, p), exp(t))));
  }
}

/** Geometric distribution (SymPy Geometric(name, p)). */
export function Geometric(name: string | Sym, p: ExprLike): RandomSymbol {
  return rv(name, GeometricDistribution, [p]);
}

/** SymPy HermiteDistribution(a1, a2). */
export class HermiteDistribution extends SingleDiscreteDistribution {
  constructor(args: readonly Expr[]) {
    super('HermiteDistribution', args);
  }
  override get set(): SetExpr {
    return Naturals0;
  }
  override check(): void {
    valueCheck(isNonNegative(this.arg(0)), 'Parameter a1 must be >= 0.');
    valueCheck(isNonNegative(this.arg(1)), 'Parameter a2 must be >= 0.');
  }
  pdf(kIn: ExprLike): Expr {
    const k = sympify(kIn);
    const [a1, a2] = [this.arg(0), this.arg(1)];
    const term1 = exp(neg(add(a1, a2)));
    const j = new Dummy('j', { integer: true });
    const num = mul(pow(a1, sub(k, mul(2, j))), pow(a2, j));
    const den = mul(factorial(sub(k, mul(2, j))), factorial(j));
    return mul(term1, doit(Sum(div(num, den), [j, 0, floor(div(k, 2))])));
  }
  protected override momentGeneratingFunctionClosed(t: Expr): ClosedForm {
    const [a1, a2] = [this.arg(0), this.arg(1)];
    return exp(add(mul(a1, sub(exp(t), 1)), mul(a2, sub(exp(mul(2, t)), 1))));
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    const [a1, a2] = [this.arg(0), this.arg(1)];
    return exp(add(mul(a1, sub(exp(mul(S.I, t)), 1)), mul(a2, sub(exp(mul(2, S.I, t)), 1))));
  }
}

/** Hermite distribution (SymPy Hermite(name, a1, a2)). */
export function Hermite(name: string | Sym, a1: ExprLike, a2: ExprLike): RandomSymbol {
  return rv(name, HermiteDistribution, [a1, a2]);
}

/** SymPy LogarithmicDistribution(p). */
export class LogarithmicDistribution extends SingleDiscreteDistribution {
  constructor(args: readonly Expr[]) {
    super('LogarithmicDistribution', args);
  }
  override get set(): SetExpr {
    return Naturals;
  }
  override check(): void {
    const p = this.arg(0);
    valueCheck([Gt(p, 0), Lt(p, 1)], 'p should be between 0 and 1');
  }
  pdf(kIn: ExprLike): Expr {
    const k = sympify(kIn);
    const p = this.arg(0);
    return div(mul(-1, pow(p, k)), mul(k, log(sub(1, p))));
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    const p = this.arg(0);
    return div(log(sub(1, mul(p, exp(mul(S.I, t))))), log(sub(1, p)));
  }
  protected override momentGeneratingFunctionClosed(t: Expr): ClosedForm {
    const p = this.arg(0);
    return div(log(sub(1, mul(p, exp(t)))), log(sub(1, p)));
  }
}

/** Logarithmic distribution (SymPy Logarithmic(name, p)). */
export function Logarithmic(name: string | Sym, p: ExprLike): RandomSymbol {
  return rv(name, LogarithmicDistribution, [p]);
}

/** SymPy NegativeBinomialDistribution(r, p). */
export class NegativeBinomialDistribution extends SingleDiscreteDistribution {
  constructor(args: readonly Expr[]) {
    super('NegativeBinomialDistribution', args);
  }
  override get set(): SetExpr {
    return Naturals0;
  }
  override check(): void {
    const [r, p] = [this.arg(0), this.arg(1)];
    valueCheck(Gt(r, 0), 'r should be positive');
    valueCheck([Gt(p, 0), Lt(p, 1)], 'p should be between 0 and 1');
  }
  pdf(kIn: ExprLike): Expr {
    const k = sympify(kIn);
    const [r, p] = [this.arg(0), this.arg(1)];
    return mul(binomial(add(k, r, -1), k), pow(sub(1, p), k), pow(p, r));
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    const [r, p] = [this.arg(0), this.arg(1)];
    return pow(div(p, sub(1, mul(sub(1, p), exp(mul(S.I, t))))), r);
  }
  protected override momentGeneratingFunctionClosed(t: Expr): ClosedForm {
    const [r, p] = [this.arg(0), this.arg(1)];
    return pow(div(p, sub(1, mul(sub(1, p), exp(t)))), r);
  }
}

/** Negative binomial distribution (SymPy NegativeBinomial(name, r, p)). */
export function NegativeBinomial(name: string | Sym, r: ExprLike, p: ExprLike): RandomSymbol {
  return rv(name, NegativeBinomialDistribution, [r, p]);
}

/** SymPy PoissonDistribution(lamda). */
export class PoissonDistribution extends SingleDiscreteDistribution {
  constructor(args: readonly Expr[]) {
    super('PoissonDistribution', args);
  }
  get lamda(): Expr {
    return this.arg(0);
  }
  override get set(): SetExpr {
    return Naturals0;
  }
  override check(): void {
    valueCheck(Gt(this.lamda, 0), 'Lambda must be positive');
  }
  pdf(kIn: ExprLike): Expr {
    const k = sympify(kIn);
    return mul(div(pow(this.lamda, k), factorial(k)), exp(neg(this.lamda)));
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    return exp(mul(this.lamda, sub(exp(mul(S.I, t)), 1)));
  }
  protected override momentGeneratingFunctionClosed(t: Expr): ClosedForm {
    return exp(mul(this.lamda, sub(exp(t), 1)));
  }
  /** SymPy PoissonDistribution.expectation: E(X) = lamda and E(ff(X, n)) = lamda**n. */
  override expectation(expr: Expr, v: Sym, opts: ComputeOptions = {}): Expr {
    if (opts.evaluate ?? true) {
      if (expr.key === v.key) return this.lamda;
      if (expr instanceof Fn && expr.name === 'ff' && isIntegerValued(at(expr.args, 1)) === true && isPositive(at(expr.args, 1)) === true && at(expr.args, 0).key === v.key) {
        return pow(this.lamda, at(expr.args, 1));
      }
    }
    return super.expectation(expr, v, opts);
  }
}

/** Poisson distribution (SymPy Poisson(name, lamda)). */
export function Poisson(name: string | Sym, lamda: ExprLike): RandomSymbol {
  return rv(name, PoissonDistribution, [lamda]);
}

/** SymPy SkellamDistribution(mu1, mu2). */
export class SkellamDistribution extends SingleDiscreteDistribution {
  constructor(args: readonly Expr[]) {
    super('SkellamDistribution', args);
  }
  override check(): void {
    valueCheck(Ge(this.arg(0), 0), 'Parameter mu1 must be >= 0');
    valueCheck(Ge(this.arg(1), 0), 'Parameter mu2 must be >= 0');
  }
  pdf(kIn: ExprLike): Expr {
    const k = sympify(kIn);
    const [mu1, mu2] = [this.arg(0), this.arg(1)];
    const term1 = mul(exp(neg(add(mu1, mu2))), pow(div(mu1, mu2), div(k, 2)));
    const term2 = besseli(k, mul(2, sqrt(mul(mu1, mu2))));
    return mul(term1, term2);
  }
  protected override cdfClosed(_x: Expr): ClosedForm {
    throw new NotImplementedError("Skellam doesn't have closed form for the CDF.");
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    const [mu1, mu2] = [this.arg(0), this.arg(1)];
    return exp(add(neg(add(mu1, mu2)), mul(mu1, exp(mul(S.I, t))), mul(mu2, exp(mul(-1, S.I, t)))));
  }
  protected override momentGeneratingFunctionClosed(t: Expr): ClosedForm {
    const [mu1, mu2] = [this.arg(0), this.arg(1)];
    return exp(add(neg(add(mu1, mu2)), mul(mu1, exp(t)), mul(mu2, exp(neg(t)))));
  }
}

/** Skellam distribution (SymPy Skellam(name, mu1, mu2)). */
export function Skellam(name: string | Sym, mu1: ExprLike, mu2: ExprLike): RandomSymbol {
  return rv(name, SkellamDistribution, [mu1, mu2]);
}

/** SymPy YuleSimonDistribution(rho). */
export class YuleSimonDistribution extends SingleDiscreteDistribution {
  constructor(args: readonly Expr[]) {
    super('YuleSimonDistribution', args);
  }
  override get set(): SetExpr {
    return Naturals;
  }
  override check(): void {
    valueCheck(Gt(this.arg(0), 0), 'rho should be positive');
  }
  pdf(kIn: ExprLike): Expr {
    const k = sympify(kIn);
    const rho = this.arg(0);
    return mul(rho, beta(k, add(rho, 1)));
  }
  protected override cdfClosed(x: Expr): ClosedForm {
    const rho = this.arg(0);
    return piecewise([sub(1, mul(floor(x), beta(floor(x), add(rho, 1)))), Ge(x, 1)], [0, true]);
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    const rho = this.arg(0);
    return div(mul(rho, hyper([1, 1], [add(rho, 2)], exp(mul(S.I, t))), exp(mul(S.I, t))), add(rho, 1));
  }
  protected override momentGeneratingFunctionClosed(t: Expr): ClosedForm {
    const rho = this.arg(0);
    return div(mul(rho, hyper([1, 1], [add(rho, 2)], exp(t)), exp(t)), add(rho, 1));
  }
}

/** Yule-Simon distribution (SymPy YuleSimon(name, rho)). */
export function YuleSimon(name: string | Sym, rho: ExprLike): RandomSymbol {
  return rv(name, YuleSimonDistribution, [rho]);
}

/** SymPy ZetaDistribution(s). */
export class ZetaDistribution extends SingleDiscreteDistribution {
  constructor(args: readonly Expr[]) {
    super('ZetaDistribution', args);
  }
  override get set(): SetExpr {
    return Naturals;
  }
  override check(): void {
    valueCheck(Gt(this.arg(0), 1), 's should be greater than 1');
  }
  pdf(kIn: ExprLike): Expr {
    const k = sympify(kIn);
    const s = this.arg(0);
    return pow(mul(pow(k, s), zeta(s)), -1);
  }
  protected override characteristicFunctionClosed(t: Expr): ClosedForm {
    return div(polylog(this.arg(0), exp(mul(S.I, t))), zeta(this.arg(0)));
  }
  protected override momentGeneratingFunctionClosed(t: Expr): ClosedForm {
    return div(polylog(this.arg(0), exp(t)), zeta(this.arg(0)));
  }
}

/** Zeta distribution (SymPy Zeta(name, s)). */
export function Zeta(name: string | Sym, s: ExprLike): RandomSymbol {
  return rv(name, ZetaDistribution, [s]);
}

statsClasses.discreteHandmade = (pdf) => new DiscreteDistributionHandmade([pdf]);

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/stats/frv_types.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.stats.frv_types: the finite distributions and the
 * functions that create random symbols with them (`Die('D', 6)`,
 * `Coin('C')`, `Binomial('X', n, p)`, ...).
 */

import { Dummy, Float, Rational, S, Sym, asRational } from '../core/nodes';
import type { ExprLike , Expr} from '../core/nodes';
import { add, mul, pow, sub, sympify } from '../core/ops';
import { Eq, Ge, Gt, Le, Lt, piecewise } from '../core/logic';
import { and, or } from '../core/boolalg';
import { Lambda } from '../core/lambda';
import { DictNode, Dict } from '../core/containers';
import { isIntegerQ as isIntegerValued, isNonNegative, isPositive } from '../core/assumptions';
import { at, cast, defined } from '../core/guard';
import type { SetExpr} from '../sets/sets';
import { FiniteSet, Integers, Naturals0, contains, finiteSet, intersection, interval } from '../sets/sets';
import { log } from '../functions/elementary/elementary';
import { beta as betaFn, binomial } from '../functions/special/special';
import { FiniteDensity, isRandom, statsClasses, valueCheck } from './rv';
import type { DensityResult , RandomSymbol} from './rv';
import { Density } from './rv';
import { SingleFiniteDistribution, SingleFinitePSpace } from './frv';
import type { RVOptions } from './crvtypes';

/** A finite distribution class (constructed from its parameters). */
type DistributionClass = new (args: readonly Expr[]) => SingleFiniteDistribution;

/** A random symbol with the distribution of the parameters (SymPy rv of frv_types). */
export function rv(name: string | Sym, cls: DistributionClass, params: readonly ExprLike[], opts: RVOptions = {}): RandomSymbol {
  const args = params.map(sympify);
  const dist = new cls(args);
  if (opts.check ?? true) dist.check();
  if (args.some((a) => isRandom(a))) return defined(statsClasses.compound, 'compound_rv')(name, dist);
  return new SingleFinitePSpace([typeof name === 'string' ? new Sym(name) : name, dist]).value;
}

/** x is a number, a symbol or a random expression (the argument check of the mass functions). */
function checkPmfArgument(x: Expr): void {
  if (!(x.isNumber || x instanceof Sym || isRandom(x))) {
    throw new RangeError(`'x' expected as an argument of type 'number', 'Symbol', or 'RandomSymbol' not ${x.kind}`);
  }
}

/** An integer value as a SymPy Integer. */
const int = (n: number): Expr => Rational.of(n);

/** SymPy FiniteDistributionHandmade(dict): a distribution given by its values and probabilities. */
export class FiniteDistributionHandmade extends SingleFiniteDistribution {
  constructor(args: readonly Expr[]) {
    super('FiniteDistributionHandmade', [cast(at(args, 0), DictNode, 'density dict')]);
  }
  override get dict(): DensityResult {
    return new FiniteDensity(cast(this.arg(0), DictNode).items());
  }
  /** SymPy pmf: Lambda(x, Piecewise((v, Eq(k, x)), ..., (0, True))) (applied to x). */
  pmf(xIn: ExprLike): Expr {
    const x = new Sym('x');
    const f = Lambda(x, piecewise(...cast(this.arg(0), DictNode).items().map(([k, v]) => [v, Eq(k, x)] as const), [S.Zero, true]));
    return f.call(xIn);
  }
  override get set(): SetExpr {
    return finiteSet(...cast(this.arg(0), DictNode).keys());
  }
  override check(): void {
    const items = cast(this.arg(0), DictNode).items();
    for (const [, p] of items) valueCheck([Ge(p, 0), Le(p, 1)], 'Probability at a point must be between 0 and 1.');
    const val = add(...items.map(([, p]) => p));
    valueCheck(Eq(val, 1) !== S.false, 'Total Probability must be 1.');
  }
}

/** A finite random variable with the given values and probabilities (SymPy FiniteRV(name, density)); not checked unless `check` is true. */
export function FiniteRV(name: string | Sym, densityIn: ReadonlyMap<ExprLike, ExprLike> | readonly (readonly [ExprLike, ExprLike])[], opts: RVOptions = {}): RandomSymbol {
  return rv(name, FiniteDistributionHandmade, [Dict(densityIn)], { check: opts.check ?? false });
}

/** SymPy DiscreteUniformDistribution(*items). */
export class DiscreteUniformDistribution extends SingleFiniteDistribution {
  constructor(args: readonly Expr[]) {
    super('DiscreteUniformDistribution', args);
  }
  override check(): void {
    const keys = new Set(this.args.map((a) => a.key));
    if (keys.size !== this.args.length) {
      const n = this.args.length;
      const weights = new Map<string, [Expr, number]>();
      for (const a of this.args) weights.set(a.key, [a, (weights.get(a.key)?.[1] ?? 0) + 1]);
      const w = [...weights.values()].map(([k, c]) => `${k.toString()}: ${Rational.of(c, n).toString()}`).join(', ');
      throw new RangeError(`Repeated args detected but set expected. For a distribution having different weights for each item use the following:\nS("FiniteRV('X', {${w}})")`);
    }
  }
  /** The probability of each value. */
  get p(): Expr {
    return Rational.of(1, this.args.length);
  }
  override get dict(): DensityResult {
    return new FiniteDensity(cast(this.set, FiniteSet).args.map((k) => [k, this.p] as const));
  }
  override get set(): SetExpr {
    return finiteSet(...this.args);
  }
  pmf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    return this.args.some((a) => a.key === x.key) ? this.p : S.Zero;
  }
}

/** Uniform distribution over the items (SymPy DiscreteUniform(name, items)). */
export function DiscreteUniform(name: string | Sym, items: readonly ExprLike[]): RandomSymbol {
  return rv(name, DiscreteUniformDistribution, items);
}

/** SymPy DieDistribution(sides). */
export class DieDistribution extends SingleFiniteDistribution {
  constructor(args: readonly Expr[]) {
    super('DieDistribution', args);
  }
  get sides(): Expr {
    return this.arg(0);
  }
  override check(): void {
    valueCheck([isPositive(this.sides), isIntegerValued(this.sides)], 'number of sides must be a positive integer.');
  }
  override get isSymbolic(): boolean {
    return !this.sides.isNumber;
  }
  override get high(): Expr {
    return this.sides;
  }
  override get low(): Expr {
    return S.One;
  }
  override get set(): SetExpr {
    if (this.isSymbolic) return intersection(Naturals0, interval(0, this.sides));
    return finiteSet(...Array.from({ length: Number(asRational(this.sides).p) }, (_, i) => int(i + 1)));
  }
  pmf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    checkPmfArgument(x);
    const cond = and(Ge(x, 1), Le(x, this.sides), contains(Integers, x));
    return piecewise([pow(this.sides, -1), cond], [S.Zero, true]);
  }
}

/** A fair die with the given number of sides (SymPy Die(name, sides=6)). */
export function Die(name: string | Sym, sides: ExprLike = 6): RandomSymbol {
  return rv(name, DieDistribution, [sides]);
}

/** SymPy BernoulliDistribution(p, succ, fail). */
export class BernoulliDistribution extends SingleFiniteDistribution {
  constructor(args: readonly Expr[]) {
    super('BernoulliDistribution', args);
  }
  get p(): Expr {
    return this.arg(0);
  }
  get succ(): Expr {
    return this.arg(1);
  }
  get fail(): Expr {
    return this.arg(2);
  }
  override check(): void {
    valueCheck([Ge(this.p, 0), Le(this.p, 1)], 'p should be in range [0, 1].');
  }
  override get set(): SetExpr {
    return finiteSet(this.succ, this.fail);
  }
  pmf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    // SymPy compares symbolic outcomes (H and T) structurally: x == succ
    if (this.succ instanceof Sym && this.fail instanceof Sym) {
      return piecewise([this.p, x.key === this.succ.key], [sub(1, this.p), x.key === this.fail.key], [S.Zero, true]);
    }
    return piecewise([this.p, Eq(x, this.succ)], [sub(1, this.p), Eq(x, this.fail)], [S.Zero, true]);
  }
}

/** Bernoulli distribution: succ with probability p, fail otherwise (SymPy Bernoulli(name, p, succ=1, fail=0)). */
export function Bernoulli(name: string | Sym, p: ExprLike, succ: ExprLike | string = 1, fail: ExprLike | string = 0): RandomSymbol {
  return rv(name, BernoulliDistribution, [p, succ, fail].map((v) => (typeof v === 'string' ? new Sym(v) : v)));
}

/** A coin with outcomes H and T, H with probability p (SymPy Coin(name, p=1/2)). */
export function Coin(name: string | Sym, p: ExprLike = S.Half): RandomSymbol {
  return rv(name, BernoulliDistribution, [p, new Sym('H'), new Sym('T')]);
}

/** SymPy BinomialDistribution(n, p, succ, fail). */
export class BinomialDistribution extends SingleFiniteDistribution {
  constructor(args: readonly Expr[]) {
    super('BinomialDistribution', args);
  }
  get p(): Expr {
    return this.arg(1);
  }
  override check(): void {
    valueCheck([isIntegerValued(this.arg(0)), isNonNegative(this.arg(0))], "'n' must be nonnegative integer.");
    valueCheck([Le(this.p, 1), Ge(this.p, 0)], 'p should be in range [0, 1].');
  }
  override get high(): Expr {
    return this.arg(0);
  }
  override get low(): Expr {
    return S.Zero;
  }
  override get isSymbolic(): boolean {
    return !this.arg(0).isNumber;
  }
  override get set(): SetExpr {
    if (this.isSymbolic) return intersection(Naturals0, interval(0, this.arg(0)));
    return finiteSet(...cast(this.dict, FiniteDensity).keys());
  }
  pmf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    checkPmfArgument(x);
    const [n, p] = [this.arg(0), this.p];
    const cond = and(Ge(x, 0), Le(x, n), contains(Integers, x));
    return piecewise([mul(binomial(n, x), pow(p, x), pow(sub(1, p), sub(n, x))), cond], [S.Zero, true]);
  }
  override get dict(): DensityResult {
    if (this.isSymbolic) return new Density([this]);
    const [succ, fail] = [this.arg(2), this.arg(3)];
    const n = Number(asRational(this.arg(0)).p);
    return new FiniteDensity(Array.from({ length: n + 1 }, (_, k) => [add(mul(k, succ), mul(n - k, fail)), this.pmf(k)] as const));
  }
}

/** Binomial distribution of n trials with success probability p (SymPy Binomial(name, n, p, succ=1, fail=0)). */
export function Binomial(name: string | Sym, n: ExprLike, p: ExprLike, succ: ExprLike = 1, fail: ExprLike = 0): RandomSymbol {
  return rv(name, BinomialDistribution, [n, p, succ, fail]);
}

/** SymPy BetaBinomialDistribution(n, alpha, beta). */
export class BetaBinomialDistribution extends SingleFiniteDistribution {
  constructor(args: readonly Expr[]) {
    super('BetaBinomialDistribution', args);
  }
  override check(): void {
    const [n, alpha, beta] = [this.arg(0), this.arg(1), this.arg(2)];
    valueCheck([isIntegerValued(n), isNonNegative(n)], `'n' must be nonnegative integer. n = ${n.toString()}.`);
    valueCheck(Gt(alpha, 0), `'alpha' must be: alpha > 0 . alpha = ${alpha.toString()}`);
    valueCheck(Gt(beta, 0), `'beta' must be: beta > 0 . beta = ${beta.toString()}`);
  }
  override get high(): Expr {
    return this.arg(0);
  }
  override get low(): Expr {
    return S.Zero;
  }
  override get isSymbolic(): boolean {
    return !this.arg(0).isNumber;
  }
  override get set(): SetExpr {
    if (this.isSymbolic) return intersection(Naturals0, interval(0, this.arg(0)));
    return finiteSet(...Array.from({ length: Number(asRational(this.arg(0)).p) + 1 }, (_, i) => int(i)));
  }
  pmf(kIn: ExprLike): Expr {
    const k = sympify(kIn);
    const [n, a, b] = [this.arg(0), this.arg(1), this.arg(2)];
    return mul(binomial(n, k), betaFn(add(k, a), add(sub(n, k), b)), pow(betaFn(a, b), -1));
  }
}

/** Beta-binomial distribution (SymPy BetaBinomial(name, n, alpha, beta)). */
export function BetaBinomial(name: string | Sym, n: ExprLike, alpha: ExprLike, beta: ExprLike): RandomSymbol {
  return rv(name, BetaBinomialDistribution, [n, alpha, beta]);
}

/** SymPy HypergeometricDistribution(N, m, n). */
export class HypergeometricDistribution extends SingleFiniteDistribution {
  constructor(args: readonly Expr[]) {
    super('HypergeometricDistribution', args);
  }
  override check(): void {
    // SymPy check(n, N, m) receives (N, m, n): the names are shifted, the messages follow them
    const [n, N, m] = [this.arg(0), this.arg(1), this.arg(2)];
    valueCheck([isIntegerValued(N), isNonNegative(N)], `'N' must be nonnegative integer. N = ${N.toString()}.`);
    valueCheck([isIntegerValued(n), isNonNegative(n)], `'n' must be nonnegative integer. n = ${n.toString()}.`);
    valueCheck([isIntegerValued(m), isNonNegative(m)], `'m' must be nonnegative integer. m = ${m.toString()}.`);
  }
  override get isSymbolic(): boolean {
    return !this.args.every((x) => x.isNumber);
  }
  override get high(): Expr {
    const [, m, n] = [this.arg(0), this.arg(1), this.arg(2)];
    return piecewise([n, Lt(n, m) !== S.false], [m, true]);
  }
  override get low(): Expr {
    const [N, m, n] = [this.arg(0), this.arg(1), this.arg(2)];
    return piecewise([0, Gt(0, sub(add(n, m), N)) !== S.false], [sub(add(n, m), N), true]);
  }
  override get set(): SetExpr {
    const [N, m, n] = [this.arg(0), this.arg(1), this.arg(2)].map((a) => a);
    if (this.isSymbolic) return intersection(Naturals0, interval(this.low, this.high));
    const v = (e: Expr | undefined): number => Number(asRational(defined(e)).p);
    const lo = Math.max(0, v(n) + v(m) - v(N));
    const hi = Math.min(v(n), v(m));
    return finiteSet(...Array.from({ length: Math.max(0, hi - lo + 1) }, (_, i) => int(lo + i)));
  }
  pmf(kIn: ExprLike): Expr {
    const k = sympify(kIn);
    const [N, m, n] = [this.arg(0), this.arg(1), this.arg(2)];
    return mul(binomial(m, k), binomial(sub(N, m), sub(n, k)), pow(binomial(N, n), -1));
  }
}

/** Hypergeometric distribution: n draws from N items of which m are successes (SymPy Hypergeometric(name, N, m, n)). */
export function Hypergeometric(name: string | Sym, N: ExprLike, m: ExprLike, n: ExprLike): RandomSymbol {
  return rv(name, HypergeometricDistribution, [N, m, n]);
}

/** SymPy RademacherDistribution(): -1 and 1 with probability 1/2. */
export class RademacherDistribution extends SingleFiniteDistribution {
  constructor(args: readonly Expr[] = []) {
    super('RademacherDistribution', args);
  }
  override get set(): SetExpr {
    return finiteSet(-1, 1);
  }
  pmf(xIn: ExprLike): Expr {
    const k = new Dummy('k');
    return Lambda(k, piecewise([S.Half, or(Eq(k, -1), Eq(k, 1))], [S.Zero, true])).call(xIn);
  }
}

/** Rademacher distribution (SymPy Rademacher(name)). */
export function Rademacher(name: string | Sym): RandomSymbol {
  return rv(name, RademacherDistribution, []);
}

/** Python `a and b` of three-valued SymPy assumptions (None is falsy). */
const pyAnd = (a: boolean | undefined, b: boolean | undefined): boolean | undefined => (a === true ? b : a);

/** SymPy IdealSolitonDistribution(k). */
export class IdealSolitonDistribution extends SingleFiniteDistribution {
  constructor(args: readonly Expr[]) {
    super('IdealSolitonDistribution', args);
  }
  get k(): Expr {
    return this.arg(0);
  }
  override check(): void {
    const k = this.k;
    valueCheck(pyAnd(isIntegerValued(k), isPositive(k)), "'k' must be a positive integer.");
  }
  override get low(): Expr {
    return S.One;
  }
  override get high(): Expr {
    return this.k;
  }
  override get set(): SetExpr {
    return finiteSet(...Array.from({ length: Number(asRational(this.k).p) }, (_, i) => int(i + 1)));
  }
  override get dict(): DensityResult {
    if (this.k instanceof Sym) return new Density([this]);
    const k = Number(asRational(this.k).p);
    const entries: (readonly [Expr, Expr])[] = [[S.One, Rational.of(1, k)]];
    for (let i = 2; i <= k; i++) entries.push([int(i), Rational.of(1, i * (i - 1))]);
    return new FiniteDensity(entries);
  }
  pmf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    checkPmfArgument(x);
    return idealRho(x, this.k);
  }
}

/** Python `relational & x.is_integer` (SymPy raises a TypeError for None). */
function andBool(rel: Expr, b: boolean | undefined): Expr {
  if (b === undefined) throw new TypeError("unsupported operand type(s) for &: 'Equality' and 'NoneType'");
  return and(rel, b ? S.true : S.false);
}

/** The ideal soliton mass function at x (SymPy rho). */
function idealRho(x: Expr, k: Expr): Expr {
  const isInt = isIntegerValued(x);
  const cond1 = andBool(Eq(x, 1), isInt);
  const cond2 = andBool(and(Ge(x, 1), Le(x, k)), isInt);
  return piecewise([pow(k, -1), cond1], [pow(mul(x, sub(x, 1)), -1), cond2], [S.Zero, true]);
}

/** Ideal soliton distribution (SymPy IdealSoliton(name, k)). */
export function IdealSoliton(name: string | Sym, k: ExprLike): RandomSymbol {
  return rv(name, IdealSolitonDistribution, [k]);
}

/** SymPy RobustSolitonDistribution(k, delta, c). */
export class RobustSolitonDistribution extends SingleFiniteDistribution {
  constructor(args: readonly Expr[]) {
    super('RobustSolitonDistribution', args);
  }
  get k(): Expr {
    return this.arg(0);
  }
  get delta(): Expr {
    return this.arg(1);
  }
  get c(): Expr {
    return this.arg(2);
  }
  override check(): void {
    const { k, delta, c } = this;
    valueCheck(pyAnd(isIntegerValued(k), isPositive(k)), "'k' must be a positive integer");
    valueCheck(and(Gt(delta, 0), Le(delta, 1)), "'delta' must be a real number in the interval (0,1)");
    valueCheck(isPositive(c), "'c' must be a positive real number.");
  }
  /** SymPy R = c*log(k/delta)*k**0.5. */
  get R(): Expr {
    return mul(this.c, log(mul(this.k, pow(this.delta, -1))), pow(this.k, new Float(0.5)));
  }
  /** SymPy Z: the normalization. */
  get Z(): Expr {
    let z: Expr = S.Zero;
    const top = pyRound(mul(this.k, pow(this.R, -1)));
    for (let i = 1; i < top; i++) z = add(z, Rational.of(1, i));
    z = add(z, log(mul(this.R, pow(this.delta, -1))));
    return add(1, mul(z, this.R, pow(this.k, -1)));
  }
  override get low(): Expr {
    return S.One;
  }
  override get high(): Expr {
    return this.k;
  }
  override get set(): SetExpr {
    return finiteSet(...Array.from({ length: Number(asRational(this.k).p) }, (_, i) => int(i + 1)));
  }
  override get isSymbolic(): boolean {
    return !(this.k.isNumber && this.c.isNumber && this.delta.isNumber);
  }
  pmf(xIn: ExprLike): Expr {
    const x = sympify(xIn);
    checkPmfArgument(x);
    const { k, R, delta } = this;
    const rho = idealRho(x, k);
    const top = pyRound(mul(k, pow(R, -1)));
    const c1 = and(Ge(x, 1), Le(x, top - 1));
    const c2 = Eq(x, top);
    const tau = piecewise([mul(R, pow(mul(k, x), -1)), c1], [mul(R, log(mul(R, pow(delta, -1))), pow(k, -1)), c2], [S.Zero, true]);
    return mul(add(rho, tau), pow(this.Z, -1));
  }
}

/** Python round() of a number (to nearest, ties to even). */
export function pyRound(e: Expr): number {
  const v = e.evalf().toNumber();
  const r = Math.round(v);
  return Math.abs(v - Math.trunc(v)) === 0.5 && r % 2 !== 0 ? r - 1 : r;
}

/** Robust soliton distribution (SymPy RobustSoliton(name, k, delta, c)). */
export function RobustSoliton(name: string | Sym, k: ExprLike, delta: ExprLike, c: ExprLike): RandomSymbol {
  return rv(name, RobustSolitonDistribution, [k, delta, c]);
}


// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/stats/joint_rv_types.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.stats.joint_rv_types: the joint distributions and the
 * functions that create random vectors with them (`MultivariateNormal('X',
 * mu, sigma)`, `Dirichlet('D', [a1, a2])`, `Multinomial('M', n, [p1,
 * p2])`, handmade `JointRV('X', pdf)`, ...), and `marginalDistribution`.
 *
 * Vector and matrix parameters are explicit matrices (a flat array is a
 * column vector, nested arrays are the rows) or matrix symbols, as in SymPy,
 * where lists become ImmutableMatrix arguments.
 */

import { Rational, S, Sym } from '../core/nodes';
import type { Expr } from '../core/nodes';
import type { ExprLike } from '../core/nodes';
import { add, exp, mul, pow, sqrt, sub, sympify } from '../core/ops';
import { Eq, Ge, Gt, Le, piecewise } from '../core/logic';
import { Lambda, LambdaNode } from '../core/lambda';
import { Product, Sum } from '../core/concrete';
import { Indexed, IndexedBase } from '../core/indexed';
import { TupleNode } from '../core/containers';
import { isPositive, isReal } from '../core/assumptions';
import { at, cast, first } from '../core/guard';
import { NotImplementedError } from '../core/errors';
import { Naturals0, Reals, SetExpr, interval, intersection, productSet, range } from '../sets/sets';
import { Matrix } from '../matrices/matrix';
import { ImmutableMatrixNode, MatrixExpr, MatrixElementNode, MatrixSymbolNode, det } from '../matrices/expressions/matexpr';
import { isPositiveDefinite, isPositiveSemidefinite } from '../matrices/linalg';
import { besselk } from '../functions/special/bessel';
import { expand } from '../simplify/expand';
import { factorial, gamma, rf } from '../functions/special/special';
import { randomSymbols, statsClasses, valueCheck } from './rv';
import type { MatrixParam, RandomSymbol } from './rv';
import { GammaDistribution } from './crvtypes';
import { JointDistribution, JointPSpace, jointPSpace, makeMarginalDistribution } from './jointrv';


/** A parameter as an expression: arrays and matrices as ImmutableMatrix nodes (SymPy JointDistribution.__new__). */
function param(v: MatrixParam | ExprLike): Expr {
  if (v instanceof Matrix) return new ImmutableMatrixNode(v);
  if (!isList(v)) return sympify(v);
  const rows: readonly (ExprLike | readonly ExprLike[])[] = v;
  return new ImmutableMatrixNode(rows.some(isList) ? Matrix.of(rows.filter(isList)) : Matrix.col(...rows.filter(notList)));
}

/** The value is an array (SymPy list). */
const isList = <T>(v: T): v is Extract<T, readonly unknown[]> => Array.isArray(v);

/** The value is not an array. */
const notList = <T>(v: T): v is Exclude<T, readonly unknown[]> => !Array.isArray(v);

/** The parameters given as one array or one by one (SymPy *p with p[0] a list). */
const listOrArgs = (xs: readonly (ExprLike | readonly ExprLike[])[]): ExprLike[] => {
  const f = xs[0];
  return f !== undefined && isList(f) ? [...f] : xs.filter(notList);
};

/** SymPy isinstance(n, Integer). */
const isInteger = (e: Expr): boolean => e instanceof Rational && e.q === 1n;

/** The entries of a vector parameter (SymPy iteration over an ImmutableMatrix). */
const entries = (e: Expr): Expr[] => [...cast(e, ImmutableMatrixNode, 'vector parameter').matrix.data];

/** The shape of a matrix parameter. */
const shapeOf = (e: Expr): [Expr, Expr] => cast(e, MatrixExpr, 'matrix parameter').shape;

/** The explicit matrix of a parameter. */
const explicit = (e: Expr): Matrix => cast(e, ImmutableMatrixNode, 'explicit matrix').matrix;

/** The values as an explicit column vector, or the one matrix argument (SymPy ImmutableMatrix(args)). */
function vectorArg(xs: readonly ExprLike[]): Expr {
  if (xs.length === 1) {
    const x0 = first(xs);
    if (x0 instanceof Matrix || x0 instanceof MatrixExpr) return param(x0);
  }
  return new ImmutableMatrixNode(Matrix.col(...xs));
}

/** S.Reals**k (SymPy ProductSet of k copies). */
const realsPower = (k: Expr): SetExpr => productSet(...Array.from({ length: Number(k.toString()) }, () => Reals));

/** The random vector of the distribution after checking its parameters (SymPy multivariate_rv). */
function multivariateRv(dist: JointDistribution & { check(): void }, sym: string | Sym): RandomSymbol {
  dist.check();
  return jointPSpace(sym, dist).value;
}

/** The matrix of the product as an explicit matrix when its factors are explicit (SymPy ImmutableMatrix arithmetic). */
function matMulOf(...fs: Expr[]): Expr {
  return fs.slice(1).reduce((acc, f) => cast(acc, MatrixExpr).mul(f), first(fs));
}

/** The (0, 0) entry of a 1 x 1 matrix (SymPy M[0]). */
const entry00 = (m: Expr): Expr => cast(m, MatrixExpr).at(0, 0);

/**
 * The marginal density of the components at the indices of a joint random
 * symbol (SymPy marginal_distribution): a Lambda. The indices are integers
 * or components `X.at(i)`.
 */
export function marginalDistribution(rv: RandomSymbol, ...indicesIn: (ExprLike | readonly ExprLike[])[]): Expr {
  // an array of indices is one argument, as SymPy's list
  const indices = indicesIn.map((i) => {
    const e = isList(i) ? new TupleNode(i.map(sympify)) : sympify(i);
    return e instanceof Indexed ? at(e.args, 1) : e;
  });
  if (!indices.length) throw new RangeError('At least one component for marginal density is needed.');
  const ps = cast(rv.pspace, JointPSpace, 'joint probability space');
  const dist = ps.distribution;
  if (dist instanceof JointDistributionWithMarginal) return dist.marginalDistributionOf(indices, rv.symbol);
  return ps.marginalDistribution(...indices.map((i) => Number(i.toString())));
}

/** A joint distribution with a closed form of its marginal distributions (SymPy _marginal_distribution). */
abstract class JointDistributionWithMarginal extends JointDistribution {
  abstract marginalDistributionOf(indices: readonly Expr[], sym: Sym): Expr;
}

// ---------------------------------------------------------------------------
// Handmade joint distributions
// ---------------------------------------------------------------------------

/** SymPy JointDistributionHandmade(pdf, set): a joint distribution given by a Lambda density on a set. */
export class JointDistributionHandmade extends JointDistribution {
  constructor(args: readonly Expr[]) {
    super('JointDistributionHandmade', args);
  }
  override get isContinuous(): boolean {
    return true;
  }
  /** The density (SymPy pdf, the first argument). */
  get pdfLambda(): Expr {
    return this.arg(0);
  }
  get set(): SetExpr {
    return cast(this.arg(1), SetExpr, 'set');
  }
  pdf(...xs: ExprLike[]): Expr {
    return cast(this.pdfLambda, LambdaNode, 'pdf').call(...xs);
  }
}

/** A random vector with the joint density of the components sym[i] in the expression (SymPy JointRV(symbol, pdf, _set=None)). */
export function JointRV(symbolIn: string | Sym, pdfIn: ExprLike): RandomSymbol {
  const symbol = typeof symbolIn === 'string' ? new Sym(symbolIn) : symbolIn;
  const pdf = sympify(pdfIn);
  const found = new Map<string, Indexed>();
  const go = (e: Expr): void => {
    if (e instanceof Indexed && e.base.key === symbol.key) found.set(e.key, e);
    else e.args.forEach(go);
  };
  go(pdf);
  const syms = [...found.values()].sort((a, b) => Number(at(a.args, 1).toString()) - Number(at(b.args, 1).toString()));
  const lam = Lambda(syms, pdf);
  const dist = new JointDistributionHandmade([lam, productSet(...syms.map(() => Reals))]);
  const jrv = jointPSpace(symbol, dist).value;
  if (randomSymbols(lam).length !== 0) return jointPSpace(symbol, makeMarginalDistribution(dist, [jrv])).value;
  return jrv;
}

// ---------------------------------------------------------------------------
// Multivariate normal distribution
// ---------------------------------------------------------------------------

/** SymPy MultivariateNormalDistribution(mu, sigma). */
export class MultivariateNormalDistribution extends JointDistributionWithMarginal {
  constructor(args: readonly Expr[]) {
    super('MultivariateNormalDistribution', args);
  }
  override get isContinuous(): boolean {
    return true;
  }
  get mu(): Expr {
    return this.arg(0);
  }
  get sigma(): Expr {
    return this.arg(1);
  }
  get set(): SetExpr {
    return realsPower(at(shapeOf(this.mu), 0));
  }
  check(): void {
    valueCheck(at(shapeOf(this.mu), 0).key === at(shapeOf(this.sigma), 0).key, 'Size of the mean vector and covariance matrix are incorrect.');
    // check if covariance matrix is positive semi definite or not
    if (!(this.sigma instanceof MatrixSymbolNode)) valueCheck(truthOf(isPositiveSemidefinite(explicit(this.sigma))), 'The covariance matrix must be positive semi definite. ');
  }
  pdf(...args: ExprLike[]): Expr {
    const [mu, sigma] = [this.mu, this.sigma];
    const k = at(shapeOf(mu), 0);
    const x = cast(vectorArg(args), MatrixExpr).sub(mu);
    const quad = matMulOf(cast(x, MatrixExpr).T, cast(sigma, MatrixExpr).pow(-1), x);
    const norm = pow(sqrt(mul(pow(mul(2, S.Pi), k), det(sigma))), -1);
    // SymPy's exp of the 1 x 1 matrix goes through its eigenvalue, the expanded entry
    if (quad instanceof ImmutableMatrixNode) return mul(norm, exp(mul(Rational.of(-1n, 2n), expand(entry00(quad)))));
    // a symbolic vector: SymPy's MatrixElement of the (1 x 1 matrix) density
    const xT = cast(cast(x, MatrixExpr).T, MatrixExpr);
    const quadS = matMulOf(xT.rmul(Rational.of(-1n, 2n)), cast(sigma, MatrixExpr).pow(-1), x);
    return new MatrixElementNode(mul(norm, exp(quadS)), S.Zero, S.Zero);
  }
  marginalDistributionOf(indices: readonly Expr[], sym: Sym): Expr {
    const kept = new Set(indices.map((i) => i.key));
    const k = Number(at(shapeOf(this.mu), 0).toString());
    const keep = Array.from({ length: k }, (_, i) => i).filter((i) => kept.has(sympify(i).key));
    const mu = explicit(this.mu).slice(keep, [0]);
    const sigma = explicit(this.sigma).slice(keep, keep);
    const v = Matrix.col(...indices.map((i) => new Indexed([sym, i])));
    const d = mu.sub(v);
    // (expanded as by SymPy's exp of the 1 x 1 matrix)
    const quad = expand(d.transpose().mul(sigma.inv().mul(d)).get(0, 0));
    return Lambda([...v.data], mul(pow(sqrt(mul(pow(mul(2, S.Pi), mu.rows), sigma.det())), -1), exp(mul(Rational.of(-1n, 2n), quad))));
  }
}

/** The Truth of a predicate as a value for valueCheck. */
const truthOf = (t: boolean | 'unknown' | undefined): boolean | undefined => (t === 'unknown' ? undefined : t);

/** A multivariate normal random vector (SymPy MultivariateNormal(name, mu, sigma)). */
export function MultivariateNormal(name: string | Sym, mu: MatrixParam, sigma: MatrixParam): RandomSymbol {
  return multivariateRv(new MultivariateNormalDistribution([param(mu), param(sigma)]), name);
}

// ---------------------------------------------------------------------------
// Multivariate Laplace distribution
// ---------------------------------------------------------------------------

/** SymPy MultivariateLaplaceDistribution(mu, sigma). */
export class MultivariateLaplaceDistribution extends JointDistribution {
  constructor(args: readonly Expr[]) {
    super('MultivariateLaplaceDistribution', args);
  }
  override get isContinuous(): boolean {
    return true;
  }
  get mu(): Expr {
    return this.arg(0);
  }
  get sigma(): Expr {
    return this.arg(1);
  }
  get set(): SetExpr {
    return realsPower(at(shapeOf(this.mu), 0));
  }
  check(): void {
    valueCheck(at(shapeOf(this.mu), 0).key === at(shapeOf(this.sigma), 0).key, 'Size of the mean vector and covariance matrix are incorrect.');
    // check if covariance matrix is positive definite or not
    if (!(this.sigma instanceof MatrixSymbolNode)) valueCheck(truthOf(isPositiveDefinite(explicit(this.sigma))), 'The covariance matrix must be positive definite. ');
  }
  pdf(...xs: ExprLike[]): Expr {
    const mu = explicit(this.mu);
    const sigma = explicit(this.sigma);
    const k = sympify(mu.rows);
    const sigmaInv = sigma.inv();
    const args = Matrix.col(...xs);
    const x = mu.transpose().mul(sigmaInv).mul(mu).get(0, 0);
    const y = args.transpose().mul(sigmaInv).mul(args).get(0, 0);
    const v = sub(1, mul(k, S.Half));
    return mul(
      2,
      pow(mul(y, pow(add(2, x), -1)), mul(v, S.Half)),
      besselk(v, sqrt(mul(add(2, x), y))),
      exp(args.transpose().mul(sigmaInv).mul(mu).get(0, 0)),
      pow(mul(pow(mul(2, S.Pi), mul(k, S.Half)), sqrt(sigma.det())), -1),
    );
  }
}

/** A multivariate Laplace random vector (SymPy MultivariateLaplace(name, mu, sigma)). */
export function MultivariateLaplace(name: string | Sym, mu: MatrixParam, sigma: MatrixParam): RandomSymbol {
  return multivariateRv(new MultivariateLaplaceDistribution([param(mu), param(sigma)]), name);
}

// ---------------------------------------------------------------------------
// Multivariate Student t distribution
// ---------------------------------------------------------------------------

/** SymPy MultivariateTDistribution(mu, shape_mat, dof). */
export class MultivariateTDistribution extends JointDistribution {
  constructor(args: readonly Expr[]) {
    super('MultivariateTDistribution', args);
  }
  override get isContinuous(): boolean {
    return true;
  }
  get mu(): Expr {
    return this.arg(0);
  }
  get shapeMat(): Expr {
    return this.arg(1);
  }
  get dof(): Expr {
    return this.arg(2);
  }
  get set(): SetExpr {
    return realsPower(at(shapeOf(this.mu), 0));
  }
  check(): void {
    valueCheck(at(shapeOf(this.mu), 0).key === at(shapeOf(this.shapeMat), 0).key, 'Size of the location vector and shape matrix are incorrect.');
    // check if covariance matrix is positive definite or not
    if (!(this.shapeMat instanceof MatrixSymbolNode)) valueCheck(truthOf(isPositiveDefinite(explicit(this.shapeMat))), 'The shape matrix must be positive definite. ');
  }
  pdf(...xs: ExprLike[]): Expr {
    const mu = explicit(this.mu);
    const sigma = explicit(this.shapeMat);
    const v = this.dof;
    const k = sympify(mu.rows);
    const x = Matrix.col(...xs).sub(mu);
    const q = x.transpose().mul(sigma.inv()).mul(x).get(0, 0);
    const c = mul(gamma(mul(add(k, v), S.Half)), pow(mul(gamma(mul(v, S.Half)), pow(mul(v, S.Pi), mul(k, S.Half)), sqrt(sigma.det())), -1));
    return mul(c, pow(add(1, mul(pow(v, -1), q)), mul(sub(mul(-1, v), k), S.Half)));
  }
}

/** A multivariate Student t random vector (SymPy MultivariateT(syms, mu, sigma, v)). */
export function MultivariateT(name: string | Sym, mu: MatrixParam, sigma: MatrixParam, v: ExprLike): RandomSymbol {
  return multivariateRv(new MultivariateTDistribution([param(mu), param(sigma), sympify(v)]), name);
}

// ---------------------------------------------------------------------------
// Normal-gamma distribution
// ---------------------------------------------------------------------------

/** SymPy NormalGammaDistribution(mu, lamda, alpha, beta). */
export class NormalGammaDistribution extends JointDistributionWithMarginal {
  constructor(args: readonly Expr[]) {
    super('NormalGammaDistribution', args);
  }
  override get isContinuous(): boolean {
    return true;
  }
  get mu(): Expr {
    return this.arg(0);
  }
  get lamda(): Expr {
    return this.arg(1);
  }
  get alpha(): Expr {
    return this.arg(2);
  }
  get beta(): Expr {
    return this.arg(3);
  }
  check(): void {
    valueCheck(truthOf(isReal(this.mu)), 'Location must be real.');
    valueCheck(Gt(this.lamda, 0), 'Lambda must be positive');
    valueCheck(Gt(this.alpha, 0), 'alpha must be positive');
    valueCheck(Gt(this.beta, 0), 'beta must be positive');
  }
  get set(): SetExpr {
    return productSet(Reals, interval(0, S.Infinity));
  }
  pdf(xIn: ExprLike, tauIn: ExprLike): Expr {
    const [x, tau] = [sympify(xIn), sympify(tauIn)];
    const [mu, lamda, alpha, beta] = [this.mu, this.lamda, this.alpha, this.beta];
    return mul(
      pow(beta, alpha),
      sqrt(lamda),
      pow(mul(gamma(alpha), sqrt(mul(2, S.Pi))), -1),
      pow(tau, sub(alpha, S.Half)),
      exp(mul(-1, beta, tau)),
      exp(mul(-1, lamda, tau, pow(sub(x, mu), 2), S.Half)),
    );
  }
  marginalDistributionOf(indices: readonly Expr[], sym: Sym): Expr {
    // SymPy self.pdf(*sym) with the one symbol: a TypeError
    if (indices.length === 2) throw new TypeError('NormalGammaDistribution.pdf() missing 1 required positional argument: tau');
    if (first(indices).key === S.Zero.key) {
      // for the marginal over x, the non-standardized Student t distribution
      const x = sym;
      const v = sub(this.alpha, S.Half);
      const sigma = mul(this.beta, pow(mul(this.lamda, this.alpha), -1));
      const c = mul(gamma(mul(add(v, 1), S.Half)), pow(mul(gamma(mul(v, S.Half)), sqrt(mul(S.Pi, v)), sigma), -1));
      return Lambda(sym, mul(c, pow(add(1, mul(pow(v, -1), pow(mul(sub(x, this.mu), pow(sigma, -1)), 2))), mul(sub(mul(-1, v), 1), S.Half))));
    }
    // for the marginal over tau, the Gamma distribution of the construction
    return Lambda(sym, new GammaDistribution([this.alpha, this.beta]).pdf(sym));
  }
}

/** A normal-gamma random vector (SymPy NormalGamma(sym, mu, lamda, alpha, beta)). */
export function NormalGamma(sym: string | Sym, mu: ExprLike, lamda: ExprLike, alpha: ExprLike, beta: ExprLike): RandomSymbol {
  return multivariateRv(new NormalGammaDistribution([mu, lamda, alpha, beta].map(sympify)), sym);
}

// ---------------------------------------------------------------------------
// Multivariate beta (Dirichlet) distribution
// ---------------------------------------------------------------------------

/** SymPy MultivariateBetaDistribution(alpha). */
export class MultivariateBetaDistribution extends JointDistribution {
  constructor(args: readonly Expr[]) {
    super('MultivariateBetaDistribution', args);
  }
  override get isContinuous(): boolean {
    return true;
  }
  get alpha(): Expr {
    return this.arg(0);
  }
  check(): void {
    const alpha = entries(this.alpha);
    valueCheck(alpha.length >= 2, 'At least two categories should be passed.');
    for (const a of alpha) valueCheck(Gt(a, 0) !== S.false, 'Each concentration parameter should be positive.');
  }
  get set(): SetExpr {
    return productSet(...entries(this.alpha).map(() => interval(0, 1)));
  }
  pdf(...syms: ExprLike[]): Expr {
    const alpha = entries(this.alpha);
    const B = mul(...alpha.map((a) => gamma(a)), pow(gamma(add(...alpha)), -1));
    return mul(...alpha.map((a, i) => pow(sympify(at(syms, i)), sub(a, 1))), pow(B, -1));
  }
}

/** A multivariate beta (Dirichlet) random vector (SymPy MultivariateBeta(syms, *alpha)): the parameters as an array or one by one. */
export function MultivariateBeta(syms: string | Sym, ...alpha: (ExprLike | readonly ExprLike[])[]): RandomSymbol {
  const a = listOrArgs(alpha);
  return multivariateRv(new MultivariateBetaDistribution([param(a)]), syms);
}

/** SymPy Dirichlet: the multivariate beta distribution. */
export const Dirichlet = MultivariateBeta;

// ---------------------------------------------------------------------------
// Multivariate Ewens distribution
// ---------------------------------------------------------------------------

/** SymPy MultivariateEwensDistribution(n, theta). */
export class MultivariateEwensDistribution extends JointDistribution {
  constructor(args: readonly Expr[]) {
    super('MultivariateEwensDistribution', args);
  }
  override get isDiscrete(): boolean {
    return true;
  }
  get theta(): Expr {
    return this.arg(1);
  }
  check(): void {
    valueCheck(Gt(this.arg(0), 0), 'sample size should be positive integer.');
    valueCheck(truthOf(isPositive(this.theta)), 'mutation rate should be positive.');
  }
  get set(): SetExpr {
    const n = this.arg(0);
    // SymPy: Product(Intersection(Naturals0, Interval(0, n//i)), (i, 1, n)), a product of sets that is not a set
    if (!isInteger(n)) throw new NotImplementedError('the set of a multivariate Ewens distribution of symbolic dimension is not implemented');
    const k = Number(n.toString());
    return productSet(range(0, k + 1), ...Array.from({ length: k - 1 }, (_, j) => range(0, Math.floor(k / (j + 2)) + 1)));
  }
  pdf(...syms: (ExprLike | IndexedBase)[]): Expr {
    const [n, theta] = [this.arg(0), this.theta];
    const condi = isInteger(n);
    if (!(first(syms) instanceof IndexedBase || condi)) throw new RangeError('Please use IndexedBase object for syms as the dimension is symbolic');
    const term1 = mul(factorial(n), pow(rf(theta, n), -1));
    if (condi) {
      const k = Number(n.toString());
      const xs = syms.slice(0, k).map((s) => (s instanceof IndexedBase ? s.label : sympify(s)));
      const term2 = mul(...xs.map((s, j) => mul(pow(theta, s), pow(mul(pow(j + 1, s), factorial(s)), -1))));
      const cond = Eq(add(...xs.map((s, j) => mul(j + 1, s))), n);
      return piecewise([mul(term1, term2), cond], [0, true]);
    }
    const base = cast(first(syms), IndexedBase);
    const j = new Sym('j', { positive: true, integer: true });
    const k = new Sym('k', { positive: true, integer: true });
    const term2 = Product(mul(pow(theta, base.at(j)), pow(mul(pow(add(j, 1), base.at(j)), factorial(base.at(j))), -1)), [j, 0, sub(n, 1)]);
    const cond = Eq(Sum(mul(add(k, 1), base.at(k)), [k, 0, sub(n, 1)]), n);
    return piecewise([mul(term1, term2), cond], [0, true]);
  }
}

/** A multivariate Ewens random vector (SymPy MultivariateEwens(syms, n, theta)). */
export function MultivariateEwens(syms: string | Sym, n: ExprLike, theta: ExprLike): RandomSymbol {
  return multivariateRv(new MultivariateEwensDistribution([sympify(n), sympify(theta)]), syms);
}

// ---------------------------------------------------------------------------
// Generalized multivariate log-gamma distribution
// ---------------------------------------------------------------------------

/** SymPy GeneralizedMultivariateLogGammaDistribution(delta, v, lamda, mu). */
export class GeneralizedMultivariateLogGammaDistribution extends JointDistribution {
  constructor(args: readonly Expr[]) {
    super('GeneralizedMultivariateLogGammaDistribution', args);
  }
  override get isContinuous(): boolean {
    return true;
  }
  get delta(): Expr {
    return this.arg(0);
  }
  get v(): Expr {
    return this.arg(1);
  }
  get lamda(): Expr {
    return this.arg(2);
  }
  get mu(): Expr {
    return this.arg(3);
  }
  check(): void {
    valueCheck([Ge(this.delta, 0), Le(this.delta, 1)], 'delta must be in range [0, 1].');
    valueCheck(Gt(this.v, 0), 'v must be positive');
    for (const lk of entries(this.lamda)) valueCheck(Gt(lk, 0), 'lamda must be a positive vector.');
    for (const muk of entries(this.mu)) valueCheck(Gt(muk, 0), 'mu must be a positive vector.');
    valueCheck(entries(this.lamda).length > 1, 'the distribution should have at least two random variables.');
  }
  get set(): SetExpr {
    return realsPower(sympify(entries(this.lamda).length));
  }
  pdf(...yIn: ExprLike[]): Expr {
    const [d, v] = [this.delta, this.v];
    const [l, mu] = [entries(this.lamda), entries(this.mu)];
    const y = yIn.map(sympify);
    const n = new Sym('n', { nonnegative: true, integer: true });
    const k = l.length;
    const sterm1 = mul(pow(sub(1, d), n), pow(mul(pow(gamma(add(v, n)), k - 1), gamma(v), gamma(add(n, 1))), -1));
    const sterm2 = mul(...mu.map((m, i) => mul(m, pow(at(l, i), sub(mul(-1, v), n)))));
    const sterm3 = mul(add(v, n), add(...mu.map((m, i) => mul(m, at(y, i)))));
    const sterm4 = add(...mu.map((m, i) => mul(exp(mul(m, at(y, i))), pow(at(l, i), -1))));
    return mul(pow(d, v), Sum(mul(sterm1, sterm2, exp(sub(sterm3, sterm4))), [n, 0, S.Infinity]));
  }
}

/** A generalized multivariate log-gamma random vector (SymPy GeneralizedMultivariateLogGamma(syms, delta, v, lamda, mu)). */
export function GeneralizedMultivariateLogGamma(syms: string | Sym, delta: ExprLike, v: ExprLike, lamda: readonly ExprLike[], mu: readonly ExprLike[]): RandomSymbol {
  return multivariateRv(new GeneralizedMultivariateLogGammaDistribution([sympify(delta), sympify(v), param(lamda), param(mu)]), syms);
}

/**
 * A generalized multivariate log-gamma random vector given the matrix
 * omega, whose determinant gives delta (SymPy
 * GeneralizedMultivariateLogGammaOmega(syms, omega, v, lamda, mu)).
 */
export function GeneralizedMultivariateLogGammaOmega(syms: string | Sym, omegaIn: Matrix | readonly (readonly ExprLike[])[], v: ExprLike, lamda: readonly ExprLike[], mu: readonly ExprLike[]): RandomSymbol {
  const omega = omegaIn instanceof Matrix ? omegaIn : Matrix.of(omegaIn);
  valueCheck(omega.isSquare, 'omega must be a square matrix');
  for (const val of omega.data) valueCheck([Ge(val, 0), Le(val, 1)], 'all values in matrix must be between 0 and 1(both inclusive).');
  valueCheck(Array.from({ length: omega.rows }, (_, i) => omega.get(i, i)).every((d) => d.key === S.One.key), 'all the elements of diagonal should be 1.');
  valueCheck([omega.rows === lamda.length, lamda.length === mu.length], 'lamda, mu should be of same length and omega should  be of shape (length of lamda, length of mu)');
  valueCheck(lamda.length > 1, 'the distribution should have at least two random variables.');
  const delta = pow(omega.det(), Rational.of(1n, BigInt(lamda.length - 1)));
  return GeneralizedMultivariateLogGamma(syms, delta, v, lamda, mu);
}

// ---------------------------------------------------------------------------
// Multinomial distribution
// ---------------------------------------------------------------------------

/** SymPy MultinomialDistribution(n, p). */
export class MultinomialDistribution extends JointDistribution {
  constructor(args: readonly Expr[]) {
    super('MultinomialDistribution', args);
  }
  override get isDiscrete(): boolean {
    return true;
  }
  get p(): Expr {
    return this.arg(1);
  }
  check(): void {
    valueCheck(Gt(this.arg(0), 0), 'number of trials must be a positive integer');
    for (const pk of entries(this.p)) valueCheck([Ge(pk, 0), Le(pk, 1)], 'probability must be in range [0, 1]');
    valueCheck(Eq(add(...entries(this.p)), 1), 'probabilities must sum to 1');
  }
  get set(): SetExpr {
    const s = intersection(Naturals0, interval(0, this.arg(0)));
    return productSet(...entries(this.p).map(() => s));
  }
  pdf(...xIn: ExprLike[]): Expr {
    const [n, p] = [this.arg(0), entries(this.p)];
    const x = xIn.map(sympify);
    const term1 = mul(factorial(n), pow(mul(...x.map((xk) => factorial(xk))), -1));
    const term2 = mul(...p.map((pk, i) => pow(pk, at(x, i))));
    return piecewise([mul(term1, term2), Eq(add(...x), n)], [0, true]);
  }
}

/** A multinomial random vector (SymPy Multinomial(syms, n, *p)): the probabilities as an array or one by one. */
export function Multinomial(syms: string | Sym, n: ExprLike, ...p: (ExprLike | readonly ExprLike[])[]): RandomSymbol {
  const ps = listOrArgs(p);
  return multivariateRv(new MultinomialDistribution([sympify(n), param(ps)]), syms);
}

// ---------------------------------------------------------------------------
// Negative multinomial distribution
// ---------------------------------------------------------------------------

/** SymPy NegativeMultinomialDistribution(k0, p). */
export class NegativeMultinomialDistribution extends JointDistribution {
  constructor(args: readonly Expr[]) {
    super('NegativeMultinomialDistribution', args);
  }
  override get isDiscrete(): boolean {
    return true;
  }
  get k0(): Expr {
    return this.arg(0);
  }
  get p(): Expr {
    return this.arg(1);
  }
  check(): void {
    valueCheck(Gt(this.k0, 0), 'number of failures must be a positive integer');
    for (const pk of entries(this.p)) valueCheck([Ge(pk, 0), Le(pk, 1)], 'probability must be in range [0, 1].');
    valueCheck(Le(add(...entries(this.p)), 1), 'success probabilities must not be greater than 1.');
  }
  get set(): SetExpr {
    return productSet(...entries(this.p).map(() => range(0, S.Infinity)));
  }
  pdf(...kIn: ExprLike[]): Expr {
    const [k0, p] = [this.k0, entries(this.p)];
    const k = kIn.map(sympify);
    const term1 = mul(gamma(add(k0, ...k)), pow(sub(1, add(...p)), k0), pow(gamma(k0), -1));
    const term2 = mul(...p.map((pi, i) => mul(pow(pi, at(k, i)), pow(factorial(at(k, i)), -1))));
    return mul(term1, term2);
  }
}

/** A negative multinomial random vector (SymPy NegativeMultinomial(syms, k0, *p)): the probabilities as an array or one by one. */
export function NegativeMultinomial(syms: string | Sym, k0: ExprLike, ...p: (ExprLike | readonly ExprLike[])[]): RandomSymbol {
  const ps = listOrArgs(p);
  return multivariateRv(new NegativeMultinomialDistribution([sympify(k0), param(ps)]), syms);
}

statsClasses.multivariateNormal = MultivariateNormal;
statsClasses.multivariateLaplace = MultivariateLaplace;

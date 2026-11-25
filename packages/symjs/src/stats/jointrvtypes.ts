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

import { Mul, Pow, Rational, S, Sym } from '../core/nodes';
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
import { factorial, gamma } from '../functions/special/special';
import { rf } from '../functions/combinatorial/factorials';
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
 * Constructs the marginal density for the components selected by integer indices or indexed symbols.
 *
 * @param rv - Random variable whose distribution is requested.
 * @param indicesIn - Component indices to retain.
 * @returns A lambda for the joint density of the retained components.
 * @throws RangeError when no component is selected.
 * @see SymPy `sympy.stats.joint_rv_types.marginal_distribution`
 * @example
 * ```ts
 * import { Lambda, MultivariateNormal, marginalDistribution } from '@symjs/symjs';
 *
 * const m = MultivariateNormal('X', [1, 2], [[2, 1], [1, 2]]);
 * (marginalDistribution(m, 0) as Lambda).call(1); // => 1/(2*sqrt(pi))
 * ```
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

/**
 * A joint distribution given by a Lambda density on a set.
 *
 * @see SymPy `sympy.stats.joint_rv_types.JointDistributionHandmade`
 */
export class JointDistributionHandmade extends JointDistribution {
  /**
   * Constructs a new `JointDistributionHandmade`.
   *
   * @param args - Operands in the order `pdf`, `set`.
   */
  constructor(args: readonly Expr[]) {
    super('JointDistributionHandmade', args);
  }
  /**
   * Indicates whether the probability law is continuous.
   *
   * @returns `true` for this distribution.
   * @see SymPy `sympy.stats.joint_rv_types.JointDistributionHandmade.is_Continuous`
   */
  override get isContinuous(): boolean {
    return true;
  }
  /**
   * Identifies the function defining the supplied joint density.
   *
   * @returns The density function.
   * @see SymPy `sympy.stats.joint_rv_types.JointDistributionHandmade.pdf`
   */
  get pdfLambda(): Expr {
    return this.arg(0);
  }
  /**
   * Specifies the set on which the probability law is supported.
   *
   * @returns The distribution's support.
   * @see SymPy `sympy.stats.joint_rv_types.JointDistributionHandmade.set`
   */
  get set(): SetExpr {
    return cast(this.arg(1), SetExpr, 'set');
  }
  /**
   * Evaluates the probability density at the supplied outcome.
   *
   * @param xs - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.joint_rv_types.JointDistributionHandmade.pdf`
   */
  pdf(...xs: ExprLike[]): Expr {
    return cast(this.pdfLambda, LambdaNode, 'pdf').call(...xs);
  }
}

/**
 * Constructs a joint random variable from a density expressed in its indexed components.
 *
 * @param symbolIn - Name or symbol for the random variable.
 * @param pdfIn - Joint density expressed in the indexed components.
 * @returns A random vector with the joint density of the components sym[i] in the expression.
 * @see SymPy `sympy.stats.joint_rv_types.JointRV`
 * @example
 * ```ts
 * import { IndexedBase, JointDistribution, JointRV, density, ex, exp } from '@symjs/symjs';
 *
 * const u = new IndexedBase('x').at(1), v = new IndexedBase('x').at(2);
 * const pdf = exp(u.pow(2).add(v.pow(2)).mul(ex`-1/2`).add(u).sub(ex`1/2`)).div(ex`2*pi`);
 * const X = JointRV('x', pdf);
 * (density(X) as JointDistribution).call(ex`1`, ex`2`); // => exp(-2)/(2*pi)
 * ```
 */
export function JointRV(symbolIn: string | Sym, pdfIn: ExprLike): RandomSymbol {
  const symbol = typeof symbolIn === 'string' ? new Sym(symbolIn) : symbolIn;
  const pdf = sympify(pdfIn);
  const found = new Map<string, Indexed>();
  const go = (e: Expr): void => {
    if (e instanceof Indexed && (e.base instanceof IndexedBase ? e.base.label : e.base).key === symbol.key) found.set(e.key, e);
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

/**
 * The normal law of a random vector with a specified mean vector and covariance matrix.
 *
 * @see SymPy `sympy.stats.joint_rv_types.MultivariateNormalDistribution`
 */
export class MultivariateNormalDistribution extends JointDistributionWithMarginal {
  /**
   * Constructs a new `MultivariateNormalDistribution`.
   *
   * @param args - Distribution parameters in the order `mu`, `sigma`.
   */
  constructor(args: readonly Expr[]) {
    super('MultivariateNormalDistribution', args);
  }
  /**
   * Indicates whether the probability law is continuous.
   *
   * @returns `true` for this distribution.
   * @see SymPy `sympy.stats.joint_rv_types.MultivariateNormalDistribution.is_Continuous`
   */
  override get isContinuous(): boolean {
    return true;
  }
  /**
   * Specifies the expected value of each coordinate.
   *
   * @returns The mean vector.
   * @see SymPy `sympy.stats.joint_rv_types.MultivariateNormalDistribution.mu`
   */
  get mu(): Expr {
    return this.arg(0);
  }
  /**
   * Describes joint dispersion using a positive semidefinite matrix.
   *
   * @returns The covariance matrix.
   * @see SymPy `sympy.stats.joint_rv_types.MultivariateNormalDistribution.sigma`
   */
  get sigma(): Expr {
    return this.arg(1);
  }
  /**
   * Specifies the set on which the probability law is supported.
   *
   * @returns The distribution's support.
   * @see SymPy `sympy.stats.joint_rv_types.MultivariateNormalDistribution.set`
   */
  get set(): SetExpr {
    return realsPower(at(shapeOf(this.mu), 0));
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters fail the requirement for compatible dimensions and a positive semidefinite covariance matrix.
   * @see SymPy `sympy.stats.joint_rv_types.MultivariateNormalDistribution.check`
   */
  check(): void {
    valueCheck(at(shapeOf(this.mu), 0).key === at(shapeOf(this.sigma), 0).key, 'Size of the mean vector and covariance matrix are incorrect.');
    // check if covariance matrix is positive semi definite or not
    if (!(this.sigma instanceof MatrixSymbolNode)) valueCheck(truthOf(isPositiveSemidefinite(explicit(this.sigma))), 'The covariance matrix must be positive semi definite. ');
  }
  /**
   * Evaluates the probability density at the supplied outcome.
   *
   * @param args - Coordinate values in component order.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.joint_rv_types.MultivariateNormalDistribution.pdf`
   */
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
    if (k instanceof Rational) return new MatrixElementNode(mul(norm, exp(quadS)), S.Zero, S.Zero);
    // Keep the multivariate normal's normalization under one square root,
    // when the dimension is symbolic and the covariance is a matrix symbol.
    const symbolicNorm = new Pow(mul(pow(mul(2, S.Pi), k), det(sigma)), Rational.of(-1, 2));
    return new MatrixElementNode(new Mul([symbolicNorm, exp(quadS)]), S.Zero, S.Zero);
  }
  /**
   * Integrates out the unselected coordinates of the joint distribution.
   *
   * @param indices - Component indices to retain.
   * @param sym - Name or symbol for the random variable.
   * @returns The marginal density.
   */
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

/**
 * Constructs a multivariate normal random vector.
 *
 * @param name - Name of the symbol.
 * @param mu - Mean vector.
 * @param sigma - Positive semidefinite covariance matrix.
 * @returns The random vector with this distribution.
 * @throws RangeError when the parameters fail the requirement for compatible dimensions and a positive semidefinite covariance matrix.
 * @see SymPy `sympy.stats.joint_rv_types.MultivariateNormal`
 * @remarks For the second marginal in the example, SymPy prints the equivalent factored exponent in `exp(-(y - 4)**2/4)/(2*sqrt(pi))`.
 * @example
 * ```ts
 * import { JointDistribution, Lambda, MultivariateNormal, density, ex, marginalDistribution } from '@symjs/symjs';
 *
 * const X = MultivariateNormal('X', [3, 4], [[2, 1], [1, 2]]);
 * (density(X) as JointDistribution).call(ex`1`, ex`2`); // => sqrt(3)*exp(-4/3)/(6*pi)
 * (marginalDistribution(X, 1) as Lambda).call(ex`y`); // => exp(-y**2/4 + 2*y - 4)/(2*sqrt(pi))
 * ```
 */
export function MultivariateNormal(name: string | Sym, mu: MatrixParam, sigma: MatrixParam): RandomSymbol {
  return multivariateRv(new MultivariateNormalDistribution([param(mu), param(sigma)]), name);
}

// ---------------------------------------------------------------------------
// Multivariate Laplace distribution
// ---------------------------------------------------------------------------

/**
 * A multivariate Laplace law parameterized by a vector and a positive definite matrix.
 *
 * @see SymPy `sympy.stats.joint_rv_types.MultivariateLaplaceDistribution`
 */
export class MultivariateLaplaceDistribution extends JointDistribution {
  /**
   * Constructs a new `MultivariateLaplaceDistribution`.
   *
   * @param args - Distribution parameters in the order `mu`, `sigma`.
   */
  constructor(args: readonly Expr[]) {
    super('MultivariateLaplaceDistribution', args);
  }
  /**
   * Indicates whether the probability law is continuous.
   *
   * @returns `true` for this distribution.
   * @see SymPy `sympy.stats.joint_rv_types.MultivariateLaplaceDistribution.is_Continuous`
   */
  override get isContinuous(): boolean {
    return true;
  }
  /**
   * Specifies the center of the multivariate law.
   *
   * @returns The location vector.
   * @see SymPy `sympy.stats.joint_rv_types.MultivariateLaplaceDistribution.mu`
   */
  get mu(): Expr {
    return this.arg(0);
  }
  /**
   * Defines multivariate scale by a positive definite matrix.
   *
   * @returns The scale matrix.
   * @see SymPy `sympy.stats.joint_rv_types.MultivariateLaplaceDistribution.sigma`
   */
  get sigma(): Expr {
    return this.arg(1);
  }
  /**
   * Specifies the set on which the probability law is supported.
   *
   * @returns The distribution's support.
   * @see SymPy `sympy.stats.joint_rv_types.MultivariateLaplaceDistribution.set`
   */
  get set(): SetExpr {
    return realsPower(at(shapeOf(this.mu), 0));
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters fail the requirement for compatible dimensions and a positive definite scale matrix.
   * @see SymPy `sympy.stats.joint_rv_types.MultivariateLaplaceDistribution.check`
   */
  check(): void {
    valueCheck(at(shapeOf(this.mu), 0).key === at(shapeOf(this.sigma), 0).key, 'Size of the mean vector and covariance matrix are incorrect.');
    // check if covariance matrix is positive definite or not
    if (!(this.sigma instanceof MatrixSymbolNode)) valueCheck(truthOf(isPositiveDefinite(explicit(this.sigma))), 'The covariance matrix must be positive definite. ');
  }
  /**
   * Evaluates the probability density at the supplied outcome.
   *
   * @param xs - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.joint_rv_types.MultivariateLaplaceDistribution.pdf`
   */
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

/**
 * Constructs a multivariate Laplace random vector.
 *
 * @param name - Name of the symbol.
 * @param mu - Location vector.
 * @param sigma - Positive definite scale matrix.
 * @returns The random vector with this distribution.
 * @throws RangeError when the parameters fail the requirement for compatible dimensions and a positive definite scale matrix.
 * @see SymPy `sympy.stats.joint_rv_types.MultivariateLaplace`
 * @example
 * ```ts
 * import { JointDistribution, MultivariateLaplace, density, ex } from '@symjs/symjs';
 *
 * const X = MultivariateLaplace('X', [2, 4], [[3, 1], [1, 3]]);
 * (density(X) as JointDistribution).call(ex`1`, ex`2`); // => sqrt(2)*exp(11/4)*besselk(0, sqrt(165)/4)/(4*pi)
 * ```
 */
export function MultivariateLaplace(name: string | Sym, mu: MatrixParam, sigma: MatrixParam): RandomSymbol {
  return multivariateRv(new MultivariateLaplaceDistribution([param(mu), param(sigma)]), name);
}

// ---------------------------------------------------------------------------
// Multivariate Student t distribution
// ---------------------------------------------------------------------------

/**
 * A multivariate Student t law with a location vector, shape matrix, and degrees of freedom.
 *
 * @see SymPy `sympy.stats.joint_rv_types.MultivariateTDistribution`
 */
export class MultivariateTDistribution extends JointDistribution {
  /**
   * Constructs a new `MultivariateTDistribution`.
   *
   * @param args - Distribution parameters in the order `mu`, `shape_mat`, `dof`.
   */
  constructor(args: readonly Expr[]) {
    super('MultivariateTDistribution', args);
  }
  /**
   * Indicates whether the probability law is continuous.
   *
   * @returns `true` for this distribution.
   * @see SymPy `sympy.stats.joint_rv_types.MultivariateTDistribution.is_Continuous`
   */
  override get isContinuous(): boolean {
    return true;
  }
  /**
   * Specifies the center of the multivariate law.
   *
   * @returns The location vector.
   * @see SymPy `sympy.stats.joint_rv_types.MultivariateTDistribution.mu`
   */
  get mu(): Expr {
    return this.arg(0);
  }
  /**
   * Specifies how the multivariate distribution is shaped across coordinates.
   *
   * @returns The shape matrix.
   * @see SymPy `sympy.stats.joint_rv_types.MultivariateTDistribution.shape_mat`
   */
  get shapeMat(): Expr {
    return this.arg(1);
  }
  /**
   * Gives the degrees of freedom that parametrize the distribution.
   *
   * @returns The degrees of freedom.
   * @see SymPy `sympy.stats.joint_rv_types.MultivariateTDistribution.dof`
   */
  get dof(): Expr {
    return this.arg(2);
  }
  /**
   * Specifies the set on which the probability law is supported.
   *
   * @returns The distribution's support.
   * @see SymPy `sympy.stats.joint_rv_types.MultivariateTDistribution.set`
   */
  get set(): SetExpr {
    return realsPower(at(shapeOf(this.mu), 0));
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters fail the requirement for compatible dimensions and a positive definite shape matrix.
   * @see SymPy `sympy.stats.joint_rv_types.MultivariateTDistribution.check`
   */
  check(): void {
    valueCheck(at(shapeOf(this.mu), 0).key === at(shapeOf(this.shapeMat), 0).key, 'Size of the location vector and shape matrix are incorrect.');
    // check if covariance matrix is positive definite or not
    if (!(this.shapeMat instanceof MatrixSymbolNode)) valueCheck(truthOf(isPositiveDefinite(explicit(this.shapeMat))), 'The shape matrix must be positive definite. ');
  }
  /**
   * Evaluates the probability density at the supplied outcome.
   *
   * @param xs - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.joint_rv_types.MultivariateTDistribution.pdf`
   */
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

/**
 * Constructs a multivariate Student t random vector.
 *
 * @param name - Name of the symbol.
 * @param mu - Location vector.
 * @param sigma - Positive definite shape matrix.
 * @param v - Degrees of freedom.
 * @returns The random vector with this distribution.
 * @throws RangeError when the parameters fail the requirement for compatible dimensions and a positive definite shape matrix.
 * @see SymPy `sympy.stats.joint_rv_types.MultivariateT`
 * @example
 * ```ts
 * import { JointDistribution, MultivariateT, density, ex } from '@symjs/symjs';
 *
 * const X = MultivariateT('X', [1, 1], [[1, 0], [0, 1]], 2);
 * (density(X) as JointDistribution).call(ex`1`, ex`2`); // => 2/(9*pi)
 * ```
 */
export function MultivariateT(name: string | Sym, mu: MatrixParam, sigma: MatrixParam, v: ExprLike): RandomSymbol {
  return multivariateRv(new MultivariateTDistribution([param(mu), param(sigma), sympify(v)]), name);
}

// ---------------------------------------------------------------------------
// Normal-gamma distribution
// ---------------------------------------------------------------------------

/**
 * The joint law of a normally distributed component conditional on a gamma-distributed precision.
 *
 * @see SymPy `sympy.stats.joint_rv_types.NormalGammaDistribution`
 */
export class NormalGammaDistribution extends JointDistributionWithMarginal {
  /**
   * Constructs a new `NormalGammaDistribution`.
   *
   * @param args - Distribution parameters in the order `mu`, `lamda`, `alpha`, `beta`.
   */
  constructor(args: readonly Expr[]) {
    super('NormalGammaDistribution', args);
  }
  /**
   * Indicates whether the probability law is continuous.
   *
   * @returns `true` for this distribution.
   * @see SymPy `sympy.stats.joint_rv_types.NormalGammaDistribution.is_Continuous`
   */
  override get isContinuous(): boolean {
    return true;
  }
  /**
   * Specifies the location of the conditional normal law.
   *
   * @returns The conditional mean parameter.
   * @see SymPy `sympy.stats.joint_rv_types.NormalGammaDistribution.mu`
   */
  get mu(): Expr {
    return this.arg(0);
  }
  /**
   * Scales the precision of the conditional normal distribution.
   *
   * @returns The positive precision factor.
   * @see SymPy `sympy.stats.joint_rv_types.NormalGammaDistribution.lamda`
   */
  get lamda(): Expr {
    return this.arg(1);
  }
  /**
   * Sets the shape of the gamma component.
   *
   * @returns The gamma shape parameter.
   * @see SymPy `sympy.stats.joint_rv_types.NormalGammaDistribution.alpha`
   */
  get alpha(): Expr {
    return this.arg(2);
  }
  /**
   * Sets the rate of the gamma component.
   *
   * @returns The gamma rate parameter.
   * @see SymPy `sympy.stats.joint_rv_types.NormalGammaDistribution.beta`
   */
  get beta(): Expr {
    return this.arg(3);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters fail the requirement for real location, positive precision factor, and positive gamma shape and rate.
   * @see SymPy `sympy.stats.joint_rv_types.NormalGammaDistribution.check`
   */
  check(): void {
    valueCheck(truthOf(isReal(this.mu)), 'Location must be real.');
    valueCheck(Gt(this.lamda, 0), 'Lambda must be positive');
    valueCheck(Gt(this.alpha, 0), 'alpha must be positive');
    valueCheck(Gt(this.beta, 0), 'beta must be positive');
  }
  /**
   * Specifies the set on which the probability law is supported.
   *
   * @returns The distribution's support.
   * @see SymPy `sympy.stats.joint_rv_types.NormalGammaDistribution.set`
   */
  get set(): SetExpr {
    return productSet(Reals, interval(0, S.Infinity));
  }
  /**
   * Evaluates the probability density at the supplied outcome.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @param tauIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.joint_rv_types.NormalGammaDistribution.pdf`
   */
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
  /**
   * Integrates out the unselected coordinates of the joint distribution.
   *
   * @param indices - Component indices to retain.
   * @param sym - Name or symbol for the random variable.
   * @returns The marginal density.
   * @throws TypeError when the selected coordinates require both normal and precision arguments.
   */
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

/**
 * Constructs a normal-gamma random vector.
 *
 * @param sym - Name or symbol for the random variable.
 * @param mu - Conditional normal location.
 * @param lamda - Positive scaling factor for the precision.
 * @param alpha - Gamma shape.
 * @param beta - Gamma rate.
 * @returns The random vector with this distribution.
 * @throws RangeError when the parameters fail the requirement for real location, positive precision factor, and positive gamma shape and rate.
 * @see SymPy `sympy.stats.joint_rv_types.NormalGamma`
 * @example
 * ```ts
 * import { JointDistribution, NormalGamma, density, ex } from '@symjs/symjs';
 *
 * const X = NormalGamma('X', 0, 1, 2, 3);
 * (density(X) as JointDistribution).call(ex`1`, ex`2`); // => 18*exp(-7)/sqrt(pi)
 * ```
 */
export function NormalGamma(sym: string | Sym, mu: ExprLike, lamda: ExprLike, alpha: ExprLike, beta: ExprLike): RandomSymbol {
  return multivariateRv(new NormalGammaDistribution([mu, lamda, alpha, beta].map(sympify)), sym);
}

// ---------------------------------------------------------------------------
// Multivariate beta (Dirichlet) distribution
// ---------------------------------------------------------------------------

/**
 * The Dirichlet law of a vector of proportions with a specified concentration for each category.
 *
 * @see SymPy `sympy.stats.joint_rv_types.MultivariateBetaDistribution`
 */
export class MultivariateBetaDistribution extends JointDistributionWithMarginal {
  /**
   * Constructs a new `MultivariateBetaDistribution`.
   *
   * @param args - Distribution parameters in the order `alpha`.
   */
  constructor(args: readonly Expr[]) {
    super('MultivariateBetaDistribution', args);
  }
  /**
   * Indicates whether the probability law is continuous.
   *
   * @returns `true` for this distribution.
   * @see SymPy `sympy.stats.joint_rv_types.MultivariateBetaDistribution.is_Continuous`
   */
  override get isContinuous(): boolean {
    return true;
  }
  /**
   * Specifies the concentration of each category.
   *
   * @returns The concentration vector.
   * @see SymPy `sympy.stats.joint_rv_types.MultivariateBetaDistribution.alpha`
   */
  get alpha(): Expr {
    return this.arg(0);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters fail the requirement for at least two positive concentration parameters.
   * @see SymPy `sympy.stats.joint_rv_types.MultivariateBetaDistribution.check`
   */
  check(): void {
    const alpha = entries(this.alpha);
    valueCheck(alpha.length >= 2, 'At least two categories should be passed.');
    for (const a of alpha) valueCheck(Gt(a, 0) !== S.false, 'Each concentration parameter should be positive.');
  }
  /**
   * Specifies the set on which the probability law is supported.
   *
   * @returns The distribution's support.
   * @see SymPy `sympy.stats.joint_rv_types.MultivariateBetaDistribution.set`
   */
  get set(): SetExpr {
    return productSet(...entries(this.alpha).map(() => interval(0, 1)));
  }
  /**
   * Evaluates the probability density at the supplied outcome.
   *
   * @param syms - Name or symbol for the random vector.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.joint_rv_types.MultivariateBetaDistribution.pdf`
   */
  pdf(...syms: ExprLike[]): Expr {
    const alpha = entries(this.alpha);
    const B = mul(...alpha.map((a) => gamma(a)), pow(gamma(add(...alpha)), -1));
    return mul(...alpha.map((a, i) => pow(sympify(at(syms, i)), sub(a, 1))), pow(B, -1));
  }
  /**
   * The density of the selected proportions. The remaining categories are merged into one, so the
   * selected proportions and their complement follow a Dirichlet law; one proportion follows
   * `Beta(alpha_i, sum(alpha) - alpha_i)`.
   *
   * @param indices - Component indices to retain.
   * @param sym - Name or symbol for the random vector.
   * @returns The marginal density.
   */
  marginalDistributionOf(indices: readonly Expr[], sym: Sym): Expr {
    const alpha = entries(this.alpha);
    const flat = indices.flatMap((i) => (i instanceof TupleNode ? [...i.args] : [i]));
    const kept = flat.map((i) => Number(i.toString()));
    const v = flat.map((i) => new Indexed([sym, i]));
    const rest = alpha.filter((_, i) => !kept.includes(i));
    if (!rest.length) return Lambda(v, this.pdf(...alpha.map((_, i) => at(v, kept.indexOf(i)))));
    const a = kept.map((i) => at(alpha, i));
    const r = add(...rest);
    const B = mul(...a.map((ai) => gamma(ai)), gamma(r), pow(gamma(add(...alpha)), -1));
    const density = mul(...a.map((ai, j) => pow(at(v, j), sub(ai, 1))), pow(sub(1, add(...v)), sub(r, 1)), pow(B, -1));
    return Lambda(v, density);
  }
}

/**
 * Constructs a multivariate beta (Dirichlet) random vector, accepting the parameters separately or as
 * an array.
 *
 * @param syms - Name or symbol for the random vector.
 * @param alpha - Positive concentration parameters, as an array or separate values.
 * @returns The random vector with this distribution.
 * @throws RangeError when the parameters fail the requirement for at least two positive concentration parameters.
 * @see SymPy `sympy.stats.joint_rv_types.MultivariateBeta`
 * @example
 * ```ts
 * import { JointDistribution, MultivariateBeta, density, ex } from '@symjs/symjs';
 *
 * const X = MultivariateBeta('X', [2, 3]);
 * (density(X) as JointDistribution).call(ex`1/2`, ex`1/2`); // => 3/2
 * ```
 */
export function MultivariateBeta(syms: string | Sym, ...alpha: (ExprLike | readonly ExprLike[])[]): RandomSymbol {
  const a = listOrArgs(alpha);
  return multivariateRv(new MultivariateBetaDistribution([param(a)]), syms);
}

/**
 * Creates a random vector with a Dirichlet distribution.
 *
 * @param syms - Name or symbol for the random vector.
 * @param alpha - Positive concentration parameters, as an array or separate values.
 * @returns The random vector with this distribution.
 * @throws RangeError when the parameters fail the requirement for at least two positive concentration parameters.
 * @see SymPy `sympy.stats.joint_rv_types.MultivariateBeta`
 * @example
 * ```ts
 * import { Dirichlet, JointDistribution, density, ex } from '@symjs/symjs';
 *
 * const X = Dirichlet('X', [2, 3]);
 * (density(X) as JointDistribution).call(ex`1/2`, ex`1/2`); // => 3/2
 * ```
 */
export const Dirichlet = MultivariateBeta;

// ---------------------------------------------------------------------------
// Multivariate Ewens distribution
// ---------------------------------------------------------------------------

/**
 * The Ewens sampling law for the counts of groups of each size in a sample.
 *
 * @see SymPy `sympy.stats.joint_rv_types.MultivariateEwensDistribution`
 */
export class MultivariateEwensDistribution extends JointDistribution {
  /**
   * Constructs a new `MultivariateEwensDistribution`.
   *
   * @param args - Distribution parameters in the order `n`, `theta`.
   */
  constructor(args: readonly Expr[]) {
    super('MultivariateEwensDistribution', args);
  }
  /**
   * Indicates whether the law is discrete.
   *
   * @returns `true` for this distribution.
   * @see SymPy `sympy.stats.joint_rv_types.MultivariateEwensDistribution.is_Discrete`
   */
  override get isDiscrete(): boolean {
    return true;
  }
  /**
   * Controls mutation in the distribution.
   *
   * @returns The positive mutation parameter.
   * @see SymPy `sympy.stats.joint_rv_types.MultivariateEwensDistribution.theta`
   */
  get theta(): Expr {
    return this.arg(1);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters fail the requirement for a positive integer sample size and a positive mutation parameter.
   * @see SymPy `sympy.stats.joint_rv_types.MultivariateEwensDistribution.check`
   */
  check(): void {
    valueCheck(Gt(this.arg(0), 0), 'sample size should be positive integer.');
    valueCheck(truthOf(isPositive(this.theta)), 'mutation rate should be positive.');
  }
  /**
   * Specifies the set on which the probability law is supported.
   *
   * @returns The distribution's support.
   * @throws NotImplementedError when the dimension is symbolic.
   * @see SymPy `sympy.stats.joint_rv_types.MultivariateEwensDistribution.set`
   */
  get set(): SetExpr {
    const n = this.arg(0);
    // SymPy: Product(Intersection(Naturals0, Interval(0, n//i)), (i, 1, n)), a product of sets that is not a set
    if (!isInteger(n)) throw new NotImplementedError('the set of a multivariate Ewens distribution of symbolic dimension is not implemented');
    const k = Number(n.toString());
    return productSet(range(0, k + 1), ...Array.from({ length: k - 1 }, (_, j) => range(0, Math.floor(k / (j + 2)) + 1)));
  }
  /**
   * Evaluates the probability density at the supplied outcome.
   *
   * @param syms - Name or symbol for the random vector.
   * @returns The density evaluated at the supplied outcome.
   * @throws RangeError when a symbolic dimension is used without an indexed base.
   * @see SymPy `sympy.stats.joint_rv_types.MultivariateEwensDistribution.pdf`
   */
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

/**
 * Constructs a multivariate Ewens random vector.
 *
 * @param syms - Name or symbol for the random vector.
 * @param n - Sample size.
 * @param theta - Positive mutation parameter.
 * @returns The random vector with this distribution.
 * @throws RangeError when the parameters fail the requirement for a positive integer sample size and a positive mutation parameter.
 * @see SymPy `sympy.stats.joint_rv_types.MultivariateEwens`
 * @example
 * ```ts
 * import { JointDistribution, MultivariateEwens, density, ex } from '@symjs/symjs';
 *
 * const X = MultivariateEwens('X', 2, 1);
 * (density(X) as JointDistribution).call(ex`2`, ex`0`); // => 1/2
 * ```
 */
export function MultivariateEwens(syms: string | Sym, n: ExprLike, theta: ExprLike): RandomSymbol {
  return multivariateRv(new MultivariateEwensDistribution([sympify(n), sympify(theta)]), syms);
}

// ---------------------------------------------------------------------------
// Generalized multivariate log-gamma distribution
// ---------------------------------------------------------------------------

/**
 * A joint log-gamma law with dependence parameter `delta` and component-specific parameters.
 *
 * @see SymPy `sympy.stats.joint_rv_types.GeneralizedMultivariateLogGammaDistribution`
 */
export class GeneralizedMultivariateLogGammaDistribution extends JointDistribution {
  /**
   * Constructs a new `GeneralizedMultivariateLogGammaDistribution`.
   *
   * @param args - Distribution parameters in the order `delta`, `v`, `lamda`, `mu`.
   */
  constructor(args: readonly Expr[]) {
    super('GeneralizedMultivariateLogGammaDistribution', args);
  }
  /**
   * Indicates whether the probability law is continuous.
   *
   * @returns `true` for this distribution.
   * @see SymPy `sympy.stats.joint_rv_types.GeneralizedMultivariateLogGammaDistribution.is_Continuous`
   */
  override get isContinuous(): boolean {
    return true;
  }
  /**
   * Sets the dependence strength between zero and one.
   *
   * @returns The dependence parameter.
   * @see SymPy `sympy.stats.joint_rv_types.GeneralizedMultivariateLogGammaDistribution.delta`
   */
  get delta(): Expr {
    return this.arg(0);
  }
  /**
   * Specifies the distribution's positive shape parameter.
   *
   * @returns The shape value.
   * @see SymPy `sympy.stats.joint_rv_types.GeneralizedMultivariateLogGammaDistribution.v`
   */
  get v(): Expr {
    return this.arg(1);
  }
  /**
   * Specifies the positive parameter of each component.
   *
   * @returns The component parameter vector.
   * @see SymPy `sympy.stats.joint_rv_types.GeneralizedMultivariateLogGammaDistribution.lamda`
   */
  get lamda(): Expr {
    return this.arg(2);
  }
  /**
   * Specifies the positive scale of each component.
   *
   * @returns The vector of scales.
   * @see SymPy `sympy.stats.joint_rv_types.GeneralizedMultivariateLogGammaDistribution.mu`
   */
  get mu(): Expr {
    return this.arg(3);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters fail the requirement for a dependence parameter in the closed unit interval, positive shape and positive component parameters for at least two coordinates.
   * @see SymPy `sympy.stats.joint_rv_types.GeneralizedMultivariateLogGammaDistribution.check`
   */
  check(): void {
    valueCheck([Ge(this.delta, 0), Le(this.delta, 1)], 'delta must be in range [0, 1].');
    valueCheck(Gt(this.v, 0), 'v must be positive');
    for (const lk of entries(this.lamda)) valueCheck(Gt(lk, 0), 'lamda must be a positive vector.');
    for (const muk of entries(this.mu)) valueCheck(Gt(muk, 0), 'mu must be a positive vector.');
    valueCheck(entries(this.lamda).length > 1, 'the distribution should have at least two random variables.');
  }
  /**
   * Specifies the set on which the probability law is supported.
   *
   * @returns The distribution's support.
   * @see SymPy `sympy.stats.joint_rv_types.GeneralizedMultivariateLogGammaDistribution.set`
   */
  get set(): SetExpr {
    return realsPower(sympify(entries(this.lamda).length));
  }
  /**
   * Evaluates the probability density at the supplied outcome.
   *
   * @param yIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.joint_rv_types.GeneralizedMultivariateLogGammaDistribution.pdf`
   */
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

/**
 * Constructs a generalized multivariate log-gamma random vector.
 *
 * @param syms - Name or symbol for the random vector.
 * @param delta - Dependence parameter between zero and one.
 * @param v - Positive shape parameter.
 * @param lamda - Vector of positive component parameters.
 * @param mu - Vector of positive component scales.
 * @returns The random vector with this distribution.
 * @throws RangeError when the parameters fail the requirement for a dependence parameter in the closed unit interval, positive shape and positive component parameters for at least two coordinates.
 * @see SymPy `sympy.stats.joint_rv_types.GeneralizedMultivariateLogGamma`
 * @remarks SymPy writes the same density at the origin as `Sum(exp(-3)/(2**n*gamma(n + 1)**3), (n, 0, oo))/2`.
 * @example
 * ```ts
 * import { GeneralizedMultivariateLogGamma, JointDistribution, density, ex } from '@symjs/symjs';
 *
 * const X = GeneralizedMultivariateLogGamma('X', ex`1/2`, 1, [1, 1, 1], [1, 1, 1]); // => X
 * (density(X) as JointDistribution).call(ex`0`, ex`0`, ex`0`); // => Sum((1/2)**n*exp(-3)/gamma(n + 1)**3, (n, 0, oo))/2
 * ```
 */
export function GeneralizedMultivariateLogGamma(syms: string | Sym, delta: ExprLike, v: ExprLike, lamda: readonly ExprLike[], mu: readonly ExprLike[]): RandomSymbol {
  return multivariateRv(new GeneralizedMultivariateLogGammaDistribution([sympify(delta), sympify(v), param(lamda), param(mu)]), syms);
}

/**
 * Constructs a generalized multivariate log-gamma random vector using the determinant of the supplied
 * matrix for the dependence parameter.
 *
 * @param syms - Name or symbol for the random vector.
 * @param omegaIn - Square dependence matrix with unit diagonal.
 * @param v - Positive shape parameter.
 * @param lamda - Vector of positive component parameters.
 * @param mu - Vector of positive component scales.
 * @returns The random vector with this distribution.
 * @throws RangeError when the parameters fail the requirement for a square matrix with ones on its diagonal and compatible positive parameter vectors of length at least two.
 * @see SymPy `sympy.stats.joint_rv_types.GeneralizedMultivariateLogGammaOmega`
 * @remarks SymPy writes the same density at the origin as `3*Sum(exp(-2)/(4**n*gamma(n + 1)**2), (n, 0, oo))/4`.
 * @example
 * ```ts
 * import { GeneralizedMultivariateLogGammaOmega, JointDistribution, density, ex } from '@symjs/symjs';
 *
 * const X = GeneralizedMultivariateLogGammaOmega('X', [[1, ex`1/2`], [ex`1/2`, 1]], 1, [1, 1], [1, 1]); // => X
 * (density(X) as JointDistribution).call(ex`0`, ex`0`); // => 3*Sum((1/4)**n*exp(-2)/gamma(n + 1)**2, (n, 0, oo))/4
 * ```
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

/**
 * The joint counts of mutually exclusive categories in a fixed number of independent trials.
 *
 * @see SymPy `sympy.stats.joint_rv_types.MultinomialDistribution`
 */
export class MultinomialDistribution extends JointDistribution {
  /**
   * Constructs a new `MultinomialDistribution`.
   *
   * @param args - Distribution parameters in the order `n`, `p`.
   */
  constructor(args: readonly Expr[]) {
    super('MultinomialDistribution', args);
  }
  /**
   * Indicates whether the law is discrete.
   *
   * @returns `true` for this distribution.
   * @see SymPy `sympy.stats.joint_rv_types.MultinomialDistribution.is_Discrete`
   */
  override get isDiscrete(): boolean {
    return true;
  }
  /**
   * Assigns probabilities summing to one across the categories.
   *
   * @returns The category probability vector.
   * @see SymPy `sympy.stats.joint_rv_types.MultinomialDistribution.p`
   */
  get p(): Expr {
    return this.arg(1);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters fail the requirement for a positive integer trial count and probabilities in the closed unit interval that sum to one.
   * @see SymPy `sympy.stats.joint_rv_types.MultinomialDistribution.check`
   */
  check(): void {
    valueCheck(Gt(this.arg(0), 0), 'number of trials must be a positive integer');
    for (const pk of entries(this.p)) valueCheck([Ge(pk, 0), Le(pk, 1)], 'probability must be in range [0, 1]');
    valueCheck(Eq(add(...entries(this.p)), 1), 'probabilities must sum to 1');
  }
  /**
   * Specifies the set on which the probability law is supported.
   *
   * @returns The distribution's support.
   * @see SymPy `sympy.stats.joint_rv_types.MultinomialDistribution.set`
   */
  get set(): SetExpr {
    const s = intersection(Naturals0, interval(0, this.arg(0)));
    return productSet(...entries(this.p).map(() => s));
  }
  /**
   * Evaluates the probability density at the supplied outcome.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.joint_rv_types.MultinomialDistribution.pdf`
   */
  pdf(...xIn: ExprLike[]): Expr {
    const [n, p] = [this.arg(0), entries(this.p)];
    const x = xIn.map(sympify);
    const term1 = mul(factorial(n), pow(mul(...x.map((xk) => factorial(xk))), -1));
    const term2 = mul(...p.map((pk, i) => pow(pk, at(x, i))));
    return piecewise([mul(term1, term2), Eq(add(...x), n)], [0, true]);
  }
}

/**
 * Constructs a multinomial random vector, accepting the probabilities separately or as an array.
 *
 * @param syms - Name or symbol for the random vector.
 * @param n - Positive integer number of trials.
 * @param p - Category probabilities summing to one.
 * @returns The random vector with this distribution.
 * @throws RangeError when the parameters fail the requirement for a positive integer trial count and probabilities in the closed unit interval that sum to one.
 * @see SymPy `sympy.stats.joint_rv_types.Multinomial`
 * @example
 * ```ts
 * import { JointDistribution, Multinomial, density, ex } from '@symjs/symjs';
 *
 * const X = Multinomial('X', 3, ex`1/2`, ex`1/2`);
 * (density(X) as JointDistribution).call(ex`1`, ex`2`); // => 3/8
 * ```
 */
export function Multinomial(syms: string | Sym, n: ExprLike, ...p: (ExprLike | readonly ExprLike[])[]): RandomSymbol {
  const ps = listOrArgs(p);
  return multivariateRv(new MultinomialDistribution([sympify(n), param(ps)]), syms);
}

// ---------------------------------------------------------------------------
// Negative multinomial distribution
// ---------------------------------------------------------------------------

/**
 * The joint counts of successes in several categories before a fixed number of failures.
 *
 * @see SymPy `sympy.stats.joint_rv_types.NegativeMultinomialDistribution`
 */
export class NegativeMultinomialDistribution extends JointDistribution {
  /**
   * Constructs a new `NegativeMultinomialDistribution`.
   *
   * @param args - Distribution parameters in the order `k0`, `p`.
   */
  constructor(args: readonly Expr[]) {
    super('NegativeMultinomialDistribution', args);
  }
  /**
   * Indicates whether the law is discrete.
   *
   * @returns `true` for this distribution.
   * @see SymPy `sympy.stats.joint_rv_types.NegativeMultinomialDistribution.is_Discrete`
   */
  override get isDiscrete(): boolean {
    return true;
  }
  /**
   * Specifies how many failures terminate sampling.
   *
   * @returns The stopping count.
   * @see SymPy `sympy.stats.joint_rv_types.NegativeMultinomialDistribution.k0`
   */
  get k0(): Expr {
    return this.arg(0);
  }
  /**
   * Assigns probabilities to the successful outcome categories.
   *
   * @returns The success probability vector.
   * @see SymPy `sympy.stats.joint_rv_types.NegativeMultinomialDistribution.p`
   */
  get p(): Expr {
    return this.arg(1);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters fail the requirement for a positive integer failure count and probabilities in the closed unit interval whose sum is at most one.
   * @see SymPy `sympy.stats.joint_rv_types.NegativeMultinomialDistribution.check`
   */
  check(): void {
    valueCheck(Gt(this.k0, 0), 'number of failures must be a positive integer');
    for (const pk of entries(this.p)) valueCheck([Ge(pk, 0), Le(pk, 1)], 'probability must be in range [0, 1].');
    valueCheck(Le(add(...entries(this.p)), 1), 'success probabilities must not be greater than 1.');
  }
  /**
   * Specifies the set on which the probability law is supported.
   *
   * @returns The distribution's support.
   * @see SymPy `sympy.stats.joint_rv_types.NegativeMultinomialDistribution.set`
   */
  get set(): SetExpr {
    return productSet(...entries(this.p).map(() => range(0, S.Infinity)));
  }
  /**
   * Evaluates the probability density at the supplied outcome.
   *
   * @param kIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.joint_rv_types.NegativeMultinomialDistribution.pdf`
   */
  pdf(...kIn: ExprLike[]): Expr {
    const [k0, p] = [this.k0, entries(this.p)];
    const k = kIn.map(sympify);
    const term1 = mul(gamma(add(k0, ...k)), pow(sub(1, add(...p)), k0), pow(gamma(k0), -1));
    const term2 = mul(...p.map((pi, i) => mul(pow(pi, at(k, i)), pow(factorial(at(k, i)), -1))));
    return mul(term1, term2);
  }
}

/**
 * Constructs a negative multinomial random vector, accepting the probabilities separately or as an
 * array.
 *
 * @param syms - Name or symbol for the random vector.
 * @param k0 - Number of failures at which to stop.
 * @param p - Probabilities of the success categories.
 * @returns The random vector with this distribution.
 * @throws RangeError when the parameters fail the requirement for a positive integer failure count and probabilities in the closed unit interval whose sum is at most one.
 * @see SymPy `sympy.stats.joint_rv_types.NegativeMultinomial`
 * @example
 * ```ts
 * import { JointDistribution, NegativeMultinomial, density, ex } from '@symjs/symjs';
 *
 * const X = NegativeMultinomial('X', 3, ex`1/4`, ex`1/4`);
 * (density(X) as JointDistribution).call(ex`1`, ex`2`); // => 15/256
 * ```
 */
export function NegativeMultinomial(syms: string | Sym, k0: ExprLike, ...p: (ExprLike | readonly ExprLike[])[]): RandomSymbol {
  const ps = listOrArgs(p);
  return multivariateRv(new NegativeMultinomialDistribution([sympify(k0), param(ps)]), syms);
}

statsClasses.multivariateNormal = MultivariateNormal;
statsClasses.multivariateLaplace = MultivariateLaplace;

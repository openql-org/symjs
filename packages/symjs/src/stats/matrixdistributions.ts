// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/stats/matrix_distributions.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.stats.matrix_distributions: probability spaces and
 * distributions of random matrices (matrix gamma, Wishart, matrix normal
 * and matrix Student's t). A random matrix is a RandomMatrixSymbol of a
 * MatrixPSpace, and its density is the distribution, applied to a matrix
 * (`density(M).call(X)`, SymPy `density(M)(X)`).
 *
 * Sampling (SymPy sample with scipy, numpy or pymc) is not ported.
 */

import { Float, Rational, S } from '../core/nodes';
import type { Expr, ExprLike, Sym } from '../core/nodes';
import { add, exp, mul, pow, sympify } from '../core/ops';
import { isIntegerQ, isPositive } from '../core/assumptions';
import { NotImplementedError } from '../core/errors';
import { at, cast } from '../core/guard';
import { Reals } from '../sets/sets';
import type { SetExpr } from '../sets/sets';
import { multigamma } from '../functions/combinatorial/numbers';
import { Matrix } from '../matrices/matrix';
import { isPositiveDefinite } from '../matrices/linalg';
import { DeterminantNode, ImmutableMatrixNode, InverseNode, MatrixExpr, MatrixSymbolNode, TraceNode, TransposeNode } from '../matrices/expressions/matexpr';
import { MatrixSetNode } from '../matrices/expressions/misc';
import { Distribution, MatrixDomain, PSpace, RandomMatrixSymbol, randomMatrixSymbols, symbolConverter, valueCheck } from './rv';
import type { DensityResult } from './rv';

/** A matrix argument: a matrix expression, an explicit matrix or nested arrays. */
export type MatrixInput = ExprLike | Matrix | readonly (ExprLike | readonly ExprLike[])[];

/**
 * A matrix argument as a matrix expression (SymPy ImmutableMatrix(list)):
 * a list of rows, a list of scalars (a column) or a list of matrices of one
 * row (stacked).
 */
export function toMatrixArg(x: MatrixInput): Expr {
  if (x instanceof Matrix) return new ImmutableMatrixNode(x);
  if (!isList(x)) return sympify(x);
  const rows: Expr[][] = x.map((r) => {
    if (isRow(r)) return r.map((e) => sympify(e));
    const e = sympify(r);
    return e instanceof MatrixExpr ? e.asExplicit().toArray().flat() : [e];
  });
  const cols = at(rows, 0).length;
  if (rows.some((r) => r.length !== cols)) throw new RangeError('mismatched dimensions');
  return new ImmutableMatrixNode(Matrix.of(rows));
}

/** The value is a list of rows or entries (SymPy list). */
const isList = (v: MatrixInput): v is readonly (ExprLike | readonly ExprLike[])[] => Array.isArray(v);
/** The entry of a list is itself a list (a row). */
const isRow = (v: ExprLike | readonly ExprLike[]): v is readonly ExprLike[] => Array.isArray(v);

/** The matrix product a*b*... (SymPy * of matrix expressions; scalars scale). */
const mm = (a: Expr, ...bs: Expr[]): Expr => bs.reduce((acc, b) => cast(acc, MatrixExpr, 'matrix').mul(b), a);

/** The shape of a matrix argument. */
const shapeOf = (m: Expr): [Expr, Expr] => cast(m, MatrixExpr, 'matrix').shape;

/** The positive definiteness of an explicit matrix ('unknown' for a matrix symbol, which is not checked). */
const positiveDefinite = (m: Expr): boolean | undefined => {
  if (m instanceof MatrixSymbolNode) return true;
  const t = isPositiveDefinite(cast(m, MatrixExpr, 'matrix').asExplicit());
  return t === 'unknown' ? undefined : t;
};

/** The matrix is square (SymPy is_square). */
const squareOf = (m: Expr): boolean | undefined => {
  const t = cast(m, MatrixExpr, 'matrix').isSquare;
  return t === 'unknown' ? undefined : t;
};

/** SymPy Eq(a, b) of two dimensions as a truth value (structural equality, SymPy ==). */
const sameDim = (a: Expr, b: Expr): boolean => a.key === b.key;

/** The argument of the density, a matrix (SymPy raises ValueError for anything else). */
function densityArgument(xIn: MatrixInput): Expr {
  const x = toMatrixArg(xIn);
  if (!(x instanceof ImmutableMatrixNode || x instanceof MatrixSymbolNode)) throw new RangeError(`${x.toString()} should be an isinstance of Matrix or MatrixSymbol`);
  return x;
}

// ---------------------------------------------------------------------------
// Matrix probability space
// ---------------------------------------------------------------------------

/**
 * The probability space of a random matrix.
 *
 * @see SymPy `sympy.stats.matrix_distributions.MatrixPSpace`
 */
export class MatrixPSpace extends PSpace {
  /**
   * Constructs a new `MatrixPSpace`.
   *
   * @param args - Operands in the order `sym`, `distribution`, `dim_n`, `dim_m`.
   * @throws RangeError when a dimension is not known to be an integer.
   */
  constructor(args: readonly Expr[]) {
    const [n, m] = [at(args, 2), at(args, 3)];
    if (!(isIntegerQ(n) === true && isIntegerQ(m) === true)) throw new RangeError('Dimensions should be integers');
    super([symbolConverter(at(args, 0)), cast(at(args, 1), MatrixDistribution, 'matrix distribution'), n, m], 'MatrixPSpace');
  }
  /**
   * The underlying symbol naming the random variable.
   *
   * @returns The underlying symbol naming the random variable.
   * @see SymPy `sympy.stats.matrix_distributions.MatrixPSpace.symbol`
   */
  get symbol(): Sym {
    return symbolConverter(at(this.args, 0));
  }
  /**
   * The probability law governing the random variable.
   *
   * @returns The probability law governing the random variable.
   * @see SymPy `sympy.stats.matrix_distributions.MatrixPSpace.distribution`
   */
  get distribution(): MatrixDistribution {
    return cast(at(this.args, 1), MatrixDistribution);
  }
  /**
   * The domain of outcomes of this probability space.
   *
   * @returns The domain of outcomes of this probability space.
   * @see SymPy `sympy.stats.matrix_distributions.MatrixPSpace.domain`
   */
  override get domain(): MatrixDomain {
    return new MatrixDomain([this.symbol, this.distribution.set]);
  }
  /**
   * The random matrix symbol of the space.
   *
   * @returns The random matrix symbol of the space.
   * @see SymPy `sympy.stats.matrix_distributions.MatrixPSpace.value`
   */
  get value(): RandomMatrixSymbol {
    return new RandomMatrixSymbol(this.symbol, at(this.args, 2), at(this.args, 3), this);
  }
  /**
   * Whether this space supplies a density for its random symbol.
   *
   * @returns `true` for this space.
   */
  override get hasValueDensity(): boolean {
    return true;
  }
  /**
   * The density associated with the random symbol of the space.
   *
   * @returns The density associated with the random symbol of the space.
   */
  override get valueDensity(): Expr {
    return this.distribution;
  }
  /**
   * The distribution of the expression on this probability space.
   *
   * @param expr - Expression to evaluate.
   * @returns The probability distribution of the expression.
   * @throws NotImplementedError when the expression combines unsupported matrix distributions.
   * @see SymPy `sympy.stats.matrix_distributions.MatrixPSpace.compute_density`
   */
  override computeDensity(expr: Expr): DensityResult {
    if (randomMatrixSymbols(expr).length > 1 || !(expr instanceof RandomMatrixSymbol)) {
      throw new NotImplementedError('Currently, no algorithm has been implemented to handle general expressions containing multiple matrix distributions.');
    }
    return this.distribution.pdf(expr);
  }
}

/** A distribution class of random matrices (constructed from its parameters). */
type MatrixDistributionClass = new (args: readonly Expr[]) => MatrixDistribution;

/** A random matrix with the distribution of the parameters (SymPy rv of matrix_distributions). */
function rv(symbol: string | Sym, cls: MatrixDistributionClass, params: readonly MatrixInput[]): RandomMatrixSymbol {
  const dist = new cls(params.map(toMatrixArg));
  dist.check();
  const [n, m] = dist.dimension;
  return new MatrixPSpace([symbolConverter(symbol), dist, n, m]).value;
}

// ---------------------------------------------------------------------------
// Matrix distributions
// ---------------------------------------------------------------------------

/**
 * A distribution of random matrices, applied to a matrix.
 *
 * @see SymPy `sympy.stats.matrix_distributions.MatrixDistribution`
 */
export abstract class MatrixDistribution extends Distribution {
  /**
   * Constructs a new `MatrixDistribution`.
   *
   * @param name - Expression class name used for the node.
   * @param args - The defining expressions in structural order.
   */
  constructor(name: string, args: readonly Expr[]) {
    super(name, args);
  }
  /**
   * The parameters are valid.
   *
   * @see SymPy `sympy.stats.matrix_distributions.MatrixDistribution.check`
   */
  abstract check(): void;
  /**
   * The shape of the random matrices.
   *
   * @returns The shape of the random matrices.
   */
  abstract get dimension(): [Expr, Expr];
  /**
   * The density at a matrix (SymPy pdf; a nested array is a matrix).
   *
   * @param x - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   */
  abstract override pdf(x: MatrixInput): Expr;
  /**
   * The density at a matrix.
   *
   * @param x - Outcome at which to evaluate the density.
   * @returns The density at a matrix.
   * @see SymPy `sympy.stats.matrix_distributions.MatrixDistribution.__call__`
   */
  override call(x: MatrixInput): Expr {
    return this.pdf(x);
  }
  /** The set of the n x m real matrices (SymPy set). */
  protected matrixSet(n: Expr, m: Expr): SetExpr {
    return new MatrixSetNode(n, m, Reals);
  }
}

/**
 * A gamma law on positive definite matrices with a scalar shape, scalar scale, and scale matrix.
 *
 * @see SymPy `sympy.stats.matrix_distributions.MatrixGammaDistribution`
 */
export class MatrixGammaDistribution extends MatrixDistribution {
  /**
   * Constructs a new `MatrixGammaDistribution`.
   *
   * @param args - Distribution parameters in the order `alpha`, `beta`, `scale_matrix`.
   */
  constructor(args: readonly Expr[]) {
    super('MatrixGammaDistribution', args.map((a) => toMatrixArg(a)));
  }
  /**
   * Positive shape parameter.
   *
   * @returns Positive shape parameter.
   * @see SymPy `sympy.stats.matrix_distributions.MatrixGammaDistribution.alpha`
   */
  get alpha(): Expr {
    return this.arg(0);
  }
  /**
   * Positive scale parameter.
   *
   * @returns Positive scale parameter.
   * @see SymPy `sympy.stats.matrix_distributions.MatrixGammaDistribution.beta`
   */
  get beta(): Expr {
    return this.arg(1);
  }
  /**
   * Positive definite scale matrix.
   *
   * @returns Positive definite scale matrix.
   * @see SymPy `sympy.stats.matrix_distributions.MatrixGammaDistribution.scale_matrix`
   */
  get scaleMatrix(): Expr {
    return this.arg(2);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters fail the requirement for positive shape and scale and a square positive definite scale matrix.
   * @see SymPy `sympy.stats.matrix_distributions.MatrixGammaDistribution.check`
   */
  check(): void {
    valueCheck(positiveDefinite(this.scaleMatrix), 'The shape matrix must be positive definite.');
    valueCheck(squareOf(this.scaleMatrix), 'Should be square matrix');
    valueCheck(isPositive(this.alpha), 'Shape parameter should be positive.');
    valueCheck(isPositive(this.beta), 'Scale parameter should be positive.');
  }
  /**
   * The support of the distribution.
   *
   * @returns The support of the distribution.
   * @see SymPy `sympy.stats.matrix_distributions.MatrixGammaDistribution.set`
   */
  get set(): SetExpr {
    const k = at(shapeOf(this.scaleMatrix), 0);
    return this.matrixSet(k, k);
  }
  /**
   * The dimensions of a matrix in the support.
   *
   * @returns The dimensions of a matrix in the support.
   * @see SymPy `sympy.stats.matrix_distributions.MatrixGammaDistribution.dimension`
   */
  get dimension(): [Expr, Expr] {
    return shapeOf(this.scaleMatrix);
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.matrix_distributions.MatrixGammaDistribution.pdf`
   */
  pdf(xIn: MatrixInput): Expr {
    const [alpha, beta, scale] = [this.alpha, this.beta, this.scaleMatrix];
    const p = at(shapeOf(scale), 0);
    const x = densityArgument(xIn);
    const sigmaInvX = cast(mm(cast(InverseNode.create(scale).neg(), MatrixExpr), x), MatrixExpr).div(beta);
    const term1 = mul(exp(TraceNode.create(sigmaInvX)), pow(mul(pow(beta, mul(p, alpha)), multigamma(alpha, p)), -1));
    const term2 = pow(DeterminantNode.create(scale), mul(-1, alpha));
    const term3 = pow(DeterminantNode.create(x), add(alpha, mul(-1, add(p, 1), S.Half)));
    return mul(term1, term2, term3);
  }
}

/**
 * Matrix gamma distribution.
 *
 * @param symbol - Name or symbol for the random variable.
 * @param alpha - Positive shape parameter.
 * @param beta - Positive scale parameter.
 * @param scaleMatrix - Positive definite scale matrix.
 * @returns The random matrix with this distribution.
 * @throws RangeError when the parameters fail the requirement for positive shape and scale and a square positive definite scale matrix.
 * @see SymPy `sympy.stats.matrix_distributions.MatrixGamma`
 * @example
 * ```ts
 * import { doit, MatrixDistribution, MatrixGamma, density } from '@symjs/symjs';
 *
 * const M = MatrixGamma('M', 2, 3, [[2, 1], [1, 2]]);
 * doit((density(M) as MatrixDistribution).pdf([[1, 0], [0, 1]])); // => 2*exp(-4/9)/(729*pi)
 * ```
 */
export function MatrixGamma(symbol: string | Sym, alpha: ExprLike, beta: ExprLike, scaleMatrix: MatrixInput): RandomMatrixSymbol {
  return rv(symbol, MatrixGammaDistribution, [sympify(alpha), sympify(beta), scaleMatrix]);
}

/**
 * The distribution of a matrix of sums of products, parameterized by degrees of freedom and a scale matrix.
 *
 * @see SymPy `sympy.stats.matrix_distributions.WishartDistribution`
 */
export class WishartDistribution extends MatrixDistribution {
  /**
   * Constructs a new `WishartDistribution`.
   *
   * @param args - Distribution parameters in the order `n`, `scale_matrix`.
   */
  constructor(args: readonly Expr[]) {
    super('WishartDistribution', args.map((a) => toMatrixArg(a)));
  }
  /**
   * The degrees of freedom (SymPy n; `n` is evalf on expressions).
   *
   * @returns The degrees of freedom.
   * @see SymPy `sympy.stats.matrix_distributions.WishartDistribution.n`
   */
  get dof(): Expr {
    return this.arg(0);
  }
  /**
   * Positive definite scale matrix.
   *
   * @returns Positive definite scale matrix.
   * @see SymPy `sympy.stats.matrix_distributions.WishartDistribution.scale_matrix`
   */
  get scaleMatrix(): Expr {
    return this.arg(1);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters fail the requirement for positive degrees of freedom and a square positive definite scale matrix.
   * @see SymPy `sympy.stats.matrix_distributions.WishartDistribution.check`
   */
  check(): void {
    valueCheck(positiveDefinite(this.scaleMatrix), 'The shape matrix must be positive definite.');
    valueCheck(squareOf(this.scaleMatrix), 'Should be square matrix');
    valueCheck(isPositive(this.dof), 'Shape parameter should be positive.');
  }
  /**
   * The support of the distribution.
   *
   * @returns The support of the distribution.
   * @see SymPy `sympy.stats.matrix_distributions.WishartDistribution.set`
   */
  get set(): SetExpr {
    const k = at(shapeOf(this.scaleMatrix), 0);
    return this.matrixSet(k, k);
  }
  /**
   * The dimensions of a matrix in the support.
   *
   * @returns The dimensions of a matrix in the support.
   * @see SymPy `sympy.stats.matrix_distributions.WishartDistribution.dimension`
   */
  get dimension(): [Expr, Expr] {
    return shapeOf(this.scaleMatrix);
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.matrix_distributions.WishartDistribution.pdf`
   */
  pdf(xIn: MatrixInput): Expr {
    const [n, scale] = [this.dof, this.scaleMatrix];
    const p = at(shapeOf(scale), 0);
    const x = densityArgument(xIn);
    const half = Rational.of(1n, 2n);
    const sigmaInvX = cast(mm(cast(InverseNode.create(scale).neg(), MatrixExpr), x), MatrixExpr).div(2);
    const term1 = mul(exp(TraceNode.create(sigmaInvX)), pow(mul(pow(2, mul(p, n, half)), multigamma(mul(n, half), p)), -1));
    const term2 = pow(DeterminantNode.create(scale), mul(-1, n, half));
    const term3 = pow(DeterminantNode.create(x), mul(add(n, mul(-1, p), -1), half));
    return mul(term1, term2, term3);
  }
}

/**
 * Wishart distribution.
 *
 * @param symbol - Name or symbol for the random variable.
 * @param n - Degrees of freedom.
 * @param scaleMatrix - Positive definite scale matrix.
 * @returns The random matrix with this distribution.
 * @throws RangeError when the parameters fail the requirement for positive degrees of freedom and a square positive definite scale matrix.
 * @see SymPy `sympy.stats.matrix_distributions.Wishart`
 * @example
 * ```ts
 * import { doit, MatrixDistribution, Wishart, density } from '@symjs/symjs';
 *
 * const M = Wishart('M', 3, [[2, 1], [1, 2]]);
 * doit((density(M) as MatrixDistribution).pdf([[1, 0], [0, 1]])); // => sqrt(3)*exp(-2/3)/(36*pi)
 * ```
 */
export function Wishart(symbol: string | Sym, n: ExprLike, scaleMatrix: MatrixInput): RandomMatrixSymbol {
  return rv(symbol, WishartDistribution, [sympify(n), scaleMatrix]);
}

/**
 * The normal law of a random matrix with separate row and column covariances.
 *
 * @see SymPy `sympy.stats.matrix_distributions.MatrixNormalDistribution`
 */
export class MatrixNormalDistribution extends MatrixDistribution {
  /**
   * Constructs a new `MatrixNormalDistribution`.
   *
   * @param args - Distribution parameters in the order `location_matrix`, `scale_matrix_1`, `scale_matrix_2`.
   */
  constructor(args: readonly Expr[]) {
    super('MatrixNormalDistribution', args.map((a) => toMatrixArg(a)));
  }
  /**
   * Matrix of means.
   *
   * @returns Matrix of means.
   * @see SymPy `sympy.stats.matrix_distributions.MatrixNormalDistribution.location_matrix`
   */
  get locationMatrix(): Expr {
    return this.arg(0);
  }
  /**
   * Row covariance matrix.
   *
   * @returns Row covariance matrix.
   * @see SymPy `sympy.stats.matrix_distributions.MatrixNormalDistribution.scale_matrix_1`
   */
  get scaleMatrix1(): Expr {
    return this.arg(1);
  }
  /**
   * Column covariance matrix.
   *
   * @returns Column covariance matrix.
   * @see SymPy `sympy.stats.matrix_distributions.MatrixNormalDistribution.scale_matrix_2`
   */
  get scaleMatrix2(): Expr {
    return this.arg(2);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters fail the requirement for positive definite row and column covariance matrices compatible with the mean matrix.
   * @see SymPy `sympy.stats.matrix_distributions.MatrixNormalDistribution.check`
   */
  check(): void {
    const [M, U, V] = [this.locationMatrix, this.scaleMatrix1, this.scaleMatrix2];
    valueCheck(positiveDefinite(U), 'The shape matrix must be positive definite.');
    valueCheck(positiveDefinite(V), 'The shape matrix must be positive definite.');
    valueCheck(squareOf(U), 'Scale matrix 1 should be be square matrix');
    valueCheck(squareOf(V), 'Scale matrix 2 should be be square matrix');
    const [n, p] = shapeOf(M);
    valueCheck(sameDim(at(shapeOf(U), 0), n), `Scale matrix 1 should be of shape ${n.toString()} x ${n.toString()}`);
    valueCheck(sameDim(at(shapeOf(V), 0), p), `Scale matrix 2 should be of shape ${p.toString()} x ${p.toString()}`);
  }
  /**
   * The support of the distribution.
   *
   * @returns The support of the distribution.
   * @see SymPy `sympy.stats.matrix_distributions.MatrixNormalDistribution.set`
   */
  get set(): SetExpr {
    const [n, p] = shapeOf(this.locationMatrix);
    return this.matrixSet(n, p);
  }
  /**
   * The dimensions of a matrix in the support.
   *
   * @returns The dimensions of a matrix in the support.
   * @see SymPy `sympy.stats.matrix_distributions.MatrixNormalDistribution.dimension`
   */
  get dimension(): [Expr, Expr] {
    return shapeOf(this.locationMatrix);
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.matrix_distributions.MatrixNormalDistribution.pdf`
   */
  pdf(xIn: MatrixInput): Expr {
    const [M, U, V] = [this.locationMatrix, this.scaleMatrix1, this.scaleMatrix2];
    const [n, p] = shapeOf(M);
    const x = densityArgument(xIn);
    const xm = x.sub(M);
    const term1 = mm(InverseNode.create(V), new TransposeNode(cast(xm, MatrixExpr)), InverseNode.create(U), xm);
    const num = exp(mul(-1, TraceNode.create(term1), S.Half));
    const den = mul(pow(mul(2, S.Pi), mul(n, p, S.Half)), pow(DeterminantNode.create(U), mul(p, S.Half)), pow(DeterminantNode.create(V), mul(n, S.Half)));
    return mul(num, pow(den, -1));
  }
}

/**
 * Matrix normal distribution.
 *
 * @param symbol - Name or symbol for the random variable.
 * @param locationMatrix - Matrix of means.
 * @param scaleMatrix1 - Row covariance matrix.
 * @param scaleMatrix2 - Column covariance matrix.
 * @returns The random matrix with this distribution.
 * @throws RangeError when the parameters fail the requirement for positive definite row and column covariance matrices compatible with the mean matrix.
 * @see SymPy `sympy.stats.matrix_distributions.MatrixNormal`
 * @example
 * ```ts
 * import { doit, MatrixDistribution, MatrixNormal, density } from '@symjs/symjs';
 *
 * const M = MatrixNormal('M', [[1, 2]], [1], [[1, 0], [0, 1]]);
 * doit((density(M) as MatrixDistribution).pdf([[3, 4]])); // => exp(-4)/(2*pi)
 * ```
 */
export function MatrixNormal(symbol: string | Sym, locationMatrix: MatrixInput, scaleMatrix1: MatrixInput, scaleMatrix2: MatrixInput): RandomMatrixSymbol {
  return rv(symbol, MatrixNormalDistribution, [locationMatrix, scaleMatrix1, scaleMatrix2]);
}

/**
 * A matrix-valued Student t law with a location matrix and two scale matrices.
 *
 * @see SymPy `sympy.stats.matrix_distributions.MatrixStudentTDistribution`
 */
export class MatrixStudentTDistribution extends MatrixDistribution {
  /**
   * Constructs a new `MatrixStudentTDistribution`.
   *
   * @param args - Distribution parameters in the order `nu`, `location_matrix`, `scale_matrix_1`, `scale_matrix_2`.
   */
  constructor(args: readonly Expr[]) {
    super('MatrixStudentTDistribution', args.map((a) => toMatrixArg(a)));
  }
  /**
   * Degrees of freedom.
   *
   * @returns Degrees of freedom.
   * @see SymPy `sympy.stats.matrix_distributions.MatrixStudentTDistribution.nu`
   */
  get nu(): Expr {
    return this.arg(0);
  }
  /**
   * Location matrix.
   *
   * @returns Location matrix.
   * @see SymPy `sympy.stats.matrix_distributions.MatrixStudentTDistribution.location_matrix`
   */
  get locationMatrix(): Expr {
    return this.arg(1);
  }
  /**
   * First positive definite scale matrix.
   *
   * @returns First positive definite scale matrix.
   * @see SymPy `sympy.stats.matrix_distributions.MatrixStudentTDistribution.scale_matrix_1`
   */
  get scaleMatrix1(): Expr {
    return this.arg(2);
  }
  /**
   * Second positive definite scale matrix.
   *
   * @returns Second positive definite scale matrix.
   * @see SymPy `sympy.stats.matrix_distributions.MatrixStudentTDistribution.scale_matrix_2`
   */
  get scaleMatrix2(): Expr {
    return this.arg(3);
  }
  /**
   * Checks that the distribution parameters satisfy their defining constraints.
   *
   * @throws RangeError when the parameters fail the requirement for positive degrees of freedom and positive definite scale matrices compatible with the location matrix.
   * @see SymPy `sympy.stats.matrix_distributions.MatrixStudentTDistribution.check`
   */
  check(): void {
    const [nu, M, Omega, Sigma] = [this.nu, this.locationMatrix, this.scaleMatrix1, this.scaleMatrix2];
    // SymPy tests `!= False`: an undecided value passes
    valueCheck(positiveDefinite(Omega) !== false, 'The shape matrix must be positive definite.');
    valueCheck(positiveDefinite(Sigma) !== false, 'The shape matrix must be positive definite.');
    valueCheck(squareOf(Omega) !== false, 'Scale matrix 1 should be be square matrix');
    valueCheck(squareOf(Sigma) !== false, 'Scale matrix 2 should be be square matrix');
    const [n, p] = shapeOf(M);
    valueCheck(sameDim(at(shapeOf(Omega), 0), p), `Scale matrix 1 should be of shape ${p.toString()} x ${p.toString()}`);
    valueCheck(sameDim(at(shapeOf(Sigma), 0), n), `Scale matrix 2 should be of shape ${n.toString()} x ${n.toString()}`);
    valueCheck(isPositive(nu) !== false, 'Degrees of freedom must be positive');
  }
  /**
   * The support of the distribution.
   *
   * @returns The support of the distribution.
   * @see SymPy `sympy.stats.matrix_distributions.MatrixStudentTDistribution.set`
   */
  get set(): SetExpr {
    const [n, p] = shapeOf(this.locationMatrix);
    return this.matrixSet(n, p);
  }
  /**
   * The dimensions of a matrix in the support.
   *
   * @returns The dimensions of a matrix in the support.
   * @see SymPy `sympy.stats.matrix_distributions.MatrixStudentTDistribution.dimension`
   */
  get dimension(): [Expr, Expr] {
    return shapeOf(this.locationMatrix);
  }
  /**
   * The probability density at the supplied value.
   *
   * @param xIn - Outcome at which to evaluate the density.
   * @returns The density evaluated at the supplied outcome.
   * @see SymPy `sympy.stats.matrix_distributions.MatrixStudentTDistribution.pdf`
   */
  pdf(xIn: MatrixInput): Expr {
    const x = densityArgument(xIn);
    const [nu, M, Omega, Sigma] = [this.nu, this.locationMatrix, this.scaleMatrix1, this.scaleMatrix2];
    const [n, p] = shapeOf(M);
    // SymPy takes n and p from the shape, Python ints for an explicit location matrix: then n*p/2, -n/2 and
    // -p/2 are Python float divisions, and the exponents Floats
    const half = (a: Expr): Expr => (M instanceof ImmutableMatrixNode ? new Float(Number(a.toString()) / 2) : mul(a, S.Half));
    const K = mul(
      multigamma(mul(add(nu, n, p, -1), S.Half), p),
      pow(DeterminantNode.create(Omega), half(mul(-1, n))),
      pow(DeterminantNode.create(Sigma), half(mul(-1, p))),
      pow(mul(pow(S.Pi, half(mul(n, p))), multigamma(mul(add(nu, p, -1), S.Half), p)), -1),
    );
    const xm = x.sub(M);
    const inner = new ImmutableMatrixNode(Matrix.eye(Number(n.toString()))).add(mm(InverseNode.create(Sigma), xm, InverseNode.create(Omega), new TransposeNode(cast(xm, MatrixExpr))));
    return mul(K, pow(DeterminantNode.create(inner), mul(-1, add(nu, n, p, -1), S.Half)));
  }
}

/**
 * Matrix Student's t distribution.
 *
 * @param symbol - Name or symbol for the random variable.
 * @param nu - Degrees of freedom.
 * @param locationMatrix - Location matrix.
 * @param scaleMatrix1 - First positive definite scale matrix.
 * @param scaleMatrix2 - Second positive definite scale matrix.
 * @returns The random matrix with this distribution.
 * @throws RangeError when the parameters fail the requirement for positive degrees of freedom and positive definite scale matrices compatible with the location matrix.
 * @see SymPy `sympy.stats.matrix_distributions.MatrixStudentT`
 * @example
 * ```ts
 * import { doit, MatrixDistribution, MatrixStudentT, density } from '@symjs/symjs';
 *
 * const M = MatrixStudentT('M', 2, [[1, 2]], [[1, 0], [0, 1]], [1]);
 * doit((density(M) as MatrixDistribution).pdf([[1, 2]])); // => pi**(-1.0)
 * ```
 */
export function MatrixStudentT(symbol: string | Sym, nu: ExprLike, locationMatrix: MatrixInput, scaleMatrix1: MatrixInput, scaleMatrix2: MatrixInput): RandomMatrixSymbol {
  return rv(symbol, MatrixStudentTDistribution, [sympify(nu), locationMatrix, scaleMatrix1, scaleMatrix2]);
}


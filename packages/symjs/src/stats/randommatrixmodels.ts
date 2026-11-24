// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/stats/random_matrix_models.py),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy sympy.stats.random_matrix_models: the Gaussian ensembles
 * (GUE, GOE, GSE) and the circular ensembles (CUE, COE, CSE) of random
 * matrices, their densities, the joint distributions of their eigenvalues
 * and their level spacing distributions.
 *
 * A random matrix of an ensemble is a RandomMatrixSymbol whose space is a
 * RandomMatrixPSpace with the ensemble model; `density(H)` is the model,
 * applied to a matrix with `call` (SymPy `density(H)(X)`).
 */

import { Dummy, Expr, ExtensionExpr, Integral, Rational, S } from '../core/nodes';
import type { ExprLike, Sym } from '../core/nodes';
import { add, exp, mul, pow, sympify } from '../core/ops';
import { isIntegerQ } from '../core/assumptions';
import { Lambda } from '../core/lambda';
import { Product } from '../core/concrete';
import { IndexedBase } from '../core/indexed';
import { NotImplementedError } from '../core/errors';
import { at, cast } from '../core/guard';
import { doit } from '../calculus/doit';
import { abs } from '../functions/elementary/elementary';
import { gamma } from '../functions/special/special';
import { Matrix } from '../matrices/matrix';
import { ImmutableMatrixNode, MatrixExpr, MatrixSymbolNode, TraceNode } from '../matrices/expressions/matexpr';
import { Density, RandomMatrixSymbol, isRandom, symbolConverter } from './rv';
import { RandomMatrixPSpace } from './randommatrix';
import { JointDistributionHandmade } from './jointrvtypes';

/** The dimension as an integer (SymPy fails on a symbolic one: ArrayComprehension is not iterable). */
function concreteDimension(n: Expr): number {
  if (!(n instanceof Rational)) throw new TypeError("'ArrayComprehension' object is not iterable");
  return Number(n.p);
}

/**
 * The base class of the random matrix ensembles.
 *
 * @see SymPy `sympy.stats.random_matrix_models.RandomMatrixEnsembleModel`
 */
export class RandomMatrixEnsembleModel extends ExtensionExpr {
  /**
   * Constructs a new `RandomMatrixEnsembleModel`.
   *
   * @param args - Operands in the order `sym`, `dim`.
   * @param name - Expression class name used for the node.
   * @throws RangeError when the matrix dimension is not an integer.
   */
  constructor(args: readonly Expr[], name = 'RandomMatrixEnsembleModel') {
    const [sym, dim] = [symbolConverter(at(args, 0)), at(args, 1)];
    if (isIntegerQ(dim) === false) throw new RangeError(`Dimension of the random matrices must be integers, received ${dim.toString()} instead.`);
    super(name, [sym, dim]);
  }
  /**
   * Identifies the ordinary symbol that names the random variable.
   *
   * @returns The underlying symbol.
   * @see SymPy `sympy.stats.random_matrix_models.RandomMatrixEnsembleModel.symbol`
   */
  get symbol(): Sym {
    return symbolConverter(at(this.args, 0));
  }
  /**
   * Specifies the common row and column count of each ensemble matrix.
   *
   * @returns The matrix dimension.
   * @see SymPy `sympy.stats.random_matrix_models.RandomMatrixEnsembleModel.dimension`
   */
  get dimension(): Expr {
    return at(this.args, 1);
  }
  /**
   * Rebuilds this expression with the supplied operands.
   *
   * @param args - Replacement operands in the original order.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return cast(Reflect.construct(this.constructor, [args]), Expr);
  }
  /**
   * Forms the unevaluated density of a matrix drawn from the ensemble.
   *
   * @param expr - Expression to evaluate.
   * @returns The density expression.
   * @see SymPy `sympy.stats.random_matrix_models.RandomMatrixEnsembleModel.density`
   */
  density(expr: Expr): Expr {
    return new Density([expr]);
  }
  /**
   * Evaluates the density for the supplied expression.
   *
   * @param expr - Expression to evaluate.
   * @returns The density expression.
   */
  call(expr: Expr): Expr {
    return this.density(expr);
  }
  /**
   * Constructs the joint probability density of the ensemble eigenvalues.
   *
   * @returns The eigenvalue density lambda.
   * @throws NotImplementedError when the ensemble defines no eigenvalue density.
   */
  jointEigenDistribution(): Expr {
    throw new NotImplementedError(`${this.name} has no joint eigenvalue distribution`);
  }
  /**
   * Constructs the density of adjacent eigenvalue gaps in the Gaussian ensemble.
   *
   * @returns The spacing density lambda.
   * @throws NotImplementedError when the ensemble defines no spacing law.
   */
  levelSpacingDistribution(): Expr {
    throw new NotImplementedError(`${this.name} has no level spacing distribution`);
  }
}

// ---------------------------------------------------------------------------
// Gaussian ensembles
// ---------------------------------------------------------------------------

/**
 * The Gaussian ensembles.
 *
 * @see SymPy `sympy.stats.random_matrix_models.GaussianEnsembleModel`
 */
export class GaussianEnsembleModel extends RandomMatrixEnsembleModel {
  /**
   * Constructs a new `GaussianEnsembleModel`.
   *
   * @param args - The matrix symbol followed by its dimension.
   * @param name - Expression class name used for the node.
   */
  constructor(args: readonly Expr[], name = 'GaussianEnsembleModel') {
    super(args, name);
  }
  /** SymPy _compute_normalization_constant(beta, n). */
  protected normalizationOfEigenvalues(beta: Expr, n: Expr): Expr {
    const j = new Dummy('j', { integer: true, positive: true });
    const term1 = doit(Product(mul(gamma(add(1, mul(beta, j, S.Half))), pow(gamma(add(1, mul(beta, S.Half))), -1)), [j, 1, n]));
    const term2 = pow(mul(2, pow(mul(beta, n), -1)), add(mul(beta, n, add(n, -1), Rational.of(1n, 4n)), mul(n, S.Half)));
    const term3 = pow(mul(2, S.Pi), mul(n, S.Half));
    return mul(term1, term2, term3);
  }
  /** SymPy _compute_joint_eigen_distribution(beta). */
  protected jointEigenDistributionOf(beta: Expr): Expr {
    const n = this.dimension;
    const nn = concreteDimension(n);
    const Zbn = this.normalizationOfEigenvalues(beta, n);
    const l = new IndexedBase('l');
    const i = new Dummy('i', { integer: true, positive: true });
    const j = new Dummy('j', { integer: true, positive: true });
    const syms = Array.from({ length: nn }, (_, k) => l.at(k + 1));
    const term1 = exp(mul(mul(-1, n, S.Half), add(...syms.map((s) => pow(s, 2)))));
    const term2 = Product(pow(abs(add(l.at(j), mul(-1, l.at(i)))), beta), [j, add(i, 1), n], [i, 1, add(n, -1)]);
    return Lambda(syms, mul(term1, term2, pow(Zbn, -1)));
  }
  /** The density exp(-c*Trace(H**2))/Z of a random matrix of the ensemble. */
  protected traceDensity(expr: Expr, c: Expr, Z: Expr): Expr {
    const h = cast(expr, MatrixExpr, 'random matrix');
    return mul(exp(mul(-1, c, TraceNode.create(h.pow(2)))), pow(Z, -1));
  }
}

/** The normalization integral of the orthogonal and symplectic ensembles (SymPy Integral(exp(-c*Trace(_H**2)))). */
function traceIntegral(n: Expr, c: Expr): Expr {
  const H = new MatrixSymbolNode('_H', n, n);
  return new Integral([exp(mul(-1, c, TraceNode.create(H.pow(2)))), H]);
}

/**
 * The probability model for the gaussian unitary ensemble.
 *
 * @see SymPy `sympy.stats.random_matrix_models.GaussianUnitaryEnsembleModel`
 */
export class GaussianUnitaryEnsembleModel extends GaussianEnsembleModel {
  /**
   * Constructs a new `GaussianUnitaryEnsembleModel`.
   *
   * @param args - The matrix symbol followed by its dimension.
   */
  constructor(args: readonly Expr[]) {
    super(args, 'GaussianUnitaryEnsembleModel');
  }
  /**
   * Computes the Gaussian ensemble normalization from the matrix dimension.
   *
   * @returns The normalization constant.
   * @see SymPy `sympy.stats.random_matrix_models.GaussianUnitaryEnsembleModel.normalization_constant`
   */
  get normalizationConstant(): Expr {
    const n = this.dimension;
    return mul(pow(2, mul(n, S.Half)), pow(S.Pi, mul(pow(n, 2), S.Half)));
  }
  /**
   * Computes the probability law of the supplied random variable or expression.
   *
   * @param expr - Expression to evaluate.
   * @returns The resulting density.
   * @see SymPy `sympy.stats.random_matrix_models.GaussianUnitaryEnsembleModel.density`
   */
  override density(expr: Expr): Expr {
    return this.traceDensity(expr, mul(this.dimension, S.Half), this.normalizationConstant);
  }
  /**
   * Computes the joint law of the eigenvalues of an ensemble matrix.
   *
   * @returns The joint eigenvalue density.
   * @see SymPy `sympy.stats.random_matrix_models.GaussianUnitaryEnsembleModel.joint_eigen_distribution`
   */
  override jointEigenDistribution(): Expr {
    return this.jointEigenDistributionOf(Rational.of(2n));
  }
  /**
   * Computes the law of the gaps between consecutive eigenvalues.
   *
   * @returns The level-spacing density.
   * @see SymPy `sympy.stats.random_matrix_models.GaussianUnitaryEnsembleModel.level_spacing_distribution`
   */
  override levelSpacingDistribution(): Expr {
    const s = new Dummy('s');
    return Lambda(s, mul(32, pow(S.Pi, -2), pow(s, 2), exp(mul(-4, pow(S.Pi, -1), pow(s, 2)))));
  }
}

/**
 * The probability model for the gaussian orthogonal ensemble.
 *
 * @see SymPy `sympy.stats.random_matrix_models.GaussianOrthogonalEnsembleModel`
 */
export class GaussianOrthogonalEnsembleModel extends GaussianEnsembleModel {
  /**
   * Constructs a new `GaussianOrthogonalEnsembleModel`.
   *
   * @param args - The matrix symbol followed by its dimension.
   */
  constructor(args: readonly Expr[]) {
    super(args, 'GaussianOrthogonalEnsembleModel');
  }
  /**
   * Forms the matrix integral defining the normalizing constant.
   *
   * @returns An unevaluated integral.
   * @see SymPy `sympy.stats.random_matrix_models.GaussianOrthogonalEnsembleModel.normalization_constant`
   */
  get normalizationConstant(): Expr {
    return traceIntegral(this.dimension, mul(this.dimension, Rational.of(1n, 4n)));
  }
  /**
   * Computes the probability law of the supplied random variable or expression.
   *
   * @param expr - Expression to evaluate.
   * @returns The resulting density.
   * @see SymPy `sympy.stats.random_matrix_models.GaussianOrthogonalEnsembleModel.density`
   */
  override density(expr: Expr): Expr {
    return this.traceDensity(expr, mul(this.dimension, Rational.of(1n, 4n)), this.normalizationConstant);
  }
  /**
   * Computes the joint law of the eigenvalues of an ensemble matrix.
   *
   * @returns The joint eigenvalue density.
   * @see SymPy `sympy.stats.random_matrix_models.GaussianOrthogonalEnsembleModel.joint_eigen_distribution`
   */
  override jointEigenDistribution(): Expr {
    return this.jointEigenDistributionOf(S.One);
  }
  /**
   * Computes the law of the gaps between consecutive eigenvalues.
   *
   * @returns The level-spacing density.
   * @see SymPy `sympy.stats.random_matrix_models.GaussianOrthogonalEnsembleModel.level_spacing_distribution`
   */
  override levelSpacingDistribution(): Expr {
    const s = new Dummy('s');
    return Lambda(s, mul(S.Pi, S.Half, s, exp(mul(-1, S.Pi, Rational.of(1n, 4n), pow(s, 2)))));
  }
}

/**
 * The probability model for the gaussian symplectic ensemble.
 *
 * @see SymPy `sympy.stats.random_matrix_models.GaussianSymplecticEnsembleModel`
 */
export class GaussianSymplecticEnsembleModel extends GaussianEnsembleModel {
  /**
   * Constructs a new `GaussianSymplecticEnsembleModel`.
   *
   * @param args - The matrix symbol followed by its dimension.
   */
  constructor(args: readonly Expr[]) {
    super(args, 'GaussianSymplecticEnsembleModel');
  }
  /**
   * Forms the matrix integral defining the normalizing constant.
   *
   * @returns An unevaluated integral.
   * @see SymPy `sympy.stats.random_matrix_models.GaussianSymplecticEnsembleModel.normalization_constant`
   */
  get normalizationConstant(): Expr {
    return traceIntegral(this.dimension, this.dimension);
  }
  /**
   * Computes the probability law of the supplied random variable or expression.
   *
   * @param expr - Expression to evaluate.
   * @returns The resulting density.
   * @see SymPy `sympy.stats.random_matrix_models.GaussianSymplecticEnsembleModel.density`
   */
  override density(expr: Expr): Expr {
    return this.traceDensity(expr, this.dimension, this.normalizationConstant);
  }
  /**
   * Computes the joint law of the eigenvalues of an ensemble matrix.
   *
   * @returns The joint eigenvalue density.
   * @see SymPy `sympy.stats.random_matrix_models.GaussianSymplecticEnsembleModel.joint_eigen_distribution`
   */
  override jointEigenDistribution(): Expr {
    return this.jointEigenDistributionOf(Rational.of(4n));
  }
  /**
   * Computes the law of the gaps between consecutive eigenvalues.
   *
   * @returns The level-spacing density.
   * @see SymPy `sympy.stats.random_matrix_models.GaussianSymplecticEnsembleModel.level_spacing_distribution`
   */
  override levelSpacingDistribution(): Expr {
    const s = new Dummy('s');
    const c = mul(Rational.of(2n ** 18n, 3n ** 6n), pow(S.Pi, -3));
    return Lambda(s, mul(c, pow(s, 4), exp(mul(-64, pow(mul(9, S.Pi), -1), pow(s, 2)))));
  }
}

/** A model class of the ensembles. */
type ModelClass = new (args: readonly Expr[]) => RandomMatrixEnsembleModel;

/** A random matrix of an ensemble (SymPy RandomMatrixSymbol(sym, dim, dim, pspace=RandomMatrixPSpace(sym, model))). */
function ensemble(cls: ModelClass, symIn: string | Sym, dimIn: ExprLike): RandomMatrixSymbol {
  const [sym, dim] = [symbolConverter(symIn), sympify(dimIn)];
  const model = new cls([sym, dim]);
  return new RandomMatrixSymbol(sym, dim, dim, new RandomMatrixPSpace([sym, model]));
}

/**
 * Constructs a random matrix of the Gaussian ensemble.
 *
 * @param sym - Name or symbol for the random variable.
 * @param dim - Dimension of the square random matrix.
 * @returns The ensemble random matrix symbol.
 * @throws RangeError when the dimension is known not to be an integer.
 * @see SymPy `sympy.stats.random_matrix_models.GaussianEnsemble`
 */
export function GaussianEnsemble(sym: string | Sym, dim: ExprLike): RandomMatrixSymbol {
  return ensemble(GaussianEnsembleModel, sym, dim);
}

/**
 * Constructs a random matrix of the Gaussian unitary ensemble.
 *
 * @param sym - Name or symbol for the random variable.
 * @param dim - Dimension of the square random matrix.
 * @returns The ensemble random matrix symbol.
 * @throws RangeError when the dimension is known not to be an integer.
 * @see SymPy `sympy.stats.random_matrix_models.GaussianUnitaryEnsemble`
 * @example
 * ```ts
 * import { GaussianUnitaryEnsemble, MatrixSymbol, RandomMatrixEnsembleModel, density } from '@symjs/symjs';
 *
 * const U = GaussianUnitaryEnsemble('U', 2);
 * (density(U) as RandomMatrixEnsembleModel).density(MatrixSymbol('X', 2, 2)); // => exp(-Trace(X**2))/(2*pi**2)
 * ```
 */
export function GaussianUnitaryEnsemble(sym: string | Sym, dim: ExprLike): RandomMatrixSymbol {
  return ensemble(GaussianUnitaryEnsembleModel, sym, dim);
}

/**
 * Constructs a random matrix of the Gaussian orthogonal ensemble.
 *
 * @param sym - Name or symbol for the random variable.
 * @param dim - Dimension of the square random matrix.
 * @returns The ensemble random matrix symbol.
 * @throws RangeError when the dimension is known not to be an integer.
 * @see SymPy `sympy.stats.random_matrix_models.GaussianOrthogonalEnsemble`
 * @example
 * ```ts
 * import { GaussianOrthogonalEnsemble, MatrixSymbol, RandomMatrixEnsembleModel, density } from '@symjs/symjs';
 *
 * const U = GaussianOrthogonalEnsemble('U', 2);
 * (density(U) as RandomMatrixEnsembleModel).density(MatrixSymbol('X', 2, 2)); // => exp(-Trace(X**2)/2)/Integral(exp(-Trace(_H**2)/2), _H)
 * ```
 */
export function GaussianOrthogonalEnsemble(sym: string | Sym, dim: ExprLike): RandomMatrixSymbol {
  return ensemble(GaussianOrthogonalEnsembleModel, sym, dim);
}

/**
 * Constructs a random matrix of the Gaussian symplectic ensemble.
 *
 * @param sym - Name or symbol for the random variable.
 * @param dim - Dimension of the square random matrix.
 * @returns The ensemble random matrix symbol.
 * @throws RangeError when the dimension is known not to be an integer.
 * @see SymPy `sympy.stats.random_matrix_models.GaussianSymplecticEnsemble`
 * @example
 * ```ts
 * import { GaussianSymplecticEnsemble, MatrixSymbol, RandomMatrixEnsembleModel, density } from '@symjs/symjs';
 *
 * const U = GaussianSymplecticEnsemble('U', 2);
 * (density(U) as RandomMatrixEnsembleModel).density(MatrixSymbol('X', 2, 2)); // => exp(-2*Trace(X**2))/Integral(exp(-2*Trace(_H**2)), _H)
 * ```
 */
export function GaussianSymplecticEnsemble(sym: string | Sym, dim: ExprLike): RandomMatrixSymbol {
  return ensemble(GaussianSymplecticEnsembleModel, sym, dim);
}

// ---------------------------------------------------------------------------
// Circular ensembles
// ---------------------------------------------------------------------------

/**
 * The circular ensembles.
 *
 * @see SymPy `sympy.stats.random_matrix_models.CircularEnsembleModel`
 */
export class CircularEnsembleModel extends RandomMatrixEnsembleModel {
  /**
   * Constructs a new `CircularEnsembleModel`.
   *
   * @param args - The matrix symbol followed by its dimension.
   * @param name - Expression class name used for the node.
   */
  constructor(args: readonly Expr[], name = 'CircularEnsembleModel') {
    super(args, name);
  }
  /**
   * Raises an error because evaluating the circular ensemble density requires the Haar measure.
   *
   * @param _expr - Expression to evaluate.
   * @returns This operation raises `NotImplementedError`.
   * @throws NotImplementedError when computing the density requires Haar measure.
   * @see SymPy `sympy.stats.random_matrix_models.CircularEnsembleModel.density`
   */
  override density(_expr: Expr): Expr {
    throw new NotImplementedError(`Support for Haar measure hasn't been implemented yet, therefore the density of ${this.toString()} cannot be computed.`);
  }
  /** SymPy _compute_joint_eigen_distribution(beta). */
  protected jointEigenDistributionOf(beta: Expr): Expr {
    const n = this.dimension;
    const nn = concreteDimension(n);
    const Zbn = mul(pow(mul(2, S.Pi), n), gamma(add(mul(beta, n, S.Half), 1)), pow(gamma(add(mul(beta, S.Half), 1)), mul(-1, n)));
    const t = new IndexedBase('t');
    const j = new Dummy('j', { integer: true });
    const k = new Dummy('k', { integer: true });
    const syms = Array.from({ length: nn }, (_, m) => t.at(m + 1));
    const term = pow(abs(add(exp(mul(S.I, t.at(k))), mul(-1, exp(mul(S.I, t.at(j)))))), beta);
    const f = Product(term, [j, add(k, 1), n], [k, 1, add(n, -1)]);
    return Lambda(syms, mul(f, pow(Zbn, -1)));
  }
}

/**
 * The probability model for the circular unitary ensemble.
 *
 * @see SymPy `sympy.stats.random_matrix_models.CircularUnitaryEnsembleModel`
 */
export class CircularUnitaryEnsembleModel extends CircularEnsembleModel {
  /**
   * Constructs a new `CircularUnitaryEnsembleModel`.
   *
   * @param args - The matrix symbol followed by its dimension.
   */
  constructor(args: readonly Expr[]) {
    super(args, 'CircularUnitaryEnsembleModel');
  }
  /**
   * Computes the joint law of the eigenvalues of an ensemble matrix.
   *
   * @returns The joint eigenvalue density.
   * @see SymPy `sympy.stats.random_matrix_models.CircularUnitaryEnsembleModel.joint_eigen_distribution`
   */
  override jointEigenDistribution(): Expr {
    return this.jointEigenDistributionOf(Rational.of(2n));
  }
}

/**
 * The probability model for the circular orthogonal ensemble.
 *
 * @see SymPy `sympy.stats.random_matrix_models.CircularOrthogonalEnsembleModel`
 */
export class CircularOrthogonalEnsembleModel extends CircularEnsembleModel {
  /**
   * Constructs a new `CircularOrthogonalEnsembleModel`.
   *
   * @param args - The matrix symbol followed by its dimension.
   */
  constructor(args: readonly Expr[]) {
    super(args, 'CircularOrthogonalEnsembleModel');
  }
  /**
   * Computes the joint law of the eigenvalues of an ensemble matrix.
   *
   * @returns The joint eigenvalue density.
   * @see SymPy `sympy.stats.random_matrix_models.CircularOrthogonalEnsembleModel.joint_eigen_distribution`
   */
  override jointEigenDistribution(): Expr {
    return this.jointEigenDistributionOf(S.One);
  }
}

/**
 * The probability model for the circular symplectic ensemble.
 *
 * @see SymPy `sympy.stats.random_matrix_models.CircularSymplecticEnsembleModel`
 */
export class CircularSymplecticEnsembleModel extends CircularEnsembleModel {
  /**
   * Constructs a new `CircularSymplecticEnsembleModel`.
   *
   * @param args - The matrix symbol followed by its dimension.
   */
  constructor(args: readonly Expr[]) {
    super(args, 'CircularSymplecticEnsembleModel');
  }
  /**
   * Computes the joint law of the eigenvalues of an ensemble matrix.
   *
   * @returns The joint eigenvalue density.
   * @see SymPy `sympy.stats.random_matrix_models.CircularSymplecticEnsembleModel.joint_eigen_distribution`
   */
  override jointEigenDistribution(): Expr {
    return this.jointEigenDistributionOf(Rational.of(4n));
  }
}

/**
 * Constructs a random matrix of the circular ensemble.
 *
 * @param sym - Name or symbol for the random variable.
 * @param dim - Dimension of the square random matrix.
 * @returns The ensemble random matrix symbol.
 * @throws RangeError when the dimension is known not to be an integer.
 * @see SymPy `sympy.stats.random_matrix_models.CircularEnsemble`
 */
export function CircularEnsemble(sym: string | Sym, dim: ExprLike): RandomMatrixSymbol {
  return ensemble(CircularEnsembleModel, sym, dim);
}

/**
 * Constructs a random matrix of the circular unitary ensemble.
 *
 * @param sym - Name or symbol for the random variable.
 * @param dim - Dimension of the square random matrix.
 * @returns The ensemble random matrix symbol.
 * @throws RangeError when the dimension is known not to be an integer.
 * @see SymPy `sympy.stats.random_matrix_models.CircularUnitaryEnsemble`
 * @example
 * ```ts
 * import { CircularUnitaryEnsemble, jointEigenDistribution } from '@symjs/symjs';
 *
 * const U = CircularUnitaryEnsemble('U', 1);
 * jointEigenDistribution(U); // => Lambda(t[1], Product(Abs(exp(I*t[_j]) - exp(I*t[_k]))**2, (_j, _k + 1, 1), (_k, 1, 0))/(2*pi))
 * ```
 */
export function CircularUnitaryEnsemble(sym: string | Sym, dim: ExprLike): RandomMatrixSymbol {
  return ensemble(CircularUnitaryEnsembleModel, sym, dim);
}

/**
 * Constructs a random matrix of the circular orthogonal ensemble.
 *
 * @param sym - Name or symbol for the random variable.
 * @param dim - Dimension of the square random matrix.
 * @returns The ensemble random matrix symbol.
 * @throws RangeError when the dimension is known not to be an integer.
 * @see SymPy `sympy.stats.random_matrix_models.CircularOrthogonalEnsemble`
 * @example
 * ```ts
 * import { CircularOrthogonalEnsemble, jointEigenDistribution } from '@symjs/symjs';
 *
 * const U = CircularOrthogonalEnsemble('U', 1);
 * jointEigenDistribution(U); // => Lambda(t[1], Product(Abs(exp(I*t[_j]) - exp(I*t[_k])), (_j, _k + 1, 1), (_k, 1, 0))/(2*pi))
 * ```
 */
export function CircularOrthogonalEnsemble(sym: string | Sym, dim: ExprLike): RandomMatrixSymbol {
  return ensemble(CircularOrthogonalEnsembleModel, sym, dim);
}

/**
 * Constructs a random matrix of the circular symplectic ensemble.
 *
 * @param sym - Name or symbol for the random variable.
 * @param dim - Dimension of the square random matrix.
 * @returns The ensemble random matrix symbol.
 * @throws RangeError when the dimension is known not to be an integer.
 * @see SymPy `sympy.stats.random_matrix_models.CircularSymplecticEnsemble`
 * @example
 * ```ts
 * import { CircularSymplecticEnsemble, jointEigenDistribution } from '@symjs/symjs';
 *
 * const U = CircularSymplecticEnsemble('U', 1);
 * jointEigenDistribution(U); // => Lambda(t[1], Product(Abs(exp(I*t[_j]) - exp(I*t[_k]))**4, (_j, _k + 1, 1), (_k, 1, 0))/(2*pi))
 * ```
 */
export function CircularSymplecticEnsemble(sym: string | Sym, dim: ExprLike): RandomMatrixSymbol {
  return ensemble(CircularSymplecticEnsembleModel, sym, dim);
}

// ---------------------------------------------------------------------------
// Eigenvalue distributions
// ---------------------------------------------------------------------------

/** The model of a random matrix of an ensemble. */
function modelOf(mat: Expr): RandomMatrixEnsembleModel {
  if (!(mat instanceof RandomMatrixSymbol)) throw new RangeError(`${mat.toString()} is not of type, RandomMatrixSymbol.`);
  return cast(cast(mat.pspace, RandomMatrixPSpace, 'random matrix space').model, RandomMatrixEnsembleModel, 'ensemble model');
}

/**
 * Constructs the joint law of the eigenvalues of a matrix drawn from the ensemble.
 *
 * @param mat - Matrix whose eigenvalues are studied.
 * @returns The joint density lambda.
 * @see SymPy `sympy.stats.random_matrix_models.joint_eigen_distribution`
 * @example
 * ```ts
 * import { GaussianUnitaryEnsemble, jointEigenDistribution } from '@symjs/symjs';
 *
 * const U = GaussianUnitaryEnsemble('U', 2);
 * jointEigenDistribution(U); // => Lambda((l[1], l[2]), exp(-l[1]**2 - l[2]**2)*Product(Abs(l[_i] - l[_j])**2, (_j, _i + 1, 2), (_i, 1, 1))/pi)
 * ```
 */
export function jointEigenDistribution(mat: Expr): Expr {
  return modelOf(mat).jointEigenDistribution();
}

/**
 * Constructs the joint probability distribution of the eigenvalues of a matrix with random entries.
 *
 * @param mat - Matrix whose eigenvalues are studied.
 * @returns The joint distribution of the eigenvalues of a matrix with random entries.
 * @throws RangeError when the eigenvalues contain no random expressions.
 * @see SymPy `sympy.stats.random_matrix_models.JointEigenDistribution`
 * @example
 * ```ts
 * import { JointEigenDistribution, Matrix, Normal } from '@symjs/symjs';
 *
 * const A = Normal('A', 0, 1);
 * JointEigenDistribution(Matrix.of([[A]])); // => JointDistributionHandmade(A)
 * ```
 */
export function JointEigenDistribution(mat: Matrix | Expr): JointDistributionHandmade {
  const m = mat instanceof Matrix ? mat : cast(mat, MatrixExpr, 'matrix').asExplicit();
  const eigenvals = m.eigenvals();
  if (!eigenvals.every((e) => isRandom(e))) throw new RangeError('Eigen values do not have any random expression, joint distribution cannot be generated.');
  return new JointDistributionHandmade(eigenvals);
}

/**
 * Constructs the law of adjacent eigenvalue gaps in a Gaussian ensemble.
 *
 * @param mat - Matrix whose eigenvalues are studied.
 * @returns The spacing density lambda.
 * @see SymPy `sympy.stats.random_matrix_models.level_spacing_distribution`
 * @example
 * ```ts
 * import { GaussianUnitaryEnsemble, levelSpacingDistribution } from '@symjs/symjs';
 *
 * const U = GaussianUnitaryEnsemble('U', 2);
 * levelSpacingDistribution(U); // => Lambda(_s, 32*_s**2*exp(-4*_s**2/pi)/pi**2)
 * ```
 */
export function levelSpacingDistribution(mat: Expr): Expr {
  return modelOf(mat).levelSpacingDistribution();
}

void ImmutableMatrixNode;

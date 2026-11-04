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

/** SymPy RandomMatrixEnsembleModel(sym, dim): the base class of the random matrix ensembles. */
export class RandomMatrixEnsembleModel extends ExtensionExpr {
  constructor(args: readonly Expr[], name = 'RandomMatrixEnsembleModel') {
    const [sym, dim] = [symbolConverter(at(args, 0)), at(args, 1)];
    if (isIntegerQ(dim) === false) throw new RangeError(`Dimension of the random matrices must be integers, received ${dim.toString()} instead.`);
    super(name, [sym, dim]);
  }
  get symbol(): Sym {
    return symbolConverter(at(this.args, 0));
  }
  get dimension(): Expr {
    return at(this.args, 1);
  }
  withArgs(args: readonly Expr[]): Expr {
    return cast(Reflect.construct(this.constructor, [args]), Expr);
  }
  /** The density of a random matrix of the ensemble (SymPy density: unevaluated here). */
  density(expr: Expr): Expr {
    return new Density([expr]);
  }
  /** SymPy __call__: the density. */
  call(expr: Expr): Expr {
    return this.density(expr);
  }
  /** The joint distribution of the eigenvalues, a Lambda (SymPy joint_eigen_distribution of the ensembles that define it). */
  jointEigenDistribution(): Expr {
    throw new NotImplementedError(`${this.name} has no joint eigenvalue distribution`);
  }
  /** The distribution of the spacing of adjacent eigenvalues, a Lambda (SymPy level_spacing_distribution of the Gaussian ensembles). */
  levelSpacingDistribution(): Expr {
    throw new NotImplementedError(`${this.name} has no level spacing distribution`);
  }
}

// ---------------------------------------------------------------------------
// Gaussian ensembles
// ---------------------------------------------------------------------------

/** SymPy GaussianEnsembleModel: the Gaussian ensembles. */
export class GaussianEnsembleModel extends RandomMatrixEnsembleModel {
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

/** SymPy GaussianUnitaryEnsembleModel. */
export class GaussianUnitaryEnsembleModel extends GaussianEnsembleModel {
  constructor(args: readonly Expr[]) {
    super(args, 'GaussianUnitaryEnsembleModel');
  }
  /** SymPy normalization_constant: 2**(n/2)*pi**(n**2/2). */
  get normalizationConstant(): Expr {
    const n = this.dimension;
    return mul(pow(2, mul(n, S.Half)), pow(S.Pi, mul(pow(n, 2), S.Half)));
  }
  override density(expr: Expr): Expr {
    return this.traceDensity(expr, mul(this.dimension, S.Half), this.normalizationConstant);
  }
  override jointEigenDistribution(): Expr {
    return this.jointEigenDistributionOf(Rational.of(2n));
  }
  override levelSpacingDistribution(): Expr {
    const s = new Dummy('s');
    return Lambda(s, mul(32, pow(S.Pi, -2), pow(s, 2), exp(mul(-4, pow(S.Pi, -1), pow(s, 2)))));
  }
}

/** SymPy GaussianOrthogonalEnsembleModel. */
export class GaussianOrthogonalEnsembleModel extends GaussianEnsembleModel {
  constructor(args: readonly Expr[]) {
    super(args, 'GaussianOrthogonalEnsembleModel');
  }
  /** SymPy normalization_constant: an unevaluated integral over the matrices. */
  get normalizationConstant(): Expr {
    return traceIntegral(this.dimension, mul(this.dimension, Rational.of(1n, 4n)));
  }
  override density(expr: Expr): Expr {
    return this.traceDensity(expr, mul(this.dimension, Rational.of(1n, 4n)), this.normalizationConstant);
  }
  override jointEigenDistribution(): Expr {
    return this.jointEigenDistributionOf(S.One);
  }
  override levelSpacingDistribution(): Expr {
    const s = new Dummy('s');
    return Lambda(s, mul(S.Pi, S.Half, s, exp(mul(-1, S.Pi, Rational.of(1n, 4n), pow(s, 2)))));
  }
}

/** SymPy GaussianSymplecticEnsembleModel. */
export class GaussianSymplecticEnsembleModel extends GaussianEnsembleModel {
  constructor(args: readonly Expr[]) {
    super(args, 'GaussianSymplecticEnsembleModel');
  }
  /** SymPy normalization_constant: an unevaluated integral over the matrices. */
  get normalizationConstant(): Expr {
    return traceIntegral(this.dimension, this.dimension);
  }
  override density(expr: Expr): Expr {
    return this.traceDensity(expr, this.dimension, this.normalizationConstant);
  }
  override jointEigenDistribution(): Expr {
    return this.jointEigenDistributionOf(Rational.of(4n));
  }
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

/** A random matrix of the Gaussian ensemble (SymPy GaussianEnsemble(sym, dim)). */
export function GaussianEnsemble(sym: string | Sym, dim: ExprLike): RandomMatrixSymbol {
  return ensemble(GaussianEnsembleModel, sym, dim);
}

/** A random matrix of the Gaussian unitary ensemble (SymPy GaussianUnitaryEnsemble(sym, dim)). */
export function GaussianUnitaryEnsemble(sym: string | Sym, dim: ExprLike): RandomMatrixSymbol {
  return ensemble(GaussianUnitaryEnsembleModel, sym, dim);
}

/** A random matrix of the Gaussian orthogonal ensemble (SymPy GaussianOrthogonalEnsemble(sym, dim)). */
export function GaussianOrthogonalEnsemble(sym: string | Sym, dim: ExprLike): RandomMatrixSymbol {
  return ensemble(GaussianOrthogonalEnsembleModel, sym, dim);
}

/** A random matrix of the Gaussian symplectic ensemble (SymPy GaussianSymplecticEnsemble(sym, dim)). */
export function GaussianSymplecticEnsemble(sym: string | Sym, dim: ExprLike): RandomMatrixSymbol {
  return ensemble(GaussianSymplecticEnsembleModel, sym, dim);
}

// ---------------------------------------------------------------------------
// Circular ensembles
// ---------------------------------------------------------------------------

/** SymPy CircularEnsembleModel: the circular ensembles. */
export class CircularEnsembleModel extends RandomMatrixEnsembleModel {
  constructor(args: readonly Expr[], name = 'CircularEnsembleModel') {
    super(args, name);
  }
  /** SymPy: the Haar measure is not implemented, so the density cannot be computed. */
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

/** SymPy CircularUnitaryEnsembleModel. */
export class CircularUnitaryEnsembleModel extends CircularEnsembleModel {
  constructor(args: readonly Expr[]) {
    super(args, 'CircularUnitaryEnsembleModel');
  }
  override jointEigenDistribution(): Expr {
    return this.jointEigenDistributionOf(Rational.of(2n));
  }
}

/** SymPy CircularOrthogonalEnsembleModel. */
export class CircularOrthogonalEnsembleModel extends CircularEnsembleModel {
  constructor(args: readonly Expr[]) {
    super(args, 'CircularOrthogonalEnsembleModel');
  }
  override jointEigenDistribution(): Expr {
    return this.jointEigenDistributionOf(S.One);
  }
}

/** SymPy CircularSymplecticEnsembleModel. */
export class CircularSymplecticEnsembleModel extends CircularEnsembleModel {
  constructor(args: readonly Expr[]) {
    super(args, 'CircularSymplecticEnsembleModel');
  }
  override jointEigenDistribution(): Expr {
    return this.jointEigenDistributionOf(Rational.of(4n));
  }
}

/** A random matrix of the circular ensemble (SymPy CircularEnsemble(sym, dim)). */
export function CircularEnsemble(sym: string | Sym, dim: ExprLike): RandomMatrixSymbol {
  return ensemble(CircularEnsembleModel, sym, dim);
}

/** A random matrix of the circular unitary ensemble (SymPy CircularUnitaryEnsemble(sym, dim)). */
export function CircularUnitaryEnsemble(sym: string | Sym, dim: ExprLike): RandomMatrixSymbol {
  return ensemble(CircularUnitaryEnsembleModel, sym, dim);
}

/** A random matrix of the circular orthogonal ensemble (SymPy CircularOrthogonalEnsemble(sym, dim)). */
export function CircularOrthogonalEnsemble(sym: string | Sym, dim: ExprLike): RandomMatrixSymbol {
  return ensemble(CircularOrthogonalEnsembleModel, sym, dim);
}

/** A random matrix of the circular symplectic ensemble (SymPy CircularSymplecticEnsemble(sym, dim)). */
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

/** The joint distribution of the eigenvalues of a random matrix of an ensemble, a Lambda (SymPy joint_eigen_distribution). */
export function jointEigenDistribution(mat: Expr): Expr {
  return modelOf(mat).jointEigenDistribution();
}

/**
 * The joint distribution of the eigenvalues of a matrix with random
 * entries (SymPy JointEigenDistribution): a JointDistributionHandmade of
 * the eigenvalues.
 */
export function JointEigenDistribution(mat: Matrix | Expr): JointDistributionHandmade {
  const m = mat instanceof Matrix ? mat : cast(mat, MatrixExpr, 'matrix').asExplicit();
  const eigenvals = m.eigenvals();
  if (!eigenvals.every((e) => isRandom(e))) throw new RangeError('Eigen values do not have any random expression, joint distribution cannot be generated.');
  return new JointDistributionHandmade(eigenvals);
}

/** The distribution of the spacing of adjacent eigenvalues of a random matrix of a Gaussian ensemble, a Lambda (SymPy level_spacing_distribution). */
export function levelSpacingDistribution(mat: Expr): Expr {
  return modelOf(mat).levelSpacingDistribution();
}

void ImmutableMatrixNode;

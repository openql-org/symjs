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

/** A matrix argument: a matrix expression, an explicit matrix or nested arrays (SymPy list). */
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

/** SymPy MatrixPSpace(sym, distribution, dim_n, dim_m): the probability space of a random matrix. */
export class MatrixPSpace extends PSpace {
  constructor(args: readonly Expr[]) {
    const [n, m] = [at(args, 2), at(args, 3)];
    if (!(isIntegerQ(n) === true && isIntegerQ(m) === true)) throw new RangeError('Dimensions should be integers');
    super([symbolConverter(at(args, 0)), cast(at(args, 1), MatrixDistribution, 'matrix distribution'), n, m], 'MatrixPSpace');
  }
  get symbol(): Sym {
    return symbolConverter(at(this.args, 0));
  }
  get distribution(): MatrixDistribution {
    return cast(at(this.args, 1), MatrixDistribution);
  }
  override get domain(): MatrixDomain {
    return new MatrixDomain([this.symbol, this.distribution.set]);
  }
  /** The random matrix symbol of the space (SymPy value). */
  get value(): RandomMatrixSymbol {
    return new RandomMatrixSymbol(this.symbol, at(this.args, 2), at(this.args, 3), this);
  }
  override get hasValueDensity(): boolean {
    return true;
  }
  override get valueDensity(): Expr {
    return this.distribution;
  }
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

/** SymPy MatrixDistribution: a distribution of random matrices, applied to a matrix. */
export abstract class MatrixDistribution extends Distribution {
  constructor(name: string, args: readonly Expr[]) {
    super(name, args);
  }
  /** The parameters are valid (SymPy check). */
  abstract check(): void;
  /** The shape of the random matrices (SymPy dimension). */
  abstract get dimension(): [Expr, Expr];
  /** The density at a matrix (SymPy pdf; a nested array is a matrix). */
  abstract override pdf(x: MatrixInput): Expr;
  /** SymPy __call__: the density at a matrix. */
  override call(x: MatrixInput): Expr {
    return this.pdf(x);
  }
  /** The set of the n x m real matrices (SymPy set). */
  protected matrixSet(n: Expr, m: Expr): SetExpr {
    return new MatrixSetNode(n, m, Reals);
  }
}

/** SymPy MatrixGammaDistribution(alpha, beta, scale_matrix). */
export class MatrixGammaDistribution extends MatrixDistribution {
  constructor(args: readonly Expr[]) {
    super('MatrixGammaDistribution', args.map((a) => toMatrixArg(a)));
  }
  get alpha(): Expr {
    return this.arg(0);
  }
  get beta(): Expr {
    return this.arg(1);
  }
  get scaleMatrix(): Expr {
    return this.arg(2);
  }
  check(): void {
    valueCheck(positiveDefinite(this.scaleMatrix), 'The shape matrix must be positive definite.');
    valueCheck(squareOf(this.scaleMatrix), 'Should be square matrix');
    valueCheck(isPositive(this.alpha), 'Shape parameter should be positive.');
    valueCheck(isPositive(this.beta), 'Scale parameter should be positive.');
  }
  get set(): SetExpr {
    const k = at(shapeOf(this.scaleMatrix), 0);
    return this.matrixSet(k, k);
  }
  get dimension(): [Expr, Expr] {
    return shapeOf(this.scaleMatrix);
  }
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

/** Matrix gamma distribution (SymPy MatrixGamma(symbol, alpha, beta, scale_matrix)). */
export function MatrixGamma(symbol: string | Sym, alpha: ExprLike, beta: ExprLike, scaleMatrix: MatrixInput): RandomMatrixSymbol {
  return rv(symbol, MatrixGammaDistribution, [sympify(alpha), sympify(beta), scaleMatrix]);
}

/** SymPy WishartDistribution(n, scale_matrix). */
export class WishartDistribution extends MatrixDistribution {
  constructor(args: readonly Expr[]) {
    super('WishartDistribution', args.map((a) => toMatrixArg(a)));
  }
  /** The degrees of freedom (SymPy n; `n` is evalf on expressions). */
  get dof(): Expr {
    return this.arg(0);
  }
  get scaleMatrix(): Expr {
    return this.arg(1);
  }
  check(): void {
    valueCheck(positiveDefinite(this.scaleMatrix), 'The shape matrix must be positive definite.');
    valueCheck(squareOf(this.scaleMatrix), 'Should be square matrix');
    valueCheck(isPositive(this.dof), 'Shape parameter should be positive.');
  }
  get set(): SetExpr {
    const k = at(shapeOf(this.scaleMatrix), 0);
    return this.matrixSet(k, k);
  }
  get dimension(): [Expr, Expr] {
    return shapeOf(this.scaleMatrix);
  }
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

/** Wishart distribution (SymPy Wishart(symbol, n, scale_matrix)). */
export function Wishart(symbol: string | Sym, n: ExprLike, scaleMatrix: MatrixInput): RandomMatrixSymbol {
  return rv(symbol, WishartDistribution, [sympify(n), scaleMatrix]);
}

/** SymPy MatrixNormalDistribution(location_matrix, scale_matrix_1, scale_matrix_2). */
export class MatrixNormalDistribution extends MatrixDistribution {
  constructor(args: readonly Expr[]) {
    super('MatrixNormalDistribution', args.map((a) => toMatrixArg(a)));
  }
  get locationMatrix(): Expr {
    return this.arg(0);
  }
  get scaleMatrix1(): Expr {
    return this.arg(1);
  }
  get scaleMatrix2(): Expr {
    return this.arg(2);
  }
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
  get set(): SetExpr {
    const [n, p] = shapeOf(this.locationMatrix);
    return this.matrixSet(n, p);
  }
  get dimension(): [Expr, Expr] {
    return shapeOf(this.locationMatrix);
  }
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

/** Matrix normal distribution (SymPy MatrixNormal(symbol, location_matrix, scale_matrix_1, scale_matrix_2)). */
export function MatrixNormal(symbol: string | Sym, locationMatrix: MatrixInput, scaleMatrix1: MatrixInput, scaleMatrix2: MatrixInput): RandomMatrixSymbol {
  return rv(symbol, MatrixNormalDistribution, [locationMatrix, scaleMatrix1, scaleMatrix2]);
}

/** SymPy MatrixStudentTDistribution(nu, location_matrix, scale_matrix_1, scale_matrix_2). */
export class MatrixStudentTDistribution extends MatrixDistribution {
  constructor(args: readonly Expr[]) {
    super('MatrixStudentTDistribution', args.map((a) => toMatrixArg(a)));
  }
  get nu(): Expr {
    return this.arg(0);
  }
  get locationMatrix(): Expr {
    return this.arg(1);
  }
  get scaleMatrix1(): Expr {
    return this.arg(2);
  }
  get scaleMatrix2(): Expr {
    return this.arg(3);
  }
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
  get set(): SetExpr {
    const [n, p] = shapeOf(this.locationMatrix);
    return this.matrixSet(n, p);
  }
  get dimension(): [Expr, Expr] {
    return shapeOf(this.locationMatrix);
  }
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

/** Matrix Student's t distribution (SymPy MatrixStudentT(symbol, nu, location_matrix, scale_matrix_1, scale_matrix_2)). */
export function MatrixStudentT(symbol: string | Sym, nu: ExprLike, locationMatrix: MatrixInput, scaleMatrix1: MatrixInput, scaleMatrix2: MatrixInput): RandomMatrixSymbol {
  return rv(symbol, MatrixStudentTDistribution, [sympify(nu), locationMatrix, scaleMatrix1, scaleMatrix2]);
}


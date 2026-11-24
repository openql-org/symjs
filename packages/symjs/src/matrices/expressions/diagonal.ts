// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file SymPy DiagonalMatrix, DiagonalOf, DiagMatrix and diagonalize_vector
 * (sympy.matrices.expressions.diagonal).
 */

import { cast, first } from '../../core/guard';
import { callableClass } from '../../core/callable';
import type { Expr } from '../../core/nodes';
import { S } from '../../core/nodes';
import { mul } from '../../core/ops';
import { KroneckerDelta } from '../../functions/special/hyper';
import { Min } from '../../functions/special/special';
import { compareKeys, sortKey } from '../../printing/sortkey';
import { Matrix } from '../matrix';
import type { DoitHints, EntryContext, MatArg } from './matexpr';
import { IdentityNode, ImmutableMatrixNode, MatMulNode, MatrixExpr, TransposeNode, doitArg, toMatrix } from './matexpr';
import { isInt, relTruth, same } from './util';

/**
 * The length of the diagonal of an r x c matrix (SymPy diagonal_length).
 * SymPy gives None when min(r, c) cannot be decided; this gives Min(r, c).
 */
function diagonalLength(r: Expr, c: Expr): Expr {
  if (isInt(r) && isInt(c)) return r.p <= c.p ? r : c;
  if (isInt(r)) return r;
  if (isInt(c)) return c;
  if (same(r, c)) return r;
  const t = relTruth('Lt', c, r);
  if (t === true) return c;
  if (t === false) return r;
  return Min(...[r, c].sort((x, y) => compareKeys(sortKey(x), sortKey(y))));
}

/**
 * The matrix M with its off-diagonal entries replaced by zeros.
 * @see SymPy `sympy.matrices.expressions.diagonal.DiagonalMatrix`
 */
export class DiagonalMatrixNode extends MatrixExpr {
  /**
   * Constructs a `DiagonalMatrix`.
   * @param arg - The expression to operate on.
   */
  constructor(arg: Expr) {
    super('DiagonalMatrix', [arg]);
  }
  /**
   * The matrix.
   * @returns The operand of the expression.
   * @see SymPy `sympy.matrices.expressions.diagonal.DiagonalMatrix.arg`
   */
  get arg(): MatrixExpr {
    return cast(first(this.args), MatrixExpr);
  }
  /**
   * The number of rows and columns, in that order.
   * @returns The row and column dimensions.
   * @see SymPy `sympy.matrices.expressions.diagonal.DiagonalMatrix.shape`
   */
  get shape(): [Expr, Expr] {
    return this.arg.shape;
  }
  /**
   * The number of entries along the main diagonal.
   * @returns The smaller matrix dimension.
   * @see SymPy `sympy.matrices.expressions.diagonal.DiagonalMatrix.diagonal_length`
   */
  get diagonalLength(): Expr {
    return diagonalLength(...this.shape);
  }
  /**
   * Rebuilds the expression with replacement operands.
   * @param args - The operands in their defining order.
   * @returns The expression with the given operands.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new DiagonalMatrixNode(first(args));
  }
  /**
   * Computes the matrix entry at the given row and column.
   * @param i - The zero-based row index.
   * @param j - The zero-based column index.
   * @returns The scalar at the requested position.
   * @see SymPy `sympy.matrices.expressions.diagonal.DiagonalMatrix._entry`
   */
  override entry(i: Expr, j: Expr): Expr {
    const len = this.diagonalLength;
    if (relTruth('Ge', i, len) === true || relTruth('Ge', j, len) === true) return S.Zero;
    const eq = relTruth('Eq', i, j);
    if (eq === true) return this.arg.at(i, i);
    if (eq === false) return S.Zero;
    return mul(this.arg.at(i, j), KroneckerDelta(i, j));
  }
}

/**
 * The matrix M with its off-diagonal entries replaced by zeros.
 * @param m - The matrix whose diagonal is selected.
 * @returns The resulting matrix expression.
 * @see SymPy `sympy.matrices.expressions.diagonal.DiagonalMatrix`
 * @example
 * ```ts
 * import { DiagonalMatrix, MatrixSymbol, Q, ask, symbols } from '@symjs/symjs';
 *
 * const [n] = symbols('n');
 * ask(Q.diagonal(DiagonalMatrix(MatrixSymbol('x', n, n))), true); // => True
 * ```
 */
export const DiagonalMatrix = /* @__PURE__ */ callableClass(DiagonalMatrixNode, (m: MatArg): DiagonalMatrixNode => new DiagonalMatrixNode(toMatrix(m)));
export type DiagonalMatrix = DiagonalMatrixNode;

/**
 * The diagonal of M as a column vector.
 * @see SymPy `sympy.matrices.expressions.diagonal.DiagonalOf`
 */
export class DiagonalOfNode extends MatrixExpr {
  /**
   * Constructs a `DiagonalOf`.
   * @param arg - The expression to operate on.
   */
  constructor(arg: Expr) {
    super('DiagonalOf', [arg]);
  }
  /**
   * The matrix.
   * @returns The operand of the expression.
   * @see SymPy `sympy.matrices.expressions.diagonal.DiagonalOf.arg`
   */
  get arg(): MatrixExpr {
    return cast(first(this.args), MatrixExpr);
  }
  /**
   * The number of rows and columns, in that order.
   * @returns The row and column dimensions.
   * @see SymPy `sympy.matrices.expressions.diagonal.DiagonalOf.shape`
   */
  get shape(): [Expr, Expr] {
    return [diagonalLength(...this.arg.shape), S.One];
  }
  /**
   * The number of entries along the main diagonal.
   * @returns The smaller matrix dimension.
   * @see SymPy `sympy.matrices.expressions.diagonal.DiagonalOf.diagonal_length`
   */
  get diagonalLength(): Expr {
    return this.shape[0];
  }
  /**
   * Rebuilds the expression with replacement operands.
   * @param args - The operands in their defining order.
   * @returns The expression with the given operands.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new DiagonalOfNode(first(args));
  }
  /**
   * Computes the matrix entry at the given row and column.
   * @param i - The zero-based row index.
   * @param _j - The zero-based column index.
   * @param ctx - The index context for evaluating matrix entries.
   * @returns The scalar at the requested position.
   * @see SymPy `sympy.matrices.expressions.diagonal.DiagonalOf._entry`
   */
  override entry(i: Expr, _j: Expr, ctx?: EntryContext): Expr {
    return this.arg.entry(i, i, ctx);
  }
}

/**
 * The diagonal of M as a column vector.
 * @param m - The matrix whose diagonal is selected.
 * @returns The resulting matrix expression.
 * @see SymPy `sympy.matrices.expressions.diagonal.DiagonalOf`
 * @example
 * ```ts
 * import { DiagonalOf, MatrixSymbol } from '@symjs/symjs';
 * DiagonalOf(MatrixSymbol('X', 2, 3)).shape; // => [2, 1]
 * ```
 */
export const DiagonalOf = /* @__PURE__ */ callableClass(DiagonalOfNode, (m: MatArg): DiagonalOfNode => new DiagonalOfNode(toMatrix(m)));
export type DiagonalOf = DiagonalOfNode;

/**
 * The diagonal matrix with the entries of a row or column vector.
 * @see SymPy `sympy.matrices.expressions.diagonal.DiagMatrix`
 */
export class DiagMatrixNode extends MatrixExpr {
  /**
   * Constructs a `DiagMatrix`.
   * @param vector - The row or column vector.
   */
  constructor(vector: Expr) {
    super('DiagMatrix', [vector]);
  }
  /**
   * Gets the vector.
   * @returns The vector.
   */
  get vector(): MatrixExpr {
    return cast(first(this.args), MatrixExpr);
  }
  private get isColumn(): boolean {
    return !same(this.vector.rows, S.One);
  }
  /**
   * The number of rows and columns, in that order.
   * @returns The row and column dimensions.
   * @see SymPy `sympy.matrices.expressions.diagonal.DiagMatrix.shape`
   */
  get shape(): [Expr, Expr] {
    const [r, c] = this.vector.shape;
    const d = same(r, S.One) ? c : r;
    return [d, d];
  }
  /**
   * Rebuilds the expression with replacement operands.
   * @param args - The operands in their defining order.
   * @returns The expression with the given operands.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new DiagMatrixNode(first(args));
  }
  /**
   * Computes the matrix entry at the given row and column.
   * @param i - The zero-based row index.
   * @param j - The zero-based column index.
   * @param ctx - The index context for evaluating matrix entries.
   * @returns The scalar at the requested position.
   * @see SymPy `sympy.matrices.expressions.diagonal.DiagMatrix._entry`
   */
  override entry(i: Expr, j: Expr, ctx?: EntryContext): Expr {
    const r = this.isColumn ? this.vector.entry(i, S.Zero, ctx) : this.vector.entry(S.Zero, j, ctx);
    return same(i, j) ? r : mul(r, KroneckerDelta(i, j));
  }
  /**
   * Computes the transpose using the structure of this expression.
   * @returns The transpose using the structure of this expression.
   * @see SymPy `sympy.matrices.expressions.diagonal.DiagMatrix._eval_transpose`
   */
  override evalTranspose(): Expr {
    return this;
  }
  /**
   * Evaluates the entries to construct an explicit matrix.
   * @returns The resulting matrix.
   * @see SymPy `sympy.matrices.expressions.diagonal.DiagMatrix.as_explicit`
   */
  override asExplicit(): Matrix {
    const v = this.vector.asExplicit().data;
    return Matrix.diag(...v);
  }
  /**
   * Evaluates the operations represented by this expression.
   * @param hints - Evaluation options, including whether to evaluate the operands recursively.
   * @returns The evaluated expression.
   * @see SymPy `sympy.matrices.expressions.diagonal.DiagMatrix.doit`
   */
  override doit(hints: DoitHints = {}): Expr {
    const vector = hints.deep === false ? this.vector : cast(doitArg(this.vector, hints), MatrixExpr);
    if (vector instanceof IdentityNode || same(vector.rows, S.One) && same(vector.cols, S.One)) return vector;
    if (vector instanceof ImmutableMatrixNode) {
      const m = vector.matrix;
      return new ImmutableMatrixNode(Matrix.diag(...m.data));
    }
    if (vector instanceof MatMulNode) {
      const [c, ms] = vector.asCoeffMatrices();
      if (vector.args.some((a) => !(a instanceof MatrixExpr))) {
        const v = cast(MatMulNode.create(ms), MatrixExpr).doit();
        return doitMul(c, new DiagMatrixNode(v).doit());
      }
    }
    if (vector instanceof TransposeNode) return new DiagMatrixNode(vector.arg);
    return vector === this.vector ? this : new DiagMatrixNode(vector);
  }
}

function doitMul(c: Expr, m: Expr): Expr {
  return cast(MatMulNode.create([c, m]), MatrixExpr).doit();
}

/**
 * The diagonal matrix with the entries of a row or column vector.
 * @param v - The vector of diagonal entries.
 * @returns The resulting matrix expression.
 * @see SymPy `sympy.matrices.expressions.diagonal.DiagMatrix`
 * @example
 * ```ts
 * import { DiagMatrix, Identity } from '@symjs/symjs';
 * DiagMatrix(Identity(3)).doit(); // => I
 * ```
 */
export const DiagMatrix = /* @__PURE__ */ callableClass(DiagMatrixNode, (v: MatArg): DiagMatrixNode => new DiagMatrixNode(toMatrix(v)));
export type DiagMatrix = DiagMatrixNode;

/**
 * Places the entries of a vector along the diagonal of a square matrix.
 * @param vector - The row or column vector.
 * @returns The resulting symbolic expression.
 * @see SymPy `sympy.matrices.expressions.diagonal.diagonalize_vector`
 * @example
 * ```ts
 * import { Identity, diagonalizeVector } from '@symjs/symjs';
 * diagonalizeVector(Identity(3)); // => I
 * ```
 */
export function diagonalizeVector(vector: MatArg): Expr {
  return new DiagMatrixNode(toMatrix(vector)).doit();
}

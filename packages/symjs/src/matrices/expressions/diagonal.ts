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
import { ImmutableMatrixNode, MatMulNode, MatrixExpr, TransposeNode, doitArg, toMatrix } from './matexpr';
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

/** SymPy DiagonalMatrix(M): the matrix M with its off-diagonal entries replaced by zeros. */
export class DiagonalMatrixNode extends MatrixExpr {
  constructor(arg: Expr) {
    super('DiagonalMatrix', [arg]);
  }
  /** The matrix. */
  get arg(): MatrixExpr {
    return cast(first(this.args), MatrixExpr);
  }
  get shape(): [Expr, Expr] {
    return this.arg.shape;
  }
  /** SymPy diagonal_length (Min(rows, cols) where SymPy gives None). */
  get diagonalLength(): Expr {
    return diagonalLength(...this.shape);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new DiagonalMatrixNode(first(args));
  }
  override entry(i: Expr, j: Expr): Expr {
    const len = this.diagonalLength;
    if (relTruth('Ge', i, len) === true || relTruth('Ge', j, len) === true) return S.Zero;
    const eq = relTruth('Eq', i, j);
    if (eq === true) return this.arg.at(i, i);
    if (eq === false) return S.Zero;
    return mul(this.arg.at(i, j), KroneckerDelta(i, j));
  }
}

/** SymPy DiagonalMatrix(M). */
export const DiagonalMatrix = /* @__PURE__ */ callableClass(DiagonalMatrixNode, (m: MatArg): DiagonalMatrixNode => new DiagonalMatrixNode(toMatrix(m)));
export type DiagonalMatrix = DiagonalMatrixNode;

/** SymPy DiagonalOf(M): the diagonal of M as a column vector. */
export class DiagonalOfNode extends MatrixExpr {
  constructor(arg: Expr) {
    super('DiagonalOf', [arg]);
  }
  /** The matrix. */
  get arg(): MatrixExpr {
    return cast(first(this.args), MatrixExpr);
  }
  get shape(): [Expr, Expr] {
    return [diagonalLength(...this.arg.shape), S.One];
  }
  /** SymPy diagonal_length. */
  get diagonalLength(): Expr {
    return this.shape[0];
  }
  withArgs(args: readonly Expr[]): Expr {
    return new DiagonalOfNode(first(args));
  }
  override entry(i: Expr, _j: Expr, ctx?: EntryContext): Expr {
    return this.arg.entry(i, i, ctx);
  }
}

/** SymPy DiagonalOf(M). */
export const DiagonalOf = /* @__PURE__ */ callableClass(DiagonalOfNode, (m: MatArg): DiagonalOfNode => new DiagonalOfNode(toMatrix(m)));
export type DiagonalOf = DiagonalOfNode;

/** SymPy DiagMatrix(vector): the diagonal matrix with the entries of a row or column vector. */
export class DiagMatrixNode extends MatrixExpr {
  constructor(vector: Expr) {
    super('DiagMatrix', [vector]);
  }
  /** The vector. */
  get vector(): MatrixExpr {
    return cast(first(this.args), MatrixExpr);
  }
  private get isColumn(): boolean {
    return !same(this.vector.rows, S.One);
  }
  get shape(): [Expr, Expr] {
    const [r, c] = this.vector.shape;
    const d = same(r, S.One) ? c : r;
    return [d, d];
  }
  withArgs(args: readonly Expr[]): Expr {
    return new DiagMatrixNode(first(args));
  }
  override entry(i: Expr, j: Expr, ctx?: EntryContext): Expr {
    const r = this.isColumn ? this.vector.entry(i, S.Zero, ctx) : this.vector.entry(S.Zero, j, ctx);
    return same(i, j) ? r : mul(r, KroneckerDelta(i, j));
  }
  override evalTranspose(): Expr {
    return this;
  }
  override asExplicit(): Matrix {
    const v = this.vector.asExplicit().data;
    return Matrix.diag(...v);
  }
  override doit(hints: DoitHints = {}): Expr {
    const vector = hints.deep === false ? this.vector : cast(doitArg(this.vector, hints), MatrixExpr);
    if (same(vector.rows, S.One) && same(vector.cols, S.One)) return vector;
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

/** SymPy DiagMatrix(vector). */
export const DiagMatrix = /* @__PURE__ */ callableClass(DiagMatrixNode, (v: MatArg): DiagMatrixNode => new DiagMatrixNode(toMatrix(v)));
export type DiagMatrix = DiagMatrixNode;

/** SymPy diagonalize_vector(vector): DiagMatrix(vector).doit(). */
export function diagonalizeVector(vector: MatArg): Expr {
  return new DiagMatrixNode(toMatrix(vector)).doit();
}

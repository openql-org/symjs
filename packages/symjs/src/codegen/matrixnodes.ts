// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import type { Expr } from '../core/nodes';
import { at, cast } from '../core/guard';
import { callableClass } from '../core/callable';
import { Matrix } from '../matrices/matrix';
import { ImmutableMatrix, MatrixExpr } from '../matrices/expressions/matexpr';
import { srepr } from '../printing/repr';

/** An unevaluated solution of A*x = b (SymPy codegen.matrix_nodes.MatrixSolve). */
class MatrixSolveNode extends MatrixExpr {
  constructor(readonly matrix: MatrixExpr, readonly vector: MatrixExpr) {
    super('MatrixSolve', [matrix, vector]);
  }
  get shape(): [Expr, Expr] { return this.vector.shape; }
  withArgs(args: readonly Expr[]): Expr {
    return new MatrixSolveNode(cast(at(args, 0), MatrixExpr), cast(at(args, 1), MatrixExpr));
  }
  override diffSelf(x: Expr, d: (e: Expr, x: Expr) => Expr): Expr {
    const rhs = d(this.vector, x).sub(d(this.matrix, x).mul(this));
    return new MatrixSolveNode(this.matrix, cast(rhs, MatrixExpr));
  }
  override printStr(print: (e: Expr) => string): string {
    return `MatrixSolve(${print(this.matrix)}, vector=${print(this.vector)})`;
  }
  printRepr(): string { return this.printStr(srepr); }
}

const asMatrix = (m: Matrix | MatrixExpr): MatrixExpr => m instanceof Matrix ? ImmutableMatrix(m) : m;

/** Represent a linear solve without expanding an inverse or computing its entries. */
export const MatrixSolve = /* @__PURE__ */ callableClass(MatrixSolveNode,
  (matrix: Matrix | MatrixExpr, vector: Matrix | MatrixExpr) => new MatrixSolveNode(asMatrix(matrix), asMatrix(vector)));

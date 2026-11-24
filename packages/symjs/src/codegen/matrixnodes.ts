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
  /**
   * Creates a symbolic matrix solve.
   *
   * @param matrix - The coefficient matrix.
   * @param vector - The right-hand side of the system.
   */
  constructor(/** The coefficient matrix. */ readonly matrix: MatrixExpr, /** The right-hand side of the system. */ readonly vector: MatrixExpr) {
    super('MatrixSolve', [matrix, vector]);
  }
  /**
   * The row and column dimensions of the solution.
   *
   * @see SymPy `sympy.codegen.matrix_nodes.MatrixSolve.shape`
   */
  get shape(): [Expr, Expr] { return this.vector.shape; }
  /**
   * Rebuilds the node with the supplied arguments.
   *
   * @param args - The operands in node order.
   * @returns The rebuilt expression.
   */
  withArgs(args: readonly Expr[]): Expr {
    return new MatrixSolveNode(cast(at(args, 0), MatrixExpr), cast(at(args, 1), MatrixExpr));
  }
  /**
   * Differentiates the linear system and solves for the derivative of its solution.
   *
   * @param x - The differentiation variable.
   * @param d - The callback for differentiating a subexpression.
   * @returns The derivative under this node’s differentiation rule.
   */
  override diffSelf(x: Expr, d: (e: Expr, x: Expr) => Expr): Expr {
    const rhs = d(this.vector, x).sub(d(this.matrix, x).mul(this));
    return new MatrixSolveNode(this.matrix, cast(rhs, MatrixExpr));
  }
  /**
   * Formats the node using the supplied printer for its children.
   *
   * @param print - The expression printer for child nodes.
   * @returns The formatted expression.
   */
  override printStr(print: (e: Expr) => string): string {
    return `MatrixSolve(${print(this.matrix)}, vector=${print(this.vector)})`;
  }
  /**
   * Formats the matrix solve in constructor notation.
   *
   * @returns The constructor representation.
   */
  printRepr(): string { return this.printStr(srepr); }
}

const asMatrix = (m: Matrix | MatrixExpr): MatrixExpr => m instanceof Matrix ? ImmutableMatrix(m) : m;

/**
 * Represent a linear solve without expanding an inverse or computing its entries.
 *
 * @param matrix - The coefficient matrix of the system.
 * @param vector - The right-hand side of the system.
 * @returns A matrix expression representing the solution of the linear system.
 * @see SymPy `sympy.codegen.matrix_nodes.MatrixSolve`
 * @example
 * ```ts
 * import { MatrixSolve, MatrixSymbol } from '@symjs/symjs';
 *
 * MatrixSolve(MatrixSymbol('A', 3, 3), MatrixSymbol('b', 3, 1)).shape; // => [3, 1]
 * ```
 */
export const MatrixSolve = /* @__PURE__ */ callableClass(MatrixSolveNode,
  (matrix: Matrix | MatrixExpr, vector: Matrix | MatrixExpr) => new MatrixSolveNode(asMatrix(matrix), asMatrix(vector)));

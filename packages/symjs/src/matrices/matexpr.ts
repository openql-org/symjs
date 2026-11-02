// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Matrix expressions (SymPy sympy.matrices.expressions): symbolic
 * matrices `MatrixSymbol('A', n, m)` that do not commute, with their
 * transposes (`A.T`) and adjoints (`Adjoint(A)`).
 */

import type { Expr, ExprLike } from '../core/nodes';
import { ExtensionExpr } from '../core/nodes';
import { sympify } from '../core/ops';

/** SymPy MatrixSymbol: a symbolic n x m matrix. */
export class MatrixSymbol extends ExtensionExpr {
  constructor(
    readonly symbolName: string,
    rows: ExprLike,
    cols: ExprLike,
  ) {
    super('MatrixSymbol', [sympify(rows), sympify(cols)]);
  }
  get shape(): [Expr, Expr] {
    return [this.args[0]!, this.args[1]!];
  }
  withArgs(args: readonly Expr[]): Expr {
    return new MatrixSymbol(this.symbolName, args[0]!, args[1]!);
  }
  protected override computeCommutative(): boolean {
    return false;
  }
  override printStr(): string {
    return this.symbolName;
  }
  override printLatex(): string {
    return this.symbolName;
  }
  override transposeSelf(): Expr {
    return new MatrixTranspose(this);
  }
  override adjointSelf(): Expr {
    return new MatrixAdjoint(this);
  }
  override conjugateSelf(): Expr {
    return new MatrixAdjoint(new MatrixTranspose(this));
  }
  protected override computeKey(): string {
    return `MatrixSymbol(${this.symbolName},${this.args.map((a) => a.key).join(',')})`;
  }
}

/** SymPy Transpose of a matrix expression, printed A.T. */
export class MatrixTranspose extends ExtensionExpr {
  constructor(arg: Expr) {
    super('Transpose', [arg]);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new MatrixTranspose(args[0]!);
  }
  protected override computeCommutative(): boolean {
    return false;
  }
  override printStr(print: (e: Expr) => string): string {
    const a = this.args[0]!;
    return a.isAtom || a instanceof MatrixSymbol ? `${print(a)}.T` : `(${print(a)}).T`;
  }
  override printLatex(print: (e: Expr) => string): string {
    return `${print(this.args[0]!)}^{T}`;
  }
  override transposeSelf(): Expr {
    return this.args[0]!;
  }
  override adjointSelf(): Expr {
    return new MatrixAdjoint(this);
  }
}

/** SymPy Adjoint of a matrix expression. */
export class MatrixAdjoint extends ExtensionExpr {
  constructor(arg: Expr) {
    super('Adjoint', [arg]);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new MatrixAdjoint(args[0]!);
  }
  protected override computeCommutative(): boolean {
    return false;
  }
  override printLatex(print: (e: Expr) => string): string {
    return `${print(this.args[0]!)}^{\\dagger}`;
  }
  override adjointSelf(): Expr {
    return this.args[0]!;
  }
  override transposeSelf(): Expr {
    return new MatrixTranspose(this);
  }
}

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy's physics/quantum/trace.py, BSD-3-Clause.

import { Add, ExtensionExpr, ImmutableMatrix, Matrix, Mul, Pow, S, Sym, Tuple, TupleNode, add, isNumber, mul, sympify } from '@symjs/symjs';
import type { Expr, ExprLike } from '@symjs/symjs';

const isScalar = (e: Expr): boolean => isNumber(e) || e === S.Infinity || e === S.NegativeInfinity || e === S.NaN || e instanceof Sym && e.isCommutative;

/** An unevaluated operator trace, with its optional partial-trace indices. */
class TraceNode extends ExtensionExpr {
  constructor(readonly operand: Expr, readonly indices: TupleNode) {
    super('Tr', [operand, indices]);
  }
  override get isNumber(): boolean { return true; }
  withArgs(args: readonly Expr[]): Expr {
    const [operand, indices] = args;
    if (!operand || !(indices instanceof TupleNode)) throw new TypeError('Tr requires an operand and a tuple of indices');
    return Tr(operand, indices);
  }
  override printStr(print: (e: Expr) => string): string {
    return `Tr(${print(this.operand)})`;
  }
  override printLatex(print: (e: Expr) => string): string {
    return `\\operatorname{tr}\\left(${print(this.operand)}\\right)`;
  }
  protected override computeKey(): string {
    if (!(this.operand instanceof Mul)) return super.computeKey();
    // Moving the last factor to the front also combines powers straddling the ends.
    const factors = this.operand.args;
    const rotated = mul(...factors.slice(-1), ...factors.slice(0, -1));
    const cycle = rotated instanceof Mul ? rotated.args : [rotated];
    const keys = cycle.map((_, i) => mul(...cycle.slice(i), ...cycle.slice(0, i)).key);
    return `Tr(${keys.sort()[0]},${this.indices.key})`;
  }
}

/** SymPy Tr distributes over sums, extracts commuting factors and evaluates explicit matrix traces. */
export function Tr(value: ExprLike | Matrix, indices: ExprLike | readonly ExprLike[] = []): Expr {
  if (value instanceof Matrix) return value.trace();
  if (value instanceof ImmutableMatrix) return value.matrix.trace();
  const expr = sympify(value);
  const labels = indices instanceof TupleNode ? indices : Tuple(...(Array.isArray(indices) ? indices : [indices]));
  if (expr instanceof Add) return add(...expr.args.map((term) => Tr(term, labels)));
  if (expr instanceof Mul) {
    const operators = expr.args.filter((a) => !a.isCommutative);
    if (!operators.length) return expr;
    return mul(...expr.args.filter((a) => a.isCommutative), new TraceNode(mul(...operators), labels));
  }
  if (isScalar(expr) || expr instanceof Pow && isScalar(expr.base) && isScalar(expr.exp)) return expr;
  return new TraceNode(expr, labels);
}

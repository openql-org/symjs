// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 physics/secondquant.py (BSD-3-Clause).

import type { Expr, ExprLike } from '@symjs/symjs';
import { Add, ExtensionExpr, Mul, S, add, expand, mul, neg, ordered, sub, sympify } from '@symjs/symjs';

class CommutatorNode extends ExtensionExpr {
  constructor(readonly left: Expr, readonly right: Expr) {
    super('Commutator', [left, right]);
  }

  protected override computeCommutative(): boolean { return false; }

  withArgs(args: readonly Expr[]): Expr {
    const [left, right] = args;
    if (left === undefined || right === undefined || args.length !== 2) throw new RangeError('Commutator requires two operands');
    return Commutator(left, right);
  }

  override doitSelf(): Expr {
    return sub(mul(this.left, this.right), mul(this.right, this.left));
  }

  override printLatex(print: (e: Expr) => string): string {
    return `\\left[${print(this.left)},${print(this.right)}\\right]`;
  }
}

/** The second-quantization commutator of two symbolic operands. */
export function Commutator(left: ExprLike, right: ExprLike): Expr {
  const a = sympify(left);
  const b = sympify(right);
  if (a.isCommutative || b.isCommutative || a.equals(b)) return S.Zero;
  const l = expand(a);
  if (l instanceof Add) return add(...l.args.map((term) => Commutator(term, b)));
  const r = expand(b);
  if (r instanceof Add) return add(...r.args.map((term) => Commutator(l, term)));
  const leftFactors = l instanceof Mul ? l.args : [l];
  const rightFactors = r instanceof Mul ? r.args : [r];
  const scalars = [...leftFactors, ...rightFactors].filter((factor) => factor.isCommutative);
  if (scalars.length) {
    const operators = (factors: readonly Expr[]) => mul(...factors.filter((factor) => !factor.isCommutative));
    return mul(...scalars, Commutator(operators(leftFactors), operators(rightFactors)));
  }
  if (ordered([l, r])[0] === r) return neg(new CommutatorNode(r, l));
  return new CommutatorNode(l, r);
}

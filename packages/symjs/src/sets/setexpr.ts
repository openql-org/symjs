// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 sets/setexpr.py, BSD-3-Clause; see LICENSE.

import { callableClass } from '../core/callable';
import { Tuple } from '../core/containers';
import { cast, first } from '../core/guard';
import { Dummy, ExtensionExpr, registerArithmetic } from '../core/nodes';
import type { Expr } from '../core/nodes';
import { add, mul, pow, sub } from '../core/ops';
import { EmptySet, FiniteSet, ImageSet, Interval, SetExpr, imageSet, interval, productSet, union } from './sets';

type Operation = 'add' | 'sub' | 'mul' | 'pow';
const operation = (op: Operation, a: Expr, b: Expr): Expr => ({ add, sub, mul, pow })[op](a, b);

function pointwise(op: Operation, a: SetExpr, b: SetExpr): SetExpr {
  if (a === EmptySet || b === EmptySet) return EmptySet;
  if (a.className === 'Union') return union(...a.args.map((s) => pointwise(op, cast(s, SetExpr), b)));
  if (b.className === 'Union') return union(...b.args.map((s) => pointwise(op, a, cast(s, SetExpr))));
  const x = new Dummy('x');
  if (a instanceof FiniteSet) return union(...a.args.map((v) => imageSet(x, operation(op, v, x), b)));
  if (b instanceof FiniteSet) return union(...b.args.map((v) => imageSet(x, operation(op, x, v), a)));
  if (a instanceof Interval && b instanceof Interval) {
    if (op === 'add') return interval(add(a.start, b.start), add(a.end, b.end), a.leftOpen || b.leftOpen, a.rightOpen || b.rightOpen);
    if (op === 'sub') return interval(sub(a.start, b.end), sub(a.end, b.start), a.leftOpen || b.rightOpen, a.rightOpen || b.leftOpen);
  }
  const y = new Dummy('y');
  return new ImageSet(Tuple(x, y), operation(op, x, y), productSet(a, b));
}

/** SymPy SetExpr: a scalar expression ranging over a set, with pointwise arithmetic. */
export class SetExpressionNode extends ExtensionExpr {
  constructor(readonly set: SetExpr) { super('SetExpr', [set]); }
  withArgs(args: readonly Expr[]): SetExpressionNode { return new SetExpressionNode(cast(first(args), SetExpr)); }
  /** Map a function over all possible values. */
  applyfunc(fn: (e: Expr) => Expr): SetExpressionNode {
    const x = new Dummy('x');
    return new SetExpressionNode(imageSet(x, fn(x), this.set));
  }
}
export const SetExpression = callableClass(SetExpressionNode, (set: SetExpr): SetExpressionNode => new SetExpressionNode(set));
export type SetExpression = SetExpressionNode;

registerArithmetic((op, args) => {
  if (!args.some((e) => e instanceof SetExpressionNode)) return undefined;
  const asSet = (e: Expr): SetExpr => e instanceof SetExpressionNode ? e.set : FiniteSet.of(e);
  const sets = args.map(asSet);
  return new SetExpressionNode(sets.slice(1).reduce((a, b) => pointwise(op, a, b), first(sets)));
});

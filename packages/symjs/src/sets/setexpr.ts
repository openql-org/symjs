// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14 sets/setexpr.py, BSD-3-Clause; see LICENSE.

import { callableClass } from '../core/callable';
import { Tuple } from '../core/containers';
import { cast, first, last } from '../core/guard';
import { Dummy, ExtensionExpr, S, registerArithmetic } from '../core/nodes';
import type { Expr } from '../core/nodes';
import { add, mul, pow, sub } from '../core/ops';
import { EmptySet, FiniteSet, ImageSet, Interval, SetExpr, Reals, imageSet, interval, productSet, union, cmpReal, realValue, containsQ } from './sets';

type Operation = 'add' | 'sub' | 'mul' | 'pow';
const operation = (op: Operation, a: Expr, b: Expr): Expr => ({ add, sub, mul, pow })[op](a, b);

/** Endpoint products, with zero treated by its continuous limiting value. */
function intervalProduct(a: Interval, b: Interval): SetExpr | undefined {
  const candidates = [
    [a.start, b.start, a.leftOpen || b.leftOpen],
    [a.start, b.end, a.leftOpen || b.rightOpen],
    [a.end, b.start, a.rightOpen || b.leftOpen],
    [a.end, b.end, a.rightOpen || b.rightOpen],
  ] as const;
  const values = candidates.map(([x, y, open]) => ({ value: x.key === S.Zero.key || y.key === S.Zero.key ? S.Zero : mul(x, y), open }));
  if (values.some((v) => realValue(v.value) === undefined)) return undefined;
  // oxlint-disable-next-line typescript/prefer-nullish-coalescing -- Equal endpoints must be ordered by attainment.
  values.sort((x, y) => cmpReal(x.value, y.value) || Number(x.open) - Number(y.open));
  const lo = first(values), hi = last(values);
  const attained = (e: Expr): boolean => values.some((v) => v.value.key === e.key && !v.open) || e.key === S.Zero.key && (containsQ(a, S.Zero) === true || containsQ(b, S.Zero) === true);
  return interval(lo.value, hi.value, !attained(lo.value), !attained(hi.value));
}

/** Integer powers use monotonic branches on either side of zero. */
function intervalPower(a: Interval, exponent: Expr): SetExpr | undefined {
  const lo = realValue(a.start), hi = realValue(a.end), n = realValue(exponent);
  if (lo === undefined || hi === undefined || n === undefined) return undefined;
  if (n === Infinity) {
    if (lo >= 0) return hi < 1 ? FiniteSet.of(0) : lo > 1 ? FiniteSet.of(S.Infinity) : interval(0, S.Infinity);
    if (hi < 0) return lo > -1 ? FiniteSet.of(0) : hi < -1 ? FiniteSet.of(S.NegativeInfinity, S.Infinity) : interval(S.NegativeInfinity, S.Infinity);
    return lo > -1 ? hi < 1 ? FiniteSet.of(0) : interval(0, S.Infinity) : interval(S.NegativeInfinity, S.Infinity);
  }
  if (n === -Infinity) {
    if (lo < 0) return undefined;
    return intervalPower(cast(interval(pow(a.end, -1), pow(a.start, -1), a.rightOpen, a.leftOpen), Interval), S.Infinity);
  }
  if (n === 0) return FiniteSet.of(1);
  if (!Number.isInteger(n) && lo < 0) return undefined;
  const x = pow(a.start, exponent), y = pow(a.end, exponent);
  if (lo > 0 || hi < 0 || !Number.isInteger(n) && n > 0) {
    return cmpReal(x, y) === 1 ? interval(y, x, a.rightOpen, a.leftOpen) : interval(x, y, a.leftOpen, a.rightOpen);
  }
  if (n < 0) {
    if (n % 2 !== 0) {
      if (lo === 0) return interval(y, S.Infinity, a.rightOpen, true);
      if (hi === 0) return interval(S.NegativeInfinity, x, true, a.leftOpen);
      return union(interval(S.NegativeInfinity, x, true, a.leftOpen), interval(y, S.Infinity, a.rightOpen, true));
    }
    if (lo === 0) return interval(y, S.Infinity, a.rightOpen, true);
    if (hi === 0) return interval(x, S.Infinity, a.leftOpen, true);
    const order = cmpReal(x, y);
    return interval(order === 1 ? y : x, S.Infinity, order === 1 ? a.rightOpen : order === -1 ? a.leftOpen : a.leftOpen && a.rightOpen, true);
  }
  if (n % 2 !== 0) return interval(x, y, a.leftOpen, a.rightOpen);
  const order = cmpReal(x, y);
  return interval(0, order === 1 ? x : y, containsQ(a, S.Zero) !== true, order === 1 ? a.leftOpen : order === -1 ? a.rightOpen : a.leftOpen && a.rightOpen);
}

function pointwise(op: Operation, a: SetExpr, b: SetExpr): SetExpr {
  if (a === EmptySet || b === EmptySet) return EmptySet;
  if (a.className === 'Union') return union(...a.args.map((s) => pointwise(op, cast(s, SetExpr), b)));
  if (b.className === 'Union') return union(...b.args.map((s) => pointwise(op, a, cast(s, SetExpr))));
  if (op === 'pow' && a instanceof Interval && b instanceof FiniteSet) {
    const images = b.args.map((e) => intervalPower(a, e));
    if (images.every((s): s is SetExpr => s !== undefined)) return union(...images);
  }
  const x = new Dummy('x');
  if (a instanceof FiniteSet) return union(...a.args.map((v) => imageSet(x, operation(op, v, x), b)));
  if (b instanceof FiniteSet) return union(...b.args.map((v) => imageSet(x, operation(op, x, v), a)));
  if (a instanceof Interval && b instanceof Interval) {
    if (op === 'mul') {
      const result = intervalProduct(a, b);
      if (result !== undefined) return result;
    }
    if (op === 'add') return interval(add(a.start, b.start), add(a.end, b.end), a.leftOpen || b.leftOpen, a.rightOpen || b.rightOpen);
    if (op === 'sub') return interval(sub(a.start, b.end), sub(a.end, b.start), a.leftOpen || b.rightOpen, a.rightOpen || b.leftOpen);
  }
  const y = new Dummy('y');
  return new ImageSet(Tuple(x, y), operation(op, x, y), productSet(a, b));
}

/** SymPy SetExpr: a scalar expression ranging over a set, with pointwise arithmetic. */
export class SetExpressionNode extends ExtensionExpr {
  constructor(readonly set: SetExpr) { super('SetExpr', [set]); }
  printStr(p: (e: Expr) => string): string {
    return `SetExpr(${p(this.set === Reals ? new Interval(S.NegativeInfinity, S.Infinity, true, true) : this.set)})`;
  }
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

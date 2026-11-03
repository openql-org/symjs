// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Functions of an AccumBounds interval (SymPy's _eval for
 * AccumulationBounds arguments): monotone functions map the end points,
 * sin and cos also reach their extrema inside the interval.
 */

import type { Expr, FnName } from '../core/nodes';
import { S, impl } from '../core/nodes';
import { defined } from '../core/guard';

const INCREASING = new Set(['exp', 'log', 'atan', 'asinh', 'sinh', 'tanh', 'erf', 'asin', 'acosh', 'atanh']);
const DECREASING = new Set(['acos', 'acot']);

/** f([a, b]) for a function of one AccumBounds argument; undefined when it is not handled. */
export function accumBoundsFunction(name: FnName, iv: Expr, apply: (name: FnName, x: Expr) => Expr): Expr | undefined {
  const ab = defined(impl.accumBounds, 'AccumBounds support');
  const [lo, hi] = ab.bounds(iv);
  if (INCREASING.has(name)) return ab.make(apply(name, lo), apply(name, hi));
  if (DECREASING.has(name)) return ab.make(apply(name, hi), apply(name, lo));
  if (name === 'sin' || name === 'cos') {
    const a = lo.toNumber();
    const b = hi.toNumber();
    if (!Number.isFinite(a) || !Number.isFinite(b) || b - a >= 2 * Math.PI) return ab.make(S.NegOne, S.One);
    // extrema of sin at pi/2 + k*pi (of cos at k*pi) inside the interval
    const shift = name === 'sin' ? Math.PI / 2 : 0;
    const vals: Expr[] = [apply(name, lo), apply(name, hi)];
    for (let k = Math.ceil((a - shift) / Math.PI); k * Math.PI + shift <= b; k++) vals.push(k % 2 === 0 ? S.One : S.NegOne);
    const num = (e: Expr) => e.toNumber();
    const min = vals.reduce((m, v) => (num(v) < num(m) ? v : m));
    const max = vals.reduce((m, v) => (num(v) > num(m) ? v : m));
    return ab.make(min, max);
  }
  // SymPy: sec = 1/cos, csc = 1/sin, cot(x) = -tan(x + pi/2) for an interval
  if (name === 'sec' || name === 'csc') return impl.pow(apply(name === 'sec' ? 'cos' : 'sin', iv), -1);
  if (name === 'cot') return impl.mul(-1, apply('tan', impl.add(iv, impl.mul(S.Pi, S.Half))));
  if (name === 'tan') {
    const a = lo.toNumber();
    const b = hi.toNumber();
    // continuous between consecutive poles pi/2 + k*pi
    const k = Math.floor((a + Math.PI / 2) / Math.PI);
    if (b < k * Math.PI + Math.PI / 2) return ab.make(apply(name, lo), apply(name, hi));
    return ab.make(S.NegativeInfinity, S.Infinity);
  }
  return undefined;
}

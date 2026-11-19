// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { expect, it } from 'vitest';
import { And, Eq, Ge, Gt, Le, Lt, MatrixSymbol, Max, Ne, Piecewise, S, add, mul, pow, simplify, symbol, symbols } from '../../../src';

it('clamps symbolic upper endpoints only after the lower half-line is covered', () => {
  const [x, y, z] = symbols('x y z', { real: true });
  const L = symbol('L', { nonnegative: true });
  const value = Piecewise([S.NaN, Le(x, 0)], [0, And(Gt(L, x), Le(add(L, mul(-1, x)), 0))],
    [1, And(Ge(x, 0), Gt(L, x))], [2, Gt(L, x)], [S.NaN, true]);
  expect(simplify(value).equals(Piecewise([S.NaN, Le(x, 0)], [1, Gt(L, x)], [S.NaN, true]))).toBe(true);
  expect(simplify(value.subs(L, y)).equals(Piecewise([S.NaN, Le(x, 0)], [1, Lt(x, Max(0, y))], [2, Lt(x, y)], [S.NaN, true]))).toBe(true);
  const matrix = MatrixSymbol('M', 2, 2);
  const nonScalar = Piecewise([1, Eq(matrix, 0)], [2, Lt(x, y)], [3, true]);
  expect(simplify(nonScalar).equals(nonScalar)).toBe(true);
  const closed = Piecewise([1, Le(x, 1)], [2, And(Gt(x, 0), Le(x, y))], [3, true]);
  expect(simplify(closed).equals(Piecewise([1, Le(x, 1)], [2, Le(x, Max(0, y))], [3, true]))).toBe(true);
  const bounded = Piecewise([0, Le(x, 0)], [1, And(Ge(x, 0), Lt(x, y), Le(x, z))], [2, true]);
  const clamped = And(Lt(x, Max(0, y)), Le(x, Max(0, z)));
  expect(simplify(bounded).equals(Piecewise([0, Le(x, 0)], [1, clamped], [2, true]))).toBe(true);
  for (const c of [And(Lt(x, y), Lt(x, z)), Eq(x, y), Ne(x, y), And(Lt(y, 4), Ge(x, 2)), And(Ge(x, 1), Lt(x, y)),
    And(Ge(x, 1), Lt(x, mul(y, pow(x, 2)))), And(Ge(x, 1), Lt(x, y), Gt(y, 3))]) {
    const p = Piecewise([1, Lt(x, 0)], [2, c], [3, true]);
    const point = [[x, 2], [y, 3]] as const;
    expect(simplify(p).subs(point).equals(p.subs(point))).toBe(true);
  }
});

it('integrates a bounded pulse in either direction from its first breakpoint', () => {
  const [t, start, stop, end, height] = symbols('t start stop end height');
  const pulse = Piecewise([0, Lt(t, start)], [height, And(Le(start, t), Lt(t, stop))], [0, Ge(t, stop)]);
  const area = pulse.integrate(t, [start, end]);
  for (const a of [0, 1, 2]) {
    for (const b of [0, 1, 2]) {
      for (const c of [0, 1, 2]) {
        const value = area.subs([[start, a], [stop, b], [end, c], [height, 3]]);
        expect(value.equals(3 * Math.max(0, Math.min(b, c) - a))).toBe(true);
      }
    }
  }
});

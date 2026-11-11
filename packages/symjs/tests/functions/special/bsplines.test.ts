// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { bsplineBasis, bsplineBasisSet, interpolatingSpline, symbol, Rational, S } from '../../../src';
const x = symbol('x');
it('Cox-de Boor bases, including repeated knots', () => {
  expect(String(bsplineBasis(0,[0,1,2,3,4],0,x))).toBe('Piecewise((1, (x >= 0) & (x <= 1)), (0, True))');
  const cubic = bsplineBasis(3,[0,1,2,3,4],0,x);
  expect(String(cubic)).toBe('Piecewise((x**3/6, (x >= 0) & (x <= 1)), (-x**3/2 + 2*x**2 - 2*x + 2/3, (x >= 1) & (x <= 2)), (x**3/2 - 4*x**2 + 10*x - 22/3, (x >= 2) & (x <= 3)), (-x**3/6 + 2*x**2 - 8*x + 32/3, (x >= 3) & (x <= 4)), (0, True))');
  expect(String(bsplineBasis(1,[0,0,2,3,4],0,x))).toBe('Piecewise((1 - x/2, (x >= 0) & (x <= 2)), (0, True))');
  expect(bsplineBasis(1,[0,0,0],0,x)).toBe(S.Zero);
  expect(bsplineBasisSet(1,[0,0,1,2,2],x)).toHaveLength(3);
  expect(cubic.subs(x,2).toString()).toBe('2/3');
  expect(() => bsplineBasis(-1,[0,1],0,x)).toThrow(RangeError);
  expect(() => bsplineBasis(0,[0,1],2,x)).toThrow(RangeError);
  expect(() => bsplineBasisSet(2,[0,1,2],x)).toThrow(RangeError);
  expect(() => bsplineBasis(2n**60n,[0,1],0,x)).toThrow(RangeError);
  expect(() => bsplineBasis(Rational.of(1,2),[0,1],0,x)).toThrow();
});
it('linear, quadratic and cubic interpolation and zero-valued intervals', () => {
  const linear = interpolatingSpline(1,x,[1,2,4,7],[3,6,5,7]);
  expect(String(linear)).toBe('Piecewise((3*x, (x >= 1) & (x <= 2)), (7 - x/2, (x >= 2) & (x <= 4)), (2*x/3 + 7/3, (x >= 4) & (x <= 7)))');
  const cubic = interpolatingSpline(3,x,[-2,0,1,3,4],[4,2,1,1,3]);
  expect(String(cubic)).toBe('Piecewise((7*x**3/117 + 7*x**2/117 - 131*x/117 + 2, (x >= -2) & (x <= 1)), (10*x**3/117 - 2*x**2/117 - 122*x/117 + 77/39, (x >= 1) & (x <= 4)))');
  const quadratic = interpolatingSpline(2,x,[0,1,2,3],[0,1,4,9]);
  for (const a of [0,1,2,3]) expect(quadratic.subs(x,a).toString()).toBe(String(a*a));
  expect(interpolatingSpline(1,x,[0,1,2],[0,0,1]).subs(x,Rational.of(1,2)).equals(S.Zero)).toBe(true);
  expect(() => interpolatingSpline(0,x,[0,1],[0,1])).toThrow(RangeError);
  expect(() => interpolatingSpline(2,x,[0,1],[0,1])).toThrow(RangeError);
  expect(() => interpolatingSpline(1,x,[0,1],[0])).toThrow(RangeError);
  expect(() => interpolatingSpline(1,x,[1,0],[0,1])).toThrow(RangeError);
});

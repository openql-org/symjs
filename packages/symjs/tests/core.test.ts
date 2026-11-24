// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import * as sj from '../src';

it('public constructors evaluate by default and preserve explicit unevaluated arithmetic', () => {
  const x = sj.Sym('x'), y = sj.Sym('y', { real: true });
  expect(sj.symbol('x').equals(x)).toBe(true);
  expect(sj.symbol('y', { real: true }).equals(y)).toBe(true);
  expect(sj.var('x y').map(String)).toEqual(['x', 'y']);
  expect(sj.var('x', { positive: true })[0]?.assumptions.positive).toBe(true);
  expect(sj.Add(1, 2).equals(3)).toBe(true);
  expect(sj.Add(1, 2, {}).equals(3)).toBe(true);
  expect(sj.Add(1, 2, { evaluate: false }).args.map(String)).toEqual(['1', '2']);
  expect(sj.Mul(2, 3).equals(6)).toBe(true);
  expect(sj.Mul(2, 3, { evaluate: false }).args.map(String)).toEqual(['2', '3']);
  expect(sj.Pow(2, 3).equals(8)).toBe(true);
  expect(sj.Pow(2, 3, { evaluate: false }).args.map(String)).toEqual(['2', '3']);
  expect(() => sj.Add({ evaluate: false }, 1)).toThrow(TypeError);
  expect(sj.func(sj.Add(x, y))).toBe(sj.Add);
  expect(sj.doit(sj.Derivative(sj.pow(x, 3), x)).equals(sj.mul(3, sj.pow(x, 2)))).toBe(true);
  expect(sj.doit(sj.Derivative(sj.pow(x, 3), [x, 2])).equals(sj.mul(6, x))).toBe(true);
  expect(sj.Dummy().equals(sj.Dummy())).toBe(false);
  expect(sj.Dummy('d', { positive: true }).assumptions.positive).toBe(true);
});

it('Derivative computes the derivative with a last argument { evaluate: true }', () => {
  const [x, y] = sj.symbols('x y');
  const f = sj.SymFunction('f');
  expect(String(sj.Derivative(sj.ex`x**2*y`, x, { evaluate: true }))).toBe('2*x*y');
  expect(String(sj.Derivative(sj.ex`x**3*y**2`, [x, 2], y, { evaluate: true }))).toBe('12*x*y');
  expect(String(sj.Derivative(f(x).pow(2), f(x), { evaluate: true }))).toBe('2*f(x)');
  expect(String(sj.Derivative(sj.ex`x**2`, x, { evaluate: false }))).toBe('Derivative(x**2, x)');
  // the options object must be the last argument
  expect(() => sj.Derivative(sj.ex`x**2`, { evaluate: true }, x)).toThrow(TypeError);
});

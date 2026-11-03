// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/solvers/homogeneous.ts: homogeneous_order; expected values from SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { homogeneousOrder, NoMatch, parse, symbols, SymFunction as Fn } from '../../src';

const [x, y] = symbols('x y');
const f = Fn('f');
const ho = (e: string, ...s: ReturnType<typeof parse>[]) => String(homogeneousOrder(parse(e), ...s));

// expected values from SymPy 1.14 (None is NoMatch)
describe('homogeneous_order', () => {
  it('orders', () => {
    expect(ho('x**2 + y**2', x, y)).toBe('2');
    expect(ho('x + y', x, y)).toBe('1');
    expect(ho('sqrt(x**2 + y**2)', x, y)).toBe('1');
    expect(ho('x*f(x, y)', parse('f(x, y)'), x, y)).toBe('2');
    expect(ho('sin(x/y)', x, y)).toBe('0');
    expect(ho('x*exp(x/y)', x, y)).toBe('1');
    expect(ho('x**a + y**a', x, y)).toBe('a');
    expect(ho('3', x)).toBe('0');
    expect(ho('x**(1/3) + y**(1/3)', x, y)).toBe('1/3');
    expect(ho('log(x/y)', x, y)).toBe('0');
    expect(ho('log(x/y) + 1', x, y)).toBe('0');
  });
  it('not homogeneous', () => {
    expect(homogeneousOrder(parse('Derivative(f(x), x)'), x)).toBe(NoMatch);
    expect(homogeneousOrder(parse('x*f(x, y)'), f(x), x)).toBe(NoMatch);
    expect(homogeneousOrder(parse('x*f(x, y)'), parse('f(x, y)'), x)).toBe(NoMatch);
    expect(homogeneousOrder(parse('x**2 + 1'), x)).toBe(NoMatch);
    expect(homogeneousOrder(parse('a*x'), y)).toBe(NoMatch);
    expect(homogeneousOrder(parse('sin(x)'), x)).toBe(NoMatch);
    expect(homogeneousOrder(parse('cos(x + y)'), x, y)).toBe(NoMatch);
  });
});

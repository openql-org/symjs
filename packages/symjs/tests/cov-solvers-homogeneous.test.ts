// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { describe, expect, it } from 'vitest';
import { NoMatch, SymFunction as Fn, homogeneousOrder, isDecreasing, isStrictlyDecreasing, isStrictlyIncreasing, oo, parse, symbols } from '../src';
import { interval } from '../src/sets/sets';

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

describe('monotonicity wrappers', () => {
  it('follow SymPy (None is unknown)', () => {
    const pos = interval(0, oo);
    const neg = interval(oo.neg(), 0);
    const unit = interval(0, 1);
    expect([parse('-x**3'), parse('x**2')].map((e) => isStrictlyIncreasing(e))).toEqual([false, false]);
    expect([isStrictlyIncreasing(parse('-x'), unit, x), isStrictlyIncreasing(parse('x**2'), neg)]).toEqual([false, false]);
    expect([parse('-x**3'), parse('x**2')].map((e) => isDecreasing(e))).toEqual([true, false]);
    expect([isDecreasing(parse('-x'), unit), isDecreasing(parse('x**2'), pos, x)]).toEqual([true, false]);
    expect([parse('x**3'), parse('x**2')].map((e) => isStrictlyDecreasing(e))).toEqual([false, false]);
    expect([isStrictlyDecreasing(parse('-x'), unit), isStrictlyDecreasing(parse('x**2'), pos, x)]).toEqual([true, false]);
  });
});

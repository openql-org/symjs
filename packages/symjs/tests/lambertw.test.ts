// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { describe, expect, it } from 'vitest';
import { E, LambertW, Rational, diff, evalf, float, parse, solve, symbols } from '../src';

const [x] = symbols('x');

describe('LambertW (SymPy)', () => {
  it('special values and derivative', () => {
    expect(String(LambertW(0))).toBe('0');
    expect(String(LambertW(E))).toBe('1');
    expect(String(LambertW(0, -1))).toBe('-oo');
    expect(String(diff(LambertW(x), x))).toBe('LambertW(x)/(x*(LambertW(x) + 1))');
  });
  it('numeric values on several branches', () => {
    expect(String(LambertW(float(1.2)))).toBe('0.635564016364870');
    expect(String(evalf(LambertW(float(1.2), -1)))).toBe('-1.34747534407696 - 4.41624341514535*I');
    expect(String(evalf(LambertW(1), 30))).toBe('0.567143290409783872999968662210');
    expect(String(evalf(LambertW(Rational.of(-1, 5), -1), 20))).toBe('-2.5426413577735264243');
  });
  it('solves equations of Lambert type', () => {
    expect(String(solve(parse('x + exp(x)'), x))).toBe('-LambertW(1)');
    expect(String(solve(parse('2*x + 3 - exp(-x)'), x))).toBe('-3/2 + LambertW(exp(3/2)/2)');
    expect(String(solve(parse('x + exp(x/2)/4'), x))).toBe('-2*LambertW(1/8)');
  });
});

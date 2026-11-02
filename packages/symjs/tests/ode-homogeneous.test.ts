// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/** dsolve hints 1st_homogeneous_coeff_best and linear_coefficients (SymPy 1.14 output). */

import { describe, expect, it } from 'vitest';
import * as sj from '../src';

const f = sj.Function('f');
const x = new sj.Sym('x');
const solve = (s: string, hint?: string) => {
  const r = sj.dsolve(sj.parse(s), f(x), hint ? { hint } : {});
  return Array.isArray(r) ? r.map(String) : String(r);
};

describe('homogeneous and linear coefficients', () => {
  it('1st_homogeneous_coeff_best', () => {
    expect(solve('Derivative(f(x), x) - (x + f(x))/(x - f(x))')).toBe('Eq(log(x), C1 - log(sqrt(1 + f(x)**2/x**2)) + atan(f(x)/x))');
    expect(solve('Derivative(f(x),x) - (2*x + f(x))/(x - 2*f(x))')).toBe('Eq(log(x), C1 - log(sqrt(1 + f(x)**2/x**2)) + atan(f(x)/x)/2)');
    expect(solve('Derivative(f(x), x) - (x + f(x))/(x - f(x))', '1st_homogeneous_coeff_best')).toBe('Eq(log(x), C1 - log(sqrt(1 + f(x)**2/x**2)) + atan(f(x)/x))');
  });
  it('linear_coefficients: shifted to the intersection of the two lines', () => {
    expect(solve('Derivative(f(x), x) - (x + f(x) - 1)/(x - f(x) + 3)')).toBe('Eq(log(x + 1), C1 - log(sqrt(1 + (f(x) - 2)**2/(x + 1)**2)) + atan((f(x) - 2)/(x + 1)))');
    expect(solve('Derivative(f(x), x) - (x + f(x) - 1)/(x - f(x) + 3)', 'linear_coefficients')).toBe('Eq(log(x + 1), C1 - log(sqrt(1 + (f(x) - 2)**2/(x + 1)**2)) + atan((f(x) - 2)/(x + 1)))');
  });
  it('does not apply to non-homogeneous or parallel lines', () => {
    expect(() => sj.dsolve(sj.parse('Derivative(f(x), x) - (x + f(x) - 1)/(x + f(x) + 3)'), f(x), { hint: 'linear_coefficients' })).toThrow();
    expect(() => sj.dsolve(sj.parse('Derivative(f(x), x) - (x**2 + f(x))/(x - f(x))'), f(x), { hint: '1st_homogeneous_coeff_best' })).toThrow();
  });
});

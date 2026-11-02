// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { describe, expect, it } from 'vitest';
import { Function as Fn, dsolve, integrate, parse, symbols } from '../src';

const [x] = symbols('x');
const f = Fn('f');
const show = (r: unknown) => (Array.isArray(r) ? `[${r.map(String).join(', ')}]` : String(r));
const solve = (s: string) => show(dsolve(parse(s), f(x)));

// expected values from SymPy 1.14 dsolve
describe('dsolve hints (SymPy solver_map order and odesimp)', () => {
  it('first order', () => {
    expect(solve('-x*f(x) + Derivative(f(x), x)')).toBe('Eq(f(x), C1*exp(x**2/2))');
    expect(solve('-f(x)**2 + Derivative(f(x), x)')).toBe('Eq(f(x), -1/(C1 + x))');
    expect(solve('-exp(x + f(x)) + Derivative(f(x), x)')).toBe('Eq(f(x), log(-1/(C1 + exp(x))))');
    expect(solve('-2*f(x) - exp(x) + Derivative(f(x), x)')).toBe('Eq(f(x), (C1*exp(x) - 1)*exp(x))');
    expect(solve('f(x)*cos(x) - sin(2*x)/2 + Derivative(f(x), x)')).toBe('Eq(f(x), C1*exp(-sin(x)) + sin(x) - 1)');
    expect(solve('-f(x)**2 + Derivative(f(x), x) + f(x)/x')).toBe('Eq(f(x), 1/(x*(C1 - log(x))))');
    expect(solve('f(x)**2 + Derivative(f(x), x) + 2/x**2')).toBe('Eq(f(x), (-sqrt(7)*tan(C1 + sqrt(7)*log(x)/2) + 1)/(2*x))');
  });
  it('factorable and higher order', () => {
    expect(solve('(-f(x) + Derivative(f(x), x))*(Derivative(f(x), x) - 1)')).toBe('[Eq(f(x), C1 + x), Eq(f(x), C1*exp(x))]');
    expect(solve('2*f(x) - 3*Derivative(f(x), x) + Derivative(f(x), x, x)')).toBe('Eq(f(x), (C1 + C2*exp(x))*exp(x))');
    expect(solve('-x*exp(x) + f(x) - 2*Derivative(f(x), x) + Derivative(f(x), x, x)')).toBe('Eq(f(x), (C1 + x*(C2 + x**2/6))*exp(x))');
    expect(solve('f(x) + Derivative(f(x), x, x) - 1/cos(x)')).toBe('Eq(f(x), (C1 + x)*sin(x) + (C2 + log(cos(x)))*cos(x))');
    expect(solve('x**2*Derivative(f(x), x, x) - x*Derivative(f(x), x) + f(x)')).toBe('Eq(f(x), x*(C1 + C2*log(x)))');
    expect(solve('Derivative(f(x), x)**2 + Derivative(f(x), x, x)')).toBe('Eq(f(x), C1 + log(C2 + x))');
    expect(solve('-Derivative(f(x), x, x) + Derivative(f(x), x, x, x)')).toBe('Eq(f(x), C1 + C2*x + C3*exp(x))');
  });
  it('integration by substitution', () => {
    expect(String(integrate(parse('x*cos(x**2)'), x))).toBe('sin(x**2)/2');
    expect(String(integrate(parse('exp(x)*cos(exp(x))'), x))).toBe('sin(exp(x))');
  });
});

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { describe, expect, it } from 'vitest';
import { NotImplementedError, SymFunction as Fn, dsolve, parse, symbols } from '../src';

const [t] = symbols('t');
const [f, g, h] = [Fn('f'), Fn('g'), Fn('h')];
const show = (r: unknown) => (Array.isArray(r) ? `[${r.map(String).join(', ')}]` : String(r));
const sys = (eqs: string[], fs = [f(t), g(t)]) => show(dsolve(eqs.map((e) => parse(e)), fs));

// expected values from SymPy 1.14 dsolve
describe('dsolve systems', () => {
  it('a Jordan block of size 3', () => {
    expect(sys(['Derivative(f(t), t) - f(t) - g(t)', 'Derivative(g(t), t) - g(t) - h(t)', 'Derivative(h(t), t) - h(t)'], [f(t), g(t), h(t)])).toBe(
      '[Eq(f(t), C1*exp(t) + C2*t*exp(t) + C3*t**2*exp(t)/2), Eq(g(t), C2*exp(t) + C3*t*exp(t)), Eq(h(t), C3*exp(t))]',
    );
  });
  it('complex coefficients keep the complex exponentials', () => {
    expect(sys(['Derivative(f(t), t) - I*f(t)', 'Derivative(g(t), t) - 2*I*g(t)'])).toBe('[Eq(f(t), C1*exp(I*t)), Eq(g(t), C2*exp(2*I*t))]');
    expect(sys(['Derivative(f(t), t) - I*f(t) - g(t)', 'Derivative(g(t), t) - I*g(t)'])).toBe('[Eq(f(t), C1*exp(I*t) + C2*t*exp(I*t)), Eq(g(t), C2*exp(I*t))]');
    expect(sys(['Derivative(f(t), t) + g(t)', 'Derivative(g(t), t) - f(t)'])).toBe('[Eq(f(t), -C1*sin(t) - C2*cos(t)), Eq(g(t), C1*cos(t) - C2*sin(t))]');
  });
  it('triangular nonlinear systems', () => {
    // a second-order equation first: its two constants keep their order
    expect(sys(['Derivative(f(t), t, 2)*f(t)', 'Derivative(g(t), t) - f(t)**2'])).toBe(
      '[Eq(f(t), C1 + C2*t), Eq(g(t), C1**2*t + C1*C2*t**2 + C2**2*t**3/3 + C3)]',
    );
    // SymPy returns both solution sets [[Eq(f(t), C1 - t), Eq(g(t), C1*t + C2 - t**2/2)],
    // [Eq(f(t), C1 + t), Eq(g(t), C1*t + C2 + t**2/2)]]; the system solver keeps the first
    // solution of the first equation
    expect(sys(['Derivative(f(t), t)**2 - 1', 'Derivative(g(t), t) - f(t)'])).toBe('[Eq(f(t), C1 + t), Eq(g(t), C1*t + C2 + t**2/2)]');
    // SymPy: NotImplementedError as well
    expect(() => sys(['Derivative(f(t), t) - g(t)**2', 'Derivative(g(t), t) - f(t)**2'])).toThrow(NotImplementedError);
  });
  it('the unknown functions are those with derivatives', () => {
    // only f has a derivative, so one function for two equations
    expect(() => dsolve([parse('Derivative(f(t), t) - g(t)'), parse('Derivative(f(t), t) + f(t)')])).toThrow(TypeError);
  });
});

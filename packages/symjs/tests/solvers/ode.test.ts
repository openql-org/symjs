// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/solvers/ode.ts: the dsolve entry point; expected values from SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Derivative, dsolve, NotImplementedError, parse, Subs, symbols, SymFunction as Fn } from '../../src';

const [x, y] = symbols('x y');
const f = Fn('f');
const g = Fn('g');
const show = (r: unknown) => (Array.isArray(r) ? `[${r.map(String).join(', ')}]` : String(r));

// expected values from SymPy 1.14 dsolve
describe('dsolve entry point', () => {
  it('initial conditions', () => {
    expect(show(dsolve(parse('Derivative(f(x), x) - f(x)'), f(x), { ics: [[f(0), 2]] }))).toBe('Eq(f(x), 2*exp(x))');
    const d1 = Subs(Derivative(f(x), x), x, 0);
    expect(show(dsolve(parse('Derivative(f(x), x, x) + f(x)'), f(x), { ics: [[f(0), 1], [d1, 0]] }))).toBe('Eq(f(x), cos(x))');
    const ics: [ReturnType<typeof parse>, number][] = [[f(0), 1], [Subs(Derivative(f(x), x), x, 1), 2], [Subs(Derivative(f(x), x, x), x, 0), 3]];
    expect(show(dsolve(parse('Derivative(f(x), x, 3) - Derivative(f(x), x, 2)'), f(x), { ics }))).toBe('Eq(f(x), x*(2 - 3*E) + 3*exp(x) - 2)');
    // Derivative(f(0), (x, 1)) is also read as f'(0)
    expect(show(dsolve(parse('Derivative(f(x), x, x) + f(x)'), f(x), { ics: [[f(0), 0], [Derivative(f(0), x), 1]] }))).toBe('Eq(f(x), sin(x))');
    // f(x).diff(x).subs(x, y) is Derivative(f(y), y)
    expect(show(dsolve(parse('Derivative(f(x), x) - f(x)'), f(x), { ics: [[Derivative(f(y), y), 1]] }))).toBe('Eq(f(x), exp(x)*exp(-y))');
    expect(show(dsolve(parse('(Derivative(f(x), x) - f(x))*(Derivative(f(x), x) - 1)'), f(x), { ics: [[f(0), 1]] }))).toBe('[Eq(f(x), x + 1), Eq(f(x), exp(x))]');
  });
  it('invalid initial conditions raise like SymPy (ValueError)', () => {
    const e = parse('Derivative(f(x), x)');
    expect(() => dsolve(e, f(x), { ics: [[f(0), 1], [f(1), 2]] })).toThrow(RangeError);
    for (const c of [x, g(0), f(x), parse('f(x, 0)')]) expect(() => dsolve(e, f(x), { ics: [[c, 1]] })).toThrow(RangeError);
    expect(() => dsolve(e, f(x), { ics: [[f(0), x]] })).toThrow(RangeError);
    for (const c of [Subs(Derivative(f(x), x), x, x), Subs(Derivative(g(x), x), x, 0), Subs(Derivative(f(x), x), y, 0), Subs(Derivative(parse('f(x)*x'), x), x, 0), Derivative(f(y), y, x), Subs(f(x), x, 0)]) {
      expect(() => dsolve(e, f(x), { ics: [[c, 1]] })).toThrow(RangeError);
    }
    expect(() => dsolve(e, f(x), { ics: [[Subs(Derivative(f(x), x), x, 0), x]] })).toThrow(RangeError);
  });
  it('systems and argument checks', () => {
    const sys = [parse('Derivative(f(x), x) - g(x)'), parse('Derivative(g(x), x) + f(x)')];
    const expected = '[Eq(f(x), C1*sin(x) + C2*cos(x)), Eq(g(x), C1*cos(x) - C2*sin(x))]';
    expect(show(dsolve(sys, [f(x), g(x)]))).toBe(expected);
    expect(show(dsolve(sys))).toBe(expected);
    // SymPy finds the function: dsolve(f(x).diff(x)) is Eq(f(x), C1)
    expect(show(dsolve(parse('Derivative(f(x), x)')))).toBe('Eq(f(x), C1)');
    expect(() => dsolve(parse('Derivative(f(x), x)'), [f(x)])).toThrow(TypeError);
    // SymPy: dsolve() and classify_ode() only work with functions of one variable
    expect(() => dsolve(parse('Derivative(f(x, y), x) - f(x, y)'), parse('f(x, y)'))).toThrow(TypeError);
    expect(() => dsolve(parse('Derivative(f(x), x)'), x)).toThrow(TypeError);
    expect(() => dsolve(parse('Derivative(f(2*x), x)'), f(parse('2*x')))).toThrow(TypeError);
    // no hint matches (SymPy: NotImplementedError)
    expect(() => dsolve(parse('Derivative(f(x), x, 3) + x*f(x)'), f(x))).toThrow(NotImplementedError);
  });
});

describe('dsolve without the unknown function (SymPy _preprocess)', () => {
  it('takes the function whose derivatives the equation contains', () => {
    // SymPy: dsolve(f(x).diff(x, 2)) is Eq(f(x), C1 + C2*x)
    expect(show(dsolve(parse('Derivative(f(x), (x, 2))')))).toBe('Eq(f(x), C1 + C2*x)');
    expect(() => dsolve(parse('Derivative(f(x), x) + Derivative(g(x), x)'))).toThrow('the unknown function f(x) is required');
    expect(() => dsolve(parse('f(x) - 1'))).toThrow('the unknown function f(x) is required');
  });
});

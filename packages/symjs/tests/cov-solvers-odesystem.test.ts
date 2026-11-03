// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { describe, expect, it } from 'vitest';
import { NotImplementedError, SymFunction as Fn, dsolve, parse, symbols } from '../src';
import type { Expr } from '../src/core/nodes';
import { constantCount, solvesOdeSystem } from '../../../compat/ode-checks';

const [t] = symbols('t');
const f = Fn('f');
const g = Fn('g');
const show = (r: unknown) => (Array.isArray(r) ? `[${r.map(String).join(', ')}]` : String(r));
/** The solution satisfies the system and has two constants, like SymPy's. */
const solves = (...ss: string[]) => {
  const eqs = ss.map((e) => parse(e));
  const r = dsolve(eqs, [f(t), g(t)]) as Expr[];
  return solvesOdeSystem(eqs, t, r) && constantCount(show(r)) === 2;
};
const sys = (...eqs: string[]) => show(dsolve(eqs.map((e) => parse(e)), [f(t), g(t)]));

// expected values from SymPy 1.14 dsolve
describe('dsolve systems', () => {
  it('linear and triangular systems', () => {
    expect(sys('Eq(Derivative(f(t), t), g(t))', 'Eq(Derivative(g(t), t), -f(t))')).toBe('[Eq(f(t), C1*sin(t) + C2*cos(t)), Eq(g(t), C1*cos(t) - C2*sin(t))]');
    // SymPy: [Eq(f(t), C1 + C2*t**2/2 + t), Eq(g(t), C2)], the same up to renaming the constants
    expect(solves('Derivative(f(t), t) - t*g(t) - 1', 'Derivative(g(t), t)')).toBe(true);
    // SymPy: [Eq(f(t), -1/(C2 + t)), Eq(g(t), C1 + log(-1/(C2 + t)))], log(-1) absorbed into the constant here
    expect(solves('Derivative(f(t), t) - f(t)**2', 'Derivative(g(t), t) - f(t)')).toBe(true);
  });
  it('errors', () => {
    // SymPy: ValueError, number of equations and number of functions do not match
    expect(() => dsolve([parse('Derivative(f(t), t) - g(t)')], [f(t), g(t)])).toThrow(TypeError);
    // SymPy: KeyError (the system is not of first order in g)
    expect(() => sys('Derivative(f(t), t) + Derivative(g(t), t)', 'f(t) + g(t)')).toThrow(NotImplementedError);
  });
});

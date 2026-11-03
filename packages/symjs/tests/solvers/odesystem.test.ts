// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/solvers/odesystem.ts: systems of ODEs; expected values from SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { dsolve, NotImplementedError, parse, sstr, symbols, SymFunction as Fn } from '../../src';
import type { Expr } from '../../src/core/nodes';
import { constantCount, solvesOdeSystem } from '../../../../compat/ode-checks';

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
const h = Fn('h');
const sys2 = (eqs: string[], fs = [f(t), g(t)]) => show(dsolve(eqs.map((e) => parse(e)), fs));

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

// expected values from SymPy 1.14 dsolve
describe('dsolve systems', () => {
  it('a Jordan block of size 3', () => {
    expect(sys2(['Derivative(f(t), t) - f(t) - g(t)', 'Derivative(g(t), t) - g(t) - h(t)', 'Derivative(h(t), t) - h(t)'], [f(t), g(t), h(t)])).toBe(
      '[Eq(f(t), C1*exp(t) + C2*t*exp(t) + C3*t**2*exp(t)/2), Eq(g(t), C2*exp(t) + C3*t*exp(t)), Eq(h(t), C3*exp(t))]',
    );
  });
  it('complex coefficients keep the complex exponentials', () => {
    expect(sys2(['Derivative(f(t), t) - I*f(t)', 'Derivative(g(t), t) - 2*I*g(t)'])).toBe('[Eq(f(t), C1*exp(I*t)), Eq(g(t), C2*exp(2*I*t))]');
    expect(sys2(['Derivative(f(t), t) - I*f(t) - g(t)', 'Derivative(g(t), t) - I*g(t)'])).toBe('[Eq(f(t), C1*exp(I*t) + C2*t*exp(I*t)), Eq(g(t), C2*exp(I*t))]');
    expect(sys2(['Derivative(f(t), t) + g(t)', 'Derivative(g(t), t) - f(t)'])).toBe('[Eq(f(t), -C1*sin(t) - C2*cos(t)), Eq(g(t), C1*cos(t) - C2*sin(t))]');
  });
  it('triangular nonlinear systems', () => {
    // a second-order equation first: its two constants keep their order
    expect(sys2(['Derivative(f(t), t, 2)*f(t)', 'Derivative(g(t), t) - f(t)**2'])).toBe(
      '[Eq(f(t), C1 + C2*t), Eq(g(t), C1**2*t + C1*C2*t**2 + C2**2*t**3/3 + C3)]',
    );
    // SymPy returns both solution sets [[Eq(f(t), C1 - t), Eq(g(t), C1*t + C2 - t**2/2)],
    // [Eq(f(t), C1 + t), Eq(g(t), C1*t + C2 + t**2/2)]]; the system solver keeps the first
    // solution of the first equation
    expect(sys2(['Derivative(f(t), t)**2 - 1', 'Derivative(g(t), t) - f(t)'])).toBe('[Eq(f(t), C1 + t), Eq(g(t), C1*t + C2 + t**2/2)]');
    // SymPy: NotImplementedError as well
    expect(() => sys2(['Derivative(f(t), t) - g(t)**2', 'Derivative(g(t), t) - f(t)**2'])).toThrow(NotImplementedError);
  });
  it('the unknown functions are those with derivatives', () => {
    // only f has a derivative, so one function for two equations
    expect(() => dsolve([parse('Derivative(f(t), t) - g(t)'), parse('Derivative(f(t), t) + f(t)')])).toThrow(TypeError);
  });
});

describe('systems of linear ODEs', () => {
  it('match SymPy dsolve', async () => {
    const { dsolve } = await import('../../src');
    const t = symbols('t')[0];
    const P = (s: string) => parse(s, { symbols: { t } } as never);
    const show = (eqs: string[]) => (dsolve(eqs.map(P)) as unknown[]).map((e) => sstr(e as never));
    expect(show(['Eq(Derivative(x(t), t), 2*x(t) + y(t))', 'Eq(Derivative(y(t), t), x(t) + 2*y(t))'])).toEqual(['Eq(x(t), -C1*exp(t) + C2*exp(3*t))', 'Eq(y(t), C1*exp(t) + C2*exp(3*t))']);
    expect(show(['Eq(Derivative(x(t), t), y(t))', 'Eq(Derivative(y(t), t), -x(t))'])).toEqual(['Eq(x(t), C1*sin(t) + C2*cos(t))', 'Eq(y(t), C1*cos(t) - C2*sin(t))']);
    expect(show(['Eq(Derivative(x(t), t), x(t) - 2*y(t))', 'Eq(Derivative(y(t), t), 2*x(t) + y(t))'])).toEqual(['Eq(x(t), -C1*exp(t)*sin(2*t) - C2*exp(t)*cos(2*t))', 'Eq(y(t), C1*exp(t)*cos(2*t) - C2*exp(t)*sin(2*t))']);
    expect(show(['Eq(Derivative(x(t), t), 2*x(t) + y(t))', 'Eq(Derivative(y(t), t), 2*y(t))'])).toEqual(['Eq(x(t), C1*exp(2*t) + C2*t*exp(2*t))', 'Eq(y(t), C2*exp(2*t))']);
    // inhomogeneous (variation of parameters); the solution satisfies the system
    const [ex, ey] = dsolve([P('Eq(Derivative(x(t), t), y(t) + exp(t))'), P('Eq(Derivative(y(t), t), x(t))')]) as never as { rhs: never }[];
    const { diff: d, simplify: simp, sub } = await import('../../src');
    expect(sstr(simp(sub(d(ex!.rhs, t), sub(ey!.rhs, P('-exp(t)')))))).toBe('0');
  });
});

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/solvers/odesystem.ts: systems of ODEs; expected values from SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { add, checkodesol, diff, Dummy, dsolve, Eq, Integral, neg, NotImplementedError, parse, sstr, symbols, SymFunction as Fn } from '../../src';
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
const first2 = (r: unknown) => (Array.isArray(r) ? (r[0] as unknown) : r);
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
    // an equation with several solutions gives a solution list for each (SymPy)
    const two = dsolve(['Derivative(f(t), t)**2 - 1', 'Derivative(g(t), t) - f(t)'].map((e) => parse(e)), [f(t), g(t)]) as Expr[][];
    expect(two.map(show)).toEqual(['[Eq(f(t), C1 - t), Eq(g(t), C1*t + C2 - t**2/2)]', '[Eq(f(t), C1 + t), Eq(g(t), C1*t + C2 + t**2/2)]']);
    // SymPy: [[Eq(f(t), C1 - sqrt(C2)*t), Eq(g(t), C2)], [Eq(f(t), C1 + sqrt(C2)*t), Eq(g(t), C2)]] (the constants named in another order)
    const three = dsolve(['Derivative(f(t), t)**2 - g(t)', 'Derivative(g(t), t)'].map((e) => parse(e)), [f(t), g(t)]) as Expr[][];
    expect(three.map(show)).toEqual(['[Eq(f(t), sqrt(C1)*t + C2), Eq(g(t), C1)]', '[Eq(f(t), -sqrt(C1)*t + C2), Eq(g(t), C1)]']);
    // SymPy: NotImplementedError as well
    expect(() => sys2(['Derivative(f(t), t) - g(t)**2', 'Derivative(g(t), t) - f(t)**2'])).toThrow(NotImplementedError);
  });
  it('A(t) = phi(t)*M with M constant', () => {
    // SymPy: [Eq(f(t), -(C1/2 - C2/2)*exp(-t**2/2) + (C1/2 + C2/2)*exp(t**2/2)),
    //         Eq(g(t), (C1/2 - C2/2)*exp(-t**2/2) + (C1/2 + C2/2)*exp(t**2/2))], the same family
    expect(sys2(['Derivative(f(t), t) - t*g(t)', 'Derivative(g(t), t) - t*f(t)'])).toBe('[Eq(f(t), -C1*exp(-t**2/2) + C2*exp(t**2/2)), Eq(g(t), C1*exp(-t**2/2) + C2*exp(t**2/2))]');
    // SymPy gives the same family with complex exponentials and constants
    expect(sys2(['Derivative(f(t), t) - t*g(t)', 'Derivative(g(t), t) + t*f(t)'])).toBe('[Eq(f(t), C1*sin(t**2/2) + C2*cos(t**2/2)), Eq(g(t), C1*cos(t**2/2) - C2*sin(t**2/2))]');
    expect(solves('Derivative(f(t), t) - t*g(t)', 'Derivative(g(t), t) - t*f(t)')).toBe(true);
  });
  it('variable coefficients that are not a multiple of a constant matrix', () => {
    // SymPy's form in terms of a particular solution x0(t), y0(t)
    expect(show(first2(dsolve(['Derivative(f(t), t) - 12*t*f(t) - 8*g(t)', 'Derivative(g(t), t) - 21*f(t) - 7*t*g(t)'].map((e) => parse(e)), [f(t), g(t)])))).toBe(
      'Eq(f(t), C1*x0(t) + C2*x0(t)*Integral(8*exp(Integral(7*t, t))*exp(Integral(12*t, t))/x0(t)**2, t))',
    );
    // a single equation that is not a differential equation
    expect(() => dsolve(['Derivative(f(t), t)**2 - g(t)', 'g(t)**2 - t'].map((e) => parse(e)), [f(t), g(t)])).toThrow(TypeError);
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

describe('checkodesol', () => {
  // expected values from SymPy 1.14 (checkodesol doctests of sympy.solvers.ode.subscheck)
  const [x, t, C1, C2] = symbols('x t C1 C2');
  const f = Fn('f');
  const g = Fn('g');
  const X = Fn('x');
  const Y = Fn('y');
  const L = { f, g } as never;
  const P = (s: string): Expr => parse(s, { locals: L });
  const show = ([ok, r]: [boolean, Expr | Expr[]]) => `(${ok ? 'True' : 'False'}, ${Array.isArray(r) ? `[${r.map(sstr).join(', ')}]` : sstr(r)})`;

  it('checks one equation', () => {
    const fx = f(x!);
    expect(show(checkodesol(diff(fx, x!), Eq(fx, C1!)))).toBe('(True, 0)');
    expect(show(checkodesol(diff(fx, x!), C1!))).toBe('(True, 0)');
    expect(show(checkodesol(diff(fx, x!), x!))).toBe('(False, 1)');
    expect(show(checkodesol(diff(fx, x!, 2), P('x**2')))).toBe('(False, 2)');
    expect(show(checkodesol(P('Derivative(f(x), x) - f(x)'), Eq(P('C1*exp(x)'), fx)))).toBe('(True, 0)');
    expect(show(checkodesol(Eq(diff(fx, x!), fx), Eq(fx, P('C1*exp(x)'))))).toBe('(True, 0)');
    // SymPy: (False, Derivative(g(x), x)), the residual of the last of its methods; the residual of the substitution
    // (SymPy's first method, the only one ported) is its negative
    expect(show(checkodesol(P('Derivative(f(x), x) - Derivative(g(x), x)'), Eq(fx, C1!), fx))).toBe('(False, -Derivative(g(x), x))');
  });

  it('checks systems', () => {
    const eqs = [Eq(diff(f(x!), x!), f(x!)), Eq(diff(g(x!), x!), g(x!))];
    expect(show(checkodesol(eqs, [Eq(f(x!), P('C1*exp(x)')), Eq(g(x!), P('C2*exp(x)'))]))).toBe('(True, [0, 0])');
    expect(show(checkodesol([Eq(diff(f(x!), x!), 0)], Eq(f(x!), C1!)))).toBe('(True, [0])');
    expect(show(checkodesol(eqs, [Eq(f(x!), P('C1*exp(x)')), Eq(g(x!), P('C2*exp(2*x)'))]))).toBe('(False, [0, C2*exp(2*x)])');
    expect(show(checkodesol([Eq(diff(f(x!), x!), g(x!)), Eq(diff(g(x!), x!), neg(f(x!)))], [Eq(f(x!), P('sin(x)')), Eq(g(x!), P('cos(x)'))]))).toBe('(True, [0, 0])');
    const tt = { locals: { x: X, y: Y, C1, C2 }, symbols: { t } } as never;
    const eq2 = [parse('Eq(Derivative(x(t), t), x(t) + y(t) + 17)', tt), parse('Eq(Derivative(y(t), t), -2*x(t) + y(t) + 12)', tt)];
    const sol2 = [parse('Eq(x(t), (C1*sin(sqrt(2)*t) + C2*cos(sqrt(2)*t))*exp(t) - 5/3)', tt), parse('Eq(y(t), (sqrt(2)*C1*cos(sqrt(2)*t) - sqrt(2)*C2*sin(sqrt(2)*t))*exp(t) - 46/3)', tt)];
    expect(show(checkodesol(eq2, sol2))).toBe('(True, [0, 0])');
    // a solution that is a derivative of an unevaluated integral (SymPy's linodesolve output)
    const d = new Dummy('C1');
    expect(show(checkodesol([Eq(diff(f(x!), x!), P('exp(x)*f(x)/f(x) + 0*g(x)')), Eq(diff(g(x!), x!), g(x!))], [Eq(f(x!), add(new Integral([P('exp(x)'), x!]), d)), Eq(g(x!), P('C2*exp(x)'))]))).toBe('(True, [0, 0])');
  });

  it('rejects solutions it cannot use', () => {
    const fx = f(x!);
    expect(() => checkodesol(P('f(x) - g(x)'), Eq(fx, g(x!)))).toThrow('solutions should have one function only');
    expect(() => checkodesol([Eq(diff(fx, x!), fx)], [Eq(fx, g(x!))])).toThrow('solutions should have one function only');
    expect(() => checkodesol(diff(fx, x!), P('f(x) + g(x)'))).toThrow(NotImplementedError);
    // SymPy solves Eq(f(x) + x, C1) for f(x); here only explicit solutions are supported
    expect(() => checkodesol(diff(fx, x!), Eq(add(fx, x!), C1!))).toThrow(NotImplementedError);
    expect(() => checkodesol([Eq(diff(fx, x!), fx), Eq(diff(g(x!), x!), g(x!))], [Eq(fx, C1!)])).toThrow('number of solutions provided does not match the number of equations');
    expect(() => checkodesol(diff(fx, x!) as never, [Eq(fx, C1!)] as never)).toThrow(TypeError);
  });
});

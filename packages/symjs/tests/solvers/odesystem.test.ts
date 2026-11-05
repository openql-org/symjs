// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/solvers/odesystem.ts: systems of ODEs; expected values from SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { add, checkodesol, diff, Dummy, dsolve, Eq, Integral, neg, NotImplementedError, parse, sstr, symbols, SymFunction as Fn, cancel, Rel, UndefFn, xreplace, sub, Rational } from '../../src';
import type { Expr } from '../../src/core/nodes';
import { constantCount, solvesOdeSystem } from '../../../../compat/ode-checks';
import { at, cast } from '../../src/core/guard';

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

/** Normalize the public union after checking every returned relation. */
function systemFamilies(result: ReturnType<typeof dsolve>): Rel[][] {
  if (!Array.isArray(result)) throw new TypeError('expected system solution relations');
  if (result.some(Array.isArray)) return result.map((family) => {
    if (!Array.isArray(family)) throw new TypeError('expected a complete solution family');
    return family.map((relation) => cast(relation, Rel));
  });
  return [result.map((relation) => cast(relation, Rel))];
}

/** Differentiate every returned relation, then substitute the original vector field and algebraic relations. */
function checkRelations(families: Expr[][], functions: Expr[], velocities: Expr[]): void {
  expect(families.length).toBeGreaterThan(0);
  for (const family of families) {
    expect(family).toHaveLength(functions.length);
    const equations = family.map((e) => cast(e, Rel));
    const explicit = equations.filter((r) => r.lhs instanceof UndefFn).map((r): [Expr, Expr] => [r.lhs, r.rhs]);
    for (const relation of equations) {
      const derivative = diff(sub(relation.lhs, relation.rhs), t);
      const r = cancel(xreplace(xreplace(derivative, functions.map((f, i): [Expr, Expr] => [diff(f, t), at(velocities, i)])), explicit));
      for (const point of [0.23, 0.67, 1.13]) {
        const hundredths = Math.round(point * 100);
        const values: [Expr, Expr][] = [...r.freeSymbols()].map((s, i) => [s, Rational.of(s.key === t.key ? hundredths : 100 * (3 + i) + hundredths, 100)]);
        values.push(...functions.map((f, i): [Expr, Expr] => [f, Rational.of(hundredths + 20 * i, 100)]));
        const value = xreplace(r, values).evalf(40).toComplex();
        expect(Math.hypot(value.re, value.im)).toBeLessThan(1e-10);
      }
    }
  }
}

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
    // This autonomous system has an algebraic orbit and a valid time quadrature.
    const eqs = ['Derivative(f(t), t) - g(t)**2', 'Derivative(g(t), t) - f(t)**2'].map((e) => parse(e));
    checkRelations(systemFamilies(dsolve(eqs, [f(t), g(t)])), [f(t), g(t)], ['g(t)**2', 'f(t)**2'].map((e) => parse(e)));
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
  const show = ([ok, r]: [boolean, Expr | Expr[]]) => `(${ok ? 'True' : 'False'}, ${Array.isArray(r) ? `[${r.map((e) => sstr(e)).join(', ')}]` : sstr(r)})`;

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

// SymPy test_systems.py test_nonlinear_2eq_order1 (SymPy's flat list of the solution pairs)
describe('nonlinear systems of two first-order equations', () => {
  const X = Fn('x');
  const Y = Fn('y');
  const nl = (a: string, b: string) => show(dsolve([parse(a), parse(b)], [X(t), Y(t)]));
  const q = '(-1/(4*C2 + 4*t))';
  it('type 1: x\' = x**n*f, y\' = g*f', () => {
    expect(nl('Derivative(x(t), t) - x(t)*y(t)**3', 'Derivative(y(t), t) - y(t)**5')).toBe(
      `[Eq(x(t), C1*exp(${q}**(-1/4))), Eq(y(t), -${q}**(1/4)), Eq(x(t), C1*exp(-1/${q}**(1/4))), Eq(y(t), ${q}**(1/4)), Eq(x(t), C1*exp(-I/${q}**(1/4))), Eq(y(t), -I*${q}**(1/4)), Eq(x(t), C1*exp(I/${q}**(1/4))), Eq(y(t), I*${q}**(1/4))]`,
    );
    expect(nl('Derivative(x(t), t) - x(t)**2*y(t)**3', 'Derivative(y(t), t) - y(t)**5')).toBe(
      `[Eq(x(t), 1/(C1 - 1/${q}**(1/4))), Eq(y(t), -${q}**(1/4)), Eq(x(t), 1/(C1 + ${q}**(-1/4))), Eq(y(t), ${q}**(1/4)), Eq(x(t), 1/(C1 + I/${q}**(1/4))), Eq(y(t), -I*${q}**(1/4)), Eq(x(t), 1/(C1 - I/${q}**(1/4))), Eq(y(t), I*${q}**(1/4))]`,
    );
  });
  it('type 2: x\' = exp(n*x)*f, y\' = g*f', () => {
    expect(nl('Derivative(x(t), t) - exp(3*x(t))*y(t)**3', 'Derivative(y(t), t) - y(t)**5')).toBe(
      `[Eq(x(t), -log(C1 - 3/${q}**(1/4))/3), Eq(y(t), -${q}**(1/4)), Eq(x(t), -log(C1 + 3/${q}**(1/4))/3), Eq(y(t), ${q}**(1/4)), Eq(x(t), -log(C1 + 3*I/${q}**(1/4))/3), Eq(y(t), -I*${q}**(1/4)), Eq(x(t), -log(C1 - 3*I/${q}**(1/4))/3), Eq(y(t), I*${q}**(1/4))]`,
    );
  });
  it('type 4: separable f/g', () => {
    // SymPy: {Eq(x(t), -2*exp(C1)/(C2*exp(C1) + t - sin(2*t)/2)), Eq(y(t), -2/(C1 + t - sin(2*t)/2))}, which does
    // not satisfy the system (x/y must be constant): x comes from the first integral x = exp(C1)*y here
    expect(nl('Derivative(x(t), t) - x(t)*y(t)*sin(t)**2', 'Derivative(y(t), t) - y(t)**2*sin(t)**2')).toBe(
      '[Eq(x(t), exp(C1)/(C2 - t/2 + sin(t)*cos(t)/2)), Eq(y(t), 1/(C2 - t/2 + sin(t)*cos(t)/2))]',
    );
    const eqs = ['Derivative(x(t), t) - x(t)*y(t)*sin(t)**2', 'Derivative(y(t), t) - y(t)**2*sin(t)**2'].map((e) => parse(e));
    expect(solvesOdeSystem(eqs, t, dsolve(eqs, [X(t), Y(t)]) as Expr[])).toBe(true);
  });
  it('type 5: Clairaut systems', () => {
    // SymPy: {Eq(x(t), C1*C2 + C1*t), Eq(y(t), C2**2 + C2*t)}
    expect(nl('x(t) - t*Derivative(x(t), t) - Derivative(x(t), t)*Derivative(y(t), t)', 'y(t) - t*Derivative(y(t), t) - Derivative(y(t), t)**2')).toBe(
      '[Eq(x(t), C1*C2 + C1*t), Eq(y(t), C2**2 + C2*t)]',
    );
    // the other sign (SymPy does not finish on this system, whose functions it orders otherwise)
    expect(nl('-x(t) + t*Derivative(x(t), t) + Derivative(y(t), t)**2', '-y(t) + t*Derivative(y(t), t) + Derivative(x(t), t)**2')).toBe(
      '[Eq(x(t), C1*t + C2**2), Eq(y(t), C1**2 + C2*t)]',
    );
  });
  it('other systems', () => {
    // SymPy: NotImplementedError; x' + y' is not of the form x' = f(x, y, t)
    expect(nl('Derivative(x(t), t) + Derivative(y(t), t) - y(t)**2', 'Derivative(y(t), t) - y(t)**2')).toBe('[Eq(x(t), C2), Eq(y(t), -1/(C1 + t))]');
    // SymPy returns three quadratures. One quadrature plus two shared algebraic invariants
    // keeps the phase constants consistent and represents all four square-root branches.
    const Z = Fn('z');
    for (const timeFactor of ['1', 'sin(t)']) {
      const velocities = [`-y(t)*z(t)*${timeFactor}/2`, `x(t)*z(t)*${timeFactor}/3`, `x(t)*y(t)*${timeFactor}/5`].map((e) => parse(e));
      const fs = [X(t), Y(t), Z(t)];
      const solutions = systemFamilies(dsolve(fs.map((f, i) => sub(diff(f, t), at(velocities, i))), fs));
      expect(solutions).toHaveLength(4);
      expect(constantCount(String(solutions))).toBe(3);
      checkRelations(solutions, fs, velocities);
    }
  });
  it('type 3: an autonomous power system, including its zero-invariant family', () => {
    const eqs = ['Derivative(x(t), t) - y(t)*x(t)', 'Derivative(y(t), t) - x(t)**3'].map((e) => parse(e));
    const families = systemFamilies(dsolve(eqs, [X(t), Y(t)]));
    expect(families).toHaveLength(2);
    expect(constantCount(String(families[0]))).toBe(2);
    expect(constantCount(String(families[1]))).toBe(1);
    checkRelations(families, [X(t), Y(t)], ['y(t)*x(t)', 'x(t)**3'].map((e) => parse(e)));
  });
  it('uses an orbit quadrature for a noninteger power without assuming a power identity', () => {
    const fs = [X(t), Y(t)];
    const rhs = ['x(t)*y(t)', 'sqrt(x(t))'].map((e) => parse(e));
    const families = systemFamilies(dsolve(fs.map((f, i) => sub(diff(f, t), at(rhs, i))), fs));
    checkRelations(families, fs, rhs);
  });
  it('keeps input parameters distinct from new integration constants', () => {
    const two = [X(t), Y(t)];
    const velocities = ['C1*x(t)*y(t)', 'x(t)**3'].map((e) => parse(e));
    const result = systemFamilies(dsolve(two.map((f, i) => sub(diff(f, t), at(velocities, i))), two));
    expect([...at(result, 0).flatMap((r) => [...r.freeSymbols()])].map(String)).toContain('C1');
    expect(constantCount(String(at(result, 0)))).toBe(3); // one parameter and two integration constants
    checkRelations(result, two, velocities);
    const three = [...two, Fn('z')(t)];
    const rhs = ['C1*y(t)*z(t)', '2*x(t)*z(t)', '3*x(t)*y(t)'].map((e) => parse(e));
    const families = systemFamilies(dsolve(three.map((f, i) => sub(diff(f, t), at(rhs, i))), three));
    expect(constantCount(String(at(families, 0)))).toBe(4);
    checkRelations(families, three, rhs);
  });
  it('uses the second orbit coordinate when its time equation is invertible', () => {
    const fs = [X(t), Y(t)];
    const rhs = ['y(t)*(x(t)+y(t))', 'y(t)'].map((e) => parse(e));
    const result = systemFamilies(dsolve(fs.map((f, i) => sub(diff(f, t), at(rhs, i))), fs));
    // Integrating dx/dy=x+y gives x=C1*exp(y)-y-1 and y=C2*exp(t).
    expect(constantCount(String(result))).toBe(2);
    checkRelations(result, fs, rhs);
  });
  it('keeps the time quadrature when the orbit cannot be inverted in the first coordinate', () => {
    const fs = [X(t), Y(t)];
    const rhs = ['x(t)+y(t)', '(x(t)+y(t))*(y(t)+log(y(t)))'].map((e) => parse(e));
    const result = systemFamilies(dsolve(fs.map((f, i) => sub(diff(f, t), at(rhs, i))), fs));
    expect(constantCount(String(result))).toBe(2);
    checkRelations(result, fs, rhs);
  });
  it.each([
    ['Derivative(x(t),t)**2-y(t)*z(t)', 'Derivative(y(t),t)-x(t)*z(t)', 'Derivative(z(t),t)-x(t)*y(t)'],
    ['Derivative(x(t),t)+Derivative(y(t),t)-y(t)*z(t)', '2*Derivative(x(t),t)+2*Derivative(y(t),t)-x(t)*z(t)', 'Derivative(z(t),t)-x(t)*y(t)'],
    ['Derivative(x(t),t)-y(t)**2-z(t)', 'Derivative(y(t),t)-x(t)*z(t)', 'Derivative(z(t),t)-x(t)*y(t)'],
    ['Derivative(x(t),t)-y(t)*z(t)', 'Derivative(y(t),t)-t*x(t)*z(t)', 'Derivative(z(t),t)-x(t)*y(t)'],
  ])('does not apply the Euler formula to an unsupported system: %s', (...equations) => {
    // These systems do not meet the Euler reduction's hypotheses. An unsupported
    // valid system raises NotImplementedError, never a malformed solution.
    expect(() => dsolve(equations.map((e) => parse(e)), [X(t), Y(t), Fn('z')(t)])).toThrow(NotImplementedError);
  });
  it('reports an unsupported coupled nonlinear system of four functions', () => {
    const fs = [X(t), Y(t), Fn('z')(t), Fn('w')(t)];
    const rhs = ['y(t)*z(t)', 'z(t)*w(t)', 'w(t)*x(t)', 'x(t)*y(t)'].map((e) => parse(e));
    expect(() => dsolve(fs.map((f, i) => sub(diff(f, t), at(rhs, i))), fs)).toThrow(NotImplementedError);
  });
});


describe('sub_func_doit and checksysodesol (SymPy 1.14)', () => {
  it('substitutes a function and its derivatives', () => {
    const x = sj.symbol('x');
    const y = sj.SymFunction('y');
    expect(sj.str(sj.subFuncDoit(sj.sub(sj.mul(3, sj.Derivative(y(x), x)), 1), y(x), x))).toBe('2');
    const t = sj.symbol('t');
    const [f, g] = [sj.SymFunction('f'), sj.SymFunction('g')];
    const eqs = [sj.Eq(sj.Derivative(f(t), t), g(t)), sj.Eq(sj.Derivative(g(t), t), sj.mul(-1, f(t)))];
    const sols = [sj.Eq(f(t), sj.sin(t)), sj.Eq(g(t), sj.cos(t))];
    expect(sj.checksysodesol(eqs, sols).map(String)).toEqual(['true', '0,0']);
  });
});

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/solvers/liegroup.ts: infinitesimals, checkinfsol and the lie_group hint of dsolve;
// expected values from SymPy 1.14 (sympy/solvers/ode/tests/test_lie_group.py and dsolve(..., hint='lie_group')).

import { describe, expect, it } from 'vitest';
import { checkinfsol, dsolve, Eq, infinitesimals, NotImplementedError, parse, symbols, SymFunction } from '../../src';
import type { Expr } from '../../src';
import { lieGroupRemove } from '../../src/solvers/liegroup';

const [x] = symbols('x');
const fx = SymFunction('f')(x);
const showInf = (r: Map<Expr, Expr>[]) => `[${r.map((m) => `{${[...m].map(([k, v]) => `${String(k)}: ${String(v)}`).join(', ')}}`).join(', ')}]`;
const inf = (eq: string, hint?: string) => infinitesimals(parse(eq), hint ? { hint } : {});
const checks = (eq: string, r: Map<Expr, Expr>[]) => checkinfsol(parse(eq), r).map(([ok]) => ok);
const lie = (eq: string) => {
  const r = dsolve(parse(eq), fx, { hint: 'lie_group' });
  return Array.isArray(r) ? `[${r.map(String).join(', ')}]` : String(r);
};

describe('infinitesimals (SymPy test_lie_group)', () => {
  it('abaco1_simple', () => {
    const r = inf('Derivative(f(x), x) - x**2*f(x)', 'abaco1_simple');
    expect(showInf(r)).toBe('[{xi(x, f(x)): 0, eta(x, f(x)): exp(x**3/3)}, {xi(x, f(x)): 0, eta(x, f(x)): f(x)}, {xi(x, f(x)): x**(-2), eta(x, f(x)): 0}]');
    expect(checks('Derivative(f(x), x) - x**2*f(x)', r)).toEqual([true, true, true]);
    expect(showInf(inf('a*f(x) - c*exp(b*x) + Derivative(f(x), x)', 'abaco1_simple'))).toBe('[{xi(x, f(x)): 0, eta(x, f(x)): exp(-a*x)}]');
    expect(showInf(inf('2*x*f(x) - x*exp(-x**2) + Derivative(f(x), x)', 'abaco1_simple'))).toBe('[{xi(x, f(x)): 0, eta(x, f(x)): exp(-x**2)}]');
    expect(showInf(inf('x**2*exp(x - 1/x) + x**2*Derivative(f(x), x) - f(x)', 'abaco1_simple'))).toBe('[{xi(x, f(x)): 0, eta(x, f(x)): exp(-1/x)}]');
    expect(showInf(inf('Derivative(f(x), x) - 1/sqrt(a0 + a1*x + a2*x**2 + a3*x**3 + a4*x**4)', 'abaco1_simple'))).toBe(
      '[{xi(x, f(x)): 0, eta(x, f(x)): 1}, {xi(x, f(x)): sqrt(a0 + a1*x + a2*x**2 + a3*x**3 + a4*x**4), eta(x, f(x)): 0}]',
    );
    // SymPy: [{xi: 2*x + 1, eta: 0}, {xi: 1/(exp(f(x)) - 2), eta: 0}]; SymPy's h_y/h is not simplified and keeps x,
    // so it misses the (valid) symmetry eta = 2*exp(-f(x)) - 1 that is found first here
    const r3 = inf('(2*x + 1)*Derivative(f(x), x) + 2 - 4*exp(-f(x))', 'abaco1_simple');
    expect(r3.length).toBe(3);
    expect(checks('(2*x + 1)*Derivative(f(x), x) + 2 - 4*exp(-f(x))', r3)).toEqual([true, true, true]);
  });
  it('abaco1_product', () => {
    const eq = 'Derivative(f(x), x) - (x*log(x**2/f(x)) + 2)*f(x)/x';
    const r = inf(eq, 'abaco1_product');
    expect(showInf(r)).toBe('[{eta(x, f(x)): f(x)*exp(-x), xi(x, f(x)): 0}]');
    expect(checks(eq, r)).toEqual([true]);
  });
  it('chi and bivariate', () => {
    // SymPy: [{eta(x, f(x)): 1 - f(x)**2, xi(x, f(x)): 0}] (the free coefficient chosen differs)
    const r = inf('x*Derivative(f(x), x) - f(x)**2 + 1', 'chi');
    expect(showInf(r)).toBe('[{eta(x, f(x)): f(x)**2 - 1, xi(x, f(x)): 0}]');
    expect(checks('x*Derivative(f(x), x) - f(x)**2 + 1', r)).toEqual([true]);
    expect(showInf(inf('x**2*Derivative(f(x), x) + x**2 + x*f(x) + f(x)**2', 'bivariate'))).toBe('[{eta(x, f(x)): f(x), xi(x, f(x)): x}]');
    // only the trivial symmetry xi = 1, eta = h (SymPy)
    expect(showInf(inf('Derivative(f(x), x) - x**3 - f(x)**3', 'bivariate'))).toBe('[{eta(x, f(x)): x**3 + f(x)**3, xi(x, f(x)): 1}]');
  });
  it('bivariate with a parameter', () => {
    // SymPy: [{eta: x**2*f(x) + x + x**2*f(x)**2/a - 2/a, xi: x**2/a}], the same up to the factor a
    const eq = '-a*x**2*f(x) - a*x + x**2*(-f(x)**2 + Derivative(f(x), x)) + 2';
    const r = inf(eq, 'bivariate');
    expect(showInf(r)).toBe('[{eta(x, f(x)): a*x**2*f(x) + a*x + x**2*f(x)**2 - 2, xi(x, f(x)): x**2}]');
    expect(checks(eq, r)).toEqual([true]);
  });
  it('function_sum', () => {
    const eq = '-x*(1 - 3*f(x))/f(x)**2 - (3*x**2/f(x)**2 + 3)*atan(f(x)/x) + Derivative(f(x), x) - (1 - 2*f(x))/x';
    expect(showInf(inf(eq, 'function_sum'))).toBe('[{eta(x, f(x)): f(x)**(-2) + x**(-2), xi(x, f(x)): 0}]');
  });
  it('abaco2_similar', () => {
    expect(showInf(inf('-F(a*x + b*f(x)) + Derivative(f(x), x)', 'abaco2_similar'))).toBe('[{xi(x, f(x)): 1, eta(x, f(x)): -a/b}]');
    const eq = 'Derivative(f(x), x) - f(x)**2/(-x**2 + 2*x*f(x) - sin(x - f(x)))';
    const r = inf(eq, 'abaco2_similar');
    expect(showInf(r)).toBe('[{eta(x, f(x)): f(x)**2, xi(x, f(x)): f(x)**2}]');
    expect(checks(eq, r)).toEqual([true]);
  });
  it('abaco2_unique_unknown', () => {
    expect(showInf(inf('tan(F(x**2 + f(x)**2) + atan(x/f(x))) + Derivative(f(x), x)', 'abaco2_unique_unknown'))).toBe('[{xi(x, f(x)): -f(x), eta(x, f(x)): x}]');
    // SymPy: [{xi: x/x**a, eta: -f(x)/f(x)**b}], which its own checkinfsol rejects; not found here
    expect(() => inf('-x**(a - 1)*F(f(x)**b/b + x**a/a)*f(x)**(1 - b) + Derivative(f(x), x)', 'abaco2_unique_unknown')).toThrow(RangeError);
  });
  it('default, all and errors', () => {
    expect(showInf(inf('Derivative(f(x), x) - x**2*f(x)'))).toBe('[{xi(x, f(x)): 0, eta(x, f(x)): exp(x**3/3)}]');
    expect(inf('Derivative(f(x), x) - x**2*f(x)', 'all').length).toBeGreaterThanOrEqual(3);
    expect(() => inf('Derivative(f(x), x) - x**2*f(x)', 'nope')).toThrow(RangeError);
    expect(() => inf('Derivative(f(x), x, 2) - f(x)')).toThrow(NotImplementedError);
    expect(() => inf('f(x) - 1')).toThrow(TypeError);
  });
  it('checkinfsol rejects wrong infinitesimals', () => {
    const r = inf('Derivative(f(x), x) - x**2*f(x)');
    const [ok, res] = checkinfsol(parse('Derivative(f(x), x) - f(x)'), r)[0] ?? [];
    expect(ok).toBe(false);
    expect(String(res)).not.toBe('0');
  });
});

describe('dsolve with the lie_group hint (SymPy)', () => {
  it('reaches LambertW and implicit solutions', () => {
    expect(lie('Derivative(f(x), x) - 1/(x + f(x))')).toBe('Eq(f(x), -x - LambertW(C1*exp(-x - 1)) - 1)');
    expect(lie('Derivative(f(x), x) - 1/(x - f(x))**2')).toBe('Eq(C1 + f(x) - log(x - f(x) - 1)/2 + log(x - f(x) + 1)/2, 0)');
    expect(lie('-tan(x + f(x)) + Derivative(f(x), x)')).toBe('Eq(C1 + x/2 - f(x)/2 - log(-tan(x + f(x)) - 1)/2 + log(tan(x + f(x))**2 + 1)/4, 0)');
    expect(lie('Derivative(f(x), x) - f(x)/(x + f(x)**2)')).toBe('[Eq(f(x), C1/2 - sqrt(C1**2 + 4*x)/2), Eq(f(x), C1/2 + sqrt(C1**2 + 4*x)/2)]');
    // SymPy: Eq(f(x), log(C1/(2*x + 1) + 2)) from the next infinitesimals, as its solve does not invert
    // C1 - 2*y - 2*log(exp(-y) - 1/2) - 2*log(2*x + 1) (multiple generators); this is that solution with C1 - 2 for C1
    expect(lie('(2*x + 1)*Derivative(f(x), x) + 2 - 4*exp(-f(x))')).toBe('Eq(f(x), log((C1 + 4*x)/(2*x + 1)))');
    expect(lie('2*x*f(x) - x*exp(-x**2) + Derivative(f(x), x)')).toBe('Eq(f(x), (C1 + x**2/2)*exp(-x**2))');
    expect(lie('x**2*exp(x - 1/x) + x**2*Derivative(f(x), x) - f(x)')).toBe('Eq(f(x), (C1 - exp(x))*exp(-1/x))');
    expect(lie('Derivative(f(x), x) - exp(x)*f(x)**2')).toBe('Eq(f(x), 1/(C1 - exp(x)))');
    expect(lie('Derivative(f(x), x) - exp(f(x))')).toBe('Eq(f(x), log(1/(C1 - x)))');
  });
  it('is the default for first-order equations no other hint solves', () => {
    expect(String(dsolve(parse('Derivative(f(x), x) - 1/(x + f(x))'), fx))).toBe('Eq(f(x), -x - LambertW(C1*exp(-x - 1)) - 1)');
  });
  it('inverts implicit solutions polynomial in tan(u/2) (SymPy)', () => {
    expect(lie('-sin(x + f(x)) + Derivative(f(x), x)')).toBe('Eq(f(x), -x - 2*atan((C1 + x + 2)/(C1 + x)))');
    expect(lie('Derivative(f(x), x) - cos(x - f(x))')).toBe('Eq(f(x), x + 2*atan(1/(C1 + x)))');
  });
  it('keeps implicit solutions with an integral in f(x)', () => {
    // SymPy: Eq(f(x), 1/(C1 - Integral(1/(_r**2 - sin(_r)), (_r, C2 - x)))), which treats the integral's limit,
    // which depends on f(x), as a constant: the implicit solution is kept
    expect(lie('Derivative(f(x), x) - f(x)**2/(-x**2 + 2*x*f(x) - sin(x - f(x)))')).toBe('Eq(C1 - Integral(1/(_r**2 - sin(_r)), (_r, -x + f(x))) - 1/f(x), 0)');
  });
  it('user-given infinitesimals', () => {
    // SymPy test_user_infinitesimals uses xi = sqrt(f(x) - 1)/sqrt(f(x) + 1), eta = 0 for x*f' + 1 - f**2 and gets
    // Eq(f(x), (C1 + x**2)/(C1 - x**2)); here simplify takes too long on its coordinates and solve does not invert
    // x*sqrt(y + 1)/sqrt(y - 1) = C1, so cases SymPy also solves this way are used
    expect(String(dsolve(parse('Derivative(f(x), x) - x**2*f(x)'), fx, { hint: 'lie_group', xi: 0, eta: fx }))).toBe('Eq(f(x), C1*exp(x**3/3))');
    expect(String(dsolve(parse('Derivative(f(x), x) - 1/(x + f(x))'), fx, { hint: 'lie_group', xi: 1, eta: -1 }))).toBe('Eq(f(x), -x - LambertW(C1*exp(-x - 1)) - 1)');
  });
  it('where SymPy fails', () => {
    // SymPy raises a TypeError (in abaco2_similar); the solution is that of separable,
    // Eq(f(x), log(-1/(C1 + exp(x)))), with -C1 for C1
    expect(lie('-exp(x + f(x)) + Derivative(f(x), x)')).toBe('Eq(f(x), log(1/(C1 - exp(x))))');
  });
});

describe('lieGroupRemove (SymPy _lie_group_remove doctests)', () => {
  it('drops the arbitrary functions', () => {
    expect(String(lieGroupRemove(parse('x**2*y')))).toBe('x**2*y');
    expect(String(lieGroupRemove(parse('F(x**2*y)')))).toBe('x**2*y');
    expect(String(lieGroupRemove(parse('x*y**2 + F(x**3)')))).toBe('x*y**2');
    expect(String(lieGroupRemove(parse('(F(x**3) + y)*x**4')))).toBe('x**4*y');
    expect(String(lieGroupRemove(parse('F(x)**2')))).toBe('x**2');
  });
});

describe('every heuristic gives valid infinitesimals', () => {
  const heuristics = ['abaco1_simple', 'abaco1_product', 'abaco2_similar', 'abaco2_unique_unknown', 'linear', 'function_sum', 'bivariate', 'chi', 'default'];
  const eqs = [
    'Derivative(f(x),x) - (f(x)+x)/(x-f(x))', 'Derivative(f(x),x) - f(x)/x', 'Derivative(f(x),x) - x*f(x)', 'Derivative(f(x),x) - exp(f(x))',
    'Derivative(f(x),x) - f(x)**2/x**2', 'Derivative(f(x),x) - x/f(x)', 'Derivative(f(x),x) - f(x)**2', 'Derivative(f(x),x) - (x+f(x)+1)/(x+1)',
    'Derivative(f(x),x) - exp(x)*f(x)**2', 'Derivative(f(x),x) - sqrt(x*f(x))', 'Derivative(f(x),x) - (x - f(x))**(1/3)', 'Derivative(f(x),x) - 1/(exp(x)*f(x))',
  ];
  it.each(eqs)('%s', (eq) => {
    let found = 0;
    for (const hint of heuristics) {
      let r: Map<Expr, Expr>[];
      try {
        r = inf(eq, hint);
      } catch (err) {
        expect(err).toBeInstanceOf(RangeError);
        continue;
      }
      found += r.length;
      expect(checks(eq, r).every(Boolean)).toBe(true);
    }
    expect(found).toBeGreaterThan(0);
  });
});

describe('lie_group edge cases', () => {
  const ode = (eq: string, opts: { xi?: string; eta?: string } = {}) =>
    String(dsolve(parse(eq), fx, { hint: 'lie_group', ...(opts.xi !== undefined ? { xi: parse(opts.xi) } : {}), ...(opts.eta !== undefined ? { eta: parse(opts.eta) } : {}) }));
  it('equations and arguments', () => {
    // SymPy: Eq(f(x), C1)
    expect(ode('Derivative(f(x), x)')).toBe('Eq(f(x), C1)');
    expect(showInf(infinitesimals(Eq(parse('Derivative(f(x), x)'), parse('x**2*f(x)'))))).toBe('[{xi(x, f(x)): 0, eta(x, f(x)): exp(x**3/3)}]');
    expect(checkinfsol(Eq(parse('Derivative(f(x), x)'), parse('x**2*f(x)')), inf('Derivative(f(x), x) - x**2*f(x)'), { func: fx }).map(([ok]) => ok)).toEqual([true]);
    const g = SymFunction('g');
    const [y] = symbols('y');
    expect(() => infinitesimals(parse('Derivative(g(x, y), x)'), { func: g(x, y) })).toThrow(RangeError);
  });
  it('no infinitesimals', () => {
    const eq = 'Derivative(f(x), x) - sin(f(x)*x)*exp(f(x)**2*x)';
    expect(() => inf(eq)).toThrow(NotImplementedError);
    expect(() => inf(eq, 'all')).toThrow(NotImplementedError);
    expect(() => ode(eq)).toThrow(NotImplementedError);
    // SymPy: NotImplementedError as well (infinitesimals are found, but no solution from them)
    expect(() => ode('Derivative(f(x),x) - sqrt(x*f(x))')).toThrow(NotImplementedError);
    // SymPy: NotImplementedError (solve(eq, f'(x)) fails)
    expect(() => ode('Derivative(f(x), x) + exp(Derivative(f(x), x)) + Derivative(f(x), x)**2')).toThrow(NotImplementedError);
  });
  it('user-given infinitesimals: an invariant coordinate s, and trivial symmetries', () => {
    // SymPy: Eq(f(x), C1*exp(x))
    expect(ode('Derivative(f(x), x) - f(x)', { xi: '-exp(x)/f(x)', eta: '0' })).toBe('Eq(f(x), C1*exp(x))');
    // SymPy: KeyError and NotImplementedError
    expect(() => ode('Derivative(f(x), x) - 1/(x + f(x))', { xi: '0', eta: '0' })).toThrow(NotImplementedError);
    expect(() => ode('Derivative(f(x), x) - 1/(x + f(x))', { xi: '1', eta: '1/(x + f(x))' })).toThrow(NotImplementedError);
  });
});

describe('heuristics in their other forms', () => {
  it('function_sum with xi = f(x) + g(y), eta = 0', () => {
    // the equation of the SymPy test with x and y exchanged
    const eq = 'Derivative(f(x),x) - 1/(3*(1 + f(x)**2/x**2)*atan(x/f(x)) + (1 - 2*x)/f(x) + (1 - 3*x)*f(x)/x**2)';
    const r = inf(eq, 'function_sum');
    expect(showInf(r)).toBe('[{xi(x, f(x)): f(x)**(-2) + x**(-2), eta(x, f(x)): 0}]');
    expect(checks(eq, r)).toEqual([true]);
  });
  it('abaco1_product as the default, and with eta = f(x)*g(y)', () => {
    expect(showInf(inf('Derivative(f(x), x) - (x*log(x**2/f(x)) + 2)*f(x)/x'))).toBe('[{eta(x, f(x)): f(x)*exp(-x), xi(x, f(x)): 0}]');
    const eq = 'Derivative(f(x),x) - (x*f(x) + 1)/(x**2 + 1)';
    expect(checks(eq, inf(eq, 'abaco1_product'))).toEqual([true]);
    // the equation of SymPy's test with x and y exchanged: eta = f(x)*g(y)
    const dual = 'Derivative(f(x),x) - f(x)/(x*(f(x)*log(f(x)**2/x) + 2))';
    expect(checks(dual, inf(dual, 'abaco1_product'))).toEqual([true]);
    // the separated factor leaves g depending on x
    expect(() => inf('Derivative(f(x),x) - 1/(x**2 + f(x))', 'abaco1_product')).toThrow(RangeError);
  });
  it('function_sum on sums of functions of x and of f(x)', () => {
    // SymPy: [{xi: x**3 + f(x)**3, eta: 0}] and [{eta: exp(x) + exp(f(x)), xi: 0}], which are no symmetries (its
    // checkinfsol gives False): no infinitesimals here
    for (const eq of ['Derivative(f(x),x) - 1/(x**3 + f(x)**3)', 'Derivative(f(x),x) - (exp(x) + exp(f(x)))']) expect(() => inf(eq, 'function_sum')).toThrow(RangeError);
    // the condition on the constant k has no solution
    expect(() => inf('Derivative(f(x),x) - x/(f(x) + x**2)', 'function_sum')).toThrow(RangeError);
  });
  it('rational equations without polynomial infinitesimals of these forms', () => {
    expect(() => inf('Derivative(f(x),x) - 1/(x**2 + f(x))', 'chi')).toThrow(RangeError);
    expect(() => inf('Derivative(f(x),x) - f(x)**2/(x*(x + 1))', 'chi')).toThrow(RangeError);
  });
  it('first-order equations of other forms', () => {
    expect(showInf(inf('Derivative(f(x), x)'))).toBe('[{xi(x, f(x)): 0, eta(x, f(x)): 1}]');
    // SymPy: ValueError (its grouping of the terms turns C3 = 0 into 1 = 0)
    expect(checks('Derivative(f(x), x)', inf('Derivative(f(x), x)', 'linear'))).toEqual([true]);
    // solve(eq, f'(x)) for h: SymPy takes the first root as well
    const r = inf('Derivative(f(x), x)**2 - x');
    expect(checks('Derivative(f(x), x)**2 - x', r)).toEqual([true]);
    expect(() => inf('exp(Derivative(f(x), x))')).toThrow(NotImplementedError);
  });
  it('abaco2_unique_unknown without a separable ratio', () => {
    expect(() => inf('Derivative(f(x),x) - sqrt(x**2 + x*f(x) + f(x)**2)', 'abaco2_unique_unknown')).toThrow(RangeError);
  });
});


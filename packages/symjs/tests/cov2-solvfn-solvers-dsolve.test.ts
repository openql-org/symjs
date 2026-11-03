// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { describe, expect, it } from 'vitest';
import { NotImplementedError, SymFunction as Fn, classifyOde, dsolve, parse, symbols } from '../src';
import type { UndefFn } from '../src/core/nodes';

const [x] = symbols('x');
const f = Fn('f');
const fx = f(x) as UndefFn;
const show = (r: unknown): string => (Array.isArray(r) ? `[${r.map(show).join(', ')}]` : String(r));
const ds = (s: string, hint?: string) => show(dsolve(parse(s), fx, hint ? { hint } : {}));

/** a is a subsequence of b. */
const subsequence = (a: readonly string[], b: readonly string[]) => {
  let j = 0;
  for (const h of a) {
    while (j < b.length && b[j] !== h) j++;
    if (j === b.length) return false;
    j++;
  }
  return true;
};

// SymPy 1.14 classify_ode(eq, f(x)) without 'default' (an error name where it raises): the
// hints matched here are a subsequence (symjs has no matcher for several of SymPy's hints)
const CLASSIFY: [string, string[] | string][] = [
  ['Derivative(f(x), x)**2 + f(x)', ['factorable', 'lie_group']],
  ['Derivative(f(x), x)*exp(Derivative(f(x), x)) + f(x)', ['factorable', 'lie_group']],
  ['Derivative(f(x), x)', ['nth_algebraic', 'separable', '1st_exact', '1st_linear', 'Bernoulli', '1st_homogeneous_coeff_best', '1st_homogeneous_coeff_subs_indep_div_dep', '1st_homogeneous_coeff_subs_dep_div_indep', '1st_power_series', 'lie_group', 'nth_linear_constant_coeff_homogeneous', 'nth_linear_euler_eq_homogeneous', 'nth_algebraic_Integral', 'separable_Integral', '1st_exact_Integral', '1st_linear_Integral', 'Bernoulli_Integral', '1st_homogeneous_coeff_subs_indep_div_dep_Integral', '1st_homogeneous_coeff_subs_dep_div_indep_Integral']],
  ['Derivative(f(x), x)**2 - 4*f(x)', ['factorable', 'lie_group']],
  ['Derivative(f(x), x) + f(x) + x*f(x)**2 + f(x)**2', ['factorable', 'Bernoulli', '1st_rational_riccati', '1st_power_series', 'lie_group', 'Bernoulli_Integral']],
  ['Derivative(f(x), x) + f(x)**2 + f(x)**3', ['factorable', 'separable', '1st_exact', '1st_power_series', 'lie_group', 'separable_Integral', '1st_exact_Integral']],
  ['Derivative(f(x), x) + x*f(x)', ['separable', '1st_exact', '1st_linear', 'Bernoulli', 'almost_linear', '1st_power_series', 'lie_group', 'separable_Integral', '1st_exact_Integral', '1st_linear_Integral', 'Bernoulli_Integral', 'almost_linear_Integral']],
  ['Derivative(f(x), x) + f(x)/x', ['separable', '1st_exact', '1st_linear', 'Bernoulli', '1st_homogeneous_coeff_best', '1st_homogeneous_coeff_subs_indep_div_dep', '1st_homogeneous_coeff_subs_dep_div_indep', 'almost_linear', 'lie_group', 'nth_linear_euler_eq_homogeneous', 'separable_Integral', '1st_exact_Integral', '1st_linear_Integral', 'Bernoulli_Integral', '1st_homogeneous_coeff_subs_indep_div_dep_Integral', '1st_homogeneous_coeff_subs_dep_div_indep_Integral', 'almost_linear_Integral']],
  ['Derivative(f(x), x) + exp(Derivative(f(x), x)) + Derivative(f(x), x)**2', 'ERR NotImplementedError'],
  ['exp(Derivative(f(x), x))', 'ERR TypeError'],
  ['Derivative(f(x), x, 5) - Derivative(f(x), x) + f(x)', ['factorable', 'nth_linear_constant_coeff_homogeneous']],
  ['Derivative(f(x), x, 5) - Derivative(f(x), x) + f(x) - x', ['factorable', 'nth_linear_constant_coeff_undetermined_coefficients', 'nth_linear_constant_coeff_variation_of_parameters', 'nth_linear_constant_coeff_variation_of_parameters_Integral']],
  ['Derivative(f(x), x, 2) + f(x) - x*sin(x)', ['nth_linear_constant_coeff_undetermined_coefficients', 'nth_linear_constant_coeff_variation_of_parameters', 'nth_linear_constant_coeff_variation_of_parameters_Integral']],
  ['Derivative(f(x), x, 2)*Derivative(f(x), x) + f(x)', ['factorable']],
  ['Derivative(f(x), x, 2) + Derivative(f(x), x)**3', ['factorable', 'nth_order_reducible']],
  ['(x**2 + 1)*Derivative(f(x), x, 2) + f(x)', ['2nd_hypergeometric', '2nd_hypergeometric_Integral', '2nd_power_series_ordinary']],
  ['x**2*Derivative(f(x), x, 2) + x**2*Derivative(f(x), x) + f(x)', ['factorable', '2nd_power_series_regular']],
  ['x**2*Derivative(f(x), x, 2) + x*Derivative(f(x), x) + (x**2 + x)*f(x)', ['factorable', '2nd_power_series_regular']],
  ['x**2*Derivative(f(x), x, 2) + x*Derivative(f(x), x) + sin(x)*f(x)', ['factorable', '2nd_power_series_regular']],
  ['x**2*Derivative(f(x), x, 2) + x*Derivative(f(x), x) + (x - 4)*f(x)', ['factorable', '2nd_linear_bessel', '2nd_power_series_regular']],
  ['x**2*Derivative(f(x), x, 2) + x*Derivative(f(x), x) + (x**2 - 4)*f(x)', ['factorable', '2nd_linear_bessel', '2nd_power_series_regular']],
  ['Derivative(f(x), x, 2) - x*f(x)', ['2nd_linear_airy', '2nd_power_series_ordinary']],
  ['Derivative(f(x), x) - (x + f(x) + 1)/(x - f(x) - 3)', ['linear_coefficients', '1st_power_series', 'lie_group', 'linear_coefficients_Integral']],
  ['Derivative(f(x), x) - (x + f(x) + 1)*(x**2 + 1)/((x - f(x) - 3)*(x**2 + 2))', ['factorable', '1st_power_series', 'lie_group']],
  ['Derivative(f(x), x) - (f(x)/x)**2 - exp(f(x)/x)', ['1st_homogeneous_coeff_best', '1st_homogeneous_coeff_subs_indep_div_dep', '1st_homogeneous_coeff_subs_dep_div_indep', 'lie_group', '1st_homogeneous_coeff_subs_indep_div_dep_Integral', '1st_homogeneous_coeff_subs_dep_div_indep_Integral']],
  ['Derivative(f(x), x) - f(x)/x + exp(-f(x)/x)*x/f(x)', ['1st_homogeneous_coeff_best', '1st_homogeneous_coeff_subs_indep_div_dep', '1st_homogeneous_coeff_subs_dep_div_indep', 'lie_group', '1st_homogeneous_coeff_subs_indep_div_dep_Integral', '1st_homogeneous_coeff_subs_dep_div_indep_Integral']],
  ['x*Derivative(f(x), x) - f(x) - sqrt(x**2 + f(x)**2)', ['factorable', '1st_homogeneous_coeff_best', '1st_homogeneous_coeff_subs_indep_div_dep', '1st_homogeneous_coeff_subs_dep_div_indep', 'lie_group', '1st_homogeneous_coeff_subs_indep_div_dep_Integral', '1st_homogeneous_coeff_subs_dep_div_indep_Integral']],
  ['Derivative(f(x), x, 2) + Derivative(f(x), x)**2', ['factorable', 'Liouville', 'nth_order_reducible', 'Liouville_Integral']],
  ['Derivative(f(x), x, 3) - Derivative(f(x), x, 2)**2', ['nth_order_reducible']],
  ['Derivative(f(x), x, 2) - exp(Derivative(f(x), x))', ['factorable', 'nth_order_reducible']],
  ['x**2*Derivative(f(x), x, 2) - 2*x*Derivative(f(x), x) + 2*f(x) - x**3*exp(x)', ['factorable', 'nth_linear_euler_eq_nonhomogeneous_variation_of_parameters', 'nth_linear_euler_eq_nonhomogeneous_variation_of_parameters_Integral']],
  ['x**2*Derivative(f(x), x, 2) - 2*x*Derivative(f(x), x) + 2*f(x) - log(x)', ['factorable', 'nth_linear_euler_eq_nonhomogeneous_undetermined_coefficients', 'nth_linear_euler_eq_nonhomogeneous_variation_of_parameters', 'nth_linear_euler_eq_nonhomogeneous_variation_of_parameters_Integral']],
  ['x**2*Derivative(f(x), x, 2) + x*Derivative(f(x), x) - f(x) - 1/x', ['factorable', 'nth_linear_euler_eq_nonhomogeneous_undetermined_coefficients', 'nth_linear_euler_eq_nonhomogeneous_variation_of_parameters', 'nth_linear_euler_eq_nonhomogeneous_variation_of_parameters_Integral']],
  ['(Derivative(f(x), x) - f(x))*(Derivative(f(x), x) + f(x))', ['factorable', 'lie_group']],
  ['(Derivative(f(x), x) - x)*(Derivative(f(x), x) - 1)*(Derivative(f(x), x) + x**2)', ['factorable', 'nth_algebraic', 'lie_group', 'nth_algebraic_Integral']],
  ['Derivative(f(x), x)**2 - x**2', ['factorable', 'nth_algebraic', 'lie_group', 'nth_algebraic_Integral']],
  ['Derivative(f(x), x)**3 - 1', ['factorable', 'nth_algebraic', 'lie_group', 'nth_algebraic_Integral']],
  ['f(x)*Derivative(f(x), x, 2) + Derivative(f(x), x)**2', ['factorable', 'Liouville', 'Liouville_Integral']],
  ['f(x) - x', ['nth_algebraic', 'nth_algebraic_Integral']],  ['Derivative(f(x), x) - f(x)/x', ['separable', '1st_exact', '1st_linear', 'Bernoulli', 'almost_linear', 'lie_group', 'nth_linear_euler_eq_homogeneous', 'separable_Integral', '1st_exact_Integral', '1st_linear_Integral', 'Bernoulli_Integral', 'almost_linear_Integral']],
  ['Derivative(f(x), x) - (f(x) + 1)/(x + 2)', ['separable', '1st_exact', '1st_linear', 'Bernoulli', 'almost_linear', 'linear_coefficients', '1st_power_series', 'lie_group', 'separable_Integral', '1st_exact_Integral', '1st_linear_Integral', 'Bernoulli_Integral', 'almost_linear_Integral', 'linear_coefficients_Integral']],
  ['x*Derivative(f(x), x, 2) + sin(Derivative(f(x), x, 2)) + Derivative(f(x), x, 3)', ['nth_order_reducible']],
  ['-Derivative(f(x), x, 2)**3 - Derivative(f(x), x, 2)**2 + Derivative(f(x), x, 3)', ['nth_order_reducible']],
  ['(f(x) + Derivative(f(x), x)*Derivative(f(x), x, 2))*(2*f(x) + Derivative(f(x), x)*Derivative(f(x), x, 2))', ['factorable']],
  ['(x + Derivative(f(x), x))*(x + f(x) + Derivative(f(x), x))', ['factorable', 'lie_group']],
  ['-x*exp(x) + f(x) - 2*Derivative(f(x), x) + Derivative(f(x), x, 2)', ['factorable', 'nth_linear_constant_coeff_undetermined_coefficients', 'nth_linear_constant_coeff_variation_of_parameters', 'nth_linear_constant_coeff_variation_of_parameters_Integral']],
  ['(x + Derivative(f(x), x))*(x + Derivative(f(x), x)**2 + Derivative(f(x), x))', ['factorable', 'nth_algebraic', 'lie_group', 'nth_algebraic_Integral']],
  ['(x**2 + 1)*(x - f(x) - 3)*Derivative(f(x), x) - (x**2 + 1)*(x + f(x) + 1)', ['factorable', '1st_power_series', 'lie_group']],
  ['(-f(x) + Derivative(f(x), x))**2', ['factorable', 'separable', '1st_exact', '1st_linear', 'Bernoulli', 'almost_linear', '1st_power_series', 'lie_group', 'separable_Integral', '1st_exact_Integral', '1st_linear_Integral', 'Bernoulli_Integral', 'almost_linear_Integral']],
];

const FORM = ['Derivative(f(x), x) - (x + f(x) + 1)/(x - f(x) - 3)', 'Derivative(f(x), x) - (f(x) + 1)/(x + 2)'];

describe('classify_ode reports hints SymPy reports', () => {
  it.each(CLASSIFY)('classify_ode(%s)', (src, expected) => {
    const got = classifyOde(parse(src), fx);
    // SymPy raises for these: no hint matches here
    if (typeof expected === 'string') expect(got).toEqual([]);
    // SymPy reports factorable when solve(eq, f') gives f' - root in another form than eq, which
    // depends on the form of the root (here the root of these two keeps another form)
    else if (FORM.includes(src)) expect(subsequence(got, ['factorable', ...expected])).toBe(true);
    else expect(subsequence(got, expected)).toBe(true);
  });
  it('the equation may be an Eq', () => {
    expect(classifyOde(parse('Eq(Derivative(f(x), x), x)'), fx)).toEqual(classifyOde(parse('Derivative(f(x), x) - x'), fx));
  });
});

// expected values from SymPy 1.14 dsolve
describe('dsolve', () => {
  it('Euler equations with a logarithm on the right-hand side (x = exp(t) with t positive)', () => {
    expect(ds('x**2*Derivative(f(x), x, 2) - 2*x*Derivative(f(x), x) + 2*f(x) - log(x)')).toBe('Eq(f(x), C1*x + C2*x**2 + log(x)/2 + 3/4)');
  });
  it('Bessel equations with a half-integer power', () => {
    expect(ds('x**2*Derivative(f(x), x, 2) + x*Derivative(f(x), x) + (x - 4)*f(x)')).toBe('Eq(f(x), C1*besselj(4, 2*sqrt(x)) + C2*bessely(4, 2*sqrt(x)))');
  });
  it('undetermined coefficients with a resonant right-hand side', () => {
    expect(ds('-x*exp(x) + f(x) - 2*Derivative(f(x), x) + Derivative(f(x), x, 2)')).toBe('Eq(f(x), (C1 + x*(C2 + x**2/6))*exp(x))');
  });
  it('factors in Mul argument order', () => {
    // SymPy lists the two branches of the quadratic factor the other way round (its nth_algebraic
    // sorts the solutions it gets from solve for f(x)); the first factor comes first in both
    const r = dsolve(parse('(x + Derivative(f(x), x))*(x + Derivative(f(x), x)**2 + Derivative(f(x), x))'), fx) as unknown[];
    expect(String(r[0])).toBe('Eq(f(x), C1 - x**2/2)');
    expect(r.slice(1).map(String).sort()).toEqual(['Eq(f(x), C1 - x/2 + (1 - 4*x)**(3/2)/12)', 'Eq(f(x), C1 - x/2 - (1 - 4*x)**(3/2)/12)']);
  });
  it('unsupported equations', () => {
    // SymPy: a solution with CRootOf(_x**5 - _x + 1, k); roots() does not give CRootOf here
    expect(() => ds('Derivative(f(x), x, 5) - Derivative(f(x), x) + f(x)')).toThrow(NotImplementedError);
    // SymPy: Eq(Integral(1/LambertW(-_y), (_y, f(x))), C1 + x)
    expect(() => ds('Derivative(f(x), x)*exp(Derivative(f(x), x)) + f(x)')).toThrow(NotImplementedError);
    // SymPy: NotImplementedError as well
    expect(() => ds('Derivative(f(x), x, 2)*Derivative(f(x), x) + f(x)')).toThrow(NotImplementedError);
  });
});

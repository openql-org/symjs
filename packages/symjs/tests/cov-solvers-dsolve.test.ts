// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { describe, expect, it } from 'vitest';
import { SymFunction as Fn, classifyOde, dsolve, parse, symbols } from '../src';
import type { UndefFn } from '../src/core/nodes';

const [x] = symbols('x');
const f = Fn('f');
const fx = f(x) as UndefFn;
const show = (r: unknown) => (Array.isArray(r) ? `[${r.map(String).join(', ')}]` : String(r));

/** SymPy hints that classifyOde does not report (no matcher here). */
const UNMATCHED = new Set(['1st_rational_riccati', 'separable_reduced', 'separable_reduced_Integral', '2nd_power_series_ordinary', '2nd_power_series_regular', 'nth_linear_euler_eq_nonhomogeneous_variation_of_parameters', 'nth_linear_euler_eq_nonhomogeneous_variation_of_parameters_Integral', 'almost_linear', 'almost_linear_Integral', '2nd_nonlinear_autonomous_conserved', '2nd_nonlinear_autonomous_conserved_Integral']);

// expected values from SymPy 1.14 classify_ode, without the hints in UNMATCHED
const CLASSIFY: [string, string[]][] = [
  ['Derivative(f(x),x,x)*f(x) + x', []],
  ['Derivative(f(x),x) - f(x)**2*sin(x) - f(x)*cos(x)', ['factorable', 'Bernoulli', '1st_power_series', 'lie_group', 'Bernoulli_Integral']],
  ['Derivative(f(x),x,x) + Derivative(f(x),x)*x**2 + f(x)*x', ['factorable']],
  ['x*Derivative(f(x),x,x) + Derivative(f(x),x) + f(x)**2', []],
  ['Derivative(f(x),x) + f(x)**2*exp(x) - 2*f(x)', ['factorable', 'Bernoulli', '1st_power_series', 'lie_group', 'Bernoulli_Integral']],
  ['Derivative(f(x),x,x)+f(x)-exp(x)*log(x)', ['nth_linear_constant_coeff_variation_of_parameters', 'nth_linear_constant_coeff_variation_of_parameters_Integral']],
  ['Derivative(f(x),x) - f(x)**2*x', ['separable', '1st_exact', 'Bernoulli', '1st_power_series', 'lie_group', 'separable_Integral', '1st_exact_Integral', 'Bernoulli_Integral']],
  ['Derivative(f(x),x) + f(x)/x - x*f(x)**3', ['Bernoulli', 'lie_group', 'Bernoulli_Integral']],
  ['Derivative(f(x),x) - f(x) - x*f(x)**2', ['factorable', 'Bernoulli', '1st_power_series', 'lie_group', 'Bernoulli_Integral']],
  ['Derivative(f(x),x) + f(x)**2 + 2/x**2', ['Riccati_special_minus2', 'lie_group']],
  ['Derivative(f(x),x) - a*f(x)**2 - b/x**2', ['Riccati_special_minus2', 'lie_group']],
  ['Derivative(f(x),x,x) - x*f(x)', ['2nd_linear_airy']],
  ['Derivative(f(x),x,x) + 4*x*f(x)', ['2nd_linear_airy']],
  ['x**2*Derivative(f(x),x,x) + x*Derivative(f(x),x) + (x**2 - 4)*f(x)', ['factorable', '2nd_linear_bessel']],
  ['x**2*Derivative(f(x),x,x) + x*Derivative(f(x),x) + (x**2 - 1/4)*f(x)', ['factorable', '2nd_linear_bessel']],
  ['Derivative(f(x),x,x) + Derivative(f(x),x)**2/f(x) + Derivative(f(x),x)/x', ['factorable', 'Liouville', 'Liouville_Integral']],
  ['Derivative(f(x),x,x) + 2/f(x)*Derivative(f(x),x)**2', ['factorable', 'Liouville', 'Liouville_Integral']],
  ['Derivative(f(x),x,3) - Derivative(f(x),x,2)/x', ['nth_linear_euler_eq_homogeneous', 'nth_order_reducible']],
  ['x**2*Derivative(f(x),x,x) - 2*f(x) - x**3', ['nth_linear_euler_eq_nonhomogeneous_undetermined_coefficients']],
  ['x**3*Derivative(f(x),x,3) + x*Derivative(f(x),x) - f(x)', ['factorable', 'nth_linear_euler_eq_homogeneous']],
  ['Derivative(f(x),x,x) + f(x) - tan(x)', ['nth_linear_constant_coeff_variation_of_parameters', 'nth_linear_constant_coeff_variation_of_parameters_Integral']],
  ['Derivative(f(x),x,x) - 2*Derivative(f(x),x) + f(x) - exp(x)/x', ['factorable', 'nth_linear_constant_coeff_variation_of_parameters', 'nth_linear_constant_coeff_variation_of_parameters_Integral']],
  ['(x**2 + f(x)**2) - 2*x*f(x)*Derivative(f(x),x)', ['factorable', '1st_exact', 'Bernoulli', '1st_homogeneous_coeff_best', '1st_homogeneous_coeff_subs_indep_div_dep', '1st_homogeneous_coeff_subs_dep_div_indep', 'lie_group', '1st_exact_Integral', 'Bernoulli_Integral', '1st_homogeneous_coeff_subs_indep_div_dep_Integral', '1st_homogeneous_coeff_subs_dep_div_indep_Integral']],
  ['2*x*f(x) + (x**2 + f(x)**2)*Derivative(f(x),x)', ['factorable', '1st_exact', '1st_homogeneous_coeff_best', '1st_homogeneous_coeff_subs_indep_div_dep', '1st_homogeneous_coeff_subs_dep_div_indep', '1st_power_series', 'lie_group', '1st_exact_Integral', '1st_homogeneous_coeff_subs_indep_div_dep_Integral', '1st_homogeneous_coeff_subs_dep_div_indep_Integral']],
  ['cos(f(x)) - x*sin(f(x))*Derivative(f(x),x)', ['factorable', 'separable', '1st_exact', 'lie_group', 'separable_Integral', '1st_exact_Integral']],
  ['Derivative(f(x),x) - exp(f(x))*x', ['separable', '1st_exact', '1st_power_series', 'lie_group', 'separable_Integral', '1st_exact_Integral']],
  ['Derivative(f(x),x)*exp(-f(x)) - x', ['factorable', 'separable', '1st_exact', '1st_power_series', 'lie_group', 'separable_Integral', '1st_exact_Integral']],
  ['Derivative(f(x),x) - f(x)*log(f(x))/x', ['separable', '1st_exact', 'lie_group', 'separable_Integral', '1st_exact_Integral']],
  ['Derivative(f(x),x) - sin(x)*cos(f(x))', ['separable', '1st_exact', '1st_power_series', 'lie_group', 'separable_Integral', '1st_exact_Integral']],
  ['f(x)*Derivative(f(x),x) - x', ['factorable', 'separable', '1st_exact', 'Bernoulli', '1st_homogeneous_coeff_best', '1st_homogeneous_coeff_subs_indep_div_dep', '1st_homogeneous_coeff_subs_dep_div_indep', '1st_power_series', 'lie_group', 'separable_Integral', '1st_exact_Integral', 'Bernoulli_Integral', '1st_homogeneous_coeff_subs_indep_div_dep_Integral', '1st_homogeneous_coeff_subs_dep_div_indep_Integral']],
  ['Derivative(f(x),x,x)**2 - 1', ['factorable', 'nth_algebraic', 'nth_algebraic_Integral']],
  ['Derivative(f(x),x,x) - exp(x)', ['nth_algebraic', 'nth_linear_constant_coeff_undetermined_coefficients', 'nth_linear_constant_coeff_variation_of_parameters', 'nth_algebraic_Integral', 'nth_linear_constant_coeff_variation_of_parameters_Integral']],
  ['Derivative(f(x),x,3) - x', ['nth_algebraic', 'nth_linear_constant_coeff_undetermined_coefficients', 'nth_linear_euler_eq_nonhomogeneous_undetermined_coefficients', 'nth_linear_constant_coeff_variation_of_parameters', 'nth_algebraic_Integral', 'nth_linear_constant_coeff_variation_of_parameters_Integral']],
  ['Derivative(f(x),x,x) + 3*Derivative(f(x),x) + 2*f(x) - sin(x)*exp(x)', ['factorable', 'nth_linear_constant_coeff_undetermined_coefficients', 'nth_linear_constant_coeff_variation_of_parameters', 'nth_linear_constant_coeff_variation_of_parameters_Integral']],
  ['Derivative(f(x),x,x) + f(x) - x*cos(x)', ['nth_linear_constant_coeff_undetermined_coefficients', 'nth_linear_constant_coeff_variation_of_parameters', 'nth_linear_constant_coeff_variation_of_parameters_Integral']],
  ['Derivative(f(x),x,4) + 2*Derivative(f(x),x,2) + f(x)', ['nth_linear_constant_coeff_homogeneous']],
  ['Derivative(f(x),x,x) - 4*Derivative(f(x),x) + 13*f(x)', ['factorable', 'nth_linear_constant_coeff_homogeneous']],
  ['Derivative(f(x),x,x) - a**2*f(x)', ['nth_linear_constant_coeff_homogeneous']],
  ['Derivative(f(x),x,x) + I*f(x)', ['nth_linear_constant_coeff_homogeneous']],
  ['Derivative(f(x),x) - a*f(x) - exp(b*x)', ['1st_exact', '1st_linear', 'Bernoulli', '1st_power_series', 'lie_group', 'nth_linear_constant_coeff_undetermined_coefficients', 'nth_linear_constant_coeff_variation_of_parameters', '1st_exact_Integral', '1st_linear_Integral', 'Bernoulli_Integral', 'nth_linear_constant_coeff_variation_of_parameters_Integral']],
  ['Derivative(f(x),x) + 2*x*f(x) - x', ['factorable', 'separable', '1st_exact', '1st_linear', 'Bernoulli', '1st_power_series', 'lie_group', 'separable_Integral', '1st_exact_Integral', '1st_linear_Integral', 'Bernoulli_Integral']],
  ['Derivative(f(x),x) + f(x)*tan(x) - sin(2*x)', ['1st_exact', '1st_linear', 'Bernoulli', '1st_power_series', 'lie_group', '1st_exact_Integral', '1st_linear_Integral', 'Bernoulli_Integral']],
  ['Derivative(f(x),x,x) + x*Derivative(f(x),x) + f(x)', ['factorable']],
  ['Derivative(f(x),x,x) + Derivative(f(x),x)*f(x)', ['factorable']],
  ['Derivative(f(x),x) - x**2 - f(x)**2', ['1st_power_series', 'lie_group']],
  ['x*Derivative(f(x),x) + f(x) - f(x)**2*log(x)', ['factorable', 'Bernoulli', 'lie_group', 'Bernoulli_Integral']],
  ['Derivative(f(x),x) - 1/(x + f(x))', ['1st_power_series', 'lie_group']],
  ['Derivative(f(x),x) - sin(x + f(x))', ['1st_power_series', 'lie_group']],
  ['Derivative(f(x),x) - f(x)**3*sin(x)', ['separable', '1st_exact', 'Bernoulli', '1st_power_series', 'lie_group', 'separable_Integral', '1st_exact_Integral', 'Bernoulli_Integral']],
  ['Derivative(f(x),x)*x*log(x) - f(x)', ['factorable', 'separable', '1st_exact', '1st_linear', 'Bernoulli', 'lie_group', 'separable_Integral', '1st_exact_Integral', '1st_linear_Integral', 'Bernoulli_Integral']],
  ['x*Derivative(f(x),x) - f(x) - x*exp(f(x)/x)', ['factorable', '1st_homogeneous_coeff_best', '1st_homogeneous_coeff_subs_indep_div_dep', '1st_homogeneous_coeff_subs_dep_div_indep', 'lie_group', '1st_homogeneous_coeff_subs_indep_div_dep_Integral', '1st_homogeneous_coeff_subs_dep_div_indep_Integral']],
  ['Derivative(f(x),x) + sin(f(x))', ['separable', '1st_exact', '1st_power_series', 'lie_group', 'separable_Integral', '1st_exact_Integral']],
  ['Derivative(f(x),x) - 3*f(x)**(2/3)', ['separable', '1st_exact', 'Bernoulli', '1st_power_series', 'lie_group', 'separable_Integral', '1st_exact_Integral', 'Bernoulli_Integral']],
  ['x**2*Derivative(f(x),x) - f(x)**2 - x*f(x)', ['factorable', 'Bernoulli', '1st_homogeneous_coeff_best', '1st_homogeneous_coeff_subs_indep_div_dep', '1st_homogeneous_coeff_subs_dep_div_indep', 'lie_group', 'Bernoulli_Integral', '1st_homogeneous_coeff_subs_indep_div_dep_Integral', '1st_homogeneous_coeff_subs_dep_div_indep_Integral']],
  ['Derivative(f(x),x,x) - 1/f(x)**3', []],
  ['f(x)*Derivative(f(x),x,x) - Derivative(f(x),x)**2', ['factorable', 'Liouville', 'Liouville_Integral']],
  ['Derivative(f(x),x,x) + exp(f(x))', []],
  ['Derivative(f(x),x,x,x)*Derivative(f(x),x,x) - 1', ['nth_order_reducible']],
  ['Derivative(f(x),x) - cos(x)*f(x) - cos(x)', ['factorable', 'separable', '1st_exact', '1st_linear', 'Bernoulli', '1st_power_series', 'lie_group', 'separable_Integral', '1st_exact_Integral', '1st_linear_Integral', 'Bernoulli_Integral']],
  ['x*Derivative(f(x),x) + f(x) - x*exp(x)', ['factorable', '1st_exact', '1st_linear', 'Bernoulli', 'lie_group', '1st_exact_Integral', '1st_linear_Integral', 'Bernoulli_Integral']],
  ['Derivative(f(x),x) - x*exp(-f(x))', ['separable', '1st_exact', '1st_power_series', 'lie_group', 'separable_Integral', '1st_exact_Integral']],
  ['Derivative(f(x),x,x) - x**2*f(x)', []],
  ['x**2*Derivative(f(x),x,x) + f(x) - x', ['nth_linear_euler_eq_nonhomogeneous_undetermined_coefficients']],
  ['x**3*Derivative(f(x),x,3) + 3*x**2*Derivative(f(x),x,2) + 2*x*Derivative(f(x),x)', ['factorable', 'nth_linear_euler_eq_homogeneous', 'nth_order_reducible']],
  ['x**2*Derivative(f(x),x,x) - 3*x*Derivative(f(x),x) + 4*f(x) - x**2', ['factorable', 'nth_linear_euler_eq_nonhomogeneous_undetermined_coefficients']],
  ['Derivative(f(x),x,x) + f(x) - sin(x)/x', ['nth_linear_constant_coeff_variation_of_parameters', 'nth_linear_constant_coeff_variation_of_parameters_Integral']],
  ['Derivative(f(x),x,x) + f(x) - exp(x**2)', ['nth_linear_constant_coeff_variation_of_parameters', 'nth_linear_constant_coeff_variation_of_parameters_Integral']],
  ['Derivative(f(x),x,x) - f(x) - 1/cosh(x)', ['nth_linear_constant_coeff_variation_of_parameters', 'nth_linear_constant_coeff_variation_of_parameters_Integral']],
  ['Derivative(f(x),x,3) - 3*Derivative(f(x),x,2) + 3*Derivative(f(x),x) - f(x) - exp(x)', ['factorable', 'nth_linear_constant_coeff_undetermined_coefficients', 'nth_linear_constant_coeff_variation_of_parameters', 'nth_linear_constant_coeff_variation_of_parameters_Integral']],
  ['Derivative(f(x),x) - f(x)*x - x*f(x)**2', ['factorable', 'separable', '1st_exact', 'Bernoulli', '1st_power_series', 'lie_group', 'separable_Integral', '1st_exact_Integral', 'Bernoulli_Integral']],
  ['Derivative(f(x),x) - f(x)**2 - f(x)/x - 1/x**2', ['Riccati_special_minus2', 'lie_group']],
  ['Derivative(f(x),x) + f(x)**2 - 1/x**2', ['Riccati_special_minus2', 'lie_group']],
  ['Derivative(f(x),x,x)*Derivative(f(x),x) - 1', ['factorable', 'nth_order_reducible']],
  ['Derivative(f(x),x,x) - Derivative(f(x),x)/x - x**2*Derivative(f(x),x)**2', ['factorable', 'nth_order_reducible']],
  ['f(x)*Derivative(f(x),x) + x*f(x)**2 - x', ['factorable', 'separable', '1st_exact', 'Bernoulli', '1st_power_series', 'lie_group', 'separable_Integral', '1st_exact_Integral', 'Bernoulli_Integral']],
  ['x*f(x)*Derivative(f(x),x) - f(x)**2 - x**2', ['factorable', '1st_exact', 'Bernoulli', '1st_homogeneous_coeff_best', '1st_homogeneous_coeff_subs_indep_div_dep', '1st_homogeneous_coeff_subs_dep_div_indep', 'lie_group', '1st_exact_Integral', 'Bernoulli_Integral', '1st_homogeneous_coeff_subs_indep_div_dep_Integral', '1st_homogeneous_coeff_subs_dep_div_indep_Integral']],
  ['(x + f(x))*Derivative(f(x),x) + f(x) - x', ['factorable', '1st_exact', '1st_homogeneous_coeff_best', '1st_homogeneous_coeff_subs_indep_div_dep', '1st_homogeneous_coeff_subs_dep_div_indep', '1st_power_series', 'lie_group', '1st_exact_Integral', '1st_homogeneous_coeff_subs_indep_div_dep_Integral', '1st_homogeneous_coeff_subs_dep_div_indep_Integral']],
  ['(2*x + 3*f(x) + 1)*Derivative(f(x),x) - (x - f(x) + 2)', ['factorable', 'linear_coefficients', '1st_power_series', 'lie_group', 'linear_coefficients_Integral']],
  ['(x + f(x) + 1)*Derivative(f(x),x) - (2*x + 2*f(x) - 1)', ['factorable', '1st_power_series', 'lie_group']],
  ['Derivative(f(x),x) - exp(x - f(x))', ['separable', '1st_exact', '1st_power_series', 'lie_group', 'separable_Integral', '1st_exact_Integral']],
  ['Derivative(f(x),x) - f(x)/(x + f(x)**2)', ['1st_power_series', 'lie_group']],
  ['Derivative(f(x),x) - x**2*exp(-x**3)*f(x)', ['separable', '1st_exact', '1st_linear', 'Bernoulli', '1st_power_series', 'lie_group', 'separable_Integral', '1st_exact_Integral', '1st_linear_Integral', 'Bernoulli_Integral']],
  ['sin(x)*Derivative(f(x),x) + cos(x)*f(x) - 1', ['factorable', '1st_exact', '1st_linear', 'Bernoulli', 'lie_group', '1st_exact_Integral', '1st_linear_Integral', 'Bernoulli_Integral']],
  ['Derivative(f(x),x,x) + exp(x)*f(x)', []],
  ['Derivative(f(x),x,x) + a*x*f(x)', ['2nd_linear_airy']],
  ['Derivative(f(x),x,x) - (x**2 + 1)*f(x)', []],
  ['x*Derivative(f(x),x,x) + 2*Derivative(f(x),x) + x*f(x)', ['factorable', '2nd_linear_bessel']],
  ['x**2*Derivative(f(x),x,x) + x*Derivative(f(x),x) + (4*x**4 - 9)*f(x)', ['factorable', '2nd_linear_bessel']],
  ['Derivative(f(x),x,x) - 2*Derivative(f(x),x) + 2*f(x) - exp(x)*cos(x)', ['factorable', 'nth_linear_constant_coeff_undetermined_coefficients', 'nth_linear_constant_coeff_variation_of_parameters', 'nth_linear_constant_coeff_variation_of_parameters_Integral']],
  ['Derivative(f(x),x,x) + f(x) - sin(2*x)*cos(x)', ['nth_linear_constant_coeff_variation_of_parameters', 'nth_linear_constant_coeff_variation_of_parameters_Integral']],
  ['Derivative(f(x),x,x) + 4*f(x) - x**2*exp(x) - sin(x)', ['nth_linear_constant_coeff_undetermined_coefficients', 'nth_linear_constant_coeff_variation_of_parameters', 'nth_linear_constant_coeff_variation_of_parameters_Integral']],
  ['Derivative(f(x),x,x) + 4*f(x) - log(x)', ['nth_linear_constant_coeff_variation_of_parameters', 'nth_linear_constant_coeff_variation_of_parameters_Integral']],
  ['Derivative(f(x),x,x) + 4*f(x) - x*sin(x)**2', ['nth_linear_constant_coeff_variation_of_parameters', 'nth_linear_constant_coeff_variation_of_parameters_Integral']],
  ['Derivative(f(x),x,x) + 2*x*Derivative(f(x),x)**2', ['factorable', 'nth_order_reducible']],
  ['x*Derivative(f(x),x,x) + Derivative(f(x),x)**2', ['factorable', 'nth_order_reducible']],
  ['Derivative(f(x),x,4) - Derivative(f(x),x,2)', ['nth_linear_constant_coeff_homogeneous', 'nth_order_reducible']],
  ['Derivative(f(x),x,3) + Derivative(f(x),x)', ['nth_linear_constant_coeff_homogeneous', 'nth_order_reducible']],
  ['Derivative(f(x),x) - f(x)**2 + f(x)*sin(x) - cos(x)', ['1st_power_series', 'lie_group']],
  ['Derivative(f(x),x) + f(x)**2 - 2/x**2 + 1/x', ['lie_group']],
  ['Derivative(f(x),x) - a/x**2 - f(x)**2', ['Riccati_special_minus2', 'lie_group']],
  ['2*x*Derivative(f(x),x) - f(x) - x**2*f(x)**3', ['factorable', '1st_exact', 'Bernoulli', 'lie_group', '1st_exact_Integral', 'Bernoulli_Integral']],
  ['Derivative(f(x),x) - f(x)**(1/2)*x', ['separable', '1st_exact', 'Bernoulli', '1st_power_series', 'lie_group', 'separable_Integral', '1st_exact_Integral', 'Bernoulli_Integral']],
];

// expected values from SymPy 1.14 dsolve
const DSOLVE: [string, string][] = [
  // Euler equations with complex characteristic roots: one sin and one cos term per conjugate pair
  ['x**2*Derivative(f(x),x,x) + f(x)', 'Eq(f(x), sqrt(x)*(C1*sin(sqrt(3)*log(x)/2) + C2*cos(sqrt(3)*log(x)/2)))'],
  ['Derivative(f(x),x,x) + f(x)/x**2', 'Eq(f(x), sqrt(x)*(C1*sin(sqrt(3)*log(x)/2) + C2*cos(sqrt(3)*log(x)/2)))'],
  ['x**2*Derivative(f(x),x,x) + x*Derivative(f(x),x) + f(x)', 'Eq(f(x), C1*sin(log(x)) + C2*cos(log(x)))'],
  ['x**3*Derivative(f(x),x,3) + 3*x**2*Derivative(f(x),x,2) + 2*x*Derivative(f(x),x)', 'Eq(f(x), C1 + C2*sin(log(x)) + C3*cos(log(x)))'],
  ['x**2*Derivative(f(x),x,x) + f(x) - x', 'Eq(f(x), C1*sqrt(x)*sin(sqrt(3)*log(x)/2) + C2*sqrt(x)*cos(sqrt(3)*log(x)/2) + x)'],
  ['Derivative(f(x),x) + f(x)**2 + 2/x**2', 'Eq(f(x), (-sqrt(7)*tan(C1 + sqrt(7)*log(x)/2) + 1)/(2*x))'],
  ['Derivative(f(x),x) - a*f(x)**2 - b/x**2', 'Eq(f(x), -(-sqrt(4*a*b - 1)*tan(C1 + sqrt(4*a*b - 1)*log(x)/2) + 1)/(2*a*x))'],
  ['Derivative(f(x),x,x) - x*f(x)', 'Eq(f(x), C1*airyai(x) + C2*airybi(x))'],
  ['Derivative(f(x),x,x) + 4*x*f(x)', 'Eq(f(x), C1*airyai(-2**(2/3)*x) + C2*airybi(-2**(2/3)*x))'],
  ['x**2*Derivative(f(x),x,x) + x*Derivative(f(x),x) + (x**2 - 4)*f(x)', 'Eq(f(x), C1*besselj(2, x) + C2*bessely(2, x))'],
  ['x**2*Derivative(f(x),x,x) + x*Derivative(f(x),x) + (x**2 - 1/4)*f(x)', 'Eq(f(x), C1*besselj(1/2, x) + C2*bessely(1/2, x))'],
  ['x*Derivative(f(x),x,x) - Derivative(f(x),x)', 'Eq(f(x), C1 + C2*x**2)'],
  ['Derivative(f(x),x,3) - Derivative(f(x),x,2)/x', 'Eq(f(x), C1 + C2*x + C3*x**3)'],
  ['x**3*Derivative(f(x),x,3) + x*Derivative(f(x),x) - f(x)', 'Eq(f(x), x*(C1 + C2*log(x) + C3*log(x)**2))'],
  ['Derivative(f(x),x,x) - 2*Derivative(f(x),x) + f(x) - exp(x)/x', 'Eq(f(x), (C1 + x*(C2 + log(x)))*exp(x))'],
  ['Derivative(f(x),x) - (x + f(x) + 1)/(x - f(x) + 3)', 'Eq(log(x + 2), C1 - log(sqrt(1 + (f(x) - 1)**2/(x + 2)**2)) + atan((f(x) - 1)/(x + 2)))'],
  ['(x**2 + f(x)**2) - 2*x*f(x)*Derivative(f(x),x)', '[Eq(f(x), -sqrt(x*(C1 + x))), Eq(f(x), sqrt(x*(C1 + x)))]'],
  ['cos(f(x)) - x*sin(f(x))*Derivative(f(x),x)', '[Eq(f(x), -acos(C1/x) + 2*pi), Eq(f(x), acos(C1/x))]'],
  ['exp(f(x)) + x*exp(f(x))*Derivative(f(x),x)', 'Eq(f(x), C1 - log(x))'],
  ['Derivative(f(x),x) - f(x)*log(f(x))/x', 'Eq(f(x), exp(C1*x))'],
  ['f(x)*Derivative(f(x),x) - x', '[Eq(f(x), -sqrt(C1 + x**2)), Eq(f(x), sqrt(C1 + x**2))]'],
  ['Derivative(f(x),x)**2 - x**2', '[Eq(f(x), C1 + x**2/2), Eq(f(x), C1 - x**2/2)]'],
  ['(Derivative(f(x),x) - x)*(Derivative(f(x),x) + f(x))', '[Eq(f(x), C1 + x**2/2), Eq(f(x), C1*exp(-x))]'],
  ['Derivative(f(x),x)*(f(x) - 1)**2', 'Eq(f(x), C1)'],
  ['Derivative(f(x),x,x) - exp(x)', 'Eq(f(x), C1 + C2*x + exp(x))'],
  ['Derivative(f(x),x,x) + 3*Derivative(f(x),x) + 2*f(x) - sin(x)*exp(x)', 'Eq(f(x), C1*exp(-2*x) + C2*exp(-x) + (sin(x) - cos(x))*exp(x)/10)'],
  ['Derivative(f(x),x,x) + f(x) - x*cos(x)', 'Eq(f(x), (C1 + x/4)*cos(x) + (C2 + x**2/4)*sin(x))'],
  ['Derivative(f(x),x,4) + 2*Derivative(f(x),x,2) + f(x)', 'Eq(f(x), (C1 + C2*x)*sin(x) + (C3 + C4*x)*cos(x))'],
  ['Derivative(f(x),x,x) - 4*Derivative(f(x),x) + 13*f(x)', 'Eq(f(x), (C1*sin(3*x) + C2*cos(3*x))*exp(2*x))'],
  ['Derivative(f(x),x,x) - a**2*f(x)', 'Eq(f(x), C1*exp(-a*x) + C2*exp(a*x))'],
  ['Derivative(f(x),x,x) + I*f(x)', 'Eq(f(x), C1*exp(-x*sqrt(-I)) + C2*exp(x*sqrt(-I)))'],
  ['Derivative(f(x),x) - a*f(x) - exp(b*x)', 'Eq(f(x), C1*exp(a*x) - exp(b*x)/(a - b))'],
  ['Derivative(f(x),x) - f(x)/x - x**2*sin(x)', 'Eq(f(x), x*(C1 - x*cos(x) + sin(x)))'],
  ['Derivative(f(x),x)*x*log(x) - f(x)', 'Eq(f(x), C1*log(x))'],
  ['Derivative(f(x),x) - 3*f(x)**(2/3)', 'Eq(f(x), C1**3/27 + C1**2*x/3 + C1*x**2 + x**3)'],
  ['x**2*Derivative(f(x),x) - f(x)**2 - x*f(x)', 'Eq(f(x), x/(C1 - log(x)))'],
  ['Derivative(f(x),x) - cos(x)*f(x) - cos(x)', 'Eq(f(x), C1*exp(sin(x)) - 1)'],
  ['x*Derivative(f(x),x) + f(x) - x*exp(x)', 'Eq(f(x), C1/x + exp(x) - exp(x)/x)'],
  ['Derivative(f(x),x) - (f(x) + x)/x', 'Eq(f(x), x*(C1 + log(x)))'],
  ['Derivative(f(x),x) - x*exp(-f(x))', 'Eq(f(x), log(C1 + x**2/2))'],
  ['Derivative(f(x),x,x) + f(x)/x**2', 'Eq(f(x), sqrt(x)*(C1*sin(sqrt(3)*log(x)/2) + C2*cos(sqrt(3)*log(x)/2)))'],
];

describe('classify_ode', () => {
  it.each(CLASSIFY)('%s', (eq, hints) => {
    expect(classifyOde(parse(eq), fx).filter((h) => !UNMATCHED.has(h))).toEqual(hints);
  });
});

describe('dsolve', () => {
  it.each(DSOLVE)('%s', (eq, sol) => {
    expect(show(dsolve(parse(eq), fx))).toBe(sol);
  });
});

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/simplify/simplify.ts: the cases of SymPy 1.14 sympy/simplify/tests/test_simplify.py
// (assert simplify(e) == r), with the results SymPy 1.14 prints. acos(I) is written out as
// pi/2 - I*log(1 + sqrt(2)), the value SymPy's acos evaluates it to.

import { describe, expect, it } from 'vitest';
import { parse, simplify } from '../../src';

const cases: [string, string][] = [
  ["factorial(x)/x", "gamma(x)"],
  ["factorial(factorial(x))", "factorial(factorial(x))"],
  ["1/x + 1/y", "(x + y)/(x*y)"],
  ["A**2*s**4/(4*pi*k*m**3)", "A**2*s**4/(4*pi*k*m**3)"],
  ["(4 + 4*x - 2*(2 + 2*x))/(2 + 2*x)", "0"],
  ["(-4*x*y**2 - 2*y**3 - 2*x**2*y)/(x + y)**2", "-2*y"],
  ["-x - y - (x + y)**(-1)*y**2 + (x + y)**(-1)*x**2", "-2*y"],
  ["(x + x*y)/x", "y + 1"],
  ["(f(x) + y*f(x))/f(x)", "y + 1"],
  ["(2 * (1/n - cos(n * pi)/n))/pi", "2*(1 - cos(pi*n))/(pi*n)"],
  ["-x + y/(z + t) + z*x/(z + t) + z*a/(z + t) + t*x/(z + t)", "(a*z + y)/(t + z)"],
  ["log(2) + log(3)", "log(6)"],
  ["log(2*x) - log(2)", "log(x)"],
  ["sin(x)**2 + cos(x)**2", "1"],
  ["gamma(x + 1)/gamma(x)", "x"],
  ["sin(x)**2 + cos(x)**2 + factorial(x)/gamma(x)", "x + 1"],
  ["2**(2 + x)/4", "2**x"],
  ["exp(-1/2) + exp(-3/2)", "(1 + E)*exp(-3/2)"],
  ["E + exp(-E)", "exp(-E) + E"],
  ["(x + y)**2/(-4*x*y**2 - 2*y**3 - 2*x**2*y)", "-1/(2*y)"],
  ["-x/-y", "x/y"],
  ["-x/y", "-x/y"],
  ["x/-y", "-x/y"],
  ["-a*x/(-y - b)", "a*x/(b + y)"],
  ["(4*x + 6*f(y))/(2*x + 3*f(y))", "2"],
  ["(x + 2*y)*(2*x + 2)", "2*(x + 1)*(x + 2*y)"],
  ["2*x**2 + 4*x*y + 2*x + 4*y", "2*x**2 + 4*x*y + 2*x + 4*y"],
  ["x + csch(sinc(1))", "x + csch(sinc(1))"],
  ["asin(sin(x))", "asin(sin(x))"],
  ["cos(x)**I", "cos(x)**I"],
  ["cos(x)**(2 + 3*I)", "cos(x)**(2 + 3*I)"],
  ["Abs(x)/Abs(x**2)", "1/Abs(x)"],
  ["5*Abs((x**2 - 1)/(x - 1))", "5*Abs(x + 1)"],
  ["1/(x**3 + 1)", "1/(x**3 + 1)"],
  ["exp(x)*exp(y)", "exp(x + y)"],
  ["(x**2 - 1)/(x - 1)", "x + 1"],
  ["sqrt(y + 1)/sqrt(y - 1) - sqrt((y + 1)/(y - 1))", "-sqrt(y/(y - 1) + 1/(y - 1)) + sqrt(y + 1)/sqrt(y - 1)"],
  ["x**(1/(pi/2 - I*log(1 + sqrt(2))))", "x**(2/(pi - 2*I*log(1 + sqrt(2))))"],
  ["(pi/2 - I*log(1 + sqrt(2)))**2*(pi/2 + I*log(1 + sqrt(2)))**2", "log(1 + sqrt(2))**4 + pi**2*log(1 + sqrt(2))**2/2 + pi**4/16"],
  ["2**((pi/2 - I*log(1 + sqrt(2)))**2)", "2**((pi - 2*I*log(1 + sqrt(2)))**2/4)"],
];

describe('simplify: SymPy 1.14 test_simplify.py cases', () => {
  it.each(cases)('simplify(%s)', (e, want) => expect(String(simplify(parse(e)))).toBe(want));
  it('sign and Abs cancel exactly', () => {
    // SymPy: x (simplify rewrites sign(x) as Piecewise((0, Eq(x, 0)), (x/Abs(x), True)) and folds the Piecewise)
    expect(String(simplify(parse('sign(x)*Abs(x)')))).toBe('x');
  });
});

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/integrals/manualintegrate.ts (SymPy sqrt_quadratic_rule). Expected values are those of SymPy 1.14
// manualintegrate.

import { describe, expect, it } from 'vitest';
import { Sym, parse, sstr } from '../../src';
import { sqrtQuadraticRule } from '../../src/integrals/manualintegrate';

const x = new Sym('x');
const M = (s: string): string => {
  const r = sqrtQuadraticRule(parse(s), x);
  return r === undefined ? 'None' : sstr(r);
};

describe('sqrt_quadratic_rule', () => {
  it.each([
    ['sqrt(x**2+a*x+b)', '(a/4 + x/2)*sqrt(a*x + b + x**2) + (-a**2/8 + b/2)*Piecewise((log(a + 2*x + 2*sqrt(a*x + b + x**2)), Ne(a**2/4 - b, 0)), ((a/2 + x)*log(a/2 + x)/sqrt((a/2 + x)**2), True))'],
    ['x*sqrt(x**2+a*x+b)', '(-a*b/12 - a*(-a**2/8 + b/3)/2)*Piecewise((log(a + 2*x + 2*sqrt(a*x + b + x**2)), Ne(a**2/4 - b, 0)), ((a/2 + x)*log(a/2 + x)/sqrt((a/2 + x)**2), True)) + sqrt(a*x + b + x**2)*(-a**2/8 + a*x/12 + b/3 + x**2/3)'],
    ['x*sqrt(a*x**2+b*x+c)', 'Piecewise(((-b*c/(12*a) - b*(c/3 - b**2/(8*a))/(2*a))*Piecewise((log(2*sqrt(a)*sqrt(a*x**2 + b*x + c) + 2*a*x + b)/sqrt(a), Ne(c - b**2/(4*a), 0)), ((x + b/(2*a))*log(x + b/(2*a))/sqrt(a*(x + b/(2*a))**2), True)) + (x**2/3 + b*x/(12*a) + (c/3 - b**2/(8*a))/a)*sqrt(a*x**2 + b*x + c), Ne(a, 0)), (2*(-c*(b*x + c)**(3/2)/3 + (b*x + c)**(5/2)/5)/b**2, Ne(b, 0)), (sqrt(c)*x**2/2, True))'],
    ['sqrt(a*x**2+b*x+c)', 'Piecewise(((c/2 - b**2/(8*a))*Piecewise((log(2*sqrt(a)*sqrt(a*x**2 + b*x + c) + 2*a*x + b)/sqrt(a), Ne(c - b**2/(4*a), 0)), ((x + b/(2*a))*log(x + b/(2*a))/sqrt(a*(x + b/(2*a))**2), True)) + (x/2 + b/(4*a))*sqrt(a*x**2 + b*x + c), Ne(a, 0)), (2*(b*x + c)**(3/2)/(3*b), Ne(b, 0)), (sqrt(c)*x, True))'],
    ['(x**2+1)*sqrt(a*x**2+b*x+c)', 'Piecewise(((c - b*(b - b*c/(12*a) - 3*b*(a + c/4 - 5*b**2/(48*a))/(4*a))/(2*a) - c*(a + c/4 - 5*b**2/(48*a))/(2*a))*Piecewise((log(2*sqrt(a)*sqrt(a*x**2 + b*x + c) + 2*a*x + b)/sqrt(a), Ne(c - b**2/(4*a), 0)), ((x + b/(2*a))*log(x + b/(2*a))/sqrt(a*(x + b/(2*a))**2), True)) + sqrt(a*x**2 + b*x + c)*(x**3/4 + b*x**2/(24*a) + x*(a + c/4 - 5*b**2/(48*a))/(2*a) + (b - b*c/(12*a) - 3*b*(a + c/4 - 5*b**2/(48*a))/(4*a))/a), Ne(a, 0)), (2*(-2*c*(b*x + c)**(5/2)/(5*b**2) + (b**2 + c**2)*(b*x + c)**(3/2)/(3*b**2) + (b*x + c)**(7/2)/(7*b**2))/b, Ne(b, 0)), (sqrt(c)*(x**3/3 + x), True))'],
    ['x**2/sqrt(x**2+a*x+b)', '(-3*a/4 + x/2)*sqrt(a*x + b + x**2) + (3*a**2/8 - b/2)*Piecewise((log(a + 2*x + 2*sqrt(a*x + b + x**2)), Ne(a**2/4 - b, 0)), ((a/2 + x)*log(a/2 + x)/sqrt((a/2 + x)**2), True))'],
    ['x**3/sqrt(a*x**2+b*x+c)', 'Piecewise(((-b*(-2*c/(3*a) + 5*b**2/(8*a**2))/(2*a) + 5*b*c/(12*a**2))*Piecewise((log(2*sqrt(a)*sqrt(a*x**2 + b*x + c) + 2*a*x + b)/sqrt(a), Ne(c - b**2/(4*a), 0)), ((x + b/(2*a))*log(x + b/(2*a))/sqrt(a*(x + b/(2*a))**2), True)) + (x**2/(3*a) + (-2*c/(3*a) + 5*b**2/(8*a**2))/a - 5*b*x/(12*a**2))*sqrt(a*x**2 + b*x + c), Ne(a, 0)), (2*(-c**3*sqrt(b*x + c) + c**2*(b*x + c)**(3/2) - 3*c*(b*x + c)**(5/2)/5 + (b*x + c)**(7/2)/7)/b**4, Ne(b, 0)), (x**4/(4*sqrt(c)), True))'],
    ['(2*x+a)*sqrt(x**2+a*x+b)', '(2*a*x/3 + 2*b/3 + 2*x**2/3)*sqrt(a*x + b + x**2)'],
    ['sqrt(2*x**2+a*x+b)', '(a/8 + x/2)*sqrt(a*x + b + 2*x**2) + (-a**2/16 + b/2)*Piecewise((sqrt(2)*log(a + 4*x + 2*sqrt(2)*sqrt(a*x + b + 2*x**2))/2, Ne(a**2/8 - b, 0)), (sqrt(2)*(a/4 + x)*log(a/4 + x)/(2*sqrt((a/4 + x)**2)), True))'],
    ['x*sqrt(x**2+a*x)', 'a**3*Piecewise((log(a + 2*x + 2*sqrt(a*x + x**2)), Ne(a**2, 0)), ((a/2 + x)*log(a/2 + x)/sqrt((a/2 + x)**2), True))/16 + sqrt(a*x + x**2)*(-a**2/8 + a*x/12 + x**2/3)'],
    ['x*sqrt(a*x**2+2*x)', 'Piecewise((sqrt(a*x**2 + 2*x)*(x**2/3 + x/(6*a) - 1/(2*a**2)) + Piecewise((log(2*sqrt(a)*sqrt(a*x**2 + 2*x) + 2*a*x + 2)/sqrt(a), Ne(1/a, 0)), ((x + 1/a)*log(x + 1/a)/sqrt(a*(x + 1/a)**2), True))/(2*a**2), Ne(a, 0)), (2*sqrt(2)*x**(5/2)/5, True))'],
    ['sqrt(a*x**2+2*x+b)', 'Piecewise(((b/2 - 1/(2*a))*Piecewise((log(2*sqrt(a)*sqrt(a*x**2 + b + 2*x) + 2*a*x + 2)/sqrt(a), Ne(b - 1/a, 0)), ((x + 1/a)*log(x + 1/a)/sqrt(a*(x + 1/a)**2), True)) + (x/2 + 1/(2*a))*sqrt(a*x**2 + b + 2*x), Ne(a, 0)), ((b + 2*x)**(3/2)/3, True))'],
  ])('%s', (f, want) => expect(M(f)).toBe(want));

  it('applies to symbolic coefficients with b != 0 and odd powers 1 and -1 only', () => {
    // SymPy integrate: sqrt(a)*x*sqrt(1 + x**2/a)/2 + a*asinh(x/sqrt(a))/2 (meijerint before manualintegrate)
    expect(M('sqrt(x**2+a)')).toBe('None');
    // real coefficients: SymPy chooses asinh (integrate handles them itself)
    expect(M('sqrt(x**2+x+1)')).toBe('None');
    // a numerator of degree below 2 under 1/sqrt (SymPy: inverse_trig_rule)
    expect(M('1/sqrt(x**2+a*x+b)')).toBe('None');
    expect(M('(x**2+a*x+b)**(3/2)')).toBe('None');
    expect(M('x*sqrt(x**3+a)')).toBe('None');
    expect(M('sin(x)*sqrt(x**2+a*x+1)')).toBe('None');
    expect(M('exp(x)')).toBe('None');
  });
});

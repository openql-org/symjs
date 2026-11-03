// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Limits that reach the branches of series/limits.ts. Expected values are the str() forms
// printed by SymPy 1.14 (p is a positive, q a negative and r a real symbol; f and g are functions).

import { describe, expect, it } from 'vitest';
import { Sym, limit, parse } from '../src';

const syms = [new Sym('p', { positive: true }), new Sym('q', { negative: true }), new Sym('r', { real: true })];
const P = (s: string) => parse(s, { symbols: syms });
const V = (s: string): Sym => {
  const v = P(s);
  if (!(v instanceof Sym)) throw new TypeError(s);
  return v;
};
const lim = (e: string, v: string, p: string, d: '+' | '-' | '+-' = '+') => String(limit(P(e), V(v), P(p), d));

const cases: [string, string, string, '+' | '-' | '+-', string][] = [
  ["1/(f(y) + x)", "x", "0", "+", "1/f(y)"],
  ["1/(x - I)", "x", "I", "+", "oo"],
  ["1/(x - a)", "x", "a", "+", "oo"],
  ["1/(x*p)", "x", "0", "+", "oo"],
  ["1/(x*y)", "x", "0", "+", "oo*sign(1/y)"],
  ["log(x)", "x", "I", "+", "I*pi/2"],
  ["log(x - 1 - 1/1000000)", "x", "1", "+", "-log(1000000) + I*pi"],
  ["log(x)*g(2)", "x", "2", "+", "g(2)*log(2)"],
  ["floor(1/x)", "x", "oo", "+", "0"],
  ["floor(1/x)", "x", "-oo", "+", "-1"],
  ["floor(p*x)", "x", "0", "+", "0"],
  ["floor(q*x)", "x", "0", "+", "-1"],
  ["sign(x*y)", "x", "0", "+", "sign(y)"],
  ["sign(p*x)", "x", "0", "-", "-1"],
  ["log(-x - I)", "x", "oo", "+", "oo"],
  ["sin(x) + x", "x", "oo", "+", "oo"],
  ["sin(x)/x", "x", "oo", "+", "0"],
  ["(1 + I)*x", "x", "oo", "+", "oo*sign(1 + I)"],
  ["(sqrt(2) - 1)*x", "x", "oo", "+", "oo"],
  ["-(sqrt(2) - 1)*x", "x", "oo", "+", "-oo"],
  ["(1/x)**(-1/x)", "x", "0", "+", "0"],
  ["(x + I*x)**(-1)", "x", "oo", "+", "0"],
  ["(x + I*x)**(-2)", "x", "oo", "+", "0"],
  ["(1 - cos(a)**2 - sin(a)**2 + x)**(-1)", "x", "0", "+", "oo"],
  ["2**((1 + I)*x)", "x", "oo", "+", "zoo"],
  ["2**((-1 + I)*x)", "x", "oo", "+", "0"],
  ["exp((sqrt(2) - 1)*x)", "x", "oo", "+", "oo"],
  ["exp(-(sqrt(2) - 1)*x)", "x", "oo", "+", "0"],
  ["(-x)**x", "x", "oo", "+", "zoo"],
  ["atan2(x, 1)", "x", "oo", "+", "pi/2"],
  ["besselj(x, 1)", "x", "0", "+", "besselj(0, 1)"],
  ["sin(zoo*x)", "x", "1", "+", "Limit(sin(zoo*x), x, 1, dir='+')"],
  ["gamma(x)", "x", "oo", "+", "oo"],
  ["tan(x)", "x", "pi/2", "-", "oo"],
  ["tan(x)", "x", "pi/2", "+", "-oo"],
  ["cot(x)", "x", "0", "+", "oo"],
  ["exp(1/x)*exp(-1/x)*x", "x", "0", "+", "0"],
  ["exp(1/sin(x))*exp(-cot(x))*x", "x", "0", "+", "0"],
  ["sin(1/x)*x", "x", "0", "+", "0"],
  ["log(x)*exp(-x)*x", "x", "oo", "+", "0"],
  ["(exp(x) - 1)/x + exp(x)", "x", "0", "+", "2"],
  ["(2**x - 1)/x", "x", "0", "+", "log(2)"],
  ["x/log(x)", "x", "oo", "+", "oo"],
  ["x**2/log(x)", "x", "oo", "-", "oo"],
  ["log(x)/sqrt(x)", "x", "oo", "+", "0"],
  ["-x/log(x)", "x", "oo", "+", "-oo"],
  ["exp(x)/x", "x", "oo", "+", "oo"],
  ["-exp(x)/x", "x", "oo", "+", "-oo"],
  ["x*exp(-x)*log(x)", "x", "oo", "+", "0"],
  ["(x - sin(x))/x**3", "x", "0", "+", "1/6"],
  ["x/(x+1)", "x", "oo", "+-", "1"],
  ["1/x", "x", "0", "+-", "zoo"],
  ["1/x**2", "x", "0", "+-", "oo"],
  ["x", "x", "nan", "+", "nan"],
  ["y", "x", "nan", "+", "y"],
  ["x", "x", "oo*I", "+", "oo*I"],
  ["1/x", "x", "oo*I", "+", "0"],
  ["factorial(x)/factorial(x + 1)", "x", "oo", "+", "0"],
  ["factorial(x + 1)/factorial(x)", "x", "oo", "+", "oo"],
  ["binomial(x, 2)/x**2", "x", "oo", "+", "1/2"],
  ["gamma(x + 1/2)/(gamma(x)*sqrt(x))", "x", "oo", "+", "1"],
  ["g(2)/x", "x", "0", "+", "oo*sign(g(2))"],
  ["1/(2**x - 1)", "x", "0", "+", "oo"],
  ["1/(2**x - 1)", "x", "0", "-", "-oo"],
  ["1/(I*x)", "x", "0", "+", "-oo*I"],
  ["1/(p*exp(r))", "p", "0", "+", "oo"],
  ["1/(q*exp(r))", "q", "0", "-", "-oo"],
  ["log(x*g(2))", "x", "1", "+", "log(g(2))"],
  ["sin(x)/x*log(-1 + I*x)", "x", "0", "+", "I*pi"],
  ["x*y", "x", "-oo", "+", "-oo*sign(y)"],
  ["(x + I)**2", "x", "oo", "+", "oo"],
  ["(x + I)**(1/2)", "x", "oo", "+", "oo"],
  ["sign(sin(x))", "x", "0", "+", "1"],
  ["sign(-sin(x))", "x", "0", "+", "-1"],
  ["sign(x*y)", "x", "0", "+", "sign(y)"],
  ["sign(1 + x)", "x", "0", "+", "1"],
  ["sign(I + x)", "x", "0", "+", "I"],
  ["exp(x)/(x*y)", "x", "oo", "+", "oo*sign(1/y)"],
  ["x**5*exp(-x)", "x", "oo", "+", "0"],
  ["x**2", "x", "nan", "+", "nan"],
  ["x + I*x**2", "x", "oo", "+", "oo*I"],
  ["-x + I", "x", "oo", "+", "-oo"],
  ["x + oo*I", "x", "oo", "+", "Limit(x + oo*I, x, oo, dir='-')"],
  ["exp(1/sin(x))*exp(-cot(x))", "x", "0", "+", "1"],
  ["cot(x) - 1/x", "x", "0", "+", "0"],
  ["tan(x) - 1/(pi/2 - x)", "x", "pi/2", "-", "0"],
  ["csc(x) - 1/x", "x", "0", "+", "0"],
  ["sec(x)*(x - pi/2)", "x", "pi/2", "+", "-1"],
  ["tanh(x)*(x - I*pi/2)", "x", "I*pi/2", "+", "1"],
  ["sech(x)*(x - I*pi/2)", "x", "I*pi/2", "+", "-I"],
  ["LambertW(x)/x", "x", "0", "+", "1"],
  ["acosh(x)/sqrt(x - 1)", "x", "1", "+", "sqrt(2)"],
  ["acosh(-x)/sqrt(x - 1)", "x", "1", "+", "oo*I"],
  ["(1 - cos(a)**2 - sin(a)**2 + x)**(-1)", "x", "0", "+", "oo"],
  ["sin(x)*sin(1/x)", "x", "0", "+", "0"],
  ["(1 + x)**(1/x)", "x", "0", "+", "E"],
  ["(1 + sin(x))**(1/x)", "x", "0", "+", "E"],
  ["x**x", "x", "0", "+", "1"],
  ["(sin(x))**x", "x", "0", "+", "1"],
  ["abs((-x/(x + 1))**x)", "x", "oo", "+", "exp(-1)"],
  ["log(1 + x)/x", "x", "0", "+", "1"],
  ["log(sin(x))", "x", "0", "+", "-oo"],
  ["log(-x)", "x", "0", "+", "-oo"],
  ["ceiling(x)", "x", "1", "+", "2"],
  ["ceiling(x)", "x", "1", "-", "1"],
  ["floor(x)", "x", "1", "-", "0"],
  ["floor(x**2)", "x", "0", "+", "0"],
  ["ceiling(-x**2)", "x", "0", "+", "0"],
  ["cos(1/x)*x", "x", "0", "+", "0"],
  ["sin(x)**2 + cos(x)**2 + x", "x", "oo", "+", "oo"],
  ["(x**2 + 1)**(1/x)", "x", "oo", "+", "1"],
  ["(2*x)**(1/log(x))", "x", "oo", "+", "E"],
  ["atan(x)", "x", "oo", "+", "pi/2"],
  ["atan(1/x)", "x", "0", "-", "-pi/2"],
  ["acot(x)", "x", "0", "-", "-pi/2"],
  ["erf(x)", "x", "oo", "+", "1"],
  ["x/sqrt(x**2 + 1)", "x", "-oo", "+", "-1"],
  ["x*(exp(1/x) - 1)", "x", "oo", "+", "1"],
  ["exp(-1/x)/x", "x", "0", "+", "0"],
  ["exp(1/x)", "x", "0", "-", "0"],
  ["x*log(x)", "x", "0", "+", "0"],
  ["log(x)**2*x", "x", "0", "+", "0"],
  ["x**(1/x)", "x", "oo", "+", "1"],
  ["(log(x) - log(2))/(x - 2)", "x", "2", "+", "1/2"],
  ["Abs(x)/x", "x", "0", "-", "-1"],
  ["re(x + I*x)", "x", "1", "+", "1"],
  ["Max(x, 1)", "x", "2", "+", "2"],
  ["1/(x**2 + I*x)", "x", "0", "+", "-oo*I"],
  ["1/(p + p**2*exp(r))", "p", "0", "+", "oo"],
  ["1/(q - q**2*exp(r))", "q", "0", "-", "-oo"],
  ["(exp(x) + x)/(x*I + 1)", "x", "oo", "+", "-oo*I"],
  ["(x + x**2*Ei(x))/x**2", "x", "0", "+", "oo"],
  ["(x + x**2*Ei(x))/x**2", "x", "0", "-", "-oo"],
  ["(-x + x**2*Ei(x))/x**2", "x", "0", "+", "-oo"],
  ["(x + x**2*li(x))/x**2", "x", "0", "+", "oo"],
  ["x*y + 1", "x", "oo", "+", "oo*sign(y)"],
  ["x*y + I", "x", "oo", "+", "oo*sign(y)"],
  ["x*y + sin(x)", "x", "oo", "+", "oo*sign(y)"],
  ["x - I", "x", "oo", "+", "oo"],
  ["x**2 + I*x", "x", "oo", "+", "oo"],
  ["sin(x)**2 + cos(x)**2 + x", "x", "oo", "+", "oo"],
  ["x**2 - 1", "x", "-oo*I", "+", "-oo"],
  ["x + sqrt(x*y)", "x", "oo", "+", "oo"],
  ["x - sqrt(x*y + 1)", "x", "oo", "+", "oo"],
  ["(x + I)*(x + 2) + x", "x", "oo", "+", "oo"],
  ["(x + I)*(x + 2)", "x", "oo", "+", "oo"],
  ["x + x**I", "x", "oo", "+", "oo"],
  ["(1 + I)**(-x)", "x", "oo", "+", "0"],
  ["(I/2)**x", "x", "oo", "+", "0"],
  ["(-2)**x", "x", "oo", "+", "zoo"],
  ["(-1/2)**x", "x", "oo", "+", "0"],
  ["x**(I*x)*(x + 1)**(-I*x)", "x", "oo", "+", "exp(-I)"],
];

describe('limits: results equal SymPy 1.14', () => {
  it.each(cases)('limit(%s, %s, %s, %s) = %s', (e, v, p, d, expected) => {
    expect(lim(e, v, p, d)).toBe(expected);
  });
});

describe('limits that symjs leaves unevaluated, or answers differently from SymPy 1.14', () => {
  // [expression, variable, point, direction, symjs result, SymPy 1.14 result]
  const unevaluated: [string, string, string, '+' | '-' | '+-', string, string][] = [
    // AccumBounds results are not implemented: the bounded value stays a Limit
    ['sin(x) + 1/x', 'x', 'oo', '+', "Limit(sin(x) + 1/x, x, oo, dir='-')", 'AccumBounds(-1, 1)'],
    ['sin(x)*x', 'x', 'oo', '+', "Limit(x*sin(x), x, oo, dir='-')", 'oo*sign(AccumBounds(-1, 1))'],
    ['sin(x)*cos(x)', 'x', 'oo', '+', "Limit(sin(x)*cos(x), x, oo, dir='-')", 'AccumBounds(-1, 1)'],
    ['sin(x)', 'x', '-oo', '+', "Limit(sin(x), x, -oo, dir='+')", 'AccumBounds(-1, 1)'],
    ['sin(1/x)', 'x', '0', '+-', "Limit(sin(1/x), x, 0, dir='+-')", 'AccumBounds(-1, 1)'],
    ['sin(x)*factorial(x)/factorial(x - 1)', 'x', 'oo', '+', "Limit(sin(x)*factorial(x)/factorial(x - 1), x, oo, dir='-')", 'AccumBounds(-oo, oo)'],
    // a function of an argument tending to an infinity off the real axis (other than log)
    ['atan(-x - I)', 'x', 'oo', '+', "Limit(-atan(x + I), x, oo, dir='-')", '-pi/2'],
    ['atan(x + I)*exp(-x)', 'x', 'oo', '+', "Limit(exp(-x)*atan(x + I), x, oo, dir='-')", '0'],
    // on a branch cut from the side the expansion does not see (the principal values differ)
    ['sin(x)/x*log(-1 + I*x)', 'x', '0', '-', "Limit(log(I*x - 1)*sin(x)/x, x, 0, dir='-')", '-I*pi'],
    ['sqrt(I*x - 1)', 'x', '0', '-', "Limit(sqrt(I*x - 1), x, 0, dir='-')", '-I'],
    // an exponent with a symbolic direction, or an imaginary one (SymPy gives nan or raises)
    ['2**(x*y)', 'x', 'oo', '+', "Limit(2**(x*y), x, oo, dir='-')", 'exp(oo*sign(y))'],
    ['2**(-I*x)', 'x', 'oo', '+', "Limit(2**(-I*x), x, oo, dir='-')", 'nan'],
    ['(1/2)**(I*x)', 'x', 'oo', '+', "Limit((1/2)**(I*x), x, oo, dir='-')", 'nan'],
    ['I**x', 'x', 'oo', '+', "Limit(I**x, x, oo, dir='-')", 'nan'],
    ['y**x', 'x', 'oo', '+', "Limit(y**x, x, oo, dir='-')", 'exp(oo*sign(log(y)))'],
    ['x*exp(I*x)', 'x', 'oo', '+', "Limit(x*exp(I*x), x, oo, dir='-')", 'NotImplementedError'],
    ['x**(I*x)*(x + 1)**(I*x)', 'x', 'oo', '+', "Limit(x**(I*x)*(x + 1)**(I*x), x, oo, dir='-')", 'NotImplementedError'],
    // more than 12 steps of L'Hopital's rule
    ['x**13*exp(-x)', 'x', 'oo', '+', "Limit(x**13*exp(-x), x, oo, dir='-')", '0'],
    // the quotient does not settle numerically at 10**7 (erfc underflows)
    ['erfc(x)/(1 - erf(x))**2', 'x', 'oo', '+', "Limit(erfc(x)/(1 - erf(x))**2, x, oo, dir='-')", '0'],
    // the Gamma functions do not cancel in the asymptotic form
    ['gamma(x**2)/gamma(x)', 'x', 'oo', '+', "Limit(gamma(x**2)/gamma(x), x, oo, dir='-')", 'oo'],
    // SymPy raises NotImplementedError for these
    ['x**y', 'x', '0', '+', "Limit(x**y, x, 0, dir='+')", 'NotImplementedError'],
    ['floor(y*x)', 'x', '0', '+', "Limit(floor(x*y), x, 0, dir='+')", 'NotImplementedError'],
    ['floor(sin(pi*x)/x)', 'x', 'oo', '+', "Limit(floor(sin(pi*x)/x), x, oo, dir='-')", 'NotImplementedError'],
    ['atan2(1/x, sin(x))', 'x', 'oo', '+', "Limit(atan2(1/x, sin(x)), x, oo, dir='-')", 'NotImplementedError'],
    ['exp(x)', 'x', '-oo*I', '+', "Limit(exp(x), x, -oo*I, dir='+')", 'NotImplementedError'],
  ];
  it.each(unevaluated)('limit(%s, %s, %s, %s) = %s (SymPy: %s)', (e, v, p, d, expected) => {
    expect(lim(e, v, p, d)).toBe(expected);
  });

  // [expression, variable, point, direction, symjs result (the mathematically correct one), SymPy 1.14 result]
  const correct: [string, string, string, '+' | '-' | '+-', string, string][] = [
    // coth(x) = 1/x + x/3 + O(x**3) and csch(x) = 1/x - x/6 + O(x**3)
    ['coth(x) - 1/x', 'x', '0', '+', '0', '-oo'],
    ['csch(x) - 1/x', 'x', '0', '+', '0', '-oo'],
    // |(I*x)**x| = x**x -> oo while the argument x*pi/2 turns: no direction
    ['(I*x)**x', 'x', 'oo', '+', 'zoo', 'oo'],
    // SymPy raises NotImplementedError: a bounded oscillation plus x, and |(1 + I)**x| -> oo
    ['exp((2 + I)*x)', 'x', '-oo', '+', '0', 'NotImplementedError'],
    ['x + I**x', 'x', 'oo', '+', 'oo', 'NotImplementedError'],
    ['x + 2**(I*x)', 'x', 'oo', '+', 'oo', 'NotImplementedError'],
    ['exp(I*x) + x', 'x', 'oo', '+', 'oo', 'NotImplementedError'],
    ['x*(1 + I)**x', 'x', 'oo', '+', 'zoo', 'NotImplementedError'],
    ['exp(-x)', 'x', 'oo*(1 + I)', '+', '0', 'NotImplementedError'],
    // SymPy keeps (sqrt(2) - 1)*oo + x as oo + x and leaves the limit unevaluated
    ['2**((sqrt(2) - 1)*oo + x)', 'x', '0', '+', 'oo', "Limit(2**(x + oo), x, 0, dir='+')"],
    // J1(I*y) = I*I1(y) -> oo*I (SymPy keeps besselj(1, oo*I) or the Limit)
    ['besselj(1, x)', 'x', 'oo*I', '+', 'oo*I', 'besselj(1, oo*I)'],
    ['besselj(1, x)', 'x', '-oo*I', '+', '-oo*I', "Limit(besselj(1, x), x, -oo*I, dir='+')"],
    // the same value: SymPy writes sign(1/y) as 1/sign(y)
    ['(exp(x) + x)/(x*y + 1)', 'x', 'oo', '+', 'oo*sign(1/y)', 'oo/sign(y)'],
    ['(-exp(x) - x)/(x*y + 1)', 'x', 'oo', '+', '-oo*sign(1/y)', '-oo/sign(y)'],
  ];
  it.each(correct)('limit(%s, %s, %s, %s) = %s (SymPy: %s)', (e, v, p, d, expected) => {
    expect(lim(e, v, p, d)).toBe(expected);
  });

  it('raises where SymPy raises', () => {
    // SymPy: ValueError (the one-sided limits differ)
    expect(() => lim('sign(x)', 'x', '0', '+-')).toThrow(RangeError);
    // SymPy: NotImplementedError (limits at complex infinity)
    expect(() => lim('5', 'x', 'zoo')).toThrow('complex infinity');
    expect(() => lim('x**2', 'x', 'zoo')).toThrow('complex infinity');
  });

  it('nests deeper than 60 levels (the structural recursion stops, the expansion goes on)', () => {
    let e = 'x';
    for (let i = 0; i < 62; i++) e = `sin(${e})`;
    expect(lim(e, 'x', '0')).toBe('0');
  });
});

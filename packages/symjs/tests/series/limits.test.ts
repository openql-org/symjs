// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/series/limits.ts.
// Limits. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { Sym, limit, parse, DiracDelta, Heaviside, symbol, oo } from '../../src';
import { limitWithin } from '../../src/series/limits';
import { Expr } from '../../src/core/nodes';
import { NoMatchResult } from '../../src/core/truth';

// Limits that reach the branches of series/limits.ts. Expected values are the str() forms
// printed by SymPy 1.14 (p is a positive, q a negative and r a real symbol; f and g are functions).

const syms = [new Sym('p', { positive: true }), new Sym('q', { negative: true }), new Sym('r', { real: true })];
const P = (s: string) => parse(s, { symbols: syms });
const V = (s: string): Sym => {
  const v = P(s);
  if (!(v instanceof Sym)) throw new TypeError(s);
  return v;
};
const lim = (e: string, v: string, p: string, d: '+' | '-' | '+-' = '+') => String(limit(P(e), V(v), P(p), d));

const cases: [string, string, string, '+' | '-' | '+-', string][] = [
  // powers with a common exponent are combined first (SymPy Limit.doit powsimp): ((1 + I)/2)**n
  ["(1 + I)**n/2**n", "n", "oo", "+", "0"],
  ["(1 - I)**n/3**n", "n", "oo", "+", "0"],
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
  ["sin(x) + 1/x", "x", "oo", "+", "AccumBounds(-1, 1)"],
  ["sin(x)*cos(x)", "x", "oo", "+", "AccumBounds(-1, 1)"],
  ["sin(x)", "x", "-oo", "+", "AccumBounds(-1, 1)"],
  ["sin(1/x)", "x", "0", "+-", "AccumBounds(-1, 1)"],
  ["atan(-x - I)", "x", "oo", "+", "-pi/2"],
  ["atan(x + I)*exp(-x)", "x", "oo", "+", "0"],
  ["sin(x)/x*log(-1 + I*x)", "x", "0", "-", "-I*pi"],
  ["sqrt(I*x - 1)", "x", "0", "-", "-I"],
  ["x**13*exp(-x)", "x", "oo", "+", "0"],
  ["gamma(x**2)/gamma(x)", "x", "oo", "+", "oo"],
  // the Gruntz algorithm, intervals and branch cuts (SymPy 1.14)
  ["3**x", "x", "oo", "+", "oo"],
  ["acoth(sin(x))", "x", "0", "+", "-I*pi/2"],
  ["acoth(x)", "x", "0", "-", "I*pi/2"],
  ["acsc(exp(x))", "x", "oo", "-", "0"],
  ["asec(x)", "x", "0", "+", "oo*I"],
  ["acsc(I*x)", "x", "0", "+", "-oo*I"],
  ["acsc(I*x)", "x", "0", "-", "oo*I"],
  ["x**x*sin(1/x)", "x", "0", "+", "AccumBounds(-1, 1)"],
  ["sin(x)/(1 + 1/x)", "x", "oo", "+", "AccumBounds(-1, 1)"],
  ["(1/x - 1/(x*(1 + x)))*sin(1/x)", "x", "0", "+", "AccumBounds(-1, 1)"],
  ["(sin(x) - 2)**(1/x)", "x", "oo", "+", "Limit((sin(x) - 2)**(1/x), x, oo, dir='-')"],
  ["log(sin(x) - 2)", "x", "oo", "+", "Limit(log(sin(x) - 2), x, oo, dir='-')"],
  ["tan(x)/x", "x", "oo", "+", "Limit(tan(x)/x, x, oo, dir='-')"],
  ["cot(I*x)", "x", "0", "+", "-oo*I"],
  ["cot(-I*x)", "x", "0", "+", "oo*I"],
  ["(-1)**(-I*x)", "x", "oo", "+", "oo"],
  ["sin(1/x)*log(x) + factorial(1/x)", "x", "0", "+", "oo"],
  ["cot(x*f(1))", "x", "0", "+", "oo*sign(1/f(1))"],
  ["I/x - I/sin(x)", "x", "0", "+", "0"],
  ["coth(I*x)", "x", "0", "+", "-oo*I"],
  ["factorial(1/x) - 1/x", "x", "0", "+", "oo"],
  ["x**2*sin(1/x) + 1/x - 1/sin(x)", "x", "0", "+", "0"],
];

describe('limits: results equal SymPy 1.14', () => {
  it.each(cases)('limit(%s, %s, %s, %s) = %s', (e, v, p, d, expected) => {
    expect(lim(e, v, p, d)).toBe(expected);
  });
});

describe('limits that symjs leaves unevaluated, or answers differently from SymPy 1.14', () => {
  // [expression, variable, point, direction, symjs result, SymPy 1.14 result]
  const unevaluated: [string, string, string, '+' | '-' | '+-', string, string][] = [
    // the exponential growth of besseli and Ei at infinity is not known to the Gruntz algorithm here
    ["besseli(1, 1/x) - exp(1/x)", "x", "0", "+", "Limit(-exp(1/x) + besseli(1, 1/x), x, 0, dir='+')", "-oo"],
    ["Ei(1/x) - exp(1/x)/x", "x", "0", "+", "Limit(Ei(1/x) - exp(1/x)/x, x, 0, dir='+')", "-oo"],
    ["gamma(1/x)*sin(1/x) + 1/x", "x", "0", "+", "Limit(sin(1/x)*gamma(1/x) + 1/x, x, 0, dir='+')", "oo*sign(AccumBounds(-1, 1))"],
    ["x*exp(I*x)", "x", "-oo", "+", "Limit(x*exp(I*x), x, -oo, dir='+')", "NotImplementedError"],
    ["(cos(x) + 1)**(1/x)", "x", "oo", "+", "Limit((cos(x) + 1)**(1/x), x, oo, dir='-')", "AccumBounds(0, 1)"],
    ["sin(1/x)*log(x)*x", "x", "0", "+", "Limit(x*log(x)*sin(1/x), x, 0, dir='+')", "0"],
    ["1/(x*(1 + x)) - 1/x + sin(1/x)", "x", "0", "+", "Limit(sin(1/x) - 1/x + 1/(x*(x + 1)), x, 0, dir='+')", "AccumBounds(-2, 0)"],
    // the argument-wise evaluation stops after 12 nested levels
    ["sin(sin(sin(sin(sin(sin(sin(sin(sin(sin(sin(sin(sin(sin(sin(1/x)))))))))))))))", "x", "0", "+", "Limit(sin(sin(sin(sin(sin(sin(sin(sin(sin(sin(sin(sin(sin(sin(sin(1/x))))))))))))))), x, 0, dir='+')", "AccumBounds(-sin(sin(sin(sin(sin(sin(sin(sin(sin(sin(sin(sin(sin(sin(1)))))))))))))), sin(sin(sin(sin(sin(sin(sin(sin(sin(sin(sin(sin(sin(sin(1)))))))))))))))"],
    // undecided: the product of the side value with 0*oo, an interval times a vanishing factor,
    // a direction that depends on the sign of y
    ["sin(x)/x*asin(2 + I*x)", "x", "0", "+", "Limit(sin(x)*asin(I*x + 2)/x, x, 0, dir='+')", "pi - asin(2)"],
    ["sin(x)*sin(1/x)/x", "x", "0", "+", "Limit(sin(1/x)*sin(x)/x, x, 0, dir='+')", "AccumBounds(-1, 1)"],
    ["floor(x)*sin(x)", "x", "oo", "+", "Limit(sin(x)*floor(x), x, oo, dir='-')", "oo*sign(AccumBounds(-1, 1))"],
    ["acoth(x*y)", "x", "0", "+", "Limit(acoth(x*y), x, 0, dir='+')", "-log(-1/y)/2 + log(1/y)/2"],
    // the same interval: SymPy writes oo*AccumBounds(-1, 1) as oo*sign(AccumBounds(-1, 1))
    ["sin(1/x)/(x**2 + x)", "x", "0", "+", "AccumBounds(-oo, oo)", "oo*sign(AccumBounds(-1, 1))"],
    // an infinite value in the direction I
    ["asec(exp(1/x))", "x", "0", "-", "Limit(asec(exp(1/x)), x, 0, dir='-')", "oo*I"],
    // the same interval: SymPy writes oo*AccumBounds(-1, 1) as oo*sign(AccumBounds(-1, 1))
    ["sin(x)*x", "x", "oo", "+", "AccumBounds(-oo, oo)", "oo*sign(AccumBounds(-1, 1))"],
    ["sin(x)*factorial(x)/factorial(x - 1)", "x", "oo", "+", "Limit(sin(x)*factorial(x)/factorial(x - 1), x, oo, dir='-')", "AccumBounds(-oo, oo)"],
    // an exponent with a symbolic direction, or an imaginary one (SymPy gives nan or raises)
    ["2**(x*y)", "x", "oo", "+", "Limit(2**(x*y), x, oo, dir='-')", "exp(oo*sign(y))"],
    ["2**(-I*x)", "x", "oo", "+", "Limit(2**(-I*x), x, oo, dir='-')", "nan"],
    ["(1/2)**(I*x)", "x", "oo", "+", "Limit((1/2)**(I*x), x, oo, dir='-')", "nan"],
    ["I**x", "x", "oo", "+", "Limit(I**x, x, oo, dir='-')", "nan"],
    ["y**x", "x", "oo", "+", "Limit(y**x, x, oo, dir='-')", "exp(oo*sign(log(y)))"],
    ["x*exp(I*x)", "x", "oo", "+", "Limit(x*exp(I*x), x, oo, dir='-')", "NotImplementedError"],
    ["x**(I*x)*(x + 1)**(I*x)", "x", "oo", "+", "Limit(x**(I*x)*(x + 1)**(I*x), x, oo, dir='-')", "NotImplementedError"],
    // the quotient does not settle numerically at 10**7 (erfc underflows)
    ["erfc(x)/(1 - erf(x))**2", "x", "oo", "+", "Limit(erfc(x)/(1 - erf(x))**2, x, oo, dir='-')", "0"],
    // SymPy raises NotImplementedError for these
    ["x**y", "x", "0", "+", "Limit(x**y, x, 0, dir='+')", "NotImplementedError"],
    ["floor(y*x)", "x", "0", "+", "Limit(floor(x*y), x, 0, dir='+')", "NotImplementedError"],
    ["floor(sin(pi*x)/x)", "x", "oo", "+", "Limit(floor(sin(pi*x)/x), x, oo, dir='-')", "NotImplementedError"],
    ["atan2(1/x, sin(x))", "x", "oo", "+", "Limit(atan2(1/x, sin(x)), x, oo, dir='-')", "NotImplementedError"],
    ["exp(x)", "x", "-oo*I", "+", "Limit(exp(x), x, -oo*I, dir='+')", "NotImplementedError"],
    // L'Hopital's rule needs the derivative of besselj with respect to its order, which is not implemented
    ["(besselj(x, 1) - besselj(0, 1))/x", "x", "0", "+", "Limit((besselj(x, 1) - besselj(0, 1))/x, x, 0, dir='+')", "Subs(Derivative(besselj(xi, 1), xi), xi, 0)"],
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

// Remaining branches of the limit, series and summation code. Expected values are the str() forms printed by SymPy 1.14
// (p is a positive, q a negative and r a real symbol).
const [x, y, z, n, k, a, b, c, m, t] = [V('x'), V('y'), V('z'), V('n'), V('k'), V('a'), V('b'), V('c'), V('m'), V('t')];
const [pp, qq, rr] = [V('p'), V('q'), V('r')];
const show = (v: unknown): string =>
  Array.isArray(v) ? `[${v.map(show).join(', ')}]` : v === undefined ? 'None' : v instanceof Expr || v instanceof NoMatchResult ? v.toString() : typeof v === 'string' ? v : JSON.stringify(v);
const pw = (e: unknown): sj.Piecewise => {
  if (!(e instanceof sj.Piecewise)) throw new TypeError('a Piecewise expected');
  return e;
};
/** The result, or the class name and message of what it throws. */
const run = (f: () => unknown): string => {
  try {
    return show(f());
  } catch (e) {
    return e instanceof Error ? `ERR ${e.constructor.name}: ${e.message}` : 'ERR';
  }
};
const conc = (e: unknown): sj.Concrete => {
  if (!(e instanceof sj.Concrete)) throw new TypeError('a Sum or Product expected');
  return e;
};
const conv = (e: unknown) => sj.isConvergent(conc(e));
const aconv = (e: unknown) => sj.isAbsolutelyConvergent(conc(e));
const moo = P('-oo');
void [x, y, z, n, k, a, b, c, m, t, pp, qq, rr, conv, aconv, moo, pw];

describe('results that differ from SymPy 1.14', () => {
  // [call, symjs result, SymPy 1.14 result]
  const cases: [string, () => unknown, string, string][] = [
    // |x**(I*x)| = 1: x plus a bounded term (SymPy raises NotImplementedError)
    ["sj.limit(P('x + x**(I*x)'), x, sj.oo)", () => sj.limit(P('x + x**(I*x)'), x, sj.oo), "oo", "ERR NotImplementedError"],
    // a bounded oscillation (SymPy raises NotImplementedError)
    ["sj.limit(P('x**(I*x)'), x, sj.oo)", () => sj.limit(P('x**(I*x)'), x, sj.oo), "Limit(x**(I*x), x, oo, dir='-')", "ERR NotImplementedError"],
  ];
  it.each(cases)('%s', (_label, f, expected) => {
    expect(run(f)).toBe(expected);
  });
});

describe('limits with a small budget of nested limit computations', () => {
  it('gives up when the budget is spent (SymPy 1.14: 0)', () => {
    expect(String(limitWithin(P('sin(x)*sin(1/x)'), x, 0, '+', 1))).toBe("Limit(sin(1/x)*sin(x), x, 0, dir='+')");
    expect(String(limitWithin(P('sin(x)*sin(1/x)'), x, 0, '+', 1000))).toBe('0');
  });

  it("does not apply L'Hopital's rule deeper than 30 nested limits (SymPy 1.14: 0)", () => {
    let e = 'x*Ei(x)';
    for (let i = 0; i < 31; i++) e = `sin(${e})`;
    expect(String(sj.limit(P(e), x, 0))).toBe(`Limit(${P(e).toString()}, x, 0, dir='+')`);
    expect(String(sj.limit(P('x*Ei(x)'), x, 0))).toBe('0');
  });
});

// Expected values are the str() forms printed by SymPy 1.14.

const PH = (s: string) => parse(s, { locals: { Heaviside, DiracDelta } });
const Qs = (s: string, syms: Sym[]) => parse(s, { symbols: syms, locals: { Heaviside, DiracDelta } });
/** The variable argument as a symbol. */
const asSym = (e: Expr): Sym => {
  if (!(e instanceof Sym)) throw new TypeError('a symbol expected');
  return e;
};

const showList = (v: unknown): string => (Array.isArray(v) ? `[${v.map(String).join(', ')}]` : String(v));

describe("limit: SymPy 1.14 test_limits cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["limit(Qs(\"sin(1/x)*atan(x)\", [symbol(\"x\", { real: true })]), V(Qs(\"x\", [symbol(\"x\", { real: true })])), 0)", () => limit(Qs("sin(1/x)*atan(x)", [symbol("x", { real: true })]), asSym(Qs("x", [symbol("x", { real: true })])), 0), "0"],
    ["limit(P(\"x\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("x"), asSym(PH("x")), PH("oo")), "oo"],
    ["limit(P(\"x\"), V(P(\"x\")), P(\"-oo\"))", () => limit(PH("x"), asSym(PH("x")), PH("-oo")), "-oo"],
    ["limit(P(\"-x\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("-x"), asSym(PH("x")), PH("oo")), "-oo"],
    ["limit(P(\"x**2\"), V(P(\"x\")), P(\"-oo\"))", () => limit(PH("x**2"), asSym(PH("x")), PH("-oo")), "oo"],
    ["limit(P(\"-x**2\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("-x**2"), asSym(PH("x")), PH("oo")), "-oo"],
    ["limit(P(\"x*log(x)\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("x*log(x)"), asSym(PH("x")), 0, "+"), "0"],
    ["limit(P(\"1/x\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("1/x"), asSym(PH("x")), PH("oo")), "0"],
    ["limit(P(\"exp(x)\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("exp(x)"), asSym(PH("x")), PH("oo")), "oo"],
    ["limit(P(\"-exp(x)\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("-exp(x)"), asSym(PH("x")), PH("oo")), "-oo"],
    ["limit(P(\"exp(x)/x\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("exp(x)/x"), asSym(PH("x")), PH("oo")), "oo"],
    ["limit(P(\"-exp(-x) + 1/x\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("-exp(-x) + 1/x"), asSym(PH("x")), PH("oo")), "0"],
    ["limit(P(\"x + 1/x\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("x + 1/x"), asSym(PH("x")), PH("oo")), "oo"],
    ["limit(P(\"-x**2 + x\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("-x**2 + x"), asSym(PH("x")), PH("oo")), "-oo"],
    ["limit(P(\"(x + 1)**(1 + sqrt(2))\"), V(P(\"x\")), 0)", () => limit(PH("(x + 1)**(1 + sqrt(2))"), asSym(PH("x")), 0), "1"],
    ["limit(P(\"(x + 1)**oo\"), V(P(\"x\")), 0)", () => limit(PH("(x + 1)**oo"), asSym(PH("x")), 0), "Limit((x + 1)**oo, x, 0, dir='+')"],
    ["limit(P(\"(x + 1)**oo\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("(x + 1)**oo"), asSym(PH("x")), 0, "-"), "Limit((x + 1)**oo, x, 0, dir='-')"],
    ["limit(P(\"gamma(3 + 1/x)\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("gamma(3 + 1/x)"), asSym(PH("x")), PH("oo")), "2"],
    ["limit(P(\"1/(x - 1)\"), V(P(\"x\")), 1, \"+\")", () => limit(PH("1/(x - 1)"), asSym(PH("x")), 1, "+"), "oo"],
    ["limit(P(\"1/(x - 1)\"), V(P(\"x\")), 1, \"-\")", () => limit(PH("1/(x - 1)"), asSym(PH("x")), 1, "-"), "-oo"],
    ["limit(P(\"(5 - x)**(-3)\"), V(P(\"x\")), 5, \"+\")", () => limit(PH("(5 - x)**(-3)"), asSym(PH("x")), 5, "+"), "-oo"],
    ["limit(P(\"(5 - x)**(-3)\"), V(P(\"x\")), 5, \"-\")", () => limit(PH("(5 - x)**(-3)"), asSym(PH("x")), 5, "-"), "oo"],
    ["limit(P(\"1/sin(x)\"), V(P(\"x\")), P(\"pi\"), \"+\")", () => limit(PH("1/sin(x)"), asSym(PH("x")), PH("pi"), "+"), "-oo"],
    ["limit(P(\"1/sin(x)\"), V(P(\"x\")), P(\"pi\"), \"-\")", () => limit(PH("1/sin(x)"), asSym(PH("x")), PH("pi"), "-"), "oo"],
    ["limit(P(\"1/cos(x)\"), V(P(\"x\")), P(\"pi/2\"), \"+\")", () => limit(PH("1/cos(x)"), asSym(PH("x")), PH("pi/2"), "+"), "-oo"],
    ["limit(P(\"1/cos(x)\"), V(P(\"x\")), P(\"pi/2\"), \"-\")", () => limit(PH("1/cos(x)"), asSym(PH("x")), PH("pi/2"), "-"), "oo"],
    ["limit(P(\"1/tan(x**3)\"), V(P(\"x\")), P(\"2**(1/3)*pi**(1/3)\"), \"+\")", () => limit(PH("1/tan(x**3)"), asSym(PH("x")), PH("2**(1/3)*pi**(1/3)"), "+"), "oo"],
    ["limit(P(\"1/tan(x**3)\"), V(P(\"x\")), P(\"2**(1/3)*pi**(1/3)\"), \"-\")", () => limit(PH("1/tan(x**3)"), asSym(PH("x")), PH("2**(1/3)*pi**(1/3)"), "-"), "-oo"],
    ["limit(P(\"cot(x)**(-3)\"), V(P(\"x\")), P(\"3*pi/2\"), \"+\")", () => limit(PH("cot(x)**(-3)"), asSym(PH("x")), PH("3*pi/2"), "+"), "-oo"],
    ["limit(P(\"cot(x)**(-3)\"), V(P(\"x\")), P(\"3*pi/2\"), \"-\")", () => limit(PH("cot(x)**(-3)"), asSym(PH("x")), PH("3*pi/2"), "-"), "oo"],
    ["limit(P(\"sin(x)/x\"), V(P(\"x\")), 0, \"+-\")", () => limit(PH("sin(x)/x"), asSym(PH("x")), 0, "+-"), "1"],
    ["limit(P(\"x**2\"), V(P(\"x\")), 0, \"+-\")", () => limit(PH("x**2"), asSym(PH("x")), 0, "+-"), "0"],
    ["limit(P(\"x**(-2)\"), V(P(\"x\")), 0, \"+-\")", () => limit(PH("x**(-2)"), asSym(PH("x")), 0, "+-"), "oo"],
    ["limit(P(\"1/x\"), V(P(\"x\")), 0, \"+-\")", () => limit(PH("1/x"), asSym(PH("x")), 0, "+-"), "zoo"],
    ["limit(P(\"1 + 1/x\"), V(P(\"x\")), 0)", () => limit(PH("1 + 1/x"), asSym(PH("x")), 0), "oo"],
    ["limit(P(\"1 + 1/x\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("1 + 1/x"), asSym(PH("x")), 0, "-"), "-oo"],
    ["limit(P(\"x**(-2)\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("x**(-2)"), asSym(PH("x")), 0, "-"), "oo"],
    ["limit(P(\"x**(-3)\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("x**(-3)"), asSym(PH("x")), 0, "-"), "-oo"],
    ["limit(P(\"1/sqrt(x)\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("1/sqrt(x)"), asSym(PH("x")), 0, "-"), "-oo*I"],
    ["limit(P(\"x**2\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("x**2"), asSym(PH("x")), 0, "-"), "0"],
    ["limit(P(\"sqrt(x)\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("sqrt(x)"), asSym(PH("x")), 0, "-"), "0"],
    ["limit(P(\"1/asin(x)\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("1/asin(x)"), asSym(PH("x")), 0, "+"), "oo"],
    ["limit(P(\"1/asin(x)\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("1/asin(x)"), asSym(PH("x")), 0, "-"), "-oo"],
    ["limit(P(\"1/sinh(x)\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("1/sinh(x)"), asSym(PH("x")), 0, "+"), "oo"],
    ["limit(P(\"1/sinh(x)\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("1/sinh(x)"), asSym(PH("x")), 0, "-"), "-oo"],
    ["limit(P(\"log(1/x) + 1/sin(x)\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("log(1/x) + 1/sin(x)"), asSym(PH("x")), 0, "+"), "oo"],
    ["limit(P(\"log(1/x) + 1/x\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("log(1/x) + 1/x"), asSym(PH("x")), 0, "+"), "oo"],
    ["limit(P(\"x**x\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("x**x"), asSym(PH("x")), 0, "+"), "1"],
    ["limit(P(\"(exp(x) - 1)/x\"), V(P(\"x\")), 0)", () => limit(PH("(exp(x) - 1)/x"), asSym(PH("x")), 0), "1"],
    ["limit(P(\"1 + 1/x\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("1 + 1/x"), asSym(PH("x")), PH("oo")), "1"],
    ["limit(P(\"-exp(1/x)\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("-exp(1/x)"), asSym(PH("x")), PH("oo")), "-1"],
    ["limit(P(\"x + exp(-x)\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("x + exp(-x)"), asSym(PH("x")), PH("oo")), "oo"],
    ["limit(P(\"x + exp(-x**2)\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("x + exp(-x**2)"), asSym(PH("x")), PH("oo")), "oo"],
    ["limit(P(\"x + exp(-exp(x))\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("x + exp(-exp(x))"), asSym(PH("x")), PH("oo")), "oo"],
    ["limit(P(\"13 - exp(-x) + 1/x\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("13 - exp(-x) + 1/x"), asSym(PH("x")), PH("oo")), "13"],
    ["limit(P(\"1/x\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("1/x"), asSym(PH("x")), 0, "+"), "oo"],
    ["limit(P(\"1/x\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("1/x"), asSym(PH("x")), 0, "-"), "-oo"],
    ["limit(P(\"x*y + 2*x\"), V(P(\"x\")), 0)", () => limit(PH("x*y + 2*x"), asSym(PH("x")), 0), "0"],
    ["limit(P(\"x*y + 2*x\"), V(P(\"x\")), 1)", () => limit(PH("x*y + 2*x"), asSym(PH("x")), 1), "y + 2"],
    ["limit(P(\"2*x**8 + y/x**3\"), V(P(\"x\")), -2)", () => limit(PH("2*x**8 + y/x**3"), asSym(PH("x")), -2), "512 - y/8"],
    ["limit(P(\"besselj(1, x)\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("besselj(1, x)"), asSym(PH("x")), PH("oo")), "0"],
    ["limit(P(\"besselj(1, x)\"), V(P(\"x\")), P(\"-oo\"))", () => limit(PH("besselj(1, x)"), asSym(PH("x")), PH("-oo")), "0"],
    ["limit(P(\"bessely(1, x)\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("bessely(1, x)"), asSym(PH("x")), PH("oo")), "0"],
    ["limit(P(\"bessely(1, x)\"), V(P(\"x\")), P(\"-oo\"))", () => limit(PH("bessely(1, x)"), asSym(PH("x")), PH("-oo")), "0"],
    ["limit(P(\"bessely(1, x)\"), V(P(\"x\")), P(\"oo*I\"))", () => limit(PH("bessely(1, x)"), asSym(PH("x")), PH("oo*I")), "-oo"],
    ["limit(P(\"bessely(1, x)\"), V(P(\"x\")), P(\"-oo*I\"))", () => limit(PH("bessely(1, x)"), asSym(PH("x")), PH("-oo*I")), "-oo"],
    ["limit(P(\"besseli(1, x)\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("besseli(1, x)"), asSym(PH("x")), PH("oo")), "oo"],
    ["limit(P(\"besseli(1, x)\"), V(P(\"x\")), P(\"-oo\"))", () => limit(PH("besseli(1, x)"), asSym(PH("x")), PH("-oo")), "-oo"],
    ["limit(P(\"besseli(1, x)\"), V(P(\"x\")), P(\"oo*I\"))", () => limit(PH("besseli(1, x)"), asSym(PH("x")), PH("oo*I")), "0"],
    ["limit(P(\"besseli(1, x)\"), V(P(\"x\")), P(\"-oo*I\"))", () => limit(PH("besseli(1, x)"), asSym(PH("x")), PH("-oo*I")), "0"],
    ["limit(P(\"besselk(1, x)\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("besselk(1, x)"), asSym(PH("x")), PH("oo")), "0"],
    ["limit(P(\"besselk(1, x)\"), V(P(\"x\")), P(\"oo*I\"))", () => limit(PH("besselk(1, x)"), asSym(PH("x")), PH("oo*I")), "0"],
    ["limit(P(\"besselk(1, x)\"), V(P(\"x\")), P(\"-oo*I\"))", () => limit(PH("besselk(1, x)"), asSym(PH("x")), PH("-oo*I")), "0"],
    ["limit(P(\"besselk(0, x)\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("besselk(0, x)"), asSym(PH("x")), PH("oo")), "0"],
    ["limit(P(\"asin(I*x + 2)\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("asin(I*x + 2)"), asSym(PH("x")), 0, "-"), "asin(2)"],
    ["limit(P(\"asin(I*x - 2)\"), V(P(\"x\")), 0)", () => limit(PH("asin(I*x - 2)"), asSym(PH("x")), 0), "-asin(2)"],
    ["limit(P(\"acos(I*x + 2)\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("acos(I*x + 2)"), asSym(PH("x")), 0, "-"), "acos(2)"],
    ["limit(P(\"acos(I*x - 2)\"), V(P(\"x\")), 0)", () => limit(PH("acos(I*x - 2)"), asSym(PH("x")), 0), "acos(-2)"],
    ["limit(P(\"atan(x + 2*I)\"), V(P(\"x\")), 0)", () => limit(PH("atan(x + 2*I)"), asSym(PH("x")), 0), "I*atanh(2)"],
    ["limit(P(\"atan(x - 2*I)\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("atan(x - 2*I)"), asSym(PH("x")), 0, "-"), "-I*atanh(2)"],
    ["limit(P(\"atan(1/x)\"), V(P(\"x\")), 0)", () => limit(PH("atan(1/x)"), asSym(PH("x")), 0), "pi/2"],
    ["limit(P(\"atan(1/x)\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("atan(1/x)"), asSym(PH("x")), 0, "-"), "-pi/2"],
    ["limit(P(\"atan(x)\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("atan(x)"), asSym(PH("x")), PH("oo")), "pi/2"],
    ["limit(P(\"atan(x)\"), V(P(\"x\")), P(\"-oo\"))", () => limit(PH("atan(x)"), asSym(PH("x")), PH("-oo")), "-pi/2"],
    ["limit(P(\"acot(x + I/2)\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("acot(x + I/2)"), asSym(PH("x")), 0, "-"), "-I*acoth(1/2)"],
    ["limit(P(\"acot(x - I/2)\"), V(P(\"x\")), 0)", () => limit(PH("acot(x - I/2)"), asSym(PH("x")), 0), "I*acoth(1/2)"],
    ["limit(P(\"acot(x)\"), V(P(\"x\")), 0)", () => limit(PH("acot(x)"), asSym(PH("x")), 0), "pi/2"],
    ["limit(P(\"acot(x)\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("acot(x)"), asSym(PH("x")), 0, "-"), "-pi/2"],
    ["limit(P(\"asec(I*x + 1/2)\"), V(P(\"x\")), 0)", () => limit(PH("asec(I*x + 1/2)"), asSym(PH("x")), 0), "asec(1/2)"],
    ["limit(P(\"asec(I*x - 1/2)\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("asec(I*x - 1/2)"), asSym(PH("x")), 0, "-"), "asec(-1/2)"],
    ["limit(P(\"acsc(I*x + 1/2)\"), V(P(\"x\")), 0)", () => limit(PH("acsc(I*x + 1/2)"), asSym(PH("x")), 0), "acsc(1/2)"],
    ["limit(P(\"acsc(I*x - 1/2)\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("acsc(I*x - 1/2)"), asSym(PH("x")), 0, "-"), "-acsc(1/2)"],
    ["limit(P(\"log(I*x - 1)\"), V(P(\"x\")), 0)", () => limit(PH("log(I*x - 1)"), asSym(PH("x")), 0), "I*pi"],
    ["limit(P(\"log(-I*x - 1)\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("log(-I*x - 1)"), asSym(PH("x")), 0, "-"), "I*pi"],
    ["limit(P(\"sqrt(I*x - 1)\"), V(P(\"x\")), 0)", () => limit(PH("sqrt(I*x - 1)"), asSym(PH("x")), 0), "I"],
    ["limit(P(\"sqrt(-I*x - 1)\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("sqrt(-I*x - 1)"), asSym(PH("x")), 0, "-"), "I"],
    ["limit(P(\"(I*x - 1)**(1/3)\"), V(P(\"x\")), 0)", () => limit(PH("(I*x - 1)**(1/3)"), asSym(PH("x")), 0), "(-1)**(1/3)"],
    ["limit(P(\"(-I*x - 1)**(1/3)\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("(-I*x - 1)**(1/3)"), asSym(PH("x")), 0, "-"), "(-1)**(1/3)"],
    ["limit(P(\"ceiling(x)\"), V(P(\"x\")), -2, \"+\")", () => limit(PH("ceiling(x)"), asSym(PH("x")), -2, "+"), "-1"],
    ["limit(P(\"ceiling(x)\"), V(P(\"x\")), -2, \"-\")", () => limit(PH("ceiling(x)"), asSym(PH("x")), -2, "-"), "-2"],
    ["limit(P(\"ceiling(x)\"), V(P(\"x\")), -1, \"+\")", () => limit(PH("ceiling(x)"), asSym(PH("x")), -1, "+"), "0"],
    ["limit(P(\"ceiling(x)\"), V(P(\"x\")), -1, \"-\")", () => limit(PH("ceiling(x)"), asSym(PH("x")), -1, "-"), "-1"],
    ["limit(P(\"ceiling(x)\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("ceiling(x)"), asSym(PH("x")), 0, "+"), "1"],
    ["limit(P(\"ceiling(x)\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("ceiling(x)"), asSym(PH("x")), 0, "-"), "0"],
    ["limit(P(\"ceiling(x)\"), V(P(\"x\")), 1, \"+\")", () => limit(PH("ceiling(x)"), asSym(PH("x")), 1, "+"), "2"],
    ["limit(P(\"ceiling(x)\"), V(P(\"x\")), 1, \"-\")", () => limit(PH("ceiling(x)"), asSym(PH("x")), 1, "-"), "1"],
    ["limit(P(\"ceiling(x)\"), V(P(\"x\")), 2, \"+\")", () => limit(PH("ceiling(x)"), asSym(PH("x")), 2, "+"), "3"],
    ["limit(P(\"ceiling(x)\"), V(P(\"x\")), 2, \"-\")", () => limit(PH("ceiling(x)"), asSym(PH("x")), 2, "-"), "2"],
    ["limit(P(\"ceiling(x)\"), V(P(\"x\")), 248, \"+\")", () => limit(PH("ceiling(x)"), asSym(PH("x")), 248, "+"), "249"],
    ["limit(P(\"ceiling(x)\"), V(P(\"x\")), 248, \"-\")", () => limit(PH("ceiling(x)"), asSym(PH("x")), 248, "-"), "248"],
    ["limit(P(\"ceiling(sin(x))\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("ceiling(sin(x))"), asSym(PH("x")), 0, "+"), "1"],
    ["limit(P(\"ceiling(sin(x))\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("ceiling(sin(x))"), asSym(PH("x")), 0, "-"), "0"],
    ["limit(P(\"ceiling(cos(x))\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("ceiling(cos(x))"), asSym(PH("x")), 0, "+"), "1"],
    ["limit(P(\"ceiling(cos(x))\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("ceiling(cos(x))"), asSym(PH("x")), 0, "-"), "1"],
    ["limit(P(\"ceiling(sin(x)) + 5\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("ceiling(sin(x)) + 5"), asSym(PH("x")), 0, "+"), "6"],
    ["limit(P(\"ceiling(sin(x)) + 5\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("ceiling(sin(x)) + 5"), asSym(PH("x")), 0, "-"), "5"],
    ["limit(P(\"ceiling(cos(x)) + 5\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("ceiling(cos(x)) + 5"), asSym(PH("x")), 0, "+"), "6"],
    ["limit(P(\"ceiling(cos(x)) + 5\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("ceiling(cos(x)) + 5"), asSym(PH("x")), 0, "-"), "6"],
    ["limit(Qs(\"(1 + x/n)**n\", [symbol(\"x\", { real: true })]), V(Qs(\"n\", [symbol(\"x\", { real: true })])), Qs(\"oo\", [symbol(\"x\", { real: true })]))", () => limit(Qs("(1 + x/n)**n", [symbol("x", { real: true })]), asSym(Qs("n", [symbol("x", { real: true })])), Qs("oo", [symbol("x", { real: true })])), "exp(x)"],
    ["limit(Qs(\"(1 + x/(2*n))**n\", [symbol(\"x\", { real: true })]), V(Qs(\"n\", [symbol(\"x\", { real: true })])), Qs(\"oo\", [symbol(\"x\", { real: true })]))", () => limit(Qs("(1 + x/(2*n))**n", [symbol("x", { real: true })]), asSym(Qs("n", [symbol("x", { real: true })])), Qs("oo", [symbol("x", { real: true })])), "exp(x/2)"],
    ["limit(Qs(\"(x/(2*n + 1) + 1)**n\", [symbol(\"x\", { real: true })]), V(Qs(\"n\", [symbol(\"x\", { real: true })])), Qs(\"oo\", [symbol(\"x\", { real: true })]))", () => limit(Qs("(x/(2*n + 1) + 1)**n", [symbol("x", { real: true })]), asSym(Qs("n", [symbol("x", { real: true })])), Qs("oo", [symbol("x", { real: true })])), "exp(x/2)"],
    ["limit(Qs(\"((x - 1)/(x + 1))**x\", [symbol(\"x\", { real: true })]), V(Qs(\"x\", [symbol(\"x\", { real: true })])), Qs(\"oo\", [symbol(\"x\", { real: true })]))", () => limit(Qs("((x - 1)/(x + 1))**x", [symbol("x", { real: true })]), asSym(Qs("x", [symbol("x", { real: true })])), Qs("oo", [symbol("x", { real: true })])), "exp(-2)"],
    ["limit(Qs(\"(1 + 1/x)**x + 1\", [symbol(\"x\", { real: true })]), V(Qs(\"x\", [symbol(\"x\", { real: true })])), Qs(\"oo\", [symbol(\"x\", { real: true })]))", () => limit(Qs("(1 + 1/x)**x + 1", [symbol("x", { real: true })]), asSym(Qs("x", [symbol("x", { real: true })])), Qs("oo", [symbol("x", { real: true })])), "1 + E"],
    ["limit(P(\"-oo + 1/(x + sin(x))\"), V(P(\"x\")), 0)", () => limit(PH("-oo + 1/(x + sin(x))"), asSym(PH("x")), 0), "Limit(-oo + 1/(x + sin(x)), x, 0, dir='+')"],
    ["limit(P(\"factorial(x)\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("factorial(x)"), asSym(PH("x")), PH("oo")), "oo"],
    ["limit(P(\"floor(x)\"), V(P(\"x\")), -2, \"+\")", () => limit(PH("floor(x)"), asSym(PH("x")), -2, "+"), "-2"],
    ["limit(P(\"floor(x)\"), V(P(\"x\")), -2, \"-\")", () => limit(PH("floor(x)"), asSym(PH("x")), -2, "-"), "-3"],
    ["limit(P(\"floor(x)\"), V(P(\"x\")), -1, \"+\")", () => limit(PH("floor(x)"), asSym(PH("x")), -1, "+"), "-1"],
    ["limit(P(\"floor(x)\"), V(P(\"x\")), -1, \"-\")", () => limit(PH("floor(x)"), asSym(PH("x")), -1, "-"), "-2"],
    ["limit(P(\"floor(x)\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("floor(x)"), asSym(PH("x")), 0, "+"), "0"],
    ["limit(P(\"floor(x)\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("floor(x)"), asSym(PH("x")), 0, "-"), "-1"],
    ["limit(P(\"floor(x)\"), V(P(\"x\")), 1, \"+\")", () => limit(PH("floor(x)"), asSym(PH("x")), 1, "+"), "1"],
    ["limit(P(\"floor(x)\"), V(P(\"x\")), 1, \"-\")", () => limit(PH("floor(x)"), asSym(PH("x")), 1, "-"), "0"],
    ["limit(P(\"floor(x)\"), V(P(\"x\")), 2, \"+\")", () => limit(PH("floor(x)"), asSym(PH("x")), 2, "+"), "2"],
    ["limit(P(\"floor(x)\"), V(P(\"x\")), 2, \"-\")", () => limit(PH("floor(x)"), asSym(PH("x")), 2, "-"), "1"],
    ["limit(P(\"floor(x)\"), V(P(\"x\")), 248, \"+\")", () => limit(PH("floor(x)"), asSym(PH("x")), 248, "+"), "248"],
    ["limit(P(\"floor(x)\"), V(P(\"x\")), 248, \"-\")", () => limit(PH("floor(x)"), asSym(PH("x")), 248, "-"), "247"],
    ["limit(P(\"floor(atan(x))\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("floor(atan(x))"), asSym(PH("x")), PH("oo")), "1"],
    ["limit(P(\"floor(atan(x))\"), V(P(\"x\")), P(\"-oo\"))", () => limit(PH("floor(atan(x))"), asSym(PH("x")), PH("-oo")), "-2"],
    ["limit(P(\"ceiling(atan(x))\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("ceiling(atan(x))"), asSym(PH("x")), PH("oo")), "2"],
    ["limit(P(\"ceiling(atan(x))\"), V(P(\"x\")), P(\"-oo\"))", () => limit(PH("ceiling(atan(x))"), asSym(PH("x")), PH("-oo")), "-1"],
    ["limit(P(\"floor(sin(x))\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("floor(sin(x))"), asSym(PH("x")), 0, "+"), "0"],
    ["limit(P(\"floor(sin(x))\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("floor(sin(x))"), asSym(PH("x")), 0, "-"), "-1"],
    ["limit(P(\"floor(cos(x))\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("floor(cos(x))"), asSym(PH("x")), 0, "+"), "0"],
    ["limit(P(\"floor(cos(x))\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("floor(cos(x))"), asSym(PH("x")), 0, "-"), "0"],
    ["limit(P(\"floor(sin(x)) + 5\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("floor(sin(x)) + 5"), asSym(PH("x")), 0, "+"), "5"],
    ["limit(P(\"floor(sin(x)) + 5\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("floor(sin(x)) + 5"), asSym(PH("x")), 0, "-"), "4"],
    ["limit(P(\"floor(cos(x)) + 5\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("floor(cos(x)) + 5"), asSym(PH("x")), 0, "+"), "5"],
    ["limit(P(\"floor(cos(x)) + 5\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("floor(cos(x)) + 5"), asSym(PH("x")), 0, "-"), "5"],
    ["limit(P(\"fresnels(x)\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("fresnels(x)"), asSym(PH("x")), PH("oo")), "1/2"],
    ["limit(P(\"fresnels(x) + 3\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("fresnels(x) + 3"), asSym(PH("x")), PH("oo")), "7/2"],
    ["limit(P(\"5*fresnels(x)\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("5*fresnels(x)"), asSym(PH("x")), PH("oo")), "5/2"],
    ["limit(P(\"fresnelc(x)\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("fresnelc(x)"), asSym(PH("x")), PH("oo")), "1/2"],
    ["limit(P(\"fresnels(x)\"), V(P(\"x\")), P(\"-oo\"))", () => limit(PH("fresnels(x)"), asSym(PH("x")), PH("-oo")), "-1/2"],
    ["limit(P(\"4*fresnelc(x)\"), V(P(\"x\")), P(\"-oo\"))", () => limit(PH("4*fresnelc(x)"), asSym(PH("x")), PH("-oo")), "-2"],
    ["limit(P(\"log(x) + asech(x)\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("log(x) + asech(x)"), asSym(PH("x")), PH("oo")), "oo"],
    ["limit(P(\"log(x) + acsch(x)\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("log(x) + acsch(x)"), asSym(PH("x")), 0, "-"), "-oo"],
    ["limit(P(\"log(x) + acsch(x)\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("log(x) + acsch(x)"), asSym(PH("x")), PH("oo")), "oo"],
    ["limit(Qs(\"erf(s*x)/erf(s)\", [symbol(\"s\", { real: true }), symbol(\"x\", { real: true })]), V(Qs(\"s\", [symbol(\"s\", { real: true }), symbol(\"x\", { real: true })])), 0)", () => limit(Qs("erf(s*x)/erf(s)", [symbol("s", { real: true }), symbol("x", { real: true })]), asSym(Qs("s", [symbol("s", { real: true }), symbol("x", { real: true })])), 0), "x"],
    ["limit(P(\"erfc(log(1/x))\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("erfc(log(1/x))"), asSym(PH("x")), PH("oo")), "2"],
    ["limit(P(\"x*(-1 + ((x + 1)**2 + 1)/(x**2 + 1))\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("x*(-1 + ((x + 1)**2 + 1)/(x**2 + 1))"), asSym(PH("x")), PH("oo")), "2"],
    ["limit(P(\"x*(-1 + (x + log(x + 1) + 1)/(x + log(x)))\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("x*(-1 + (x + log(x + 1) + 1)/(x + log(x)))"), asSym(PH("x")), PH("oo")), "1"],
    ["limit(P(\"acos(erfi(x))\"), V(P(\"x\")), 1)", () => limit(PH("acos(erfi(x))"), asSym(PH("x")), 1), "acos(erfi(1))"],
    ["limit(P(\"erf(sqrt(x) - x)\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("erf(sqrt(x) - x)"), asSym(PH("x")), PH("oo")), "-1"],
    ["limit(P(\"floor(sin(x)/x)\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("floor(sin(x)/x)"), asSym(PH("x")), 0, "+"), "0"],
    ["limit(P(\"floor(sin(x)/x)\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("floor(sin(x)/x)"), asSym(PH("x")), 0, "-"), "0"],
    ["limit(P(\"floor(-tan(x)/x)\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("floor(-tan(x)/x)"), asSym(PH("x")), 0, "+"), "-2"],
    ["limit(P(\"floor(-tan(x)/x)\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("floor(-tan(x)/x)"), asSym(PH("x")), 0, "-"), "-2"],
    ["limit(P(\"x**3*((x + 1)/x)**x/((x + 1)*(x + 2)*(x + 3))\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("x**3*((x + 1)/x)**x/((x + 1)*(x + 2)*(x + 3))"), asSym(PH("x")), PH("oo")), "E"],
    ["limit(P(\"exp(x)\"), V(P(\"x\")), 1000000000)", () => limit(PH("exp(x)"), asSym(PH("x")), 1000000000), "exp(1000000000)"],
    ["limit(Qs(\"(B*ti*vi - sqrt(m)*sqrt(-2*B*d*vi + m*vi**2) + m*vi)/(B*vi)\", [symbol(\"m\", { positive: true }), symbol(\"vi\", { positive: true })]), V(Qs(\"B\", [symbol(\"m\", { positive: true }), symbol(\"vi\", { positive: true })])), 0)", () => limit(Qs("(B*ti*vi - sqrt(m)*sqrt(-2*B*d*vi + m*vi**2) + m*vi)/(B*vi)", [symbol("m", { positive: true }), symbol("vi", { positive: true })]), asSym(Qs("B", [symbol("m", { positive: true }), symbol("vi", { positive: true })])), 0), "(d + ti*vi)/vi"],
    ["limit(Qs(\"binomial(n + z, n)/n**z\", [symbol(\"n\", { integer: true, positive: true }), symbol(\"z\", { positive: true })]), V(Qs(\"n\", [symbol(\"n\", { integer: true, positive: true }), symbol(\"z\", { positive: true })])), Qs(\"oo\", [symbol(\"n\", { integer: true, positive: true }), symbol(\"z\", { positive: true })]))", () => limit(Qs("binomial(n + z, n)/n**z", [symbol("n", { integer: true, positive: true }), symbol("z", { positive: true })]), asSym(Qs("n", [symbol("n", { integer: true, positive: true }), symbol("z", { positive: true })])), Qs("oo", [symbol("n", { integer: true, positive: true }), symbol("z", { positive: true })])), "1/gamma(z + 1)"],
    ["limit(Qs(\"binomial(n + z, n)/n**z\", [symbol(\"n\", { integer: true, positive: true }), symbol(\"z\", { positive: true, integer: true })]), V(Qs(\"n\", [symbol(\"n\", { integer: true, positive: true }), symbol(\"z\", { positive: true, integer: true })])), Qs(\"oo\", [symbol(\"n\", { integer: true, positive: true }), symbol(\"z\", { positive: true, integer: true })]))", () => limit(Qs("binomial(n + z, n)/n**z", [symbol("n", { integer: true, positive: true }), symbol("z", { positive: true, integer: true })]), asSym(Qs("n", [symbol("n", { integer: true, positive: true }), symbol("z", { positive: true, integer: true })])), Qs("oo", [symbol("n", { integer: true, positive: true }), symbol("z", { positive: true, integer: true })])), "1/gamma(z + 1)"],
    ["limit(Qs(\"(n + 2)**2*factorial(n)/((n + 1)*(n + 3)*factorial(n + 1))\", [symbol(\"n\", { integer: true, positive: true })]), V(Qs(\"n\", [symbol(\"n\", { integer: true, positive: true })])), Qs(\"oo\", [symbol(\"n\", { integer: true, positive: true })]))", () => limit(Qs("(n + 2)**2*factorial(n)/((n + 1)*(n + 3)*factorial(n + 1))", [symbol("n", { integer: true, positive: true })]), asSym(Qs("n", [symbol("n", { integer: true, positive: true })])), Qs("oo", [symbol("n", { integer: true, positive: true })])), "0"],
    ["limit(Qs(\"(n + 1)*factorial(n)/(n*factorial(n + 1))\", [symbol(\"n\", { integer: true, positive: true })]), V(Qs(\"n\", [symbol(\"n\", { integer: true, positive: true })])), Qs(\"oo\", [symbol(\"n\", { integer: true, positive: true })]))", () => limit(Qs("(n + 1)*factorial(n)/(n*factorial(n + 1))", [symbol("n", { integer: true, positive: true })]), asSym(Qs("n", [symbol("n", { integer: true, positive: true })])), Qs("oo", [symbol("n", { integer: true, positive: true })])), "0"],
    ["limit(P(\"sign(sin(x))\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("sign(sin(x))"), asSym(PH("x")), 0, "-"), "-1"],
    ["limit(P(\"sign(sin(x))\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("sign(sin(x))"), asSym(PH("x")), 0, "+"), "1"],
    ["limit(P(\"sin(sqrt(x))/sqrt(sin(x))\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("sin(sqrt(x))/sqrt(sin(x))"), asSym(PH("x")), 0, "+"), "1"],
    ["limit(P(\"tan(x)**(2**(sqrt(pi)))\"), V(P(\"x\")), P(\"oo\"), \"-\")", () => limit(PH("tan(x)**(2**(sqrt(pi)))"), asSym(PH("x")), PH("oo"), "-"), "Limit(tan(x)**(2**(sqrt(pi))), x, oo, dir='-')"],
    ["limit(Qs(\"LambertW(a)\", [symbol(\"a\", { positive: true }), symbol(\"b\", { positive: true })]), V(Qs(\"a\", [symbol(\"a\", { positive: true }), symbol(\"b\", { positive: true })])), Qs(\"b\", [symbol(\"a\", { positive: true }), symbol(\"b\", { positive: true })]))", () => limit(Qs("LambertW(a)", [symbol("a", { positive: true }), symbol("b", { positive: true })]), asSym(Qs("a", [symbol("a", { positive: true }), symbol("b", { positive: true })])), Qs("b", [symbol("a", { positive: true }), symbol("b", { positive: true })])), "LambertW(b)"],
    ["limit(Qs(\"exp(LambertW(a))\", [symbol(\"a\", { positive: true }), symbol(\"b\", { positive: true })]), V(Qs(\"a\", [symbol(\"a\", { positive: true }), symbol(\"b\", { positive: true })])), Qs(\"b\", [symbol(\"a\", { positive: true }), symbol(\"b\", { positive: true })]))", () => limit(Qs("exp(LambertW(a))", [symbol("a", { positive: true }), symbol("b", { positive: true })]), asSym(Qs("a", [symbol("a", { positive: true }), symbol("b", { positive: true })])), Qs("b", [symbol("a", { positive: true }), symbol("b", { positive: true })])), "exp(LambertW(b))"],
    ["limit(P(\"gamma(x)/(gamma(x - 1)*gamma(x + 2))\"), V(P(\"x\")), 0)", () => limit(PH("gamma(x)/(gamma(x - 1)*gamma(x + 2))"), asSym(PH("x")), 0), "-1"],
    ["limit(P(\"(-1/4)**x\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("(-1/4)**x"), asSym(PH("x")), PH("oo")), "0"],
    ["limit(P(\"((x + 1)**(1/x) - E)/x\"), V(P(\"x\")), 0)", () => limit(PH("((x + 1)**(1/x) - E)/x"), asSym(PH("x")), 0), "-E/2"],
    ["limit(P(\"sin(1/x)*Abs(x)\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("sin(1/x)*Abs(x)"), asSym(PH("x")), 0, "+"), "0"],
    ["limit(P(\"sin(1/x)*Abs(x)\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("sin(1/x)*Abs(x)"), asSym(PH("x")), 0, "-"), "0"],
    ["limit(P(\"sin(1/x)*Abs(x)\"), V(P(\"x\")), 0, \"+-\")", () => limit(PH("sin(1/x)*Abs(x)"), asSym(PH("x")), 0, "+-"), "0"],
    ["limit(P(\"((x + 1)**(1/x) - (2*x + 1)**(1/(2*x)))/asin(x)\"), V(P(\"x\")), 0)", () => limit(PH("((x + 1)**(1/x) - (2*x + 1)**(1/(2*x)))/asin(x)"), asSym(PH("x")), 0), "E/2"],
    ["limit(P(\"sin(pi*x)/(3*x - 12)\"), V(P(\"x\")), 4)", () => limit(PH("sin(pi*x)/(3*x - 12)"), asSym(PH("x")), 4), "pi/3"],
    ["limit(P(\"(x**(x + 1)*(log(x) + 1) + 1)/x\"), V(P(\"x\")), 11)", () => limit(PH("(x**(x + 1)*(log(x) + 1) + 1)/x"), asSym(PH("x")), 11), "3138428376722/11 + 285311670611*log(11)"],
    ["limit(P(\"besselj(7, x)/x**7\"), V(P(\"x\")), 0)", () => limit(PH("besselj(7, x)/x**7"), asSym(PH("x")), 0), "1/645120"],
    ["limit(P(\"(-1)**x/2**x\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("(-1)**x/2**x"), asSym(PH("x")), PH("oo")), "0"],
    ["limit(P(\"sqrt(30)*atan(sqrt(30)*tan(x/2)/6)/30\"), V(P(\"x\")), P(\"-pi\"))", () => limit(PH("sqrt(30)*atan(sqrt(30)*tan(x/2)/6)/30"), asSym(PH("x")), PH("-pi")), "-sqrt(30)*pi/60"],
    ["limit(P(\"sqrt(30)*atan(sqrt(30)*tan(x/2)/6)/30\"), V(P(\"x\")), P(\"-pi\"), \"-\")", () => limit(PH("sqrt(30)*atan(sqrt(30)*tan(x/2)/6)/30"), asSym(PH("x")), PH("-pi"), "-"), "sqrt(30)*pi/60"],
    ["limit(P(\"log((x - I)/(-x - I))\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("log((x - I)/(-x - I))"), asSym(PH("x")), PH("oo")), "I*pi"],
    ["limit(P(\"log(E + 1/x)**(1 - sqrt(E + 1/x))\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("log(E + 1/x)**(1 - sqrt(E + 1/x))"), asSym(PH("x")), PH("oo")), "1"],
    ["limit(P(\"(log(E + 1/x) - 1)**(-sqrt(E + 1/x))\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("(log(E + 1/x) - 1)**(-sqrt(E + 1/x))"), asSym(PH("x")), PH("oo")), "oo"],
    ["limit(P(\"sqrt(-I*x**2 + I*x - 3)\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("sqrt(-I*x**2 + I*x - 3)"), asSym(PH("x")), 0, "+"), "sqrt(3)*I"],
    ["limit(P(\"atan(exp(x))\"), V(P(\"x\")), P(\"oo\"), \"-\")", () => limit(PH("atan(exp(x))"), asSym(PH("x")), PH("oo"), "-"), "pi/2"],
    ["limit(P(\"acot(exp(x))\"), V(P(\"x\")), P(\"oo\"), \"-\")", () => limit(PH("acot(exp(x))"), asSym(PH("x")), PH("oo"), "-"), "0"],
    ["limit(P(\"asec(exp(x))\"), V(P(\"x\")), P(\"oo\"), \"-\")", () => limit(PH("asec(exp(x))"), asSym(PH("x")), PH("oo"), "-"), "pi/2"],
    ["limit(P(\"acsc(exp(x))\"), V(P(\"x\")), P(\"oo\"), \"-\")", () => limit(PH("acsc(exp(x))"), asSym(PH("x")), PH("oo"), "-"), "0"],
    ["limit(P(\"atan(sin(x)/x)\"), V(P(\"x\")), 0, \"+-\")", () => limit(PH("atan(sin(x)/x)"), asSym(PH("x")), 0, "+-"), "pi/4"],
    ["limit(P(\"atan(exp(1/x))\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("atan(exp(1/x))"), asSym(PH("x")), 0, "+"), "pi/2"],
    ["limit(P(\"atan(exp(1/x))\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("atan(exp(1/x))"), asSym(PH("x")), 0, "-"), "0"],
    ["limit(P(\"asin(sin(x)/x)\"), V(P(\"x\")), 0, \"+-\")", () => limit(PH("asin(sin(x)/x)"), asSym(PH("x")), 0, "+-"), "pi/2"],
    ["limit(P(\"acos(sin(x)/x)\"), V(P(\"x\")), 0, \"+-\")", () => limit(PH("acos(sin(x)/x)"), asSym(PH("x")), 0, "+-"), "0"],
    ["limit(P(\"acot(sin(x)/x)\"), V(P(\"x\")), 0, \"+-\")", () => limit(PH("acot(sin(x)/x)"), asSym(PH("x")), 0, "+-"), "pi/4"],
    ["limit(P(\"acot(exp(1/x))\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("acot(exp(1/x))"), asSym(PH("x")), 0, "+"), "0"],
    ["limit(P(\"acot(exp(1/x))\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("acot(exp(1/x))"), asSym(PH("x")), 0, "-"), "pi/2"],
    ["limit(P(\"asec(sin(x)/x)\"), V(P(\"x\")), 0, \"+-\")", () => limit(PH("asec(sin(x)/x)"), asSym(PH("x")), 0, "+-"), "0"],
    ["limit(P(\"asec(exp(1/x))\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("asec(exp(1/x))"), asSym(PH("x")), 0, "+"), "pi/2"],
    ["limit(P(\"acsc(sin(x)/x)\"), V(P(\"x\")), 0, \"+-\")", () => limit(PH("acsc(sin(x)/x)"), asSym(PH("x")), 0, "+-"), "pi/2"],
    ["limit(P(\"acsc(exp(1/x))\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("acsc(exp(1/x))"), asSym(PH("x")), 0, "+"), "0"],
    ["limit(P(\"atanh(sin(x)/x)\"), V(P(\"x\")), 0, \"+-\")", () => limit(PH("atanh(sin(x)/x)"), asSym(PH("x")), 0, "+-"), "oo"],
    ["limit(P(\"atanh(exp(1/x))\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("atanh(exp(1/x))"), asSym(PH("x")), 0, "+"), "-I*pi/2"],
    ["limit(P(\"atanh(exp(1/x))\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("atanh(exp(1/x))"), asSym(PH("x")), 0, "-"), "0"],
    ["limit(P(\"asinh(sin(x)/x)\"), V(P(\"x\")), 0, \"+-\")", () => limit(PH("asinh(sin(x)/x)"), asSym(PH("x")), 0, "+-"), "log(1 + sqrt(2))"],
    ["limit(P(\"asinh(exp(1/x))\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("asinh(exp(1/x))"), asSym(PH("x")), 0, "+"), "oo"],
    ["limit(P(\"asinh(exp(1/x))\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("asinh(exp(1/x))"), asSym(PH("x")), 0, "-"), "0"],
    ["limit(P(\"acosh(sin(x)/x)\"), V(P(\"x\")), 0, \"+-\")", () => limit(PH("acosh(sin(x)/x)"), asSym(PH("x")), 0, "+-"), "0"],
    ["limit(P(\"acosh(exp(1/x))\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("acosh(exp(1/x))"), asSym(PH("x")), 0, "+"), "oo"],
    ["limit(P(\"acoth(sin(x)/x)\"), V(P(\"x\")), 0, \"+-\")", () => limit(PH("acoth(sin(x)/x)"), asSym(PH("x")), 0, "+-"), "oo"],
    ["limit(P(\"acoth(exp(1/x))\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("acoth(exp(1/x))"), asSym(PH("x")), 0, "+"), "0"],
    ["limit(P(\"asech(sin(x)/x)\"), V(P(\"x\")), 0, \"+-\")", () => limit(PH("asech(sin(x)/x)"), asSym(PH("x")), 0, "+-"), "0"],
    ["limit(P(\"asech(exp(1/x))\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("asech(exp(1/x))"), asSym(PH("x")), 0, "+"), "I*pi/2"],
    ["limit(P(\"asech(exp(1/x))\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("asech(exp(1/x))"), asSym(PH("x")), 0, "-"), "oo"],
    ["limit(P(\"acsch(sin(x)/x)\"), V(P(\"x\")), 0, \"+-\")", () => limit(PH("acsch(sin(x)/x)"), asSym(PH("x")), 0, "+-"), "log(1 + sqrt(2))"],
    ["limit(P(\"acsch(exp(1/x))\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("acsch(exp(1/x))"), asSym(PH("x")), 0, "+"), "0"],
    ["limit(P(\"acsch(exp(1/x))\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("acsch(exp(1/x))"), asSym(PH("x")), 0, "-"), "oo"],
    ["limit(P(\"Abs((-x/(x + 1))**x)\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("Abs((-x/(x + 1))**x)"), asSym(PH("x")), PH("oo")), "exp(-1)"],
    ["limit(P(\"(x/(x + 1))**x\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("(x/(x + 1))**x"), asSym(PH("x")), PH("oo")), "exp(-1)"],
    ["limit(P(\"x*exp(x)/(exp(x) - 1)\"), V(P(\"x\")), P(\"-oo\"))", () => limit(PH("x*exp(x)/(exp(x) - 1)"), asSym(PH("x")), PH("-oo")), "0"],
    ["limit(P(\"(1 - cos(x))/x**2\"), V(P(\"x\")), P(\"1/2\"))", () => limit(PH("(1 - cos(x))/x**2"), asSym(PH("x")), PH("1/2")), "4 - 4*cos(1/2)"],
    ["limit(P(\"sin(sin(x + 1) + 1)\"), V(P(\"x\")), 0)", () => limit(PH("sin(sin(x + 1) + 1)"), asSym(PH("x")), 0), "sin(sin(1) + 1)"],
    ["limit(P(\"Abs(sin(x + 1) + 1)\"), V(P(\"x\")), 0)", () => limit(PH("Abs(sin(x + 1) + 1)"), asSym(PH("x")), 0), "sin(1) + 1"],
    ["limit(Qs(\"-exp(-x*z)/z\", [symbol(\"z\", { positive: true })]), V(Qs(\"x\", [symbol(\"z\", { positive: true })])), Qs(\"oo\", [symbol(\"z\", { positive: true })]))", () => limit(Qs("-exp(-x*z)/z", [symbol("z", { positive: true })]), asSym(Qs("x", [symbol("z", { positive: true })])), Qs("oo", [symbol("z", { positive: true })])), "0"],
    ["limit(P(\"x*y + x*z\"), V(P(\"z\")), 2)", () => limit(PH("x*y + x*z"), asSym(PH("z")), 2), "x*y + 2*x"],
    ["limit(P(\"1/(x + 3)\"), V(P(\"x\")), 2)", () => limit(PH("1/(x + 3)"), asSym(PH("x")), 2), "1/5"],
    ["limit(P(\"1/(x + pi)\"), V(P(\"x\")), 2)", () => limit(PH("1/(x + pi)"), asSym(PH("x")), 2), "1/(2 + pi)"],
    ["limit(P(\"log(x)/(x**2 + 3)\"), V(P(\"x\")), 2)", () => limit(PH("log(x)/(x**2 + 3)"), asSym(PH("x")), 2), "log(2)/7"],
    ["limit(P(\"log(x)/(x**2 + pi)\"), V(P(\"x\")), 2)", () => limit(PH("log(x)/(x**2 + pi)"), asSym(PH("x")), 2), "log(2)/(pi + 4)"],
    ["limit(P(\"(-sqrt(exp(x) + 1) + sqrt(exp(dx + x) + 1))/dx\"), V(P(\"dx\")), 0)", () => limit(PH("(-sqrt(exp(x) + 1) + sqrt(exp(dx + x) + 1))/dx"), asSym(PH("dx")), 0), "exp(x)/(2*sqrt(exp(x) + 1))"],
    ["limit(P(\"cot(x)\"), V(P(\"x\")), P(\"-pi/2\"), \"-\")", () => limit(PH("cot(x)"), asSym(PH("x")), PH("-pi/2"), "-"), "0"],
    ["limit(P(\"cot(x)\"), V(P(\"x\")), P(\"-pi/2\"), \"+\")", () => limit(PH("cot(x)"), asSym(PH("x")), PH("-pi/2"), "+"), "0"],
    ["limit(P(\"cot(x)\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("cot(x)"), asSym(PH("x")), 0, "-"), "-oo"],
    ["limit(P(\"cot(x)\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("cot(x)"), asSym(PH("x")), 0, "+"), "oo"],
    ["limit(P(\"cot(x)\"), V(P(\"x\")), P(\"pi/2\"), \"-\")", () => limit(PH("cot(x)"), asSym(PH("x")), PH("pi/2"), "-"), "0"],
    ["limit(P(\"cot(x)\"), V(P(\"x\")), P(\"pi/2\"), \"+\")", () => limit(PH("cot(x)"), asSym(PH("x")), PH("pi/2"), "+"), "0"],
    ["limit(P(\"cot(x)\"), V(P(\"x\")), P(\"pi\"), \"-\")", () => limit(PH("cot(x)"), asSym(PH("x")), PH("pi"), "-"), "-oo"],
    ["limit(P(\"cot(x)\"), V(P(\"x\")), P(\"pi\"), \"+\")", () => limit(PH("cot(x)"), asSym(PH("x")), PH("pi"), "+"), "oo"],
    ["limit(P(\"cot(x)\"), V(P(\"x\")), P(\"3*pi/2\"), \"-\")", () => limit(PH("cot(x)"), asSym(PH("x")), PH("3*pi/2"), "-"), "0"],
    ["limit(P(\"cot(x)\"), V(P(\"x\")), P(\"3*pi/2\"), \"+\")", () => limit(PH("cot(x)"), asSym(PH("x")), PH("3*pi/2"), "+"), "0"],
    ["limit(P(\"tan(x)\"), V(P(\"x\")), P(\"-pi/2\"), \"-\")", () => limit(PH("tan(x)"), asSym(PH("x")), PH("-pi/2"), "-"), "oo"],
    ["limit(P(\"tan(x)\"), V(P(\"x\")), P(\"-pi/2\"), \"+\")", () => limit(PH("tan(x)"), asSym(PH("x")), PH("-pi/2"), "+"), "-oo"],
    ["limit(P(\"tan(x)\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("tan(x)"), asSym(PH("x")), 0, "-"), "0"],
    ["limit(P(\"tan(x)\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("tan(x)"), asSym(PH("x")), 0, "+"), "0"],
    ["limit(P(\"tan(x)\"), V(P(\"x\")), P(\"pi/2\"), \"-\")", () => limit(PH("tan(x)"), asSym(PH("x")), PH("pi/2"), "-"), "oo"],
    ["limit(P(\"tan(x)\"), V(P(\"x\")), P(\"pi/2\"), \"+\")", () => limit(PH("tan(x)"), asSym(PH("x")), PH("pi/2"), "+"), "-oo"],
    ["limit(P(\"tan(x)\"), V(P(\"x\")), P(\"pi\"), \"-\")", () => limit(PH("tan(x)"), asSym(PH("x")), PH("pi"), "-"), "0"],
    ["limit(P(\"tan(x)\"), V(P(\"x\")), P(\"pi\"), \"+\")", () => limit(PH("tan(x)"), asSym(PH("x")), PH("pi"), "+"), "0"],
    ["limit(P(\"tan(x)\"), V(P(\"x\")), P(\"3*pi/2\"), \"-\")", () => limit(PH("tan(x)"), asSym(PH("x")), PH("3*pi/2"), "-"), "oo"],
    ["limit(P(\"tan(x)\"), V(P(\"x\")), P(\"3*pi/2\"), \"+\")", () => limit(PH("tan(x)"), asSym(PH("x")), PH("3*pi/2"), "+"), "-oo"],
    ["limit(P(\"x**(-2)\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("x**(-2)"), asSym(PH("x")), 0, "+"), "oo"],
    ["limit(P(\"x**(-3)\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("x**(-3)"), asSym(PH("x")), 0, "+"), "oo"],
    ["limit(P(\"1/sqrt(x)\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("1/sqrt(x)"), asSym(PH("x")), 0, "+"), "oo"],
    ["limit(P(\"x**(-2/3)\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("x**(-2/3)"), asSym(PH("x")), 0, "-"), "-oo*(-1)**(1/3)"],
    ["limit(P(\"x**(-2/3)\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("x**(-2/3)"), asSym(PH("x")), 0, "+"), "oo"],
    ["limit(P(\"x**2\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("x**2"), asSym(PH("x")), 0, "+"), "0"],
    ["limit(P(\"x**3\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("x**3"), asSym(PH("x")), 0, "-"), "0"],
    ["limit(P(\"x**3\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("x**3"), asSym(PH("x")), 0, "+"), "0"],
    ["limit(P(\"sqrt(x)\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("sqrt(x)"), asSym(PH("x")), 0, "+"), "0"],
    ["limit(P(\"x**(2/3)\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("x**(2/3)"), asSym(PH("x")), 0, "-"), "0"],
    ["limit(P(\"x**(2/3)\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("x**(2/3)"), asSym(PH("x")), 0, "+"), "0"],
    ["limit(P(\"-1/x**3\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("-1/x**3"), asSym(PH("x")), 0, "-"), "oo"],
    ["limit(P(\"-1/x**3\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("-1/x**3"), asSym(PH("x")), 0, "+"), "-oo"],
    ["limit(P(\"1/sqrt(-x)\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("1/sqrt(-x)"), asSym(PH("x")), 0, "-"), "oo"],
    ["limit(P(\"1/sqrt(-x)\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("1/sqrt(-x)"), asSym(PH("x")), 0, "+"), "-oo*I"],
    ["limit(P(\"(-x)**(-2/3)\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("(-x)**(-2/3)"), asSym(PH("x")), 0, "-"), "oo"],
    ["limit(P(\"(-x)**(-2/3)\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("(-x)**(-2/3)"), asSym(PH("x")), 0, "+"), "-oo*(-1)**(1/3)"],
    ["limit(P(\"-x**3\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("-x**3"), asSym(PH("x")), 0, "-"), "0"],
    ["limit(P(\"-x**3\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("-x**3"), asSym(PH("x")), 0, "+"), "0"],
    ["limit(P(\"sqrt(-x)\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("sqrt(-x)"), asSym(PH("x")), 0, "-"), "0"],
    ["limit(P(\"sqrt(-x)\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("sqrt(-x)"), asSym(PH("x")), 0, "+"), "0"],
    ["limit(P(\"(-x)**(2/3)\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("(-x)**(2/3)"), asSym(PH("x")), 0, "-"), "0"],
    ["limit(P(\"(-x)**(2/3)\"), V(P(\"x\")), 0, \"+\")", () => limit(PH("(-x)**(2/3)"), asSym(PH("x")), 0, "+"), "0"],
    ["limit(P(\"sin(x)/x\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("sin(x)/x"), asSym(PH("x")), PH("oo")), "0"],
    ["limit(P(\"gamma(x)\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("gamma(x)"), asSym(PH("x")), PH("oo")), "oo"],
    ["limit(P(\"cos(x)/x\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("cos(x)/x"), asSym(PH("x")), PH("oo")), "0"],
    ["limit(P(\"gamma(x)\"), V(P(\"x\")), P(\"1/2\"))", () => limit(PH("gamma(x)"), asSym(PH("x")), PH("1/2")), "sqrt(pi)"],
    ["limit(Qs(\"r*sin(1/r)\", [symbol(\"r\", { real: true })]), V(Qs(\"r\", [symbol(\"r\", { real: true })])), 0)", () => limit(Qs("r*sin(1/r)", [symbol("r", { real: true })]), asSym(Qs("r", [symbol("r", { real: true })])), 0), "0"],
    ["limit(P(\"(y + 1)**(1/y) - E\"), V(P(\"y\")), 0)", () => limit(PH("(y + 1)**(1/y) - E"), asSym(PH("y")), 0), "0"],
    ["limit(P(\"x**16/(x**16 + 1)\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("x**16/(x**16 + 1)"), asSym(PH("x")), PH("oo")), "1"],
    ["limit(P(\"x**100/(x**100 + 1)\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("x**100/(x**100 + 1)"), asSym(PH("x")), PH("oo")), "1"],
    ["limit(P(\"x**1885/(x**1885 + 1)\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("x**1885/(x**1885 + 1)"), asSym(PH("x")), PH("oo")), "1"],
    ["limit(P(\"-sqrt(x)*besseli(1, 2*sqrt(x))\"), V(P(\"x\")), 0, \"+-\")", () => limit(PH("-sqrt(x)*besseli(1, 2*sqrt(x))"), asSym(PH("x")), 0, "+-"), "0"],
    ["limit(P(\"-sqrt(x)*besseli(1, 2*sqrt(x))\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("-sqrt(x)*besseli(1, 2*sqrt(x))"), asSym(PH("x")), PH("oo")), "-oo"],
    ["limit(P(\"5*x**3/4 - 3*x/4 + (35*x**4/8 - 15*x**2/4 + y*(3*x**2/2 - 1/2) + 3/8)/(2*y + 2)\"), V(P(\"y\")), P(\"oo\"))", () => limit(PH("5*x**3/4 - 3*x/4 + (35*x**4/8 - 15*x**2/4 + y*(3*x**2/2 - 1/2) + 3/8)/(2*y + 2)"), asSym(PH("y")), PH("oo")), "5*x**3/4 + 3*x**2/4 - 3*x/4 - 1/4"],
    ["limit(P(\"sqrt(x/(a + x))\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("sqrt(x/(a + x))"), asSym(PH("x")), PH("oo")), "1"],
    ["limit(P(\"sqrt(x)*(sqrt(x)*(2*(3*besseli(1, 2*sqrt(2)*sqrt(x)) + besseli(3, 2*sqrt(2)*sqrt(x)))/x - sqrt(2)*(besseli(0, 2*sqrt(2)*sqrt(x)) + besseli(2, 2*sqrt(2)*sqrt(x)))/x**(3/2)) + 2*sqrt(2)*(besseli(0, 2*sqrt(2)*sqrt(x)) + besseli(2, 2*sqrt(2)*sqrt(x)))/x - besseli(1, 2*sqrt(2)*sqrt(x))/x**(3/2))/(4*besseli(1, 2*sqrt(2)*sqrt(x)))\"), V(P(\"x\")), 0)", () => limit(PH("sqrt(x)*(sqrt(x)*(2*(3*besseli(1, 2*sqrt(2)*sqrt(x)) + besseli(3, 2*sqrt(2)*sqrt(x)))/x - sqrt(2)*(besseli(0, 2*sqrt(2)*sqrt(x)) + besseli(2, 2*sqrt(2)*sqrt(x)))/x**(3/2)) + 2*sqrt(2)*(besseli(0, 2*sqrt(2)*sqrt(x)) + besseli(2, 2*sqrt(2)*sqrt(x)))/x - besseli(1, 2*sqrt(2)*sqrt(x))/x**(3/2))/(4*besseli(1, 2*sqrt(2)*sqrt(x)))"), asSym(PH("x")), 0), "2"],
    ["limit(P(\"f(x)\"), V(P(\"x\")), 4)", () => limit(PH("f(x)"), asSym(PH("x")), 4), "Limit(f(x), x, 4, dir='+')"],
    ["limit(P(\"x*f(x)**2/(x**2 + f(x)**4)\"), V(P(\"x\")), 0)", () => limit(PH("x*f(x)**2/(x**2 + f(x)**4)"), asSym(PH("x")), 0), "Limit(x*f(x)**2/(x**2 + f(x)**4), x, 0, dir='+')"],
    ["limit(P(\"tan(x)/sin(tan(x))\"), V(P(\"x\")), P(\"pi/2\"))", () => limit(PH("tan(x)/sin(tan(x))"), asSym(PH("x")), PH("pi/2")), "Limit(tan(x)/sin(tan(x)), x, pi/2, dir='+')"],
    ["limit(P(\"tan(x)/sin(tan(x))\"), V(P(\"x\")), P(\"pi/2\"), \"-\")", () => limit(PH("tan(x)/sin(tan(x))"), asSym(PH("x")), PH("pi/2"), "-"), "Limit(tan(x)/sin(tan(x)), x, pi/2, dir='-')"],
    ["limit(Qs(\"n**(-999999999/1000000000)\", [symbol(\"n\", { integer: true, positive: true })]), V(Qs(\"n\", [symbol(\"n\", { integer: true, positive: true })])), Qs(\"oo\", [symbol(\"n\", { integer: true, positive: true })]))", () => limit(Qs("n**(-999999999/1000000000)", [symbol("n", { integer: true, positive: true })]), asSym(Qs("n", [symbol("n", { integer: true, positive: true })])), Qs("oo", [symbol("n", { integer: true, positive: true })])), "0"],
    ["limit(Qs(\"erf(1 - t/d)\", [symbol(\"t\", { positive: true }), symbol(\"d\", { positive: true })]), V(Qs(\"t\", [symbol(\"t\", { positive: true }), symbol(\"d\", { positive: true })])), Qs(\"oo\", [symbol(\"t\", { positive: true }), symbol(\"d\", { positive: true })]))", () => limit(Qs("erf(1 - t/d)", [symbol("t", { positive: true }), symbol("d", { positive: true })]), asSym(Qs("t", [symbol("t", { positive: true }), symbol("d", { positive: true })])), Qs("oo", [symbol("t", { positive: true }), symbol("d", { positive: true })])), "-1"],
    ["limit(Qs(\"lamda**k*exp(-lamda)/factorial(k)\", [symbol(\"k\", { integer: true, nonnegative: true }), symbol(\"lamda\", { positive: true })]), V(Qs(\"k\", [symbol(\"k\", { integer: true, nonnegative: true }), symbol(\"lamda\", { positive: true })])), Qs(\"oo\", [symbol(\"k\", { integer: true, nonnegative: true }), symbol(\"lamda\", { positive: true })]))", () => limit(Qs("lamda**k*exp(-lamda)/factorial(k)", [symbol("k", { integer: true, nonnegative: true }), symbol("lamda", { positive: true })]), asSym(Qs("k", [symbol("k", { integer: true, nonnegative: true }), symbol("lamda", { positive: true })])), Qs("oo", [symbol("k", { integer: true, nonnegative: true }), symbol("lamda", { positive: true })])), "0"],
    ["limit(Qs(\"0\", [symbol(\"x\", { real: true })]), V(Qs(\"x\", [symbol(\"x\", { real: true })])), Qs(\"oo\", [symbol(\"x\", { real: true })]))", () => limit(Qs("0", [symbol("x", { real: true })]), asSym(Qs("x", [symbol("x", { real: true })])), Qs("oo", [symbol("x", { real: true })])), "0"],
    ["limit(P(\"sin(x)**15\"), V(P(\"x\")), 0, \"-\")", () => limit(PH("sin(x)**15"), asSym(PH("x")), 0, "-"), "0"],
    ["limit(P(\"(x + 1)**1000/((x + 1)**1000 + 1)\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("(x + 1)**1000/((x + 1)**1000 + 1)"), asSym(PH("x")), PH("oo")), "1"],
    ["limit(P(\"(x + 1)**1000/((x + 1)**1000 + 1)\"), V(P(\"x\")), P(\"-oo\"))", () => limit(PH("(x + 1)**1000/((x + 1)**1000 + 1)"), asSym(PH("x")), PH("-oo")), "1"],
    ["limit(P(\"x**(77/3)/(x**(77/3) + 1)\"), V(P(\"x\")), P(\"oo\"))", () => limit(PH("x**(77/3)/(x**(77/3) + 1)"), asSym(PH("x")), PH("oo")), "1"],
    ["limit(P(\"Abs(x)\"), V(P(\"x\")), 0)", () => limit(PH("Abs(x)"), asSym(PH("x")), 0), "0"],
    ["limit(P(\"Abs(sin(x))\"), V(P(\"x\")), 0)", () => limit(PH("Abs(sin(x))"), asSym(PH("x")), 0), "0"],
    ["limit(P(\"Abs(cos(x))\"), V(P(\"x\")), 0)", () => limit(PH("Abs(cos(x))"), asSym(PH("x")), 0), "1"],
    ["limit(P(\"Abs(sin(x + 1))\"), V(P(\"x\")), 0)", () => limit(PH("Abs(sin(x + 1))"), asSym(PH("x")), 0), "sin(1)"],
    ["limit(P(\"Abs(log(x - 1)**3 - 1)\"), V(P(\"x\")), 1, \"+\")", () => limit(PH("Abs(log(x - 1)**3 - 1)"), asSym(PH("x")), 1, "+"), "oo"],
    ["limit(P(\"Abs(log(x))\"), V(P(\"x\")), 0)", () => limit(PH("Abs(log(x))"), asSym(PH("x")), 0), "oo"],
    ["limit(P(\"Abs(log(Abs(x)))\"), V(P(\"x\")), 0)", () => limit(PH("Abs(log(Abs(x)))"), asSym(PH("x")), 0), "oo"],
    ["limit(Qs(\"cos(z)\", [symbol(\"z\", { positive: true })]), V(Qs(\"z\", [symbol(\"z\", { positive: true })])), Qs(\"pi\", [symbol(\"z\", { positive: true })]), \"-\")", () => limit(Qs("cos(z)", [symbol("z", { positive: true })]), asSym(Qs("z", [symbol("z", { positive: true })])), Qs("pi", [symbol("z", { positive: true })]), "-"), "-1"],
    ["limit(P('floor(x)'), V(P('x')), 0)", () => limit(PH('floor(x)'), asSym(PH('x')), 0), "0"],
    ["limit(P('floor(x)'), V(P('x')), 0, '-')", () => limit(PH('floor(x)'), asSym(PH('x')), 0, '-'), "-1"],
    ["limit(P('ceiling(x)'), V(P('x')), 2)", () => limit(PH('ceiling(x)'), asSym(PH('x')), 2), "3"],
    ["limit(P('ceiling(x)'), V(P('x')), 2, '-')", () => limit(PH('ceiling(x)'), asSym(PH('x')), 2, '-'), "2"],
    ["limit(P('floor(sin(x)/x)'), V(P('x')), 0)", () => limit(PH('floor(sin(x)/x)'), asSym(PH('x')), 0), "0"],
    ["limit(P('floor(x + 1/2)'), V(P('x')), 0)", () => limit(PH('floor(x + 1/2)'), asSym(PH('x')), 0), "0"],
    ["limit(P('sign(sin(x))'), V(P('x')), 0, '-')", () => limit(PH('sign(sin(x))'), asSym(PH('x')), 0, '-'), "-1"],
    ["limit(P('sign(sin(x))'), V(P('x')), 0)", () => limit(PH('sign(sin(x))'), asSym(PH('x')), 0), "1"],
    ["limit(P('k**3/2**k'), V(P('k')), P('oo'))", () => limit(PH('k**3/2**k'), asSym(PH('k')), PH('oo')), "0"],
    ["limit(P('x**2*3**(-x)'), V(P('x')), P('oo'))", () => limit(PH('x**2*3**(-x)'), asSym(PH('x')), PH('oo')), "0"],
    ["limit(P('3**x/x**5'), V(P('x')), P('oo'))", () => limit(PH('3**x/x**5'), asSym(PH('x')), PH('oo')), "oo"],
    ["limit(P('log(3)*x'), V(P('x')), P('oo'))", () => limit(PH('log(3)*x'), asSym(PH('x')), PH('oo')), "oo"],
    ["limit(P('-log(3)*x'), V(P('x')), P('oo'))", () => limit(PH('-log(3)*x'), asSym(PH('x')), PH('oo')), "-oo"],
    ["limit(P('1/(k**2-I)'), V(P('k')), P('oo'))", () => limit(PH('1/(k**2-I)'), asSym(PH('k')), PH('oo')), "0"],
    ["limit(P('k**2-I'), V(P('k')), P('oo'))", () => limit(PH('k**2-I'), asSym(PH('k')), PH('oo')), "oo"],
    ["limit(P('1/(k**2+I*k)'), V(P('k')), P('oo'))", () => limit(PH('1/(k**2+I*k)'), asSym(PH('k')), PH('oo')), "0"],
    ["limit(P('Abs((-x/(x + 1))**x)'), V(P('x')), P('oo'))", () => limit(PH('Abs((-x/(x + 1))**x)'), asSym(PH('x')), PH('oo')), "exp(-1)"],
    ["limit(P('x*exp(-x)'), V(P('x')), P('oo'))", () => limit(PH('x*exp(-x)'), asSym(PH('x')), PH('oo')), "0"],
    ["limit(P('sqrt(1 - cos(x))/x'), V(P('x')), 0)", () => limit(PH('sqrt(1 - cos(x))/x'), asSym(PH('x')), 0), "sqrt(2)/2"],
    ["limit(P('log(1 + x - sin(x))/log(x)'), V(P('x')), 0)", () => limit(PH('log(1 + x - sin(x))/log(x)'), asSym(PH('x')), 0), "0"],
    ["limit(P('sqrt(x + x**2)/sqrt(x)'), V(P('x')), 0)", () => limit(PH('sqrt(x + x**2)/sqrt(x)'), asSym(PH('x')), 0), "1"],
    ["limit(P('log(I*x - 1)'), V(P('x')), 0)", () => limit(PH('log(I*x - 1)'), asSym(PH('x')), 0), "I*pi"],
    ["limit(P('asin(1 - x**2)'), V(P('x')), 0)", () => limit(PH('asin(1 - x**2)'), asSym(PH('x')), 0), "pi/2"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(showList(run())).toBe(want);
  });
});


describe("summations: results equal SymPy 1.14", () => {
  const cases: [string, () => unknown, string][] = [
    ["limit(P('k**3/2**k'), k, oo)", () => limit(parse('k**3/2**k'), k, oo), "0"],
    ["limit(P('1/(k**2-I)'), k, oo)", () => limit(parse('1/(k**2-I)'), k, oo), "0"],
    ["limit(P('k**2-I'), k, oo)", () => limit(parse('k**2-I'), k, oo), "oo"],
    ["limit(P('x*exp(-x)'), x, oo)", () => limit(parse('x*exp(-x)'), x, oo), "0"],
    ["limit(P('x**2*3**(-x)'), x, oo)", () => limit(parse('x**2*3**(-x)'), x, oo), "0"],
    ["limit(P('3**x/x**5'), x, oo)", () => limit(parse('3**x/x**5'), x, oo), "oo"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(showList(run())).toBe(want);
  });
});

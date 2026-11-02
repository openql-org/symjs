// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { describe, expect, it } from 'vitest';
import {
  SymFunction as Fn,
  I,
  Rational,
  Sym,
  airyai,
  airybi,
  besseli,
  besselj,
  besselk,
  bessely,
  besselsimp,
  diff,
  dsolve,
  evalf,
  fn,
  latex,
  mul,
  neg,
  parse,
  symbols,
} from '../src';

const [z, nu, x] = symbols('z nu x');

// expected values from SymPy 1.14
describe('Bessel and Airy functions', () => {
  it('evaluation rules', () => {
    expect(String(besselj(0, 0))).toBe('1');
    expect(String(besselj(-1, z))).toBe('-besselj(1, z)');
    expect(String(besselj(neg(new Sym('n', { integer: true })), z))).toBe('(-1)**n*besselj(n, z)');
    expect(String(besseli(-1, z))).toBe('besseli(1, z)');
    expect(String(bessely(0, 0))).toBe('-oo');
    expect(String(airyai(0))).toBe('3**(1/3)/(3*gamma(2/3))');
  });
  it('derivatives and LaTeX', () => {
    expect(String(diff(besselj(nu, z), z))).toBe('besselj(nu - 1, z)/2 - besselj(nu + 1, z)/2');
    expect(String(diff(besselk(nu, z), z))).toBe('-besselk(nu - 1, z)/2 - besselk(nu + 1, z)/2');
    expect(String(diff(airyai(z), z, 2))).toBe('z*airyai(z)');
    expect(latex(besselj(nu, z))).toBe('J_{\\nu}\\left(z\\right)');
  });
  it('arbitrary-precision values', () => {
    expect(String(evalf(besselj(2, 1), 30))).toBe('0.114903484931900480469646881335');
    expect(String(evalf(bessely(0, 3), 25))).toBe('0.3768500100127903819671102');
    expect(String(evalf(besselk(2, Rational.of(1, 2)), 25))).toBe('7.550183551240869436567706');
    expect(String(evalf(airybi(1.5)))).toBe('1.87894150374789');
    expect(String(evalf(besselj(Rational.of(1, 3), I), 20))).toBe('0.92199783623887115975 + 0.53231569894476475691*I');
  });
  it('besselsimp', () => {
    expect(String(besselsimp(besselj(nu, mul(z, fn('polar_lift', [-1])))))).toBe('exp(I*pi*nu)*besselj(nu, z)');
    expect(String(besselsimp(besseli(Rational.of(-1, 2), z)))).toBe('sqrt(2)*cosh(z)/(sqrt(pi)*sqrt(z))');
    expect(String(besselsimp(besselj(Rational.of(3, 2), z)))).toBe('-sqrt(2)*(z*cos(z) - sin(z))/(sqrt(pi)*z**(3/2))');
    expect(String(besselsimp(parse('z*besseli(0, z) + z*besseli(2, z)/2 + besseli(1, z)')))).toBe('3*z*besseli(0, z)/2');
    expect(String(besselsimp(parse('besselj(2, z) + besselj(0, z)')))).toBe('2*besselj(1, z)/z');
  });
  it('Airy and Bessel equations in dsolve', () => {
    const f = Fn('f');
    expect(String(dsolve(parse('-x*f(x) + Derivative(f(x), x, x)'), f(x)))).toBe('Eq(f(x), C1*airyai(x) + C2*airybi(x))');
    expect(String(dsolve(parse('x**2*Derivative(f(x), x, x) + x*Derivative(f(x), x) + (x**2 - 4)*f(x)'), f(x)))).toBe(
      'Eq(f(x), C1*besselj(2, x) + C2*bessely(2, x))',
    );
  });
});

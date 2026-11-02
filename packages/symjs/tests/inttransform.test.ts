// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { describe, expect, it } from 'vitest';
import { Integral, S, add, parse, pow, principalValue, symbols, transformIntegral } from '../src';

const [x, u, a] = symbols('x u a');

describe('Integral.transform', () => {
  it('renames and shifts the integration variable', () => {
    const i = new Integral([x, x, S.Zero, S.One]);
    expect(String(transformIntegral(i, x, add(u, a), u))).toBe('Integral(a + u, (u, -a, 1 - a))');
    expect(String(transformIntegral(i, x, add(u, a), a))).toBe('Integral(a + u, (a, -u, 1 - u))');
    expect(String(transformIntegral(new Integral([parse('x*cos(x**2 - 1)'), x, S.Zero, S.One]), x, u))).toBe(
      'Integral(u*cos(u**2 - 1), (u, 0, 1))',
    );
  });
});

describe('Integral.principal_value', () => {
  it('handles singularities inside the interval and infinite limits', () => {
    expect(String(principalValue(new Integral([pow(x, -3), x, parse('-10'), parse('10')])))).toBe('0');
    expect(String(principalValue(new Integral([pow(x, -3), x, S.NegativeInfinity, S.Infinity])))).toBe('0');
    expect(String(principalValue(new Integral([add(x, 1), x, S.NegativeInfinity, S.Infinity])))).toBe('oo');
  });
});

import { exptrigsimp } from '../src';

describe('exptrigsimp', () => {
  it('recombines exponentials into hyperbolic functions and back', () => {
    expect(String(exptrigsimp(parse('exp(z) + exp(-z)')))).toBe('2*cosh(z)');
    expect(String(exptrigsimp(parse('exp(z) - exp(-z)')))).toBe('2*sinh(z)');
    expect(String(exptrigsimp(parse('cosh(z) - sinh(z)')))).toBe('exp(-z)');
  });
});

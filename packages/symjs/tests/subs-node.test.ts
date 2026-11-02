// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { describe, expect, it } from 'vitest';
import { Derivative, Function, Subs, diff, doit, freeSymbols, latex, parse, sstr, symbols } from '../src';

const [x, y, z] = symbols('x y z');
const f = Function('f');

describe('Subs (SymPy Subs)', () => {
  it('derivative at a point', () => {
    const s = diff(f(x), x).subs(x, 0 as never);
    expect(s).toBeInstanceOf(Subs);
    expect(sstr(s)).toBe('Subs(Derivative(f(x), x), x, 0)');
    expect(latex(s)).toBe('\\left. \\frac{d}{d x} f{\\left(x \\right)} \\right|_{\\substack{ x=0 }}');
    expect(freeSymbols(s).size).toBe(0);
    expect(sstr(diff(s, x))).toBe('0');
    expect(sstr(doit(s))).toBe('Subs(Derivative(f(x), x), x, 0)');
    expect(sstr(diff(f(x), x).subs(x, y))).toBe('Derivative(f(y), y)');
    expect(sstr(Derivative(f(x, y), x).subs(x, parse('y + 1')))).toBe('Subs(Derivative(f(x, y), x), x, y + 1)');
  });

  it('several variables, substitution and evaluation', () => {
    const s = Subs(parse('f(x)*sin(y) + z'), [x, y], [0, 1]);
    expect(sstr(s)).toBe('Subs(z + f(x)*sin(y), (x, y), (0, 1))');
    expect(latex(s)).toBe('\\left. z + f{\\left(x \\right)} \\sin{\\left(y \\right)} \\right|_{\\substack{ x=0\\\\ y=1 }}');
    expect([...freeSymbols(s)].map(String)).toEqual(['z']);
    expect(sstr(s.subs(x, 3 as never))).toBe(sstr(s));
    expect(sstr(s.subs(z, 3 as never))).toBe('Subs(f(x)*sin(y) + 3, (x, y), (0, 1))');
    expect(sstr(doit(s))).toBe('z + f(0)*sin(1)');
    expect(sstr(diff(Subs(parse('x**2'), x, parse('y + 1')), y))).toBe('2*y + 2');
    expect(sstr(diff(Subs(f(x), x, y), y))).toBe('Derivative(f(y), y)');
  });
});

import { combsimp, gammasimp } from '../src';

describe('gammasimp and combsimp', () => {
  const n = symbols('n', { integer: true })[0];
  it('combine integer shifts', () => {
    expect(sstr(gammasimp(parse('gamma(x + 3)/gamma(x + 1)')))).toBe('(x + 1)*(x + 2)');
    expect(sstr(gammasimp(parse('gamma(x + 1)/gamma(x)/x')))).toBe('1');
    expect(sstr(combsimp(parse('factorial(n + 2)/factorial(n)', { symbols: { n } } as never)))).toBe('(n + 1)*(n + 2)');
    expect(sstr(combsimp(parse('binomial(n + 1, 2)/binomial(n, 2)', { symbols: { n } } as never)))).toBe('(n + 1)/(n - 1)');
    expect(sstr(combsimp(parse('factorial(n)/factorial(n - 3)', { symbols: { n } } as never)))).toBe('n*(n - 2)*(n - 1)');
    expect(sstr(combsimp(parse('factorial(n)*factorial(n + 1)', { symbols: { n } } as never)))).toBe('factorial(n)*factorial(n + 1)');
  });
});

describe('parser and assumptions', () => {
  it('repeating decimals', () => {
    expect(['.[3]', '1.2[3]', '0.[142857]', '-1.[3]'].map((s) => sstr(parse(s)))).toEqual(['1/3', '37/30', '1/7', '-4/3']);
  });
  it('zero=False splits powers', async () => {
    const { expandPowerExp, Symbol: Sym } = await import('../src');
    const xn = new Sym('x', { zero: false });
    expect(sstr(expandPowerExp(parse('x**(y + 2)', { symbols: { x: xn } } as never)))).toBe('x**2*x**y');
    expect(sstr(expandPowerExp(parse('x**(y + 2)')))).toBe('x**(y + 2)');
  });
});

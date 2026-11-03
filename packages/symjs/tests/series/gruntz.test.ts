// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/series/gruntz.ts.
// Limits at infinity by the Gruntz algorithm. Expected values are those of SymPy 1.14 (gruntz).

import { describe, expect, it } from 'vitest';
import { Dummy, oo, parse, symbols, sstr } from '../../src';
import { Gruntz, GruntzError, gruntz, monomialLead } from '../../src/series/gruntz';
import type { Expr } from '../../src/core/nodes';
import { add, exp, mul, pow } from '../../src/core/ops';

const [x] = symbols('x');
const P = (s: string) => parse(s);
const G = (s: string, z0 = 'oo', dir: '+' | '-' = '+') => sstr(gruntz(P(s), x, P(z0), dir));

describe('gruntz: limits as in SymPy 1.14', () => {
  it.each([
    ['exp(x)/x', 'oo', 'oo'],
    ['x**1000/((x + 1)**1000 + exp(-x))', 'oo', '1'],
    ['(2**(x + 1) + 3**(x + 1))/(2**x + 3**x)', 'oo', '3'],
    ['(3**x + 2*x**10)/(x**10 + exp(x))', '-oo', '2'],
    ['x/factorial(x)', 'oo', '0'],
    ['16**x/(x*binomial(2*x, x)**2)', 'oo', 'pi'],
    ['x*(-2*x**3 - x**2*(2*x**3 - 2)*polygamma(0, x**3 + 1) + x**2*(2*x**3 - 2)*polygamma(0, x**3 + x + 1) + x + 3)/2', 'oo', '1/3'],
    ['log(x + exp(3*x))/log(x**100 + exp(x))', 'oo', '3'],
    ['(3**(1/x) + 5**(1/x))**x', '0', '5'],
    ['I*exp(x)', 'oo', 'oo*I'],
    ['-x*exp(x)', 'oo', '-oo'],
  ])('gruntz(%s, x, %s) = %s', (e, z0, expected) => {
    expect(G(e, z0)).toBe(expected);
  });

  it('approaches a finite point from either side', () => {
    expect(G('exp(-1/x)', '0', '+')).toBe('0');
    expect(G('exp(-1/x)', '0', '-')).toBe('oo');
  });

  it('raises GruntzError for what it cannot decide', () => {
    // several arguments depending on x, an unknown growth, a symbolic sign, no nonzero term
    for (const e of ['polygamma(x, x)', 'uppergamma(x, 1)/gamma(x)', 'exp(x*y)', 'x**y + x', 'x**I + x', 'x*(1 - cos(1/x)**2 - sin(1/x)**2)', 'f(x)']) {
      expect(() => gruntz(P(e), x, oo, '+')).toThrow(GruntzError);
    }
    expect(() => new Gruntz(3).limitinf(P('exp(exp(x))/exp(x)'), x)).toThrow('too many steps');
  });
});

describe('gruntz: the sign at infinity', () => {
  const p = new Dummy('p', { positive: true });
  const g = new Gruntz();
  const S = (s: string) => sstr(g.sign(parse(s).subs(x, p), p));
  it('follows SymPy sign()', () => {
    expect(sstr(g.sign(p, p))).toBe('1');
    expect(S('1 - x')).toBe('-1');
    expect(S('(1 - x)**3')).toBe('-1');
    expect(S('(1 - x)**(1/2)')).toBe('I');
    expect(S('exp(I*x)')).toBe('1');
    expect(S('(x - 2)*(x - 3)')).toBe('1');
    expect(S('(log(2)/log(2/3) - log(4/3)/log(2/3) + 1)*x')).toBe('0');
    expect(S('(log(2)/log(2/3) - log(4/3)/log(2/3) + 1)*(x - 2)')).toBe('0');
    expect(S('y')).toBe('sign(y)');
    expect(S('sin(1)')).toBe('1');
  });
});

describe('gruntz: the leading monomial with real exponents', () => {
  const w = new Dummy('w', { positive: true });
  const L = new Dummy('L');
  const M = (s: string) => {
    const r = monomialLead(parse(s).subs(x, w), w, L, x, mul(-1, x));
    return `${sstr(r.c)} ${sstr(r.e)}`;
  };
  it('multiplies, adds and raises leading terms', () => {
    expect(M('3*x**sqrt(2) + x')).toBe('1 1');
    expect(M('x**sqrt(2) + 2*x**sqrt(2)')).toBe('3 sqrt(2)');
    expect(M('exp(2 + x**sqrt(2))')).toBe('exp(2) 0');
    expect(M('2**x')).toBe('1 0');
    expect(M('log(x**sqrt(2))')).toBe('sqrt(2)*_L 0');
    expect(M('log(1 + x**sqrt(2))')).toBe('1 sqrt(2)');
    expect(M('cos(x**sqrt(2))')).toBe('1 0');
    expect(M('atan(2 + x**sqrt(2))')).toBe('atan(2) 0');
  });
  it('turns exp(c*log(w)) into a power of w unless c depends on x', () => {
    const lead = (e: Expr) => {
      const r = monomialLead(e, w, L, x, mul(-1, x));
      return `${sstr(r.c)} ${sstr(r.e)}`;
    };
    const lw = parse('log(x)').subs(x, w);
    expect(lead(exp(add(mul(3, lw), w)))).toBe('1 3');
    expect(lead(exp(add(mul(lw, pow(x, -1)), w)))).toBe('exp(-1) 0');
    expect(() => lead(exp(add(pow(lw, 2), w)))).toThrow(GruntzError);
  });
  it('does not decide singular or cancelling terms', () => {
    for (const s of ['exp(1/x**sqrt(2))', 'x**sqrt(2) - x**sqrt(2)*(1 + x)', 'sin(x**sqrt(2))', 'cot(x**sqrt(2))', 'cos(1/x**sqrt(2))']) {
      expect(() => monomialLead(parse(s).subs(x, w), w, L, x, mul(-1, x)), s).toThrow(GruntzError);
    }
    expect(() => monomialLead(parse('f(x)').subs(x, w), w, L, x, mul(-1, x))).toThrow(GruntzError);
  });
});

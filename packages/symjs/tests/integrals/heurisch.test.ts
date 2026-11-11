// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/integrals/heurisch.ts (SymPy heurisch for rational functions of sin and cos). Expected values are
// those of SymPy 1.14 heurisch (integrate adds the floor terms of continuous arctangents).

import { describe, expect, it } from 'vitest';
import { Integral, Piecewise, Sym, SymFunction, add, diff, integrate, parse, sstr, type Expr } from '../../src';
import { at } from '../../src/core/guard';
import { componentsOf, heurisch, heurischTrig, heurischWrapper, rootFactors, type HeurischOptions } from '../../src/integrals/heurisch';

const y = new Sym('y');
const H = (s: string): string => {
  const r = heurischTrig(parse(s), y, (g, t) => {
    const G = integrate(g, t);
    return G instanceof Integral ? undefined : G;
  });
  return r === undefined ? 'None' : sstr(r);
};

describe('heurisch in tan(u/2)', () => {
  it.each([
    ['(sin(y) + 1)/(2*(sin(y) - 1))', 'y*tan(y/2)/(2*tan(y/2) - 2) - y/(2*tan(y/2) - 2) + 4/(2*tan(y/2) - 2)'],
    ['1/(1 + sin(y))', '-2/(tan(y/2) + 1)'],
    ['1/(2 + cos(y))', '2*sqrt(3)*atan(sqrt(3)*tan(y/2)/3)/3'],
    ['1/(1 + cos(y))', 'tan(y/2)'],
    ['sin(y)/(1 + sin(y))', 'y*tan(y/2)/(tan(y/2) + 1) + y/(tan(y/2) + 1) + 2/(tan(y/2) + 1)'],
    ['1/(sin(y) + cos(y))', 'sqrt(2)*log(tan(y/2) - 1 + sqrt(2))/2 - sqrt(2)*log(tan(y/2) - sqrt(2) - 1)/2'],
    ['1/(3 + sin(2*y))', 'sqrt(2)*atan(3*sqrt(2)*tan(y)/4 + sqrt(2)/4)/4'],
    ['1/(1 - cos(y))**2', '-1/(2*tan(y/2)) - 1/(6*tan(y/2)**3)'],
  ])('%s', (f, want) => expect(H(f)).toBe(want));

  it('applies only to rational functions of sin(a*x + b) and cos(a*x + b) with a rational a', () => {
    expect(H('y/(1 + sin(y))')).toBe('None');
    expect(H('1/(sin(y) + cos(2*y))')).toBe('None');
    expect(H('1/(1 + sin(y**2))')).toBe('None');
    expect(H('1/(1 + sin(a*y))')).toBe('None');
    expect(H('1/(1 + exp(y))')).toBe('None');
    // the rational function of t is not integrated
    expect(H('1/(1 + sin(y)**5 + sin(y))')).toBe('None');
  });
});

// the heuristic Risch algorithm: the results of SymPy 1.14 heurisch and heurisch_wrapper
const [x, n, a, b] = [new Sym('x'), new Sym('n'), new Sym('a'), new Sym('b')];
const PX = (s: string): Expr => parse(s, { symbols: [x, y, n, a, b] });
const hr = (s: string, opts?: HeurischOptions): string => {
  const r = heurisch(PX(s), x, opts);
  return r === undefined ? 'None' : sstr(r);
};
const hw = (s: string): string => {
  const r = heurischWrapper(PX(s), x);
  return r === undefined ? 'None' : sstr(r);
};

describe('heurisch', () => {
  it.each([
    ['2', '2*x'],
    ['x*y', 'x**2*y/2'],
    ['x*exp(x)', 'x*exp(x) - exp(x)'],
    ['x*log(x)', 'x**2*log(x)/2 - x**2/4'],
    ['1/(x**2 + 1)', 'atan(x)'],
    ['1/(x**2 - 1)', 'log(x - 1)/2 - log(x + 1)/2'],
    ['1/(x**2 + 2*x + 5)', 'atan(x/2 + 1/2)/2'],
    ['sqrt(x)', '2*x**(3/2)/3'],
    ['x**(-3/2)', '-2/sqrt(x)'],
    ['tan(x)', 'log(tan(x)**2 + 1)/2'],
    ['tanh(x)', 'x - log(tanh(x) + 1)'],
    ['cot(x)', '-log(tan(x)**2 + 1)/2 + log(tan(x))'],
    ['coth(x)', 'x - log(tanh(x) + 1) + log(tanh(x))'],
    ['sin(x)*cos(x)', '-cos(x)**2/2'],
    ['exp(x)*sin(x)', 'exp(x)*sin(x)/2 - exp(x)*cos(x)/2'],
    ['cosh(x)**2', '-x*sinh(x)**2/2 + x*cosh(x)**2/2 + sinh(x)*cosh(x)/2'],
    ['atan(x)', 'x*atan(x) - log(x**2 + 1)/2'],
    ['LambertW(x)', 'x*LambertW(x) - x + x/LambertW(x)'],
    ['exp(x)/(1 + exp(x))', 'log(exp(x) + 1)'],
    ['1/(x*log(x))', 'log(log(x))'],
    ['erf(x)', 'x*erf(x) + exp(-x**2)/sqrt(pi)'],
    ['y*tan(x)', 'y*log(tan(x)**2 + 1)/2'],
    ['cos(n*x)', 'sin(n*x)/n'],
    ['x/(a*x + b)', 'x/a - b*log(x + b/a)/a**2'],
    ['x**(3/2)', '2*x**(5/2)/5'],
    ['x + exp(x)', 'x**2/2 + exp(x)'],
    // a complex factor without its conjugate
    ['1/(x - I)', 'log(x - I)'],
    // the derivation of sin(x)**2 + cos(x)**2 vanishes
    ['1/(sin(x)**2 + cos(x)**2)', 'x/(sin(x)**2 + cos(x)**2)'],
    // SymPy: log(x + 1)/3 - log(4*x**2 - 4*x + 4)/6 + ..., the same up to a constant
    ['1/(x**3 + 1)', 'log(x + 1)/3 - log(x**2 - x + 1)/6 + sqrt(3)*atan(2*sqrt(3)*x/3 - sqrt(3)/3)/3'],
  ])('%s', (f, F) => {
    expect(hr(f)).toBe(F);
  });
  it('root_factors', () => {
    const z = new Sym('z');
    const rf = (s: string): string[] => rootFactors(parse(s, { symbols: [z] }), z).map((e) => sstr(e));
    expect(rf('z**2 + 1')).toEqual(['z - I', 'z + I']);
    expect(rf('z**3 - 2*z**2 + z')).toEqual(['z', 'z - 1', 'z - 1']);
    expect(rf('z**5 + z + 3')).toEqual(['z**5 + z + 3']);
  });
  it('gives None without retries', () => {
    expect(hr('exp(-x**2)', { retries: -1 })).toBe('None');
  });
  it('gives None when no antiderivative is found', () => {
    for (const f of ['1/sqrt(x**2 + 1)', 'exp(-x**2)', 'log(x)/x', 'Abs(x)', 'besselj(0, x)', 'sqrt(1 - x**2)', 'DiracDelta(x)', 'exp(x)*exp(exp(x))', 'cos(x)*cos(sin(x))']) expect(hr(f)).toBe('None');
    expect(hr('exp(-x**2)', { retries: 0, degreeOffset: 1 })).toBe('None');
  });
  it('rewrites with tan and tanh', () => {
    expect(hr('sin(x)', { rewrite: true })).toBe('-2/(tan(x/2)**2 + 1)');
    expect(hr('sinh(x)', { rewrite: true })).toBe('-2/(tanh(x/2)**2 - 1)');
  });
  it('components', () => {
    expect(componentsOf(add(PX('sin(x)*cos(x)**2 + x**(2/3) + 2**x'), diff(SymFunction('f')(x), x)), x).map((e) => sstr(e)).sort()).toEqual([
      '2**x', 'Derivative(f(x), x)', 'cos(x)', 'f(x)', 'sin(x)', 'x', 'x**(1/3)',
    ]);
  });
});

describe('heurisch_wrapper', () => {
  it('adds the cases where a denominator vanishes', () => {
    expect(hw('cos(n*x)')).toBe('Piecewise((sin(n*x)/n, Ne(n, 0)), (x, True))');
    expect(hw('x/(a*x + b)')).toBe('Piecewise((x/a - b*log(x + b/a)/a**2, Ne(a, 0)), (x**2/(2*b), True))');
    expect(hw('1/(a*x**2 + b)')).toBe(
      'Piecewise((zoo*x, Eq(a, 0) & Eq(b, 0)), (x/b, Eq(a, 0)), (-1/(a*x), Eq(b, 0)), (log(x - sqrt(-b/a))/(2*a*sqrt(-b/a)) - log(x + sqrt(-b/a))/(2*a*sqrt(-b/a)), True))',
    );
  });
  it('several cases for one symbol', () => {
    // SymPy: Piecewise((..., Eq(a, -I)), (..., Eq(a, I)), (a*exp(a*x)*sin(x)/(a**2 + 1) - exp(a*x)*cos(x)/(a**2 + 1), True))
    const r = heurischWrapper(PX('exp(a*x)*sin(x)'), x);
    expect(r instanceof Piecewise ? r.pairs.map(([e, c]) => [sstr(c), e.has(x)]) : []).toEqual([
      ['Eq(a, -I)', true],
      ['Eq(a, I)', true],
      ['True', true],
    ]);
    expect(r instanceof Piecewise ? sstr(at(r.pairs, 2)[0]) : '').toBe('a*exp(a*x)*sin(x)/(a**2 + 1) - exp(a*x)*cos(x)/(a**2 + 1)');
  });
  it('integrates a special case that heurisch does not', () => {
    // SymPy: Piecewise((a*x*x**a*log(x)/(a**2 + 2*a + 1) + x*x**a*log(x)/(a**2 + 2*a + 1) - x*x**a/(a**2 + 2*a + 1), Ne(a, -1)), (log(x)**2/2, True))
    const r = heurischWrapper(PX('x**a*log(x)'), x);
    expect(r instanceof Piecewise ? r.pairs.map(([e, c]) => sstr(c) === 'True' ? sstr(e) : sstr(c)) : []).toEqual(['Ne(a, -1)', 'log(x)**2/2']);
  });
  it('keeps the result without symbolic denominators, and the poles of the integrand', () => {
    expect(hw('exp(x)')).toBe('exp(x)');
    expect(hw('y')).toBe('x*y');
    expect(hw('1/(x + a)')).toBe('log(a + x)');
    expect(hw('Abs(x)')).toBe('None');
    // gamma(a) = 0 is not solved
    expect(hw('cos(gamma(a)*x)')).toBe('sin(x*gamma(a))/gamma(a)');
  });
});

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/numeric/nfloat.ts.

import { describe, expect, it } from 'vitest';
import { comp, float, nfloat, nsimplify, parse, sstr, SymFunction } from '../../src';
import type { Expr } from '../../src';
import { simpleRational } from '../../src/numeric/nfloat';

const p = (s: string) => parse(s);
const st = (e: Expr) => sstr(e);

describe('nsimplify of exact numbers', () => {
  it('identifies closed forms like SymPy', async () => {
    const { nsimplify, pi } = await import('../../src');
    const ns = (s: string) => sstr(nsimplify(parse(s)));
    expect(['pi', 'sqrt(2)', 'cos(pi/5)', '1/(exp(3*pi*I/5)+1)', 'sin(pi/12)', '2**(1/3)', 'log(2)'].map(ns)).toEqual([
      'pi', 'sqrt(2)', '1/4 + sqrt(5)/4', '1/2 - I*sqrt(sqrt(5)/10 + 1/4)', 'sqrt(1/2 - sqrt(3)/4)', '2**(1/3)', 'log(2)',
    ]);
    expect(sstr(nsimplify(parse('4/(1+sqrt(5))'), { constants: [parse('GoldenRatio')] }))).toBe('-2 + 2*GoldenRatio');
    expect(sstr(nsimplify(parse('I**I'), { constants: [pi] }))).toBe('exp(-pi/2)');
  });
});

// Expected values from SymPy 1.14 (round, Float, nfloat, comp, nsimplify).

describe('nfloat', () => {
  it('makes rationals Floats', () => {
    expect(st(nfloat(p('1/3')))).toBe('0.333333333333333');
    expect(st(nfloat(p('1/3'), 5))).toBe('0.33333');
    expect(st(nfloat(p('sqrt(2)')))).toBe('1.41421356237310');
    expect(st(nfloat(p('x')))).toBe('x');
    expect(st(nfloat(p('x**2/3 + y**(1/2)')))).toBe('0.333333333333333*x**2 + sqrt(y)');
    expect(st(nfloat(p('x**4 + x/2 + cos(pi/3) + 1 + sqrt(y)')))).toBe('x**4 + 0.5*x + sqrt(y) + 1.5');
    expect(st(nfloat(p('sin(x)/7'), 5))).toBe('0.14286*sin(x)');
  });
  it('makes exponents Floats with exponent=true', () => {
    expect(st(nfloat(p('x**4 + x/2 + cos(pi/3) + 1 + sqrt(y)'), 15, true))).toBe('0.5*x + x**4.0 + y**0.5 + 1.5');
    expect(st(nfloat(p('x**2*(x + 1)**2/3'), 15, true))).toBe('0.333333333333333*x**2.0*(x + 1.0)**2.0');
    expect(st(nfloat(p('sin(x) + y**z'), 15, true))).toBe('y**z + sin(x)');
    expect(st(nfloat(p('(x**2 + 1)**3'), 15, true))).toBe('(x**2 + 1.0)**3.0');
    expect(st(nfloat(p('sqrt(x**2 + 1)/3'), 15, true))).toBe('0.333333333333333*(x**2.0 + 1.0)**0.5');
    expect(st(nfloat(p('1/(x**2 + 1)'), 15, true))).toBe('(x**2 + 1.0)**(-1.0)');
  });
});

describe('comp', () => {
  it('compares numbers', () => {
    const f = (s: string) => p(s);
    expect(comp(0, 0)).toBe(true);
    expect(comp(0, 1)).toBe(false);
    expect(comp(1, 1)).toBe(true);
    expect(comp(1, 2)).toBe(false);
    expect(comp(float(1.0), float('1.0000000000000001'))).toBe(true);
    expect(comp(float('3.14', 3), f('pi'))).toBe(true);
    expect(comp(float(f('pi'), 5), float('3.1416', 5))).toBe(true);
    expect(comp(float(f('sqrt(2)'), 3), float(1.41))).toBe(true);
    expect(comp(float('2.0'), 2)).toBe(true);
    expect(comp(2, float('2.0'))).toBe(true);
  });
  it('uses a tolerance', () => {
    expect(comp(1, float(1.01), 0.1)).toBe(true);
    expect(comp(100, 101, 0.1)).toBe(true);
    expect(comp(100, 101, 0.001)).toBe(false);
    expect(comp(float(1.5), float(1.6), 0.01)).toBe(false);
    expect(comp(0, float(0.05), 0.1)).toBe(true);
    expect(comp(5, 0, 0.1)).toBe(false);
  });
  it('compares strings with the null tolerance', () => {
    expect(comp(float('1.5'), float('1.5'), '')).toBe(true);
    expect(comp(float('1.5'), float('1.50', 4), '')).toBe(false);
  });
});

describe('nsimplify', () => {
  it('rationalizes Floats', () => {
    const cases: [Expr, Parameters<typeof nsimplify>[1], string][] = [
      [float(0.5), {}, '1/2'],
      [float(0.333333333333333), {}, '1/3'],
      [p('x + 0.25'), {}, 'x + 1/4'],
      [float(0.1), { rational: true, rationalConversion: 'exact' }, '3602879701896397/36028797018963968'],
      [float(3.14159), { tolerance: 0.01 }, '22/7'],
      [p('pi'), { tolerance: 0.01 }, '22/7'],
      [p('x*0.333'), { tolerance: 0.001 }, '333*x/1000'],
      [p('zoo'), {}, 'zoo'],
      [p('sqrt(3)/2 + I/2'), {}, 'sqrt(3)/2 + I/2'],
      [p('1/sqrt(7)'), {}, 'sqrt(7)/7'],
      [p('sqrt(17) - 1'), {}, '-1 + sqrt(17)'],
      [p('7/3'), {}, '7/3'],
      [p('x**2'), {}, 'x**2'],
      [float(0.5), { tolerance: 2 }, '1/2'],
      [p('oo'), { tolerance: 0.1 }, 'oo'],
      [p('oo'), {}, 'oo'],
      [p('exp(1000)'), {}, 'exp(1000)'],
      [p('1/(pi + 1)'), { constants: [p('pi')] }, '1/(1 + pi)'],
      [p('1 + sqrt(3)/7'), {}, 'sqrt(3)/7 + 1'],
      [float(0.333), { tolerance: 0.001 }, '1/3'],
      [float(2.718), { tolerance: 0.01 }, '19/7'],
      [float(0.1), { tolerance: 0.5 }, '1/10'],
      [float(-0.6667), { tolerance: 0.001 }, '-2/3'],
      [p('x + 2.718'), { tolerance: 0.01 }, 'x + 106/39'],
    ];
    for (const [e, o, want] of cases) expect([st(e), st(nsimplify(e, o))]).toEqual([st(e), want]);
  });
});

/**
 * Coverage of numeric/nfloat.ts (nsimplify), mpeval.ts and round.ts.
 * Expected values from SymPy 1.14 / mpmath 1.3.
 */

describe('nsimplify', () => {
  it('identifies exact numbers', () => {
    const cases: [string, Parameters<typeof nsimplify>[1], string][] = [
      // SymPy: an undefined function has no value, the expression comes back
      ['f(1)', {}, 'f(1)'],
      // log(x) is not linear in the constants
      ['exp(1/3)', { constants: [p('pi')] }, 'exp(1/3)'],
      // 1/2 + 1.1e-7: no quadratic with a nonzero discriminant fits
      ['1/2 + exp(-16)', {}, 'exp(-16) + 1/2'],
      // 1/2 + 1.9e-12 fits (2x - 1)(x + 1) = 0: the rational root
      ['1/2 + exp(-27)', {}, '1/2'],
      ['sqrt(2) + exp(-25)', {}, 'sqrt(2)'],
      ['-5/3 + exp(-26)', {}, '-5/3'],
    ];
    for (const [e, o, want] of cases) expect([e, sstr(nsimplify(p(e), o))]).toEqual([e, want]);
    expect(sstr(nsimplify(SymFunction('f')(1)))).toBe('f(1)');
  });
  it('gives up on a convergent that never meets the tolerance', () => {
    // no convergent of the double is within 1e-30: 40 terms, or a fraction part 0
    expect(simpleRational(Math.sqrt(3) / 8, 1e-30)).toBeUndefined();
    expect(simpleRational(5.610306332244461e-14, 1e-30)).toBeUndefined();
    expect(sstr(simpleRational(0.75, 1e-14) ?? p('0'))).toBe('3/4');
  });
});

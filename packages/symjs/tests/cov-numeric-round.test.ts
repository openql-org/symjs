// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Expected values from SymPy 1.14 (round, Float, nfloat, comp, nsimplify).

import { describe, expect, it } from 'vitest';
import { comp, float, nfloat, nsimplify, parse, round, sstr } from '../src';
import type { Expr } from '../src';
import { Float } from '../src/core/nodes';

const p = (s: string) => parse(s);
const st = (e: Expr) => sstr(e);
const prec = (e: Expr) => (e instanceof Float ? e.prec : -1);

describe('round (SymPy Expr.round)', () => {
  it('rounds numbers to decimal places', () => {
    const cases: [string, number | undefined, string][] = [
      ['1234.5678', 2, '1234.57'],
      ['1234.5678', -2, '1200.00000000000'],
      ['12345', -2, '12300'],
      ['-12355', -1, '-12360'],
      ['12345', undefined, '12345'],
      ['pi', 3, '3.142'],
      ['pi', undefined, '3'],
      ['-pi', 4, '-3.1416'],
      ['2 + 3*I*pi', 1, '2 + 9.4*I'],
      ['0', undefined, '0'],
      ['0', 2, '0'],
      ['2.5', undefined, '2'],
      ['3.5', undefined, '4'],
      ['-2.5', undefined, '-2'],
      ['1/3', 0, '0.0'],
      ['2/3', 0, '1.00000000000000'],
      ['0.0012345', 5, '0.00123'],
      ['oo', undefined, 'oo'],
      ['10**20 + 1/2', undefined, '100000000000000000000'],
      ['10**20 + 5/2', undefined, '100000000000000000002'],
      // SymPy 1.14 gives 100000000000000000001: its tie test compares a 1-digit
      // Float with 0.5, which is False since Floats of different precision are
      // unequal; half-to-even rounding of 10**20 + 3/2 is 10**20 + 2
      ['10**20 + 3/2', undefined, '100000000000000000002'],
      ['25/10', 0, '2.00000000000000'],
      ['15/100', 1, '0.2'],
      ['-1/2', undefined, '0'],
      ['1000*E', -2, '2700.00000000000'],
      ['5/10', 0, '0.0'],
      ['0.006', 2, '0.01'],
      ['0.004', 2, '0.0'],
      ['0.0051', 2, '0.01'],
      ['6/1000', 2, '0.01'],
    ];
    for (const [x, n, want] of cases) expect([x, n, st(round(p(x), n))]).toEqual([x, n, want]);
  });
  it('keeps the precision of Floats', () => {
    expect(st(round(float('0.123456789', 5), 3))).toBe('0.123');
    expect(st(round(float('12.5', 3), 0))).toBe('12.0');
    expect(st(round(float('123.456', 4), 1))).toBe('123.5');
    expect(st(round(float('1e30'), -28))).toBe('1000000000000000000000000000000.');
    expect(st(round(float(1e30), -28))).toBe('1.00000000000000e+30');
    expect(st(round(float(1e30), -31))).toBe('0.0');
    expect(st(round(float(123456789.0, 5), -2))).toBe('1.2346e+8');
  });
  it('rejects symbols', () => {
    expect(() => round(p('x'))).toThrow(TypeError);
  });
});

describe('Float constructor (SymPy Float)', () => {
  it('parses strings', () => {
    const cases: [string, string, number][] = [
      ['1.5e3', '1500.00000000000', 53],
      ['.5', '0.500000000000000', 53],
      ['-.25', '-0.250000000000000', 53],
      [' 1 000 ', '1000.00000000000', 53],
      ['1_000.5', '1000.50000000000', 53],
      ['12345678901234567890', '12345678901234567890.', 70],
      ['+1.5', '1.50000000000000', 53],
      ['1e20', '100000000000000000000.', 73],
      ['1.', '1.00000000000000', 53],
    ];
    for (const [s, want, pr] of cases) {
      const f = float(s);
      expect([s, st(f), prec(f)]).toEqual([s, want, pr]);
    }
    expect(st(float('inf'))).toBe('oo');
    expect(st(float('-inf'))).toBe('-oo');
    expect(st(float('nan'))).toBe('nan');
    expect(() => float('abc')).toThrow(SyntaxError);
    expect(() => float('1.2.3')).toThrow(SyntaxError);
    expect(() => float('')).toThrow();
  });
  it('infers the precision from the digits with the null string', () => {
    const cases: [string, string, number][] = [
      ['1.25', '1.25', 13],
      ['100', '100.', 13],
      ['1e3', '1000.', 17],
      ['0.000', '0.0', 7],
    ];
    for (const [s, want, pr] of cases) {
      const f = float(s, '');
      expect([s, st(f), prec(f)]).toEqual([s, want, pr]);
    }
    const five = float(p('5'), '');
    expect([st(five), prec(five)]).toEqual(['5.', 7]);
    expect(() => float(1.5, '')).toThrow(TypeError);
  });
  it('converts doubles, integers and exact numbers', () => {
    expect(st(float(Number.NaN))).toBe('nan');
    expect(st(float(Infinity))).toBe('oo');
    expect(st(float(-Infinity))).toBe('-oo');
    expect(st(float(0))).toBe('0.0');
    expect([st(float(12345678901234567890n)), prec(float(12345678901234567890n))]).toEqual(['12345678901234567890.', 70]);
    expect(st(float(p('1/3'), 20))).toBe('0.33333333333333333333');
    expect(st(float(float('1.5'), 30))).toBe('1.50000000000000000000000000000');
    expect(st(float(p('pi'), 20))).toBe('3.1415926535897932385');
    expect(st(float(p('oo')))).toBe('oo');
    expect([st(float(0.1, 5)), prec(float(0.1, 5))]).toEqual(['0.10000', 20]);
    const f = float('1.5');
    expect(float(f)).toBe(f);
    expect(st(float(1.5, undefined, 100))).toBe('1.5000000000000000000000000000');
  });
  it('evaluates exact expressions', () => {
    // SymPy raises TypeError (cannot create mpf from 1 + sqrt(2)); symjs evaluates
    // the real number, mpmath gives 2.414213562
    expect(st(float(p('sqrt(2) + 1'), 10))).toBe('2.414213562');
    expect(() => float(p('1 + I'), 10)).toThrow(TypeError);
    expect(() => float(p('x'), 10)).toThrow();
  });
});

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

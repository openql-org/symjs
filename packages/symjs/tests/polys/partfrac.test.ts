// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/polys/partfrac.ts: partial fraction decomposition (apart); expected values from SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { apart, doit, parse, sstr, str, symbols } from '../../src';

const [x, y] = symbols('x y');
const P = (s: string) => parse(s, { symbols: { x: x!, y: y! } });

describe('apart', () => {
  it('generators and factors free of the variable', () => {
    expect(String(sj.apart(parse('1/(y*(x + 1))'), x))).toBe('1/(y*(x + 1))');
    expect(String(sj.apart(parse('(x**2 + 1)/(x + 1)')))).toBe('x - 1 + 2/(x + 1)');
    expect(String(sj.apart(parse('1/((x + 1)*(x + 2))')))).toBe('-1/(x + 2) + 1/(x + 1)');
    // SymPy: NotImplementedError multivariate partial fraction decomposition
    expect(() => sj.apart(parse('x/(x + y)'))).toThrow(sj.NotImplementedError);
    expect(String(sj.apart(parse('1/2')))).toBe('1/2');
    expect(String(sj.apart(parse('x**2 + 1')))).toBe('x**2 + 1');
  });
});

describe('apart (expected values from SymPy 1.14)', () => {
  const cases: [string, string][] = [
    ['y/((x + 2)*(x + 1))', '-y/(x + 2) + y/(x + 1)'],
    ['1/(x**2*(x+1))', '1/(x + 1) - 1/x + x**(-2)'],
    ['(x**3+1)/(x**2-1)', 'x + 1/(x - 1)'],
    ['1/(x**2+1)/(x-1)', '-(x + 1)/(2*(x**2 + 1)) + 1/(2*(x - 1))'],
    ['(2*x+3)/(x-1)**3', '2/(x - 1)**2 + 5/(x - 1)**3'],
    ['1/(2*x+2)', '1/(2*(x + 1))'],
    ['x/(x**2-2)', 'x/(x**2 - 2)'],
  ];
  for (const [e, want] of cases) it(e, () => expect(str(apart(P(e), x!))).toBe(want));
});

describe('RootSum and full partial fractions', () => {
  it('match SymPy apart(full=True)', async () => {
    const { apart } = await import('../../src');
    const x = symbols('x')[0];
    const full = (s: string) => sstr(apart(parse(s), x, { full: true }));
    expect(full('y/(x**2 + x + 1)')).toBe('RootSum(_w**2 + _w + 1, Lambda(_a, (-2*_a*y/3 - y/3)/(-_a + x)))');
    expect(full('1/(x**2-2)')).toBe('RootSum(_w**2 - 2, Lambda(_a, _a/(-_a + x)))/4');
    expect(full('1/(x**3+1)')).toBe('-RootSum(_w**2 - _w + 1, Lambda(_a, _a/(-_a + x)))/3 + 1/(3*(x + 1))');
    expect(full('t/(x**2+x+t)')).toBe('RootSum(_w**2 + _w + t, Lambda(_a, (-2*_a*t/(4*t - 1) - t/(4*t - 1))/(-_a + x)))');
    expect(full('36/(x**5 - 2*x**4 - 2*x**3 + 4*x**2 + x - 2)')).toBe('-4/(x + 1) - 3/(x + 1)**2 - 9/(x - 1)**2 + 4/(x - 2)');
    expect(sstr(doit(apart(parse('2/(x**2-2)'), x, { full: true })))).toBe('-sqrt(2)/(2*(x + sqrt(2))) + sqrt(2)/(2*(x - sqrt(2)))');
  });
});

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/integrals/trigonometry.ts (SymPy trigintegrate). Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Sym, parse, sstr } from '../../src';
import { trigintegrate } from '../../src/integrals/trigonometry';

const x = new Sym('x');
const T = (s: string): string => {
  const r = trigintegrate(parse(s), x);
  return r === undefined ? 'None' : sstr(r);
};

describe('trigintegrate', () => {
  it.each([
    ['sin(x)**3', 'cos(x)**3/3 - cos(x)'],
    ['cos(x)**5*sin(x)**2', 'sin(x)**7/7 - 2*sin(x)**5/5 + sin(x)**3/3'],
    ['sin(x)**3*cos(x)**3', '-sin(x)**6/6 + sin(x)**4/4'],
    ['sin(x)**5*cos(x)**3', '-sin(x)**8/8 + sin(x)**6/6'],
    ['sin(x)**(-1)*cos(x)**3', 'log(sin(x)) - sin(x)**2/2'],
    ['sin(x)**3/cos(x)', '-log(cos(x)) + cos(x)**2/2'],
    ['1/(sin(x)*cos(x)**3)', 'log(cos(x)**2 - 1)/2 - log(cos(x)) + 1/(2*cos(x)**2)'],
    ['1/(sin(x)**3*cos(x))', '-log(sin(x)**2 - 1)/2 + log(sin(x)) - 1/(2*sin(x)**2)'],
    ['sin(x)**4*cos(x)**2', 'x/16 + sin(x)**5*cos(x)/6 - sin(x)**3*cos(x)/24 - sin(x)*cos(x)/16'],
    ['sin(x)**4', '3*x/8 - sin(x)**3*cos(x)/4 - 3*sin(x)*cos(x)/8'],
    ['sin(x)**4/cos(x)**2', '-3*x/2 + sin(x)**3/cos(x) + 3*sin(x)*cos(x)/2'],
    ['sin(x)**2*cos(x)**4', 'x/16 - sin(x)*cos(x)**5/6 + sin(x)*cos(x)**3/24 + sin(x)*cos(x)/16'],
    ['cos(x)**4', '3*x/8 + sin(x)*cos(x)**3/4 + 3*sin(x)*cos(x)/8'],
    ['cos(x)**4/sin(x)**2', '-3*x/2 - 3*sin(x)*cos(x)/2 - cos(x)**3/sin(x)'],
    ['sin(x)**2*cos(x)**2', 'x/8 - sin(2*x)*cos(2*x)/16'],
    ['sin(x)**(-2)*cos(x)**2', '-x - cos(x)/sin(x)'],
    ['sin(x)**2/cos(x)**2', '-x + sin(x)/cos(x)'],
    ['1/sin(x)**4', '-2*cos(x)/(3*sin(x)) - cos(x)/(3*sin(x)**3)'],
    ['1/cos(x)**4', '2*sin(x)/(3*cos(x)) + sin(x)/(3*cos(x)**3)'],
    ['1/sin(x)**3', 'log(cos(x) - 1)/4 - log(cos(x) + 1)/4 + cos(x)/(2*cos(x)**2 - 2)'],
    ['1/cos(x)**3', '-log(sin(x) - 1)/4 + log(sin(x) + 1)/4 - sin(x)/(2*sin(x)**2 - 2)'],
    ['sin(2*x)**2/cos(2*x)**4', '-sin(2*x)/(6*cos(2*x)) + sin(2*x)/(6*cos(2*x)**3)'],
    ['sin(a*x)**2', 'Piecewise(((a*x/2 - sin(a*x)*cos(a*x)/2)/a, Ne(a, 0)), (0, True))'],
    ['cos(a*x)', 'Piecewise((sin(a*x)/a, Ne(a, 0)), (x, True))'],
    // not of the form sin(a*x)**n*cos(a*x)**m
    ['sin(x)*cos(2*x)', 'None'],
    ['x*sin(x)', 'None'],
    ['sin(x)**(1/2)', 'None'],
    ['sin(x + 1)', 'None'],
    ['sin(x**2)', 'None'],
  ])('%s', (f, want) => expect(T(f)).toBe(want));

  it('differs from SymPy', () => {
    // SymPy: x (n = m = 0) and -log(cos(x)) + cos(x)**2/2 (tan rewritten as sin/cos); integrate handles both itself
    expect(T('1')).toBe('None');
    expect(T('sin(x)**2*tan(x)')).toBe('None');
  });
});

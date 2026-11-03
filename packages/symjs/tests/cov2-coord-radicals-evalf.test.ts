// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * Numeric radicals combined as SymPy Integer._eval_power and Mul.flatten do,
 * and evalf keeping the arguments of undefined functions exact. Expected
 * values from SymPy 1.14.
 */

import { describe, expect, it } from 'vitest';
import * as sj from '../src';

const [x, y] = sj.symbols('x y');
const f = sj.SymFunction('f');
const P = (s: string): sj.Expr => sj.parse(s, { symbols: { x, y }, functions: { f } } as never);

describe('numeric radicals (SymPy Integer._eval_power, Mul.flatten)', () => {
  const cases: [string, string][] = [
    ['12**(2/3)', '2*18**(1/3)'],
    ['(12*x)**(2/3)', '2*18**(1/3)*x**(2/3)'],
    ['(12*x*y)**(2/3)', '2*18**(1/3)*(x*y)**(2/3)'],
    ['(24*x)**(1/3)', '2*3**(1/3)*x**(1/3)'],
    ['72**(1/3)', '2*3**(2/3)'],
    ['12**(5/6)', '2*2**(2/3)*3**(5/6)'],
    ['(1/12)**(2/3)', '12**(1/3)/12'],
    ['(-12)**(2/3)', '2*(-1)**(2/3)*18**(1/3)'],
    ['2**(-1/3)', '2**(2/3)/2'],
    ['(3/2)**(1/3)', '2**(2/3)*3**(1/3)/2'],
    ['(2/3)**(1/2)', 'sqrt(6)/3'],
    ['sqrt(8/9)', '2*sqrt(2)/3'],
    ['2**(1/3)*3**(2/3)', '2**(1/3)*3**(2/3)'],
    ['2**(2/3)*3**(2/3)', '6**(2/3)'],
    ['2**(1/3)*5**(2/3)*7**(1/3)', '14**(1/3)*5**(2/3)'],
    ['2**(3/4)*3**(1/4)', '2**(3/4)*3**(1/4)'],
    ['sqrt(6)*2**(1/3)', '2**(5/6)*sqrt(3)'],
    ['sqrt(2)*sqrt(6)', '2*sqrt(3)'],
    ['2**(1/3)*4**(1/3)', '2'],
    ['sqrt(12)*3**(1/3)', '2*3**(5/6)'],
    ['6**(1/2)*6**(1/3)', '6**(5/6)'],
    ['sqrt(2)*2**(1/3)', '2**(5/6)'],
    ['(12*(x + y))**(2/3)', '(12*x + 12*y)**(2/3)'],
  ];
  it.each(cases)('%s', (src, expected) => {
    expect(String(P(src))).toBe(expected);
  });
});

describe('evalf keeps the arguments of undefined functions', () => {
  const cases: [string, string][] = [
    ['f(1)', 'f(1)'],
    ['f(x/3)', 'f(x/3)'],
    ['f(pi)', 'f(pi)'],
    ['f(1, x/3)', 'f(1, x/3)'],
    ['2*f(1) + pi', '2.0*f(1) + 3.14159265358979'],
  ];
  it.each(cases)('%s', (src, expected) => {
    expect(String(sj.evalf(P(src)))).toBe(expected);
  });
});

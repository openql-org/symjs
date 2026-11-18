// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { describe, expect, it } from 'vitest';
import { Eq, Float, IntervalPrinter, parse } from '../../src';

describe('IntervalPrinter', () => {
  const p = new IntervalPrinter();
  it.each([
    ['x**(1/3)', "x**(mpi('1/3'))"],
    ['x**(1/2)', "x**(mpi('1/2'))"],
    ['x**2', "x**mpi('2')"],
    ['(x+y)**(-2)', "(x + y)**(mpi('-2'))"],
    ['x+y-2', "x + y + mpi('-2')"],
    ['x-y', 'x - y'],
    ['3*x*y/2', "(mpi('3/2'))*x*y"],
    ['-x/y', '-x/y'],
    ['1/(x*y)', "mpi('1')/(x*y)"],
    ['x/(y**2*z)', "x/(y**mpi('2')*z)"],
    ['x**(-1)', "x**(mpi('-1'))"],
    ['sin(x) + exp(x)', 'mpmath.exp(x) + mpmath.sin(x)'],
    ['pi', 'mpmath.pi'],
    ['oo', 'mpmath.inf'],
  ])('prints %s as Python code', (input, expected) => expect(p.doprint(parse(input))).toBe(expected));

  it('preserves float precision and reports unsupported operators', () => {
    expect(p.doprint(new Float(0.125))).toBe('mpmath.mpf((0, 1, -3, 1))');
    expect(p.doprint(new Float(-0.125))).toBe('mpmath.mpf((1, 1, -3, 1))');
    expect(p.doprint(new Float(0))).toBe('mpmath.mpf((0, 0, 0, 0))');
    expect(() => p.doprint(Eq(parse('x'), 1))).toThrow(/interval printing/);
  });
});

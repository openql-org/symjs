// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Coverage of functions/trigext.ts. Expected values are str() results of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { S, mul, parse, tan } from '../src';

const cases: [string, string][] = [
  // _peeloff_ipi / _peeloff_pi with a coefficient below 1/2 and with negative coefficients
  ['sinh(x + I*pi/4)', 'sinh(x + I*pi/4)'],
  ['sinh(x - 3*I*pi/2)', 'I*cosh(x)'],
  ['cosh(x - I*pi)', '-cosh(x)'],
  ['tan(x - 3*pi/2)', '-cot(x)'],
  ['tan(x - pi)', 'tan(x)'],
  ['cot(x-3*pi/2)', '-tan(x)'],
  // csc and sec through the value of sin and cos
  ['csc(x + pi)', '-csc(x)'],
  ['sec(x+pi)', '-sec(x)'],
  ['csc(x+pi/2)', 'sec(x)'],
  // the half-angle formula does not apply when cos(2*x) does not evaluate
  ['tan(pi/14)', 'tan(pi/14)'],
  ['cot(pi/14)', 'cot(pi/14)'],
  ['tan(I*y - I*x)', '-I*tanh(x - y)'],
  // table values at non-real arguments
  ['acosh(I)', 'log(1 + sqrt(2)) + I*pi/2'],
  ['asech(I)', 'log(1 + sqrt(2)) - I*pi/2'],
  ['acot(sqrt(3))', 'pi/6'],
  ['acot(1-sqrt(2))', '-3*pi/8'],
  ['acot(-1-sqrt(2))', '-pi/8'],
  ['acot(sqrt(3)-2)', '-5*pi/12'],
  ['asec(3)', 'asec(3)'],
  ['acsc(3)', 'acsc(3)'],
  ['sinc(pi/2)', '2/pi'],
  ['sinc(3*pi/2)', '-2/(3*pi)'],
  ['sinc(pi/3)', 'sinc(pi/3)'],
  ['csc(asin(x))', '1/x'],
  ['cot(acot(x))', 'x'],
];

describe('trigext evaluation', () => {
  it.each(cases)('%s', (src, want) => {
    expect(String(parse(src))).toBe(want);
  });
  it('tan of an imaginary multiple', () => {
    // SymPy tan(I*(1 - x)) = -I*tanh(x - 1)
    expect(String(tan(mul(S.I, parse('1 - x'))))).toBe('-I*tanh(x - 1)');
  });
});

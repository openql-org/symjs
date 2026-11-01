// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { describe, expect, it } from 'vitest';
import { apart, parse, str, symbols } from '../src';

const [x, y] = symbols('x y');
const P = (s: string) => parse(s, { symbols: { x: x!, y: y! } });

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

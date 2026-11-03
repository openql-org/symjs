// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Coverage of the expression parser: expected values are
 * `str(parse_expr(s))` (and `evaluate=False`) of SymPy 1.14.
 */

import { describe, expect, it } from 'vitest';
import * as sj from '../src';
import { ex, parse } from '../src/parsing/parser';

const s = (src: string, opts: Parameters<typeof parse>[1] = {}): string => sj.str(parse(src, opts));

describe('parse', () => {
  const cases: [string, string][] = [
    ['x + 1   ', 'x + 1'],
    ['ln(x)', 'log(x)'],
    ['digamma(x)', 'polygamma(0, x)'],
    ['trigamma(x)', 'polygamma(1, x)'],
    ['E1(x)', 'expint(1, x)'],
    ['RisingFactorial(x, 3)', 'x*(x + 1)*(x + 2)'],
    ['FallingFactorial(x, 3)', 'x*(x - 2)*(x - 1)'],
    ['diff(x**3, x, 2)', '6*x'],
    ['diff(sin(x), x)', 'cos(x)'],
  ];
  for (const [src, want] of cases) it(src, () => expect(s(src)).toBe(want));

  const raw: [string, string][] = [
    ['x - y', 'x - y'],
    ['-x', '-x'],
    ['+x', 'x'],
    ['-2', '-2'],
    ['x + (y + z)', 'x + y + z'],
    ['x*(y*z)', 'x*y*z'],
    ['x/y', 'x/y'],
    ['(x)', 'x'],
  ];
  for (const [src, want] of raw) it(`${src} (evaluate=False)`, () => expect(s(src, { evaluate: false })).toBe(want));

  it('symbols given as a list', () => {
    const x = sj.symbol('x', { positive: true });
    const e = parse('x + 1', { symbols: [x] });
    expect(e.freeSymbols().has(x)).toBe(true);
  });

  it('syntax errors', () => {
    expect(() => parse('x $ y')).toThrow(SyntaxError);
    expect(() => parse('diff(x)')).toThrow('diff() takes at least 2 arguments');
    expect(() => parse('(x')).toThrow("Expected ')'");
    expect(() => parse('2 x')).toThrow('implicit multiplication is not supported');
    expect(() => parse('*x')).toThrow("Unexpected '*'");
    expect(() => parse('x +')).toThrow('Unexpected end of input');
    expect(() => parse('')).toThrow('Unexpected end of input');
  });

  it('ex with an interpolated number', () => {
    const x = sj.symbol('x');
    expect(sj.str(ex`${2}*${x} + 1`)).toBe('2*x + 1');
  });
});

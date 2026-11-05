// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/series/approximants.ts.
// Pade approximants of a series. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { approximants } from '../../src/series/approximants';

const range = (a: number, b: number): number[] => Array.from({ length: b - a }, (_, i) => a + i);
const strs = (g: Iterable<sj.Expr>): string[] => [...g].map(sj.str);

describe('approximants', () => {
  it('gives the approximants of numeric sequences', () => {
    expect(strs(approximants(range(0, 16).map((k) => sj.lucas(k))))).toEqual(['2', '-4/(x - 2)', '(5*x - 2)/(3*x - 1)', '(x - 2)/(x**2 + x - 1)']);
    expect(strs(approximants(range(0, 16).map((k) => sj.fibonacci(k))))).toEqual(['x', '-x/(x - 1)', '(x**2 - x)/(2*x - 1)', '-x/(x**2 + x - 1)']);
    expect(strs(approximants([1, 0, 1, 0, 1, 0]))).toEqual(['1', '-1/(x**2 - 1)']);
    expect(strs(approximants([0, 0, 0]))).toEqual([]);
  });
  it('simplifies symbolic approximants on request', () => {
    const [x, t] = sj.symbols('x t') as sj.Sym[];
    const p = range(0, 6).map((k) => sj.add(...range(0, k + 1).map((i) => sj.mul(sj.binomial(k, i), sj.pow(x!, i)))));
    expect(strs(approximants(p, t, { simplify: true })).slice(0, 3)).toEqual(['1', '-1/(t*(x + 1) - 1)', 'nan']);
    expect(strs(approximants(p, t)).slice(0, 3)).toEqual(['1', '(x + 1)/((-x - 1)*(t*(x + 1) + (x + 1)/(-x - 1)))', 'nan']);
  });
});

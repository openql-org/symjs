// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/series/kauers.ts.
// Finite differences of expressions and sums. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { finiteDiff, finiteDiffKauers } from '../../src/calculus';

const [x, y, z, n, m, k] = sj.symbols('x y z n m k') as sj.Sym[];
const P = (s: string): sj.Expr => sj.parse(s, { symbols: [x!, y!, z!, n!, m!, k!] });
const s = (e: sj.Expr): string => sj.str(e);

describe('finite differences', () => {
  it('finite_diff', () => {
    expect(s(finiteDiff(P('x**2'), x!))).toBe('2*x + 1');
    expect(s(finiteDiff(P('y**3 + 2*y**2 + 3*y + 4'), y!))).toBe('3*y**2 + 7*y + 6');
    expect(s(finiteDiff(P('x**2 + 3*x + 8'), x!, 2))).toBe('4*x + 10');
    expect(s(finiteDiff(P('z**3 + 8*z'), z!, 3))).toBe('9*z**2 + 27*z + 51');
    expect(s(finiteDiff(P('(x + 1)*(x + 2)'), x!))).toBe('2*x + 4');
  });
  it('finite_diff_kauers', () => {
    expect(s(finiteDiffKauers(sj.Sum(k!, [k!, 1, n!])))).toBe('n + 1');
    expect(s(finiteDiffKauers(sj.Sum(P('1/k'), [k!, 1, n!])))).toBe('1/(n + 1)');
    expect(s(finiteDiffKauers(sj.Sum(P('x*y**2'), [x!, 1, n!], [y!, 1, m!])))).toBe('(m + 1)**2*(n + 1)');
    expect(s(finiteDiffKauers(sj.Product(k!, [k!, 1, n!])))).toBe('n + 1');
    expect(() => finiteDiffKauers(x!)).toThrow(TypeError);
  });
});

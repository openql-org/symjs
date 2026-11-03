// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/indexed.ts.
// Indexed objects. Expected values are SymPy 1.14's.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { type Expr, IndexedBase, add, diff, mul, parse, pow, sstr, str, symbols } from '../../src';

const [x, i, j] = symbols('x i j');

const s = (e: unknown): string => str(e as Expr);

describe('small core nodes', () => {
  it('prints and differentiates indexed objects', () => {
    const A = new sj.IndexedBase('A');
    const i = sj.symbol('i');
    expect(String(A)).toBe('A');
    expect(String(new sj.IndexedBase(sj.symbol('B')))).toBe('B');
    expect(String(sj.diff(A.at(i), A.at(i)))).toBe('1');
  });
});

describe('Indexed derivatives', () => {
  const A = new IndexedBase('A');
  it('differentiates with respect to indexed objects', () => {
    expect(s(diff(A.at(i), A.at(i)))).toBe('1');
    expect(s(diff(A.at(i), A.at(j)))).toBe('KroneckerDelta(i, j)');
    expect(s(diff(pow(A.at(i), 2), A.at(i)))).toBe('2*A[i]');
    expect(s(diff(pow(A.at(i), 2), A.at(j)))).toBe('2*KroneckerDelta(i, j)*A[i]');
    expect(s(diff(mul(A.at(i), A.at(j)), A.at(j)))).toBe('KroneckerDelta(i, j)*A[j] + A[i]');
    expect(s(diff(pow(A.at(i), 3), A.at(i), 2))).toBe('6*A[i]');
    expect(s(diff(x, A.at(i)))).toBe('0');
    expect(() => diff(A.at(i, j), A.at(i))).toThrow(RangeError);
  });
  it('differentiates with respect to an index or the label', () => {
    expect(s(diff(A.at(i), i))).toBe('nan');
    expect(s(diff(A.at(add(i, 1)), i))).toBe('nan');
    expect(s(diff(A.at(i), A.label))).toBe('0');
  });
});

describe('Indexed and equations with several radicals', () => {
  it('match SymPy', async () => {
    const { IndexedBase, Sum, solve, summation } = await import('../../src');
    const f = new IndexedBase('f');
    const n = symbols('n')[0];
    expect(sstr(f.at(n))).toBe('f[n]');
    expect(sstr(summation(f.at(n).pow(2), [n, 0, 3]))).toBe('f[0]**2 + f[1]**2 + f[2]**2 + f[3]**2');
    void Sum;
    const x = symbols('x')[0];
    expect(solve(parse('-x**(1/5) + x**(1/3) + 1/7'), x).map((e) => sstr(e))).toEqual(['CRootOf(7*x**5 - 7*x**3 + 1, 1)**15', 'CRootOf(7*x**5 - 7*x**3 + 1, 2)**15']);
    expect(solve(parse('x**(1/2) - x**(1/4) - 2'), x).map((e) => sstr(e))).toEqual(['16']);
  });
});

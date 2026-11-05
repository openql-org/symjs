// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/concrete/gosper.ts.
// Gosper's algorithm. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { gosperNormal, gosperSum, gosperTerm } from '../../src/calculus';

const [n, k, m] = sj.symbols('n k m') as sj.Sym[];
const P = (s: string): sj.Expr => sj.parse(s, { symbols: [n!, k!, m!] });
const s = (e: sj.Expr | sj.NoMatchResult): string => (sj.isNoMatch(e) ? 'None' : sj.str(e));

describe('gosper_normal', () => {
  it('normal forms', () => {
    expect(gosperNormal(P('4*n + 5'), P('2*(4*n + 1)*(2*n + 3)'), n!, { polys: false }).map(sj.str)).toEqual(['1/4', 'n + 3/2', 'n + 1/4']);
    expect(gosperNormal(P('4*n + 5'), P('2*(4*n + 1)*(2*n + 3)'), n!).map(String)).toEqual(["Poly(1/4, n, domain='QQ')", "Poly(n + 3/2, n, domain='QQ')", "Poly(n + 1/4, n, domain='QQ')"]);
    expect(gosperNormal(n!, P('n + 3'), n!, { polys: false }).map(sj.str)).toEqual(['n', 'n + 3', '1']);
    expect(gosperNormal(1, P('n**2'), n!, { polys: false }).map(sj.str)).toEqual(['1', 'n**2', '1']);
    expect(gosperNormal(P('(n + 2)*(n + 4)'), P('n*(n + 1)'), n!, { polys: false }).map(sj.str)).toEqual(['1', '1', 'n**5 + 7*n**4 + 17*n**3 + 17*n**2 + 6*n']);
  });
});

describe('gosper_term and gosper_sum', () => {
  it('Gosper terms', () => {
    expect(s(gosperTerm(P('(4*n + 1)*factorial(n)/factorial(2*n + 1)'), n!))).toBe('(-n - 1/2)/(n + 1/4)');
    expect(s(gosperTerm(P('factorial(n)'), n!))).toBe('None');
    expect(s(gosperTerm(P('1/n'), n!))).toBe('None');
    expect(s(gosperTerm(n!, n!))).toBe('(n**2/2 - n/2)/n');
    expect(s(gosperTerm(P('2**n'), n!))).toBe('1');
    expect(s(gosperTerm(P('sin(n)'), n!))).toBe('None');
    expect(s(gosperTerm(P('1/(n*(n + 1))'), n!))).toBe('-n - 1');
    expect(s(gosperTerm(P('n**2'), n!))).toBe('(n**3/3 - n**2/2 + n/6)/n**2');
    expect(s(gosperTerm(P('n*(1/2)**n'), n!))).toBe('(-2*n - 2)/n');
  });
  it('Gosper sums', () => {
    const f = P('(4*k + 1)*factorial(k)/factorial(2*k + 1)');
    expect(s(gosperSum(f, [k!, 0, n!]))).toBe('(-factorial(n) + 2*factorial(2*n + 1))/factorial(2*n + 1)');
    expect(s(gosperSum(f, [k!, 3, n!]))).toBe('(-60*factorial(n) + factorial(2*n + 1))/(60*factorial(2*n + 1))');
    expect(s(gosperSum(k!, k!))).toBe('k*(k - 1)/2');
    expect(s(gosperSum(P('2**k'), [k!, 0, n!]))).toBe('2*2**n - 1');
    expect(s(gosperSum(P('binomial(n, k)'), [k!, 0, n!]))).toBe('None');
    expect(s(gosperSum(P('k*factorial(k)'), [k!, 0, n!]))).toBe('n*factorial(n) + factorial(n) - 1');
    expect(s(gosperSum(P('(-1)**k*binomial(m, k)'), [k!, 0, n!]))).toBe('(-1)**n*(m - n)*binomial(m, n)/m');
    expect(s(gosperSum(P('1/(k*(k + 1))'), [k!, 1, sj.S.Infinity]))).toBe('1');
    expect(s(gosperSum(P('k/2**k'), [k!, 0, sj.S.Infinity]))).toBe('2');
  });
});

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/solvers/calculusutil.ts.
// continuous_domain, function_range and lcim. Expected values are those of SymPy 1.14 unless a comment says otherwise.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { continuousDomain, functionRange, lcim } from '../../src/solvers';

const x = sj.symbol('x');
const P = (s: string): sj.Expr => sj.parse(s, { symbols: [x] });
const s = (v: unknown): string => (sj.isNoMatch(v) ? 'None' : sj.str(v as sj.Expr));
const { Reals, EmptySet } = sj;

describe('continuous_domain', () => {
  it('domains of continuity', () => {
    expect(s(continuousDomain(P('1/x'), x, Reals))).toBe('Union(Interval.open(-oo, 0), Interval.open(0, oo))');
    expect(s(continuousDomain(P('tan(x)'), x, sj.Interval.of(0, sj.pi)))).toBe('Union(Interval.Ropen(0, pi/2), Interval.Lopen(pi/2, pi))');
    expect(s(continuousDomain(P('sqrt(x - 2)'), x, sj.Interval.of(-5, 5)))).toBe('Interval(2, 5)');
    expect(s(continuousDomain(P('log(2*x - 1)'), x, Reals))).toBe('Interval.open(1/2, oo)');
    expect(s(continuousDomain(P('x**(1/3)'), x, Reals))).toBe('Reals');
    expect(s(continuousDomain(P('asin(x)'), x, Reals))).toBe('Interval(-1, 1)');
    expect(s(continuousDomain(P('asec(x)'), x, Reals))).toBe('Union(Interval(-oo, -1), Interval(1, oo))');
    expect(s(continuousDomain(P('acot(x)'), x, Reals))).toBe('Union(Interval.open(-oo, 0), Interval.open(0, oo))');
    expect(s(continuousDomain(P('exp(x) + x**2'), x, Reals))).toBe('Reals');
    const doms: [string, string][] = [
      ['acos(x)', 'Interval(-1, 1)'],
      ['acosh(x)', 'Interval(1, oo)'],
      ['atanh(x)', 'Interval.open(-1, 1)'],
      ['asech(x)', 'Interval.Lopen(0, 1)'],
      ['acsc(x)', 'Union(Interval(-oo, -1), Interval(1, oo))'],
      ['acoth(x)', 'Union(Interval.open(-oo, -1), Interval.open(1, oo))'],
    ];
    for (const [f, d] of doms) expect(s(continuousDomain(P(f), x, Reals))).toBe(d);
    expect(s(continuousDomain(x, x, sj.Integers))).toBe('Integers');
    expect(() => continuousDomain(x, x, sj.Complexes)).toThrow('Domain must be a subset of S.Reals.');
    expect(() => continuousDomain(P('gamma(x)'), x, Reals)).toThrow('Unable to determine the domain of the given function.');
  });
});

describe('function_range', () => {
  it('ranges', () => {
    expect(s(functionRange(P('sin(x)'), x, sj.Interval.of(0, sj.mul(2, sj.pi))))).toBe('Interval(-1, 1)');
    expect(s(functionRange(P('1/x'), x, Reals))).toBe('Union(Interval.open(-oo, 0), Interval.open(0, oo))');
    expect(s(functionRange(P('sqrt(x)'), x, sj.Interval.of(-5, 9)))).toBe('Interval(0, 3)');
    expect(s(functionRange(P('exp(x)'), x, Reals))).toBe('Interval.open(0, oo)');
    expect(s(functionRange(x, x, EmptySet))).toBe('EmptySet');
    expect(s(functionRange(3, x, Reals))).toBe('{3}');
    expect(s(functionRange(P('x**2'), x, sj.FiniteSet.of(1, 2)))).toBe('{1, 4}');
    expect(s(functionRange(P('sin(x)'), x, sj.Union(sj.Interval.of(sj.S.NegativeInfinity, 0), sj.Interval.of(1, 2))))).toBe('Interval(-1, 1)');
    expect(s(functionRange(P('x**2'), x, sj.Interval.of(-1, 2)))).toBe('Interval(0, 4)');
    expect(s(functionRange(P('x**2'), x, sj.Interval.of(-1, 2, true, true)))).toBe('Interval.Ropen(0, 4)');
    expect(() => functionRange(x, x, sj.Integers)).toThrow('Unable to find range for the given domain.');
    expect(() => functionRange(P('x - exp(x) - x**5'), x, sj.Interval.of(0, 1))).toThrow(sj.NotImplementedError);
    // (SymPy prints Interval(-oo, oo))
    expect(s(functionRange(P('log(x)'), x, Reals))).toBe('Reals');
  });
});

describe('lcim', () => {
  it('least common multiples of periods', () => {
    expect(s(lcim([sj.Rational.of(1n, 2n), sj.Rational.of(3n, 4n), sj.Rational.of(5n, 6n)]))).toBe('15/2');
    expect(s(lcim([P('2*pi'), P('3*pi'), sj.pi, P('pi/2')]))).toBe('6*pi');
    expect(s(lcim([1, P('2*pi')]))).toBe('None');
    expect(s(lcim([sj.pi, P('sqrt(2)')]))).toBe('None');
  });
});

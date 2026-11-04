// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/series/formal.ts. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { Sym, parse } from '../../src';
import { Expr } from '../../src/core/nodes';

const P = (s: string) => parse(s);
const V = (s: string): Sym => {
  const v = P(s);
  if (!(v instanceof Sym)) throw new TypeError(s);
  return v;
};
const [x, y] = [V('x'), V('y')];
const show = (v: unknown): string => (Array.isArray(v) ? `[${v.map(show).join(', ')}]` : v instanceof Expr ? v.toString() : JSON.stringify(v));

describe('formal power series operations', () => {
  const f = (e: string, x0: unknown = 0) => sj.fps(P(e), x, x0 as number);
  it('multiplies, composes and inverts series like SymPy', () => {
    expect(f('sin(x)').product(f('exp(x)'), x).truncate(4).toString()).toBe('x + x**2 + x**3/3 + O(x**4)');
    expect(f('exp(x)').compose(f('sin(x)'), x).truncate().toString()).toBe('1 + x + x**2/2 - x**4/8 - x**5/15 + O(x**6)');
    expect(f('exp(x)').compose(f('sin(x)')).truncate(8).toString()).toBe('1 + x + x**2/2 - x**4/8 - x**5/15 - x**6/240 + x**7/90 + O(x**8)');
    expect(f('exp(x)').inverse().truncate().toString()).toBe('1 - x + x**2/2 - x**3/6 + x**4/24 - x**5/120 + O(x**6)');
    expect(f('cos(x)').inverse().truncate(8).toString()).toBe('1 + x**2/2 + 5*x**4/24 + 61*x**6/720 + O(x**8)');
    expect(() => f('exp(x)').compose(f('cos(x)'), x)).toThrow('The formal power series of the inner function should not have any constant coefficient term.');
    expect(() => f('sin(x)').inverse()).toThrow('Constant coefficient should exist for an inverse of a formal power series to exist.');
    expect(() => f('sin(x)').product(sj.fps(P('exp(y)'), y), x)).toThrow('Both series should have the same symbol.');
    expect(() => f('sin(x)').product(f('exp(x)'), y)).toThrow('Both series should have the same symbol.');
    expect(() => f('sin(x)').product(f('exp(x)', 1), x)).toThrow('Both series should be calculated about the same point.');
  });

  it('integrates series', () => {
    expect(f('sin(x)').integrate(x).truncate().toString()).toBe('-1 + x**2/2 - x**4/24 + O(x**6)');
    expect(f('sin(x)').integrate().truncate().toString()).toBe('-1 + x**2/2 - x**4/24 + O(x**6)');
    expect(f('sin(x)').integrate(x, [0, 1]).toString()).toBe('1 - cos(1)');
  });

  it('keeps a symbolic factor out of the expansion', () => {
    const s = f('x**n*sin(x**2)');
    expect(s.truncate(8).toString()).toBe('-x**(n + 6)/6 + x**(n + 2) + O(x**(n + 8))');
    expect(s.polynomial(8).toString()).toBe('x**(n + 2) - x**(n + 6)/6');
    expect(show(s.terms(2))).toBe('[x**(n + 2), -x**(n + 6)/6]');
    expect(s.coeff(2).toString()).toBe('x**n');
    expect(f('x**n*cos(x)').truncate(4).toString()).toBe('-x**(n + 2)/2 + x**n + O(x**(n + 4))');
    expect(f('a*cos(x)').truncate(4).toString()).toBe('a - a*x**2/2 + O(x**4)');
    // SymPy: a*(-(x - 1)*sin(1) + cos(1)) + O((x - 1)**2, (x, 1)), the same polynomial
    expect(sj.expand(f('a*cos(x)', 1).polynomial(2)).toString()).toBe('-a*x*sin(1) + a*cos(1) + a*sin(1)');
    expect(f('a*cos(x)', 1).truncate(2).toString()).toBe('a*cos(1) - a*(x - 1)*sin(1) + O((x - 1)**2, (x, 1))');
    // SymPy prints the coefficient sequences too
    expect(f('sin(x)').toString()).toBe('FormalPowerSeries(sin(x), x, 0)');
  });
});

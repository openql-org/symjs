// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/series/fourier.ts. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { Sym, parse } from '../../src';

const V = (s: string): Sym => {
  const v = parse(s);
  if (!(v instanceof Sym)) throw new TypeError(s);
  return v;
};
const x = V('x');
const P = (s: string) => parse(s);

describe('Fourier series operations', () => {
  const s = () => sj.fourierSeries(P('x**2'), x);
  it('shifts and scales like SymPy', () => {
    expect(s().shiftx(1).truncate().toString()).toBe('-4*cos(x + 1) + cos(2*x + 2) + pi**2/3');
    expect(s().scalex(2).truncate().toString()).toBe('-4*cos(2*x) + cos(4*x) + pi**2/3');
    expect(s().shift(1).truncate().toString()).toBe('-4*cos(x) + cos(2*x) + 1 + pi**2/3');
    expect(s().scale(2).truncate().toString()).toBe('-8*cos(x) + 2*cos(2*x) + 2*pi**2/3');
    expect(s().shift(1).scale(2).truncate().toString()).toBe('-8*cos(x) + 2*cos(2*x) + 2 + 2*pi**2/3');
    expect(s().scale(2).shift(1).truncate().toString()).toBe('-8*cos(x) + 2*cos(2*x) + 1 + 2*pi**2/3');
    expect(s().scalex(2).shiftx(1).truncate().toString()).toBe('-4*cos(2*x + 2) + cos(4*x + 4) + pi**2/3');
    expect(s().shiftx(1).fn.toString()).toBe('(x + 1)**2');
    expect(s().scalex(2).fn.toString()).toBe('4*x**2');
    for (const op of ['shift', 'scale', 'shiftx', 'scalex'] as const) expect(() => s()[op](x)).toThrow("'x' should be independent of x");
  });

  it('gives sigma approximations like SymPy', () => {
    expect(sj.fourierSeries(x, x).truncate(4).toString()).toBe('2*sin(x) - sin(2*x) + 2*sin(3*x)/3 - sin(4*x)/2');
    expect(sj.fourierSeries(x, x).sigmaApproximation(4).toString()).toBe('2*sin(x)*sinc(pi/4) - 2*sin(2*x)/pi + 2*sin(3*x)*sinc(3*pi/4)/3');
    expect(sj.fourierSeries(x, x).sigmaApproximation().toString()).toBe('2*sin(x)*sinc(pi/3) - sin(2*x)*sinc(2*pi/3)');
    expect(s().sigmaApproximation(3).toString()).toBe('-4*cos(x)*sinc(pi/3) + cos(2*x)*sinc(2*pi/3) + pi**2/3');
  });
});

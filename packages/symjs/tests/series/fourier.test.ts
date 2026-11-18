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
  it('shares the SeriesBase protocol and rebuilds transformed series', () => {
    const series = s();
    expect(series).toBeInstanceOf(sj.SeriesBase);
    expect([series.start, series.stop, series.length, series.interval].map(String)).toEqual(['0', 'oo', 'oo', 'Interval(0, oo)']);
    expect(series.slice(0, 3).map(String)).toEqual(['pi**2/3', '-4*cos(x)', 'cos(2*x)']);
    expect(String(series[Symbol.iterator]().next().value)).toBe('pi**2/3');
    expect(String(series.term(sj.Rational.of(2)))).toBe('cos(2*x)');
    expect(() => series.getItem(-1)).toThrow(RangeError);
    const y = V('y');
    const shifted = sj.fourierSeries(sj.mul(y, x), x).shiftx(1).scale(2).shift(3);
    const rebuilt = sj.subs(shifted, [[y, 2]]);
    expect(rebuilt).toBeInstanceOf(sj.FourierSeries);
    if (!(rebuilt instanceof sj.FourierSeries)) throw new TypeError('FourierSeries');
    expect(rebuilt.slice(0, 3).map(String)).toEqual(['3', '8*sin(x + 1)', '-4*sin(2*x + 2)']);
    expect([...sj.freeSymbols(shifted)].map(String).sort()).toEqual(['x', 'y']);
  });

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

it('infers the variable and combines series on the same interval', () => {
  const f = sj.fourierSeries(x, x);
  expect(f.period.map(String)).toEqual(['-pi', 'pi']);
  expect(String(f.asLeadingTerm())).toBe('2*sin(x)');
  expect(f.add(f.neg()).equals(0)).toBe(true);
  expect(f.sub(f).equals(0)).toBe(true);
  expect(f.add(f)).toBeInstanceOf(sj.FourierSeries);
  expect(f.add(f.shiftx(1))).toBeInstanceOf(sj.Add);
  const shifted = f.shiftx(1).add(f.shiftx(1));
  expect(shifted instanceof sj.FourierSeries && String(shifted.term(1))).toBe('4*sin(x + 1)');
  expect(f.sub(x)).toBeInstanceOf(sj.Add);
  expect(f.add(x)).toBeInstanceOf(sj.Add);
  expect(f.subs([[x, x.pow(2)]])).toBe(f);
  expect(() => f.add(sj.fourierSeries(x, x, [0, 1]))).toThrow(RangeError);
  expect(() => f.add(sj.fourierSeries(x, x, [f.a, 1]))).toThrow(RangeError);
  expect(sj.fourierSeries(3, undefined)).toEqual(sj.rational(3));
  expect(sj.fourierSeries(x, undefined).equals(f)).toBe(true);
  expect(() => sj.fourierSeries(P('x*y'), undefined)).toThrow(RangeError);
  expect(() => Reflect.apply(sj.fourierSeries, undefined, [x, 3])).toThrow(RangeError);
  expect(() => sj.fourierSeries(x, x, [0, sj.oo])).toThrow(RangeError);
  expect(() => sj.fourierSeries(x, x, [sj.S.NegativeInfinity, 0])).toThrow(RangeError);
});

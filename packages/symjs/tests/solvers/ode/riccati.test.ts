// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { describe, expect, it } from 'vitest';
import * as sj from '../../../src';
import * as R from '../../../src/solvers/ode/riccati';

const x = new sj.Sym('x');
const f = new sj.UndefFn('f', [x]);
const p = (s: string) => sj.Poly.from(sj.parse(s), [x]);
const show = (rows: sj.Expr[][]) => rows.map((row) => row.map(String));

describe('rational Riccati coefficients', () => {
  it('matches rational equations and rejects other equations', () => {
    const d = new sj.Derivative([f, x, sj.S.One]);
    expect(R.matchRiccati(sj.Eq(d, sj.add(sj.pow(f, 2), x)), f, x)[0]).toBe(true);
    expect(R.matchRiccati(d, f, x)).toEqual([false, []]);
    expect(R.matchRiccati(sj.add(d, f), f, x)).toEqual([false, []]);
    expect(R.matchRiccati(sj.add(d, sj.pow(f, 3), sj.pow(f, 2)), f, x)[0]).toBe(false);
    expect(R.matchRiccati(sj.add(d, sj.mul(sj.sin(x), sj.pow(f, 2))), f, x)[0]).toBe(false);
    expect(R.matchRiccati(sj.add(d, sj.pow(f, 2), sj.mul(x, new sj.Sym('a'))), f, x)[0]).toBe(false);
    expect(R.matchRiccati(sj.add(d, sj.pow(f, 2), new sj.Float(0.5)), f, x)[0]).toBe(false);
  });

  it('checks valuations and pole conditions', () => {
    expect(R.valAtInf(p('x'), p('x**3'), x)).toBe(2);
    expect(String(R.limitAtInf(p('x'), p('x**3'), x))).toBe('0');
    expect(String(R.limitAtInf(p('2*x'), p('3*x'), x))).toBe('2/3');
    expect(String(R.limitAtInf(p('-x**2'), p('1'), x))).toBe('-oo');
    expect(R.checkNecessaryConds(2, [1, 2, 4])).toBe(true);
    expect(R.checkNecessaryConds(0, [0])).toBe(false);
    expect(R.checkNecessaryConds(-2, [3])).toBe(false);
    expect(R.checkNecessaryConds(-1, [])).toBe(false);
    expect(R.checkNecessaryConds(1, [])).toBe(false);
  });

  it('expands at finite points and infinity using coefficient division', () => {
    const series = R.rationalLaurentSeries(p('1'), p('1-x'), x, sj.S.Zero, 0, 5);
    expect([...series.values()].map(String)).toEqual(['1', '1', '1', '1', '1']);
    expect([...R.rationalLaurentSeries(p('1'), p('x**2'), x, sj.S.Infinity, 0, 4).values()].map(String)).toEqual(['0', '0', '1', '0']);
    expect(R.inverseTransformPoly(p('x**2'), p('x'), x).map((v) => String(v.asExpr()))).toEqual(['1', 'x']);
    expect(R.inverseTransformPoly(p('0'), p('x'), x).map((v) => String(v.asExpr()))).toEqual(['0', '1']);
  });

  it('constructs finite-pole and infinity choices', () => {
    expect(show(R.constructCCase1(p('-1/4'), p('x**2'), x, sj.S.Zero))).toEqual([['1/2']]);
    expect(show(R.constructCCase1(p('2'), p('x**2'), x, sj.S.Zero))).toEqual([['2'], ['-1']]);
    expect(show(R.constructCCase2(p('1'), p('x**4'), x, sj.S.Zero, 4))).toEqual([['-1', '1'], ['-1', '-1']]);
    expect(R.constructC(p('1'), p('x**4'), x, [sj.S.One, sj.Rational.of(2), sj.S.Zero], [1, 2, 4])).toHaveLength(3);
    expect(show(R.constructDCase6(p('-1/4'), p('x**2'), x))).toEqual([['1/2']]);
    expect(show(R.constructD(p('2'), p('x**2'), x, 2))).toEqual([['2'], ['-1']]);
    expect(show(R.constructD(p('1'), p('1'), x, 0))).toEqual([['1', '0'], ['-1', '0']]);
    expect(show(R.constructD(p('x**4'), p('1'), x, -4))).toEqual([['0', '0', '1', '-1'], ['0', '0', '-1', '-1']]);
  });
});

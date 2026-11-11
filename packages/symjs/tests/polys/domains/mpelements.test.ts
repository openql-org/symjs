// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Reference: SymPy 1.14.0 mpelements and mpmath 1.3.0 element arithmetic.
import { describe, expect, it } from 'vitest';
import { Float, Rational, S } from '../../../src/core';
import { NoMatch } from '../../../src/core/truth';
import { ComplexElement, MPContext, RealElement } from '../../../src/polys/domains/mpelements';
import * as F from '../../../src/numeric/mpf';

const c = new MPContext();
const r = (x: unknown) => c.mpf(x);
const z = (x: unknown, y: unknown = 0) => c.mpc(x, y);

describe('MPContext and its elements', () => {
  it('owns precision, tolerance and parents without global context leakage', () => {
    const high = new MPContext(53, { dps: 60 });
    const x = high.mpf('1.00000000000000000000000000000000000000000000000000000001');
    expect(high.prec).toBe(203);
    expect(high.dps).toBe(60);
    expect(x.gt(1)).toBe(true);
    expect(x.sub(1).isZero).toBe(false);
    expect(c.mpf(x).equals(1)).toBe(true);
    expect(x.context).toBe(high);
    expect(c.prec).toBe(53);
    expect(c.maxDenom).toBe(45035996273704n);
    expect(c.tolerance.value).toBe(100 * 2 ** -52);
    expect(c.makeTol().equals(c.tolerance)).toBe(true);
    expect([c.trapComplex, c.pretty]).toEqual([true, true]);
    expect(new RealElement().isZero).toBe(true);
    expect(new ComplexElement().isZero).toBe(true);
    expect(r(2).parent()).toBe(NoMatch);
    expect(z(2).parent()).toBe(NoMatch);
    high.dps = 20;
    expect(high.prec).toBe(70);
    high.prec = 0;
    expect(high.prec).toBe(1);
    expect(() => { high.prec = Infinity; }).toThrow(RangeError);
    expect(new MPContext(53, { tol: false }).maxDenom).toBe(1000000n);
    expect(new MPContext(53, { tol: '0.1' }).maxDenom).toBe(10n);
    expect(new MPContext(3).makeTol().value).toBe(25);
    for (const tol of [0.1, r(0.1), new Float(0.1)]) expect(new MPContext(3, { tol }).tolerance.value).toBe(0.1);
    expect(new MPContext(3, { tol: 123456789n }).tolerance.data).toEqual(F.fromInt(123456789n));
    expect(new MPContext(3, { tol: Infinity }).maxDenom).toBe(0n);
    expect(c.mpf().isZero).toBe(true);
    expect(c.mpc().isZero).toBe(true);
    expect(c.makeMpf({ man: 3n, exp: -1n }).value).toBe(1.5);
    expect(c.makeMpc([F.ONE, F.ONE]).equals(z(1, 1))).toBe(true);
  });

  it('converts real inputs, special values and complex literals', () => {
    for (const x of [1, 1n, true, '1', new Float(1), Rational.of(1n), { man: 2n, exp: -1n }]) expect(r(x).equals(1)).toBe(true);
    expect(r(false).isZero).toBe(true);
    expect(r(Rational.of(1n, 3n)).toString()).toBe('0.333333333333333');
    expect(r('1/3').equals(r(Rational.of(1n, 3n)))).toBe(true);
    expect(r(r(3)).value).toBe(3);
    for (const x of ['bad', {}, null, undefined, { man: 1, exp: 0n }, { man: 1n, exp: 0 }, { exp: 0n }]) {
      if (x === undefined) expect(r(x).isZero).toBe(true);
      else expect(() => r(x)).toThrow();
    }
    expect(c.convert(r(1))).toBeInstanceOf(RealElement);
    const a = z(2, 3);
    expect(c.convert(a)).toBe(a);
    expect(c.convert('3').equals(3)).toBe(true);
    expect(() => c.convert('3', false)).toThrow(TypeError);
    for (const [input, re, im] of [['1+2j', 1, 2], ['(1 - 2j)', 1, -2], ['2j', 0, 2], ['j', 0, 1], ['+j', 0, 1], ['-j', 0, -1], ['1+j', 1, 1], ['1e-3+2e-4j', 0.001, 0.0002], ['2e-4j', 0, 0.0002], ['3i', 0, 3]] as const) {
      expect(c.convert(input).equals(z(re, im))).toBe(true);
      expect(z(input).equals(z(re, im))).toBe(true);
    }
    expect(c.convert('inf').equals(c.inf)).toBe(true);
    expect(z(a).equals(a)).toBe(true);
    expect(r(' +Infinity ').value).toBe(Infinity);
    expect(r('-inf').value).toBe(-Infinity);
    expect(c.isnan('NaN')).toBe(true);
  });

  it('formats and converts exact binary values without reducing precision', () => {
    expect(r(1).toString()).toBe('1.0');
    expect(r(0.1).repr()).toBe('0.1');
    expect(z(1, 2).repr()).toBe('(1.0 + 2.0j)');
    c.pretty = false;
    expect(r(0.1).repr()).toBe("mpf('0.10000000000000001')");
    const high = new MPContext(70); high.pretty = false;
    expect(high.mpf(1).repr()).toBe("mpf('1.0')");
    expect(c.nan.repr()).toBe("mpf('nan')");
    expect(c.inf.repr()).toBe("mpf('+inf')");
    expect(z(1, -2).toString()).toBe('(1.0 - 2.0j)');
    expect(z(1, 2).toString()).toBe('(1.0 + 2.0j)');
    expect(z(1, 2).repr()).toBe("mpc(real='1.0', imag='2.0')");
    expect(r(1.5).toSympy()).toEqual(new Float(1.5));
    expect([c.inf, c.ninf, c.nan].map(x => x.toSympy())).toEqual([S.Infinity, S.NegativeInfinity, S.NaN]);
    expect(z(1, 2).toSympy().toString()).toBe('1.0 + 2.0*I');
    expect(r(2).toNumber()).toBe(2);
    expect(r(-2.9).toInt()).toBe(-2n);
    expect(r(2.9).toInt()).toBe(2n);
    expect(() => c.inf.toInt()).toThrow(RangeError);
    expect(r(1).real.value).toBe(1);
    expect(r(1).imag.isZero).toBe(true);
    c.pretty = true;
  });

  it('performs real and mixed arithmetic, comparison and powers', () => {
    const a = r(7), b = r(2);
    expect([a.add(b), a.sub(b), a.mul(b), a.div(b), a.neg(), a.pos(), a.abs(), a.conjugate()].map(String)).toEqual(['9.0', '5.0', '14.0', '3.5', '-7.0', '7.0', '7.0', '7.0']);
    expect(r(-2).abs().value).toBe(2);
    expect([a.lt(b), a.le(b), a.gt(b), a.ge(a), a.equals(b)]).toEqual([false, false, true, true, false]);
    expect(a.equals(z(7))).toBe(true);
    expect(a.equals(z(7, 1))).toBe(false);
    expect(a.add(z(1, 2)).equals(z(8, 2))).toBe(true);
    expect(a.sub(z(1, 2)).equals(z(6, -2))).toBe(true);
    expect(a.mul(z(1, 2)).equals(z(7, 14))).toBe(true);
    expect(a.div(z(1, 2)).equals(z(1.4, -2.8))).toBe(true);
    expect(() => a.div(0)).toThrow(RangeError);
    expect([r(7).mod(3), r(-7).mod(3), r(7).mod(-3), r(-6).mod(3)].map(x => x.value)).toEqual([1, 2, -2, 0]);
    expect(() => a.mod(0)).toThrow(RangeError);
    expect(c.isnan(c.inf.mod(3))).toBe(true);
    expect(c.isnan(a.mod(c.inf))).toBe(true);
    expect(r(0).pow(0.5).isZero).toBe(true);
    expect(r(0).pow(0.25).isZero).toBe(true);
    expect(r(4).pow(-0.5).equals(0.5)).toBe(true);
    expect(r(4).pow(1.5).equals(8)).toBe(true);
    expect(r(16).pow(0.25).equals(2)).toBe(true);
    expect(a.pow(2).equals(49)).toBe(true);
    expect(b.pow(-2).equals(0.25)).toBe(true);
    expect(b.pow(0.5).equals(Math.sqrt(2))).toBe(true);
    expect(() => r(-1).pow(0.5)).toThrow(RangeError);
    const loose = new MPContext(); loose.trapComplex = false;
    expect(loose.mpf(-1).pow(0.5).equals(z(0, 1))).toBe(true);
    expect(r(-1).pow(z(0.5)).equals(z(0, 1))).toBe(true);
    expect(c.almosteq(r('1e1000').div('1e999'), 10)).toBe(true);
    expect(c.almosteq(r('1e-1000').mul('1e1000'), 1)).toBe(true);
  });

  it('performs complex arithmetic and preserves the owning context', () => {
    const a = z(3, 4);
    expect(a.isZero).toBe(false);
    expect(z(0, 1).isZero).toBe(false);
    expect(a.abs().value).toBe(5);
    expect(a.neg().equals(z(-3, -4))).toBe(true);
    expect(a.pos().equals(a)).toBe(true);
    expect(a.conjugate().equals(z(3, -4))).toBe(true);
    expect(a.add(z(1, 2)).equals(z(4, 6))).toBe(true);
    expect(a.sub(z(1, 2)).equals(z(2, 2))).toBe(true);
    expect(a.mul(z(1, 2)).equals(z(-5, 10))).toBe(true);
    expect(a.div(z(1, 2)).equals(z(2.2, -0.4))).toBe(true);
    expect(a.pow(2).equals(z(-7, 24))).toBe(true);
    expect(z(0).pow(0).equals(1)).toBe(true);
    expect(a.pow(0).equals(1)).toBe(true);
    expect(z(-1).pow(0.5).equals(z(0, 1))).toBe(true);
    expect(() => a.div(0)).toThrow(RangeError);
    expect(a.add(1).context).toBe(c);
  });

  it('handles nonfinite arithmetic and predicates without finite overflow', () => {
    expect(c.inf.neg().equals(c.ninf)).toBe(true);
    expect(c.ninf.abs().equals(c.inf)).toBe(true);
    expect(c.nan.equals(c.nan)).toBe(false);
    expect(c.inf.gt('1e1000')).toBe(true);
    expect(c.ninf.lt('-1e1000')).toBe(true);
    expect(r('1e1000').lt(c.inf)).toBe(true);
    expect(r('-1e1000').gt(c.ninf)).toBe(true);
    expect(c.isnan(c.inf.add(c.ninf))).toBe(true);
    expect(c.inf.add('1e1000').equals(c.inf)).toBe(true);
    expect(r('1e1000').mul(c.inf).equals(c.inf)).toBe(true);
    expect(c.isnan(c.inf.mul(0))).toBe(true);
    expect(r(1).div(c.inf).isZero).toBe(true);
    expect(c.inf.div(-1).equals(c.ninf)).toBe(true);
    expect(c.inf.pow(2).equals(c.inf)).toBe(true);
    expect(r(2).pow(c.inf).equals(c.inf)).toBe(true);
    expect(z(Infinity).abs().equals(c.inf)).toBe(true);
    expect(z(0, Infinity).abs().equals(c.inf)).toBe(true);
    expect(c.isnan(z(Infinity, 1).mul(z(1, 1)))).toBe(false);
    expect(c.isnan(z(1, Infinity).mul(0))).toBe(true);
    expect(c.isnan(z(1, 1).mul(z(Infinity, 1)))).toBe(false);
    expect(c.isnan(z(1, 1).mul(z(1, Infinity)))).toBe(false);
    expect(c.isnan(z(Infinity, 1).div(z(1, 1)))).toBe(false);
    expect(z(1, Infinity).div(1).equals(z(1, Infinity))).toBe(true);
    expect(c.isnan(z(1, 1).div(z(Infinity, 1)))).toBe(true);
    expect(c.isnan(z(1, 1).div(z(1, Infinity)))).toBe(true);
    expect(z(Infinity, 1).pow(2).equals(z(Infinity, Infinity))).toBe(true);
    expect(z(1, Infinity).pow(2).equals(z(-Infinity, Infinity))).toBe(true);
    expect(z(Infinity, 1).pow(1).equals(z(Infinity, 1))).toBe(true);
    expect(c.isnan(z(Infinity, 1).pow(3))).toBe(true);
    expect(c.isnan(z(Infinity, 1).pow(4))).toBe(true);
    expect(c.isnan(z(Infinity, 1).pow(-1))).toBe(true);
    expect(c.isnan(z(Infinity, 1).pow(z(2, 1)))).toBe(true);
    expect(z(Infinity).pow(2).equals(z(Infinity))).toBe(true);
    for (const [a,b] of [[z(Infinity, 1), z(0.3)], [z(1, Infinity), z(0.3)], [z(1, 2), z(Infinity)], [z(1, 2), z(1, Infinity)]]) expect(c.isnan(a!.pow(b))).toBe(true);
    expect([c.isnan(z(NaN, 1)), c.isnan(z(1, NaN)), c.isnan(z(1, 2)), c.isinf(z(Infinity, 1)), c.isinf(z(1, Infinity)), c.isinf(z(1, 2)), c.isinf(c.nan)]).toEqual([true, true, false, true, true, false, false]);
    expect([c.isnormal(0), c.isnormal(1), c.isnormal(c.nan), c.isnormal(c.inf)]).toEqual([false, true, false, false]);
    expect([c.isint(1), c.isint(1.5), c.isint(c.inf), c.isint(z(1)), c.isint(z(1, 2)), c.isint(z(1, 2), true), c.isint(z(1.5, 2), true), c.isint(z(1, 2.5), true)]).toEqual([true, false, false, true, false, true, false, false]);
  });

  it('reconstructs bounded rationals, including negative and tiny values', () => {
    expect(c.toRational(r(0.1))).toEqual([1n, 10n]);
    expect(c.toRational(r(0.1), false)).toEqual([3602879701896397n, 36028797018963968n]);
    expect(c.toRational(1.5)).toEqual([3n, 2n]);
    expect(c.toRational(-0.1)).toEqual([-1n, 10n]);
    expect(() => c.toRational(c.inf)).toThrow(RangeError);
    const bounded = new MPContext(53, { tol: 0.1 });
    expect(bounded.toRational(0.123)).toEqual([1n, 8n]);
    expect(bounded.toRational(0.16)).toEqual([1n, 6n]);
    expect(bounded.toRational(0.31)).toEqual([3n, 10n]);
    expect(bounded.toRational(0.18)).toEqual([1n, 6n]);
    expect(bounded.toRational(0.001)).toEqual(bounded.toRational(0.001, false));
    expect(bounded.toRational(-0.001)).toEqual(bounded.toRational(-0.001, false));
  });

  it('accumulates sums and dot products exactly before rounding', () => {
    expect(c.fsum(['1e100', 1, '-1e100']).equals(1)).toBe(true);
    expect(c.fsum([]).isZero).toBe(true);
    expect(c.fsum([z(1, 2), z(3, 4)]).equals(z(4, 6))).toBe(true);
    expect(c.fsum([-2, z(3, 4)], { absolute: true }).equals(7)).toBe(true);
    expect(c.fsum([-2, z(3, 4)], { squared: true }).equals(z(-3, 24))).toBe(true);
    expect(c.fsum([-2, z(3, 4)], { absolute: true, squared: true }).equals(29)).toBe(true);
    expect(c.fsum([c.inf, 1]).equals(c.inf)).toBe(true);
    expect(c.isnan(c.fsum([c.inf, c.ninf]))).toBe(true);
    expect(c.fsum([c.inf], { squared: true }).equals(c.inf)).toBe(true);
    expect(c.fdot([1, 2], [3, 4]).equals(11)).toBe(true);
    expect(c.fdot([[1, 3], [2, 4]]).equals(11)).toBe(true);
    expect(c.fdot([1, 2], [3]).equals(3)).toBe(true);
    expect(c.fdot([z(1, 2)], [z(1, 2)], { conjugate: true }).equals(5)).toBe(true);
    expect(c.fdot([1], [z(1, 2)]).equals(z(1, 2))).toBe(true);
    expect(c.fdot([1], [2], { conjugate: true }).equals(2)).toBe(true);
    expect(c.fdot([c.inf], [1]).equals(c.inf)).toBe(true);
    expect(c.fdot([z(1, Infinity)], [1]).equals(z(1, Infinity))).toBe(true);
    expect(c.isnan(c.fdot([1], [c.inf]))).toBe(false);
    expect(c.fdot([1], [z(1, Infinity)]).equals(z(1, Infinity))).toBe(true);
    expect(() => c.fdot([1])).toThrow(TypeError);
    expect(() => c.fdot([[1]])).toThrow(TypeError);
    const high = new MPContext(100);
    const x = high.mpf('1.00000000000000001');
    expect(c.fdot([[x, x], [-1, 1]]).abs().gt(0)).toBe(true);
    expect([c.mag(10), c.mag(0.01), c.mag(z(0, 10)), c.mag(z(10)), c.mag(z(10, 1)), c.mag(z(1, 10))]).toEqual([4n, -6n, 4n, 4n, 5n, 5n]);
    expect(c.mag(0)).toBe(c.ninf);
    expect(c.mag(c.inf)).toBe(c.inf);
    expect(c.mag(c.nan)).toBe(c.nan);
    expect(c.mag(z(Infinity, 1))).toBe(c.inf);
    expect(c.mag(z(1, Infinity))).toBe(c.inf);
    expect(c.mag(z(NaN, 1))).toBe(c.nan);
  });

  it('compares absolute and relative errors at arbitrary precision', () => {
    expect(c.almosteq(1, 1 + 1e-15)).toBe(true);
    expect(c.almosteq(1, 1.01)).toBe(false);
    expect(c.almosteq(0, 1e-30)).toBe(true);
    expect(c.almosteq(1, 2, { absEps: 0.1 })).toBe(false);
    expect(c.almosteq(1, 2, { relEps: 0.6 })).toBe(true);
    expect(c.almosteq(2, 1, { relEps: 0.6, absEps: 0.1 })).toBe(true);
    expect(c.almosteq(z(1, 2), z(1, 2 + 1e-15))).toBe(true);
    expect(new MPContext(53, { tol: false }).almosteq(1, 1 + 1e-15)).toBe(true);
    const high = new MPContext(200);
    expect(high.almosteq('1', '1.0000000000000000000000000000000000000001')).toBe(false);
    expect(high.almosteq('1', '1.0000000000000000000000000000000000000000000000000000000000001')).toBe(true);
    expect(c.almosteq(c.nan, 1)).toBe(false);
    expect(c.almosteq(c.inf, c.inf)).toBe(false);
  });
});

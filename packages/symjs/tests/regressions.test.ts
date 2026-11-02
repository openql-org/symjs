// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { describe, expect, it } from 'vitest';
import * as sj from '../src';

const s = (e: unknown): string => String(e);

describe('regressions (values checked against SymPy 1.14)', () => {
  it('cot at odd multiples of pi/2 is 0', () => {
    expect(['pi/2', '3*pi/2', '7*pi/2', '-pi/2'].map((r) => s(sj.cot(sj.parse(r))))).toEqual(['0', '0', '0', '0']);
  });

  it('digamma at rationals uses the fractional part', () => {
    expect(s(sj.digamma(sj.Rational.of(7n, 2n)))).toBe('-2*log(2) - EulerGamma + 46/15');
    expect(s(sj.digamma(sj.Rational.of(3n, 2n)))).toBe('-2*log(2) - EulerGamma + 2');
    expect(s(sj.digamma(sj.parse('10/3')))).toBe('-log(3) - sqrt(3)*pi/6 - EulerGamma - log(sqrt(3)) + 117/28');
  });

  it('patterns do not match nodes of another class or operator', () => {
    const x = sj.symbol('x');
    const a = new sj.Wild('a');
    expect(sj.isNoMatch(sj.match(sj.DiracDelta(x), sj.Heaviside(a)))).toBe(true);
    expect(sj.isNoMatch(sj.match(sj.or(x, sj.symbol('y')), sj.and(a, sj.symbol('y'))))).toBe(true);
  });

  it('isprime rejects strong pseudoprimes', () => {
    expect(sj.isprime(318665857834031151167461n)).toBe(false);
    expect(sj.isprime(3317044064679887385961981n)).toBe(false);
  });
});

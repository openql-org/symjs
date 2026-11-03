// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/numeric/round.ts.

import { describe, expect, it } from 'vitest';
import { float, parse, round, sstr } from '../../src';
import type { Expr } from '../../src';
import { Float } from '../../src/core/nodes';

const p = (s: string) => parse(s);
const st = (e: Expr) => sstr(e);

// Expected values from SymPy 1.14 (round, Float, nfloat, comp, nsimplify).

describe('round (SymPy Expr.round)', () => {
  it('rounds numbers to decimal places', () => {
    const cases: [string, number | undefined, string][] = [
      ['1234.5678', 2, '1234.57'],
      ['1234.5678', -2, '1200.00000000000'],
      ['12345', -2, '12300'],
      ['-12355', -1, '-12360'],
      ['12345', undefined, '12345'],
      ['pi', 3, '3.142'],
      ['pi', undefined, '3'],
      ['-pi', 4, '-3.1416'],
      ['2 + 3*I*pi', 1, '2 + 9.4*I'],
      ['0', undefined, '0'],
      ['0', 2, '0'],
      ['2.5', undefined, '2'],
      ['3.5', undefined, '4'],
      ['-2.5', undefined, '-2'],
      ['1/3', 0, '0.0'],
      ['2/3', 0, '1.00000000000000'],
      ['0.0012345', 5, '0.00123'],
      ['oo', undefined, 'oo'],
      ['10**20 + 1/2', undefined, '100000000000000000000'],
      ['10**20 + 5/2', undefined, '100000000000000000002'],
      // SymPy 1.14 gives 100000000000000000001: its tie test compares a 1-digit
      // Float with 0.5, which is False since Floats of different precision are
      // unequal; half-to-even rounding of 10**20 + 3/2 is 10**20 + 2
      ['10**20 + 3/2', undefined, '100000000000000000002'],
      ['25/10', 0, '2.00000000000000'],
      ['15/100', 1, '0.2'],
      ['-1/2', undefined, '0'],
      ['1000*E', -2, '2700.00000000000'],
      ['5/10', 0, '0.0'],
      ['0.006', 2, '0.01'],
      ['0.004', 2, '0.0'],
      ['0.0051', 2, '0.01'],
      ['6/1000', 2, '0.01'],
    ];
    for (const [x, n, want] of cases) expect([x, n, st(round(p(x), n))]).toEqual([x, n, want]);
  });
  it('keeps the precision of Floats', () => {
    expect(st(round(float('0.123456789', 5), 3))).toBe('0.123');
    expect(st(round(float('12.5', 3), 0))).toBe('12.0');
    expect(st(round(float('123.456', 4), 1))).toBe('123.5');
    expect(st(round(float('1e30'), -28))).toBe('1000000000000000000000000000000.');
    expect(st(round(float(1e30), -28))).toBe('1.00000000000000e+30');
    expect(st(round(float(1e30), -31))).toBe('0.0');
    expect(st(round(float(123456789.0, 5), -2))).toBe('1.2346e+8');
  });
  it('rejects symbols', () => {
    expect(() => round(p('x'))).toThrow(TypeError);
  });
});

/**
 * Coverage of numeric/nfloat.ts (nsimplify), mpeval.ts and round.ts.
 * Expected values from SymPy 1.14 / mpmath 1.3.
 */

describe('round', () => {
  it('rounds to the first digit below a negative number', () => {
    // SymPy: Rational(-7, 100).round(1) = Float('-0.09375', precision=3), printed -0.e-1
    const r = round(p('-7/100'), 1);
    expect(r).toBeInstanceOf(Float);
    expect(sstr(r)).toBe('-0.e-1');
    expect(r instanceof Float ? r.prec : 0).toBe(3);
    expect(sstr(round(p('-pi/50'), 1))).toBe('-0.e-1');
  });
});

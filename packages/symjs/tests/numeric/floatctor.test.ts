// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/numeric/floatctor.ts.

import { describe, expect, it } from 'vitest';
import { float, parse, sstr } from '../../src';
import type { Expr } from '../../src';
import { Float } from '../../src/core/nodes';

const p = (s: string) => parse(s);
const st = (e: Expr) => sstr(e);
const prec = (e: Expr) => (e instanceof Float ? e.prec : -1);

// Expected values from SymPy 1.14 (round, Float, nfloat, comp, nsimplify).

describe('Float constructor (SymPy Float)', () => {
  it('parses strings', () => {
    const cases: [string, string, number][] = [
      ['1.5e3', '1500.00000000000', 53],
      ['.5', '0.500000000000000', 53],
      ['-.25', '-0.250000000000000', 53],
      [' 1 000 ', '1000.00000000000', 53],
      ['1_000.5', '1000.50000000000', 53],
      ['12345678901234567890', '12345678901234567890.', 70],
      ['+1.5', '1.50000000000000', 53],
      ['1e20', '100000000000000000000.', 73],
      ['1.', '1.00000000000000', 53],
    ];
    for (const [s, want, pr] of cases) {
      const f = float(s);
      expect([s, st(f), prec(f)]).toEqual([s, want, pr]);
    }
    expect(st(float('inf'))).toBe('oo');
    expect(st(float('-inf'))).toBe('-oo');
    expect(st(float('nan'))).toBe('nan');
    expect(() => float('abc')).toThrow(SyntaxError);
    expect(() => float('1.2.3')).toThrow(SyntaxError);
    expect(() => float('')).toThrow();
  });
  it('infers the precision from the digits with the null string', () => {
    const cases: [string, string, number][] = [
      ['1.25', '1.25', 13],
      ['100', '100.', 13],
      ['1e3', '1000.', 17],
      ['0.000', '0.0', 7],
    ];
    for (const [s, want, pr] of cases) {
      const f = float(s, '');
      expect([s, st(f), prec(f)]).toEqual([s, want, pr]);
    }
    const five = float(p('5'), '');
    expect([st(five), prec(five)]).toEqual(['5.', 7]);
    expect(() => float(1.5, '')).toThrow(TypeError);
  });
  it('converts doubles, integers and exact numbers', () => {
    expect(st(float(Number.NaN))).toBe('nan');
    expect(st(float(Infinity))).toBe('oo');
    expect(st(float(-Infinity))).toBe('-oo');
    expect(st(float(0))).toBe('0.0');
    expect([st(float(12345678901234567890n)), prec(float(12345678901234567890n))]).toEqual(['12345678901234567890.', 70]);
    expect(st(float(p('1/3'), 20))).toBe('0.33333333333333333333');
    expect(st(float(float('1.5'), 30))).toBe('1.50000000000000000000000000000');
    expect(st(float(p('pi'), 20))).toBe('3.1415926535897932385');
    expect(st(float(p('oo')))).toBe('oo');
    expect([st(float(0.1, 5)), prec(float(0.1, 5))]).toEqual(['0.10000', 20]);
    const f = float('1.5');
    expect(float(f)).toBe(f);
    expect(st(float(1.5, undefined, 100))).toBe('1.5000000000000000000000000000');
  });
  it('evaluates exact expressions', () => {
    // SymPy raises TypeError (cannot create mpf from 1 + sqrt(2)); symjs evaluates
    // the real number, mpmath gives 2.414213562
    expect(st(float(p('sqrt(2) + 1'), 10))).toBe('2.414213562');
    expect(() => float(p('1 + I'), 10)).toThrow(TypeError);
    expect(() => float(p('x'), 10)).toThrow();
  });
});

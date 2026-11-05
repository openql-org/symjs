// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/numeric/nfloat.ts.

import { describe, expect, it } from 'vitest';
import { comp, evalf, float, MatrixSymbol, mul, nfloat, nsimplify, parse, sstr, SymFunction } from '../../src';
import type { Expr } from '../../src';

const p = (s: string) => parse(s);
const st = (e: Expr) => sstr(e);

// Expected values from SymPy 1.14 (round, Float, nfloat, comp, nsimplify).

describe('nfloat', () => {
  it('makes rationals Floats', () => {
    expect(st(nfloat(p('1/3')))).toBe('0.333333333333333');
    expect(st(nfloat(p('1/3'), 5))).toBe('0.33333');
    expect(st(nfloat(p('sqrt(2)')))).toBe('1.41421356237310');
    expect(st(nfloat(p('x')))).toBe('x');
    expect(st(nfloat(p('x**2/3 + y**(1/2)')))).toBe('0.333333333333333*x**2 + sqrt(y)');
    expect(st(nfloat(p('x**4 + x/2 + cos(pi/3) + 1 + sqrt(y)')))).toBe('x**4 + 0.5*x + sqrt(y) + 1.5');
    expect(st(nfloat(p('sin(x)/7'), 5))).toBe('0.14286*sin(x)');
  });
  it('makes exponents Floats with exponent=true', () => {
    expect(st(nfloat(p('x**4 + x/2 + cos(pi/3) + 1 + sqrt(y)'), 15, true))).toBe('0.5*x + x**4.0 + y**0.5 + 1.5');
    expect(st(nfloat(p('x**2*(x + 1)**2/3'), 15, true))).toBe('0.333333333333333*x**2.0*(x + 1.0)**2.0');
    expect(st(nfloat(p('sin(x) + y**z'), 15, true))).toBe('y**z + sin(x)');
    expect(st(nfloat(p('(x**2 + 1)**3'), 15, true))).toBe('(x**2 + 1.0)**3.0');
    expect(st(nfloat(p('sqrt(x**2 + 1)/3'), 15, true))).toBe('0.333333333333333*(x**2.0 + 1.0)**0.5');
    expect(st(nfloat(p('1/(x**2 + 1)'), 15, true))).toBe('(x**2 + 1.0)**(-1.0)');
  });
});

describe('comp', () => {
  it('compares numbers', () => {
    const f = (s: string) => p(s);
    expect(comp(0, 0)).toBe(true);
    expect(comp(0, 1)).toBe(false);
    expect(comp(1, 1)).toBe(true);
    expect(comp(1, 2)).toBe(false);
    expect(comp(float(1.0), float('1.0000000000000001'))).toBe(true);
    expect(comp(float('3.14', 3), f('pi'))).toBe(true);
    expect(comp(float(f('pi'), 5), float('3.1416', 5))).toBe(true);
    // (SymPy Float(sqrt(2), 3) raises TypeError: sqrt(2).n(3) is the Float of sqrt(2))
    expect(comp(evalf(f('sqrt(2)'), 3), float(1.41))).toBe(true);
    expect(comp(float('2.0'), 2)).toBe(true);
    expect(comp(2, float('2.0'))).toBe(true);
  });
  it('uses a tolerance', () => {
    expect(comp(1, float(1.01), 0.1)).toBe(true);
    expect(comp(100, 101, 0.1)).toBe(true);
    expect(comp(100, 101, 0.001)).toBe(false);
    expect(comp(float(1.5), float(1.6), 0.01)).toBe(false);
    expect(comp(0, float(0.05), 0.1)).toBe(true);
    expect(comp(5, 0, 0.1)).toBe(false);
  });
  it('compares strings with the null tolerance', () => {
    expect(comp(float('1.5'), float('1.5'), '')).toBe(true);
    expect(comp(float('1.5'), float('1.50', 4), '')).toBe(false);
  });
});

// SymPy 1.14 nsimplify(sympify(s), **opts) (test_nsimplify, test_issue_9448, the docstring and more).
type NsOpts = { constants?: string[]; tolerance?: number; full?: boolean; rational?: boolean; rationalConversion?: 'base10' | 'exact' };

describe('nsimplify of a matrix expression', () => {
  it('replaces the Floats by Rationals (a MatrixSymbol is a free symbol in SymPy)', () => {
    // nsimplify(0.5*A) -> (1/2)*A
    expect(sstr(nsimplify(mul(0.5, MatrixSymbol('A', 2, 2))))).toBe('(1/2)*A');
  });
});

describe('nsimplify', () => {
  const cases: [string, NsOpts, string][] = [
    ["0", {}, "0"],
    ["-1", {}, "-1"],
    ["1 + x", {}, "x + 1"],
    ["2.7", {}, "27/10"],
    ["1 - GoldenRatio", {}, "1/2 - sqrt(5)/2"],
    ["(1 + sqrt(5))/4", {"constants": ["GoldenRatio"]}, "GoldenRatio/2"],
    ["2/GoldenRatio", {"constants": ["GoldenRatio"]}, "-2 + 2*GoldenRatio"],
    ["exp(5*pi*I/3)", {}, "1/2 - sqrt(3)*I/2"],
    ["sin(3*pi/5)", {}, "sqrt(sqrt(5)/8 + 5/8)"],
    ["sqrt(pi/4)*(2 + I)", {"constants": ["pi"]}, "sqrt(pi) + I*sqrt(pi)/2"],
    ["2 + exp(2*atan(1/4)*I)", {}, "49/17 + 8*I/17"],
    ["pi", {"tolerance": 0.01}, "22/7"],
    ["pi", {"tolerance": 0.001}, "355/113"],
    ["0.33333", {"tolerance": 0.0001}, "1/3"],
    ["2.0**(1/3.)", {"tolerance": 0.001}, "635/504"],
    ["2.0**(1/3.)", {"tolerance": 0.001, "full": true}, "2**(1/3)"],
    ["x + .5", {"rational": true}, "x + 1/2"],
    ["1/.3 + x", {"rational": true}, "x + 10/3"],
    ["1.09861228866811", {"rational": true}, "109861228866811/100000000000000"],
    ["0.272198261287950", {"constants": ["pi", "log(2)"]}, "pi*log(2)/8"],
    ["0.272", {"constants": ["pi", "log(2)"]}, "34/125"],
    ["x/7.0", {}, "x/7"],
    ["pi/1e2", {}, "pi/100"],
    ["pi/1e2", {"rational": false}, "0.01*pi"],
    ["pi/1e-7", {}, "10000000*pi"],
    ["x**0.0", {}, "1"],
    ["3.333333", {"tolerance": 0.1, "rational": true}, "10/3"],
    ["3.333333", {"tolerance": 0.01, "rational": true}, "10/3"],
    ["3.666666", {"tolerance": 0.1, "rational": true}, "11/3"],
    ["33", {"tolerance": 10, "rational": true}, "33"],
    ["33.33", {"tolerance": 10, "rational": true}, "30"],
    ["37.76", {"tolerance": 10, "rational": true}, "40"],
    ["-203.1", {}, "-2031/10"],
    [".2", {"tolerance": 0}, "1/5"],
    ["-.2", {"tolerance": 0}, "-1/5"],
    [".2222", {"tolerance": 0}, "1111/5000"],
    ["-.2222", {"tolerance": 0}, "-1111/5000"],
    ["2e-8", {}, "1/50000000"],
    ["1e-42", {"rational": true}, "6277101735386681/6277101735386680763835789423207666416102355444464034512896"],
    ["0.33333333", {"rational": true, "rationalConversion": "exact"}, "3002399721556333/9007199254740992"],
    ["1/(1 - (-1)**(2/3) - (-1)**(1/3)) + 1/(1 + (-1)**(2/3) + (-1)**(1/3))", {}, "1/2"],
    ["pi", {"tolerance": 1e-30}, "pi"],
    ["3.14159265358979", {"constants": ["pi"]}, "pi"],
    ["3.14159265358979", {"tolerance": 0.001}, "355/113"],
    ["1/2+exp(-18)", {}, "1/2"],
    ["2.718281828459045", {"constants": ["E"]}, "E"],
    ["4/(1+sqrt(5))", {"constants": ["GoldenRatio"]}, "-2 + 2*GoldenRatio"],
    ["1/(exp(3*pi*I/5)+1)", {}, "1/2 - I*sqrt(sqrt(5)/10 + 1/4)"],
    ["I**I", {"constants": ["pi"]}, "exp(-pi/2)"],
    ["pi", {}, "pi"],
    ["sqrt(2)", {}, "sqrt(2)"],
    ["cos(pi/5)", {}, "1/4 + sqrt(5)/4"],
    ["sin(pi/12)", {}, "sqrt(1/2 - sqrt(3)/4)"],
    ["2**(1/3)", {}, "2**(1/3)"],
    ["log(2)", {}, "log(2)"],
    ["0.5", {}, "1/2"],
    ["0.333333333333333", {}, "1/3"],
    ["x + 0.25", {}, "x + 1/4"],
    ["0.1", {"rational": true, "rationalConversion": "exact"}, "3602879701896397/36028797018963968"],
    ["3.14159", {"tolerance": 0.01}, "22/7"],
    ["x*0.333", {"tolerance": 0.001}, "333*x/1000"],
    ["zoo", {}, "zoo"],
    ["sqrt(3)/2 + I/2", {}, "sqrt(3)/2 + I/2"],
    ["1/sqrt(7)", {}, "sqrt(7)/7"],
    ["sqrt(17) - 1", {}, "-1 + sqrt(17)"],
    ["7/3", {}, "7/3"],
    ["x**2", {}, "x**2"],
    ["0.5", {"tolerance": 2}, "1/2"],
    ["oo", {"tolerance": 0.1}, "oo"],
    ["oo", {}, "oo"],
    ["-oo", {}, "-oo"],
    ["x+oo", {}, "x + oo"],
    ["exp(1000)", {}, "exp(1000)"],
    ["1/(pi + 1)", {"constants": ["pi"]}, "1/(1 + pi)"],
    ["1 + sqrt(3)/7", {}, "sqrt(3)/7 + 1"],
    ["0.333", {"tolerance": 0.001}, "1/3"],
    ["2.718", {"tolerance": 0.01}, "19/7"],
    ["0.1", {"tolerance": 0.5}, "1/10"],
    ["-0.6667", {"tolerance": 0.001}, "-2/3"],
    ["x + 2.718", {"tolerance": 0.01}, "x + 106/39"],
    ["f(1)", {}, "f(1)"],
    ["exp(1/3)", {"constants": ["pi"]}, "exp(1/3)"],
    ["1/2 + exp(-16)", {}, "exp(-16) + 1/2"],
    ["1/2 + exp(-27)", {}, "1/2"],
    ["sqrt(2) + exp(-25)", {}, "sqrt(2)"],
    ["-5/3 + exp(-26)", {}, "-5/3"],
    ["1.5 + 2.5*I", {}, "3/2 + 5*I/2"],
    ["0.1*I", {}, "I/10"],
    ["exp(pi)", {}, "exp(pi)"],
    ["exp(pi)", {"constants": ["pi"]}, "exp(pi)"],
    ["pi**2/6", {}, "pi**2/6"],
    ["pi**2/6", {"constants": ["pi"]}, "pi**2/6"],
    ["EulerGamma", {}, "EulerGamma"],
    ["Catalan", {"constants": ["Catalan"]}, "Catalan"],
    ["sqrt(2)+sqrt(3)", {}, "sqrt(2*sqrt(6) + 5)"],
    ["sqrt(2)+sqrt(3)", {"full": true}, "sqrt(2*sqrt(6) + 5)"],
    ["1.41421356237310", {}, "sqrt(2)"],
    ["0.785398163397448", {"constants": ["pi"]}, "pi/4"],
    ["0.123456789", {}, "123456789/1000000000"],
    ["12345.678e30", {"rational": true}, "12345678000000000000000000000000000"],
    ["3.0", {}, "3"],
    ["-2.5", {}, "-5/2"],
    ["x*1.0", {}, "x"],
    ["0.30000000000000004", {}, "3/10"],
    ["1e100", {}, "10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"],
    ["1e-100", {}, "0"],
    ["123456789.123", {}, "123456789123/1000"],
    ["pi*1.0", {"rational": false}, "1.0*pi"],
    ["1.09861228866811", {}, "log(3)"],
    ["exp(-pi/2)", {"constants": ["pi"]}, "exp(-pi/2)"],
    ["sqrt(5)", {"tolerance": 0.1}, "9/4"],
    ["0.1+0.2*x", {"rationalConversion": "exact"}, "3602879701896397*x/18014398509481984 + 3602879701896397/36028797018963968"],
    ["-1.25", {"rational": false}, "-5/4"],
    ["1.25+x", {"tolerance": 2}, "x + 2"],
    // SymPy gives zoo for these three (the parts of the value, nan and oo, go through
    // identify); symjs keeps the directed infinity, which is not a finite number to identify
    ["I*oo", {}, "oo*I"],
    ["1 + I*oo", {}, "1 + oo*I"],
    ["nan", {}, "nan"],
    ["oo + I", {}, "oo + I"],
    ["0.5*x + 0.5", {}, "x/2 + 1/2"],
    ["2.5", {"tolerance": 1, "rational": true}, "2"],
    ["3.5", {"tolerance": 1, "rational": true}, "4"],
    ["7.3", {"tolerance": 2.5, "rational": true}, "15/2"],
    ["1.5 + pi", {"constants": ["pi", "E"]}, "3/2 + pi"],
    ["1.5 + pi", {"constants": ["pi", "pi"]}, "3/2 + pi"],
    ["1.5 + pi", {"constants": ["E", "pi"]}, "3/2 + pi"],
  ];
  it.each(cases)('nsimplify(%s, %j) = %s as in SymPy', (e, o, want) => {
    expect(sstr(nsimplify(p(e), { ...o, constants: o.constants?.map(p) }))).toBe(want);
  });
  it('keeps what is not a number and checks the constants', () => {
    expect(sstr(nsimplify(SymFunction('f')(1)))).toBe('f(1)');
    // SymPy: ValueError("constants must be real-valued")
    expect(() => nsimplify(p('0.5'), { constants: [p('I')] })).toThrow(TypeError);
    // SymPy: nsimplify(pi.evalf(100)*x, rational_conversion='exact').evalf(100) == pi.evalf(100)*x
    const px = mul(evalf(p('pi'), 100), p('x'));
    expect(sstr(evalf(nsimplify(px, { rationalConversion: 'exact' }), 100))).toBe(sstr(px));
  });
});

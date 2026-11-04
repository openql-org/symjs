// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/integrals/rationaltools.ts (SymPy ratint). Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Sym, parse, sstr } from '../../src';
import { Poly } from '../../src/polys/sympoly';
import { cancelFraction, isRationalIn, logToAtan, logToReal, ratint, ratintLogpart, ratintRatpart } from '../../src/integrals/rationaltools';

const x = new Sym('x');
const t = new Sym('t');
const P = (s: string, g: Sym = x) => Poly.from(parse(s), [g]);
const R = (s: string): string => {
  const r = ratint(parse(s), x);
  return r === undefined ? 'None' : sstr(r);
};

describe('ratint', () => {
  it.each([
    ['1/(x**2+2*a*x+a**2)', '-1/(a + x)'],
    ['x/(x**2+2*a*x+a**2)', 'a/(a + x) + log(a + x)'],
    ['(x+1)/(x-a)**2', '(-a - 1)/(-a + x) + log(-a + x)'],
    ['1/(x**2-a**2)', '(log(-a + x)/2 - log(a + x)/2)/a'],
    ['1/(x**2+a)', '-sqrt(-1/a)*log(-a*sqrt(-1/a) + x)/2 + sqrt(-1/a)*log(a*sqrt(-1/a) + x)/2'],
    ['1/(x**2+a**2)', '(-I*log(-I*a + x)/2 + I*log(I*a + x)/2)/a'],
    ['x/(x**2+a)', 'log(a + x**2)/2'],
    ['1/((x+a)*(x+b))', 'log(-a**2/(2*(a - b)) + a*b/(a - b) + a/2 - b**2/(2*(a - b)) + b/2 + x)/(a - b) - log(a**2/(2*(a - b)) - a*b/(a - b) + a/2 + b**2/(2*(a - b)) + b/2 + x)/(a - b)'],
    ['1/(x**3+a)', 'RootSum(27*_t**3*a**2 - 1, Lambda(_t, _t*log(3*_t*a + x)))'],
    ['1/(x**2+I)', '-sqrt(I)*log(x - sqrt(I)*I)/2 + sqrt(I)*log(x + sqrt(I)*I)/2'],
    ['1/(x**2-2)', 'sqrt(2)*log(x - sqrt(2))/4 - sqrt(2)*log(x + sqrt(2))/4'],
    ['1/(x**2+2*x+5)', 'atan(x/2 + 1/2)/2'],
    ['x/(x**2-2)', 'log(x**2 - 2)/2'],
    ['1/(x**3+1)', 'log(x + 1)/3 - log(x**2 - x + 1)/6 + sqrt(3)*atan(2*sqrt(3)*x/3 - sqrt(3)/3)/3'],
    ['(x**2+1)/(x**3-x)', '-log(x) + log(x**2 - 1)'],
    ['1/(x**3-2)', '2**(1/3)*log(x - 2**(1/3))/6 - 2**(1/3)*log(x**2 + 2**(1/3)*x + 2**(2/3))/12 - 2**(1/3)*sqrt(3)*atan(2**(2/3)*sqrt(3)*x/3 + sqrt(3)/3)/6'],
    ['1/x+1/(x+1)', 'log(x**2 + x)'],
    ['-1/(1-x**2)**2', 'x/(2*x**2 - 2) + log(x - 1)/4 - log(x + 1)/4'],
    ['1/(x*(x-1)**2)', 'log(x) - log(x - 1) - 1/(x - 1)'],
    ['1/(x**2+1)**2', 'x/(2*x**2 + 2) + atan(x)/2'],
    ['2/(x+1)**2', '-2/(x + 1)'],
    ['x**2/(x**2+1)', 'x - atan(x)'],
    ['3/(2*x**2+4)', '3*sqrt(2)*atan(sqrt(2)*x/2)/4'],
    ['(x**3+2)/(x**4+x**2+1)', '-log(x**2 - x + 1)/4 + 3*log(x**2 + x + 1)/4 + sqrt(3)*atan(2*sqrt(3)*x/3 - sqrt(3)/3)/6 + sqrt(3)*atan(2*sqrt(3)*x/3 + sqrt(3)/3)/2'],
    ['(x**2-1)/(x**4+x**2+1)', 'log(x**2 - x + 1)/2 - log(x**2 + x + 1)/2'],
    ['1/(x**2+x+1)**2', '(2*x + 1)/(3*x**2 + 3*x + 3) + 4*sqrt(3)*atan(2*sqrt(3)*x/3 + sqrt(3)/3)/9'],
    ['x**5/(x**2+1)**3', '(4*x**2 + 3)/(4*x**4 + 8*x**2 + 4) + log(x**2 + 1)/2'],
    ['1/(x**4+x**2)', '-atan(x) - 1/x'],
    ['(3*x+2)/(x**2-5*x+6)', '11*log(x - 3) - 8*log(x - 2)'],
    ['1/(x**2-2*x-1)', '-sqrt(2)*log(x - 1 + sqrt(2))/4 + sqrt(2)*log(x - sqrt(2) - 1)/4'],
    ['x/(x**4+1)', 'atan(x**2)/2'],
    ['x**3/(x**2+1)**2 + 1/(x-1)', 'log(x - 1) + log(x**2 + 1)/2 + 1/(2*x**2 + 2)'],
    ['(x**2+1)/(2*x**2+2*x)', 'x/2 + log(x)/2 - log(x + 1)'],
    ['3*x**2/(6*x+6)', 'x**2/4 - x/2 + log(x + 1)/2'],
    ['(x**2 + 2*x + 1)/(x + 1)', 'x**2/2 + x'],
    ['(x**2 - 1)/(1 - x)', '-x**2/2 - x'],
    ['a/(x**2-1)', 'a*(log(x - 1)/2 - log(x + 1)/2)'],
    ['(y**2/2 + x**2/2 + 1)**(-2)', '2*x/(x**2*(y**2 + 2) + y**4 + 4*y**2 + 4) - sqrt(-1/(y**2 + 2)**3)*log(x - y**4*sqrt(-1/(y**2 + 2)**3) - 4*y**2*sqrt(-1/(y**2 + 2)**3) - 4*sqrt(-1/(y**2 + 2)**3)) + sqrt(-1/(y**2 + 2)**3)*log(x + y**4*sqrt(-1/(y**2 + 2)**3) + 4*y**2*sqrt(-1/(y**2 + 2)**3) + 4*sqrt(-1/(y**2 + 2)**3))'],
    ['1/(a*x**2-a**3)', '(log(-a + x)/2 - log(a + x)/2)/a**2'],
    ['a**2/(x**2-1)', 'a**2*(log(x - 1)/2 - log(x + 1)/2)'],
    ['-(a1 + 2*a2*x + 3*a3*x**2 + 4*a4*x**3)/(2*(a0 + a1*x + a2*x**2 + a3*x**3 + a4*x**4))', '-log(a0 + a1*x + a2*x**2 + a3*x**3 + a4*x**4)/2'],
  ])('%s', (f, want) => expect(R(f)).toBe(want));

  it('roots that are not found give a RootSum or nothing', () => {
    // SymPy: (-1/(23*(1/46 + 3*sqrt(69)/1058)**(1/3)) + ...)*log(...) + ... (Cardano's formulas, not written here)
    expect(R('1/(x**3-x+1)')).toBe('RootSum(23*_t**3 + 3*_t - 1, Lambda(_t, _t*log(46*_t**2/9 + 23*_t/9 + x + 4/9)))');
    // SymPy: -sqrt(2)*log(x**2 - sqrt(2)*x + 1)/8 + sqrt(2)*log(x**2 + sqrt(2)*x + 1)/8 + sqrt(2)*atan(sqrt(2)*x - 1)/4
    // + sqrt(2)*atan(sqrt(2)*x + 1)/4 (the roots of an irreducible quartic are not found here)
    expect(R('1/(x**4+1)')).toBe('RootSum(256*_t**4 + 1, Lambda(_t, _t*log(4*_t + x)))');
    // a logarithmic part of degree 5 or more: the resultant is too large here (SymPy: a RootSum)
    expect(R('(x**4+1)/(x**5+2*x**4+3*x+1)')).toBe('None');
    expect(R('sin(x)/(x + 1)')).toBe('None');
    expect(R('1/(x + sin(x))')).toBe('None');
  });
});

describe('the parts of ratint', () => {
  it('ratint_ratpart', () => {
    expect(ratintRatpart(P('1'), P('x**2+2*x+1'), x).map(sstr)).toEqual(['-1/(x + 1)', '0']);
    expect(ratintRatpart(P('x**5'), P('(x**2+1)**3'), x).map(sstr)).toEqual(['(4*x**2 + 3)/(4*x**4 + 8*x**2 + 4)', 'x/(x**2 + 1)']);
  });
  it('ratint_logpart', () => {
    const show = (L: [Poly, Poly][]) => L.map(([h, q]) => [sstr(h.asExpr()), sstr(q.asExpr())]);
    // SymPy: [(-4*t + x, 1 - 8*t**2)] (the same root t up to the sign of q)
    expect(show(ratintLogpart(P('1'), P('x**2-2'), x, t))).toEqual([['-4*t + x', '8*t**2 - 1']]);
    // f = c*g': the single factor t - c
    expect(show(ratintLogpart(P('2*x'), P('x**2+a'), x, t))).toEqual([['a + x**2', 't - 1']]);
    expect(show(ratintLogpart(P('-3*x**2-a'), P('2*x**3+2*a*x+4'), x, t))).toEqual([['2*a*x + 2*x**3 + 4', 't + 1/2']]);
    expect(show(ratintLogpart(P('-x'), P('2*x**2+4'), x, t))).toEqual([['2*x**2 + 4', '4*t + 1']]);
    expect(show(ratintLogpart(P('a*x'), P('x**2+3'), x, t))).toEqual([['x**2 + 3', '-a/2 + t']]);
    expect(show(ratintLogpart(P('x**3+2'), P('x**4+x**2+1'), x, t))).toEqual([['60*t**3/13 - 66*t**2/13 + 35*t/13 + x + 5/13', '48*t**4 - 48*t**3 + 4*t**2 + 12*t + 3']]);
  });
  it('log_to_atan', () => {
    expect(sstr(logToAtan(P('x'), P('1')))).toBe('2*atan(x)');
    expect(sstr(logToAtan(P('1'), P('x')))).toBe('-2*atan(x)');
    expect(sstr(logToAtan(P('x**3-2*x'), P('x**2-1')))).toBe('2*atan(x) + 2*atan(x**3) + 2*atan(x**5 - 2*x**3 + x)');
  });
  it('log_to_real', () => {
    expect(String(logToReal(P('x+t/2'), P('4*t**2+1', t), x, t))).toBe('atan(4*x)');
    expect(String(logToReal(P('x-t'), P('t**2-2', t), x, t))).toBe('sqrt(2)*log(x - sqrt(2)) - sqrt(2)*log(x + sqrt(2))');
  });
  it('cancelFraction and isRationalIn', () => {
    expect(sstr(cancelFraction(parse('2*x**2 + 2*x'), parse('4*x + 4'), x))).toBe('x/2');
    expect(sstr(cancelFraction(parse('-x - 1'), parse('-x**2 + 1'), x))).toBe('1/(x - 1)');
    expect(sstr(cancelFraction(parse('-x'), parse('x**2 + 1'), x))).toBe('-x/(x**2 + 1)');
    expect(sstr(cancelFraction(parse('x'), parse('-x**2 - 1'), x))).toBe('-x/(x**2 + 1)');
    expect(sstr(cancelFraction(parse('a*x + a'), parse('x**2 - 1'), x))).toBe('a/(x - 1)');
    expect(sstr(cancelFraction(parse('-a*x'), parse('x**2 + 1'), x))).toBe('-a*x/(x**2 + 1)');
    expect(isRationalIn(parse('1/(x + a)'), x)).toBe(true);
    expect(isRationalIn(parse('sqrt(x)'), x)).toBe(false);
  });
});

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/integrals/rischpoly.ts: the polynomials over a field of rational functions and the
// matrices used by the Risch algorithm. Expected values are those of SymPy 1.14's Poly (field=True).

import { describe, expect, it } from 'vitest';
import { Sym, parse, str } from '../../src';
import type { Expr } from '../../src/core/nodes';
import { ExactQuotientFailed, NotInvertible, PolynomialError } from '../../src/core/errors';
import { KPoly, fracIn, kCancel, kColJoin, kCols, kEye, kNullspace, kRowJoin, kRref, kZeros } from '../../src/integrals/rischpoly';

const [x, t] = [new Sym('x'), new Sym('t')];
const P = (s: string, g: Sym = t): KPoly => KPoly.of(parse(s), g);
const E = (p: KPoly | Expr): string => str(p instanceof KPoly ? p.asExpr() : p);

describe('KPoly', () => {
  it('conversion from expressions', () => {
    expect(KPoly.tryOf(parse('exp(t)'), t)).toBeUndefined();
    expect(KPoly.tryOf(parse('1/t'), t)).toBeUndefined();
    expect(() => KPoly.of(parse('exp(t)'), t)).toThrow(PolynomialError);
    expect(E(P('(t + 1)**2/x'))).toBe('t**2/x + 2*t/x + 1/x');
    expect(P('t**2/x').cs.map(E)).toEqual(['0', '0', '1/x']);
    expect(String(P('t + 1'))).toBe('Poly(t + 1, t)');
  });
  it('properties', () => {
    expect([P('0').degree, P('3').degree, P('t**2').degree]).toEqual([-Infinity, 0, 2]);
    expect([P('0').isGround, P('x').isGround, P('t').isGround]).toEqual([true, true, false]);
    expect([P('1').isOne, P('x').isOne, P('t**2').isMonomial, P('t + 1').isMonomial]).toEqual([true, false, true, false]);
    expect([E(P('0').LC()), E(P('0').TC()), E(P('2*t + 3').TC()), E(P('t').nth(5))]).toEqual(['0', '0', '3', '0']);
    expect([P('x*t').has(x), P('x').has(t), P('t').has(t)]).toEqual([true, false, true]);
    expect(P('t').as(x).gen.name).toBe('x');
  });
  it('arithmetic', () => {
    expect(E(P('t').add(1))).toBe('t + 1');
    expect(E(P('t').sub(P('t')))).toBe('0');
    expect(E(P('t + 1').mul(P('t - 1')))).toBe('t**2 - 1');
    expect(E(P('0').mul(P('t')))).toBe('0');
    expect(E(P('t + 1').pow(2))).toBe('t**2 + 2*t + 1');
    expect(P('t**2 - 1').div(P('t + 1')).map(E)).toEqual(['t - 1', '0']);
    expect(() => P('t').div(P('0'))).toThrow(RangeError);
    expect(() => P('t').exquo(P('t + 1'))).toThrow(ExactQuotientFailed);
    expect(E(P('0').monic())).toBe('0');
    expect(E(P('2*t**2 + x').monic())).toBe('t**2 + x/2');
    expect(E(P('t**2').eval(x))).toBe('x**2');
    expect(E(P('t**3 + t').diff())).toBe('3*t**2 + 1');
  });
  it('gcd, lcm, gcdex and resultants', () => {
    expect(E(P('t**2 - 1').gcd(P('t**2 + 2*t + 1')))).toBe('t + 1');
    expect(E(P('t**2 - 1').lcm(P('t + 1')))).toBe('t**2 - 1');
    expect(E(P('0').lcm(P('t')))).toBe('0');
    expect(P('t**2').halfGcdex(P('t + 1')).map(E)).toEqual(['1', '1']);
    expect(E(P('t').invert(P('t**2 + 1')))).toBe('-t');
    expect(() => P('t').invert(P('t**2'))).toThrow(NotInvertible);
    expect(E(P('t').prem(P('t**2')))).toBe('t');
    // SymPy: resultant(t**2 + 1, t - x) = x**2 + 1, and 0 with a common factor
    expect(E(P('t**2 + 1').resultantPRS(P('t - x'))[0])).toBe('x**2 + 1');
    expect(E(P('t**2 - 1').resultantPRS(P('t - 1'))[0])).toBe('0');
    expect(P('0').resultantPRS(P('t'))).toEqual([parse('0'), []]);
    const [R] = P('t').innerSubresultants(P('t**3 + 1'));
    expect(R.map(E)).toEqual(['t**3 + 1', 't', '-1']);
  });
  it('square-free decomposition (SymPy sqf_list over a field)', () => {
    expect(P('0').sqfList()).toEqual([parse('0'), []]);
    const [c, fs] = P('2*(t + 1)*(t + 2)**3').sqfList();
    expect([E(c), fs.map(([f, k]) => `${E(f)}:${k}`)]).toEqual(['2', ['t + 1:1', 't + 2:3']]);
    expect(P('(t + 2)**3').sqfList(true)[1].map(([f, k]) => `${E(f)}:${k}`)).toEqual(['1:1', '1:2', 't + 2:3']);
    expect(P('2*(t + 2)**2').sqfListInclude().map(([f, k]) => `${E(f)}:${k}`)).toEqual(['2:1', 't + 2:2']);
    expect(P('2*t').sqfListInclude().map(([f, k]) => `${E(f)}:${k}`)).toEqual(['2*t:1']);
  });
  it('fractions', () => {
    expect(kCancel(P('t**2 - 1'), P('2*t - 2')).map(E)).toEqual(['t + 1', '2']);
    expect(kCancel(P('1'), P('-t')).map(E)).toEqual(['-1', 't']);
    expect(fracIn(parse('(x + 1)/x*t'), x).map(E)).toEqual(['t*x + t', 'x']);
    expect(fracIn([P('t'), P('t + 1')], x).map(E)).toEqual(['t', 't + 1']);
    expect(() => fracIn(parse('(x + 1)/log(x)*t'), x)).toThrow(PolynomialError);
  });
});

describe('KMatrix', () => {
  it('joins, rref and null spaces', () => {
    expect(kZeros(1, 2).map((r) => r.map(E))).toEqual([['0', '0']]);
    expect(kCols([], 3)).toBe(3);
    const A = kRowJoin(kEye(2), [[parse('x')], [parse('1')]]);
    expect(kColJoin(A, [[parse('0'), parse('0'), parse('1')]]).length).toBe(3);
    const [R, piv] = kRref([
      [parse('0'), parse('x')],
      [parse('2'), parse('1')],
    ]);
    expect([R.map((r) => r.map(E)), piv]).toEqual([
      [
        ['1', '0'],
        ['0', '1'],
      ],
      [0, 1],
    ]);
    expect(kNullspace([[parse('1'), parse('3'), parse('2')]]).map((v) => v.map(E))).toEqual([
      ['-3', '1', '0'],
      ['-2', '0', '1'],
    ]);
    expect(kNullspace([], 2).length).toBe(2);
  });
});

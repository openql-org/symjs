// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Expected values from SymPy 1.14.0 (sympy.polys.constructor doctests and tests/test_constructor.py).

import { describe, expect, it } from 'vitest';
import { Float, I, Rational, Sym, parseExpr as P, sin, sqrt } from '../../src/index';
import { constructDomain } from '../../src/polys/constructor';

const [x, y] = [new Sym('x'), new Sym('y')];
const repr = (v: unknown): string => (Array.isArray(v) ? `[${v.map(repr).join(', ')}]` : typeof v === 'object' && v !== null && 'repr' in v && typeof v.repr === 'function' ? String(v.repr()) : String(v));
const cd = (...a: Parameters<typeof constructDomain>): string => {
  const [d, e] = constructDomain(...a);
  return `(${String(d)}, ${repr(e)})`;
};

describe('constructDomain', () => {
  it('SymPy doctests', () => {
    expect(cd([Rational.of(1n, 2n), Rational.of(3n, 4n)])).toBe('(QQ, [MPQ(1,2), MPQ(3,4)])');
    expect(cd([P('2*x + 1'), Rational.of(3n, 4n)])).toBe('(QQ[x], [2*x + 1, 3/4])');
    expect(cd([P('2*x + 1'), y])).toBe('(ZZ[x,y], [2*x + 1, y])');
    expect(cd([P('y/x'), P('x/(1 - y)')])).toBe('(ZZ(x,y), [y/x, -x/(y - 1)])');
    expect(cd([sqrt(2)])).toBe('(EX, [EX(sqrt(2))])');
  });
  it('numeric, Gaussian and algebraic domains', () => {
    expect(cd([new Float(1.5), 2])).toBe('(RR, [1.50000000000000, 2.00000000000000])');
    expect(cd([I, 2])).toBe('(ZZ_I, [ZZ_I(0, 1), ZZ_I(2, 0)])');
    expect(cd([1, 2])).toBe('(ZZ, [1, 2])');
    expect([cd([2], { field: true }), cd([I], { field: true }), cd([sqrt(2), P('2*sqrt(2)')], { extension: true })]).toEqual(['(QQ, [MPQ(2,1)])', '(QQ_I, [QQ_I(0, 1)])', '(QQ<sqrt(2)>, [ANP([MPQ(1,1), MPQ(0,1)], [MPQ(1,1), MPQ(0,1), MPQ(-2,1)], QQ), ANP([MPQ(2,1), MPQ(0,1)], [MPQ(1,1), MPQ(0,1), MPQ(-2,1)], QQ)])']);
    expect(cd([P('I/2')])).toBe('(QQ_I, [QQ_I(0, 1/2)])');
    expect(cd([P('1.5*I')])).toBe('(CC, [1.5*I])');
    expect(cd([P('1 + 2*I'), 2], { field: true })).toBe('(QQ_I, [QQ_I(1, 2), QQ_I(2, 0)])');
    expect(cd([sqrt(2), 1], { extension: true })).toBe('(QQ<sqrt(2)>, [ANP([MPQ(1,1), MPQ(0,1)], [MPQ(1,1), MPQ(0,1), MPQ(-2,1)], QQ), ANP([MPQ(1,1)], [MPQ(1,1), MPQ(0,1), MPQ(-2,1)], QQ)])');
    expect(cd([P('sqrt(2)*(1 + sqrt(3))')], { extension: true })).toBe('(QQ<sqrt(2) + sqrt(3)>, [ANP([MPQ(1,2), MPQ(1,2), MPQ(-9,2), MPQ(-5,2)], [MPQ(1,1), MPQ(0,1), MPQ(-10,1), MPQ(0,1), MPQ(1,1)], QQ)])');
    expect(cd([sqrt(2), new Float(1.5)], { extension: true })).toBe('(EX, [EX(sqrt(2)), EX(1.50000000000000)])');
    expect(cd([new Float(1.5), sqrt(2)], { extension: true })).toBe('(EX, [EX(1.50000000000000), EX(sqrt(2))])');
    expect(cd([P('x**sqrt(2)')], { extension: true })).toBe('(EX, [EX(x**(sqrt(2)))])');
  });
  it('composite domains', () => {
    expect(cd(P('2*x'))).toBe('(ZZ[x], 2*x)');
    expect(cd([x], { extension: true })).toBe('(ZZ[x], [x])');
    expect(cd([x, P('y/2')], { field: true })).toBe('(ZZ(x,y), [x, y/2])');
    expect(cd([x, P('1.5*y')])).toBe('(RR[x,y], [x, 1.5*y])');
    // SymPy: (ZZ_I[x], [(0 + 1*I)*x]); symjs has no polynomial rings over ZZ_I
    expect(cd([P('I*x')])).toBe('(EX, [EX(I*x)])');
    expect(cd([x, P('x + sqrt(2)')])).toBe('(EX, [EX(x), EX(x + sqrt(2))])');
    expect(cd([x, P('sin(x)')])).toBe('(EX, [EX(x), EX(sin(x))])');
    expect(cd([sin(x)])).toBe('(EX, [EX(sin(x))])');
    expect(cd([P('x/2'), x], { composite: false })).toBe('(EX, [EX(x/2), EX(x)])');
    expect(cd([P('x/2'), x], { composite: true })).toBe('(QQ[x], [x/2, x])');
    expect(cd([P('x*y'), P('x**2')], { composite: true })).toBe('(ZZ[x,y], [x*y, x**2])');
  });
});

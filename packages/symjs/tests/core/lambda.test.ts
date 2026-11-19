// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/lambda.ts.
// Lambda. Expected values are SymPy 1.14's.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { Expr, NoMatch, latex, parse, sstr, symbols } from '../../src';

const [x, y] = symbols('x y');

describe('small core nodes', () => {
  it('prints Lambda and checks the number of arguments', () => {
    const f = sj.Lambda([x, y], sj.add(x, y));
    expect(sj.latex(f)).toBe('\\left( \\left( x, \\  y\\right) \\mapsto x + y \\right)');
    // SymPy raises BadArgumentsError (a TypeError)
    expect(() => f.call(1)).toThrow(TypeError);
  });
});

describe('Lambda, hypersimp and taylor terms', () => {
  it('match SymPy', async () => {
    const { Lambda, hypersimp, isHypergeometric, taylorTerm, freeSymbols: fs } = await import('../../src');
    const [x, n] = symbols('x n');
    const L = Lambda(x, parse('x**2'));
    expect(sstr(L)).toBe('Lambda(x, x**2)');
    expect(sstr(L.call(3))).toBe('9');
    expect(latex(L)).toBe('\\left( x \\mapsto x^{2} \\right)');
    expect(fs(Lambda(x, parse('x + n'))).size).toBe(1);
    expect(sstr(Lambda([x, n], parse('x + n')))).toBe('Lambda((x, n), n + x)');
    const k = symbols('k', { integer: true })[0];
    const P = (s: string) => parse(s, { symbols: { k } } as never);
    expect(sstr(hypersimp(P('factorial(k)'), k) as Expr)).toBe('k + 1');
    expect(sstr(hypersimp(P('2**k'), k) as Expr)).toBe('2');
    expect(hypersimp(P('log(k)'), k)).toBe(NoMatch);
    expect(sstr(hypersimp(P('factorial(2*k)/factorial(k)**2'), k) as Expr)).toBe('2*(2*k + 1)/(k + 1)');
    expect(isHypergeometric(P('binomial(n, k)'), k)).toBe(true);
    expect(sstr(taylorTerm(parse('exp(x)'), 3, x))).toBe('x**3/6');
    expect(sstr(taylorTerm(parse('sin(x)'), 3, x))).toBe('-x**3/6');
  });
});

describe('Id', () => {
  it('is the identity Lambda (SymPy S.IdentityFunction)', () => {
    expect(sstr(sj.Id)).toBe('Lambda(_x, _x)');
    expect(sstr(sj.Id.call(x))).toBe('x');
    expect(sstr(sj.rcall(sj.Id, y))).toBe('y');
  });
});

it('renames bound variables without capturing free names', async () => {
  const a = await import('../../src');
  const x = new a.Sym('x'), collision = new a.Sym('_0');
  expect(String(a.Lambda(x,a.mul(2,x)).canonicalVariables.get(x))).toBe('_0');
  expect(String(a.Lambda(x,a.add(x,collision)).canonicalVariables.get(x))).toBe('_1');
});

it('validates nested signatures and substitutes arguments simultaneously', () => {
  expect(() => sj.Lambda(sj.rational(1), x)).toThrow(TypeError);
  expect(() => sj.Lambda([x, x], x)).toThrow(TypeError);
  expect(() => sj.Lambda([sj.Tuple(x, y), x], x)).toThrow(TypeError);
  expect(() => sj.Lambda([sj.Tuple(x, sj.rational(1))], x)).toThrow(TypeError);
  expect(String(sj.Lambda([x, y], sj.sub(x, y)).call(y, x))).toBe('-x + y');
  const nested = sj.Lambda([sj.Tuple(x, sj.Tuple(y))], sj.add(x, y));
  expect(nested.variables).toEqual([x, y]);
  expect([...nested.freeSymbols()]).toEqual([]);
  expect(String(nested)).toBe('Lambda(((x, (y,)),), x + y)');
  expect(String(nested.call(sj.Tuple(2, sj.Tuple(3))))).toBe('5');
  expect(() => nested.call(1)).toThrow(TypeError);
  expect(() => nested.call(sj.Tuple(1))).toThrow(TypeError);
  expect(String(sj.Lambda([], 42).call())).toBe('42');
  const a = new sj.IndexedBase('A').at(0);
  expect(String(sj.Lambda(a, sj.add(a, 1)).call(2))).toBe('3');
});


it('accepts indexed bases and matrix symbols as Lambda variables', () => {
  const base = new sj.IndexedBase('A');
  const matrix = sj.MatrixSymbol('M', 2, 2);
  expect(String(sj.Lambda(base, base).call(x))).toBe('x');
  expect(String(sj.Lambda(matrix, matrix).call(matrix))).toBe('M');
});


it('protects a Lambda binding during substitution', () => {
  const f = sj.Lambda(x, sj.add(x, y));
  expect(String(f.subs(x, 1))).toBe('Lambda(x, x + y)');
  expect(String(f.subs(y, 2))).toBe('Lambda(x, x + 2)');
});

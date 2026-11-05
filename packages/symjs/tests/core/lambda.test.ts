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

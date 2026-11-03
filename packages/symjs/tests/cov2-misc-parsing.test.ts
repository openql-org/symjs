// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * Coverage of parsing/parser.ts (errors, unevaluated sums and products) and
 * the deprecated polys entry divExact. Expected values from SymPy 1.14.
 */

import { describe, expect, it } from 'vitest';
import { Add, Mul, NoMatch, parse, sstr, symbol } from '../src';
import { divExact, polyCoefficients } from '../src/polys';

describe('parse', () => {
  it('explains a missing operator', () => {
    const hint = 'implicit multiplication is not supported; use *';
    expect(() => parse('x 2')).toThrow(hint);
    expect(() => parse('2 (3)')).toThrow(hint);
    expect(() => parse('2 0.[3]')).toThrow(hint);
    expect(() => parse('2 )')).toThrow('Unexpected token at 2');
    expect(() => parse('2 )')).not.toThrow(hint);
  });
  it('needs both sides of Eq', () => {
    // SymPy: Eq(x) is a TypeError (missing rhs)
    expect(() => parse('Eq(x)')).toThrow('Eq() takes at least 2 arguments');
    expect(sstr(parse('Eq(x, 1)'))).toBe('Eq(x, 1)');
  });
  it('flattens unevaluated sums and products', () => {
    // SymPy: parse_expr('(x+y)+z', evaluate=False) has the args (x, y, z)
    const s = parse('(x+y)+z', { evaluate: false });
    expect(s).toBeInstanceOf(Add);
    expect([sstr(s), s.args.length]).toEqual(['x + y + z', 3]);
    const p = parse('(x*y)*z', { evaluate: false });
    expect(p).toBeInstanceOf(Mul);
    expect([sstr(p), p.args.length]).toEqual(['x*y*z', 3]);
  });
});

describe('divExact (deprecated)', () => {
  it('divides exactly or gives NoMatch', () => {
    const x = symbol('x');
    // SymPy exquo(x**2 - 1, x - 1) = x + 1; exquo(x**2 + 1, x - 1) raises ExactQuotientFailed
    expect(String(divExact(parse('x**2 - 1'), parse('x - 1'), [x]))).toBe('x + 1');
    expect(divExact(parse('x**2 + 1'), parse('x - 1'), [x])).toBe(NoMatch);
  });
});

describe('polyCoefficients (deprecated)', () => {
  it('maps degrees to coefficients or gives NoMatch', () => {
    const x = symbol('x');
    // SymPy Poly(x**2 + 2*x, x).as_dict() = {(2,): 1, (1,): 2}
    const c = polyCoefficients(parse('x**2 + 2*x'), x);
    expect(c instanceof Map ? [...c].map(([k, v]) => [k, sstr(v)]).sort((a, b) => Number(a[0]) - Number(b[0])) : c).toEqual([
      [1, '2'],
      [2, '1'],
    ]);
    expect(polyCoefficients(parse('sin(x)'), x)).toBe(NoMatch);
  });
});

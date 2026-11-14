// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/public.ts: the public forms of the Expr methods that return NoMatch.

import { describe, expect, it } from 'vitest';
import { NoMatch, O, Wild, add, getO, matches, symbols } from '../../src';

const [x, y, z] = symbols('x y z');
const show = (m: unknown): string => (m instanceof Map ? `{${[...m].map(([k, v]) => `${String(k)}: ${String(v)}`).join(', ')}}` : String(m));

describe('matches and getO', () => {
  it('matches is match with the pattern first (SymPy pattern.matches(expr))', () => {
    const [w, v] = [new Wild('w'), new Wild('v')];
    expect(show(matches(add(w, v), add(x, y)))).toBe('{w_: y, v_: x}');
    expect(show(matches(add(x, w), add(x, y)))).toBe('{w_: y}');
    expect(matches(add(x, w), z)).toBe(NoMatch);
    expect(show(matches(w, x))).toBe('{w_: x}');
  });
  it('getO', () => {
    const o = O(x.pow(2));
    expect(String(getO(add(1, x, o)))).toBe('O(x**2)');
    expect(String(getO(o))).toBe('O(x**2)');
    // SymPy (1 + x).getO() is None
    expect(getO(add(1, x))).toBe(NoMatch);
  });
});

it('queries irrationality, algebraicity, complexity, finiteness and primality', async () => {
  const a = await import('../../src');
  expect(a.isIrrational(a.pi)).toBe(true);
  expect(a.isIrrational(a.S.Catalan)).toBe('unknown');
  expect(a.isIrrational(2)).toBe(false);
  expect(a.isAlgebraic(a.I)).toBe(true);
  expect(a.isAlgebraic(a.pi)).toBe(false);
  expect(a.isComplex(new a.Sym('r',{real:true}))).toBe(true);
  expect(a.isFinite(a.add(a.I,a.pow(new a.Sym('p',{positive:true}),2)))).toBe(true);
  expect(a.isPrime(a.I)).toBe(false);
  expect(a.isPrime(7)).toBe(true);
});

it('queries the other assumption facts (SymPy expr.is_<fact>)', async () => {
  const a = await import('../../src');
  const [k, o] = [new a.Sym('k', { integer: true }), new a.Sym('o', { odd: true })];
  const [i, h, ah] = [new a.Sym('i', { imaginary: true }), new a.Sym('h', { hermitian: true }), new a.Sym('ah', { antihermitian: true })];
  expect(a.isReal(a.S.Infinity)).toBe(false);
  expect([a.isPositive(2), a.isNegative(-2), a.isNonNegative(0), a.isNonZero(a.I), a.isZero(k)]).toEqual([true, true, true, false, 'unknown']);
  expect(a.isIntegerValued(a.mul(2, k))).toBe(true);
  expect([a.isNonPositive(a.mul(-1, a.pow(k, 2))), a.isEven(a.mul(2, k)), a.isOdd(a.add(o, 2)), a.isOdd(a.mul(2, k))]).toEqual([true, true, true, false]);
  expect([a.isImaginary(a.mul(2, i)), a.isImaginary(a.pow(i, 2)), a.isHermitian(h), a.isAntihermitian(a.mul(a.I, h))]).toEqual([true, false, true, 'unknown']);
  expect(a.isAntihermitian(ah)).toBe(true);
  expect([a.isExtendedNegative(a.S.NegativeInfinity), a.isExtendedPositive(a.S.Infinity), a.isPolar(a.expPolar(k)), a.isPolar(k)]).toEqual([true, true, true, 'unknown']);
});

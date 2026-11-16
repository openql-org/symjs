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

describe('isReal of the infinities (SymPy oo.is_real)', () => {
  it('does not count oo, -oo and zoo as real numbers', async () => {
    const sj = await import('../../src');
    expect(sj.isReal(sj.oo)).toBe(false);
    expect(sj.isReal(sj.S.NegativeInfinity)).toBe(false);
    expect(sj.isReal(sj.zoo)).toBe(false);
    expect(sj.isReal(sj.nan)).toBe('unknown');
    expect(sj.isReal(2)).toBe(true);
  });
});

describe('the remaining assumption queries (SymPy 1.14)', () => {
  it('ask the facts of the old assumptions', async () => {
    const sj = await import('../../src');
    const [x] = sj.symbols('x');
    expect([sj.isComposite(4), sj.isComposite(5), sj.isComposite(x)]).toEqual([true, false, 'unknown']);
    expect(sj.isExtendedNonpositive(sj.mul(-1, sj.oo))).toBe(true);
    expect(sj.isExtendedNonzero(sj.oo)).toBe(true);
    expect(sj.isNoninteger(sj.Rational.of(1, 2))).toBe(true);
    expect([sj.isTranscendental(sj.pi), sj.isTranscendental(2)]).toEqual([true, false]);
    expect(sj.isCommutative(x)).toBe(true);
    // the mechanical names, and the old spellings as deprecated aliases
    expect([sj.isNonnegative(0), sj.isNonpositive(1), sj.isNonzero(0)]).toEqual([true, false, false]);
    expect(sj.isNonNegative).toBe(sj.isNonnegative);
    expect(sj.isNonPositive).toBe(sj.isNonpositive);
    expect(sj.isNonZero).toBe(sj.isNonzero);
  });
  it('isSingular gives the essential singularities and branch points of a function', async () => {
    const sj = await import('../../src');
    const [x] = sj.symbols('x');
    expect([sj.isSingular(sj.log, 0), sj.isSingular(sj.log, 1)]).toEqual([true, false]);
    expect([sj.isSingular(sj.sin, sj.zoo), sj.isSingular(sj.sin, x)]).toEqual([true, 'unknown']);
    expect(sj.isSingular(sj.acot, sj.I)).toBe(true);
    expect(sj.isSingular(sj.acot, sj.mul(-1, sj.I))).toBe(true);
    // SymPy 1.14 gives None here (it cannot tell -1/E - (-1/E) is zero); -1/E is the branch point of LambertW
    expect(sj.isSingular(sj.LambertW, sj.mul(-1, sj.pow(sj.E, -1)))).toBe(true);
    expect(sj.isSingular(sj.Abs, x)).toBe(true);
    expect(sj.isSingular(sj.zeta, 0)).toBe('unknown');
    expect(sj.isSingular('exp', sj.oo)).toBe(true);
    expect(sj.isSingular(sj.exp, 1)).toBe(false);
    expect(sj.isSingular((...ys: Parameters<typeof sj.add>) => sj.add(...ys, 1), 0)).toBe('unknown');
    expect(sj.isSingular(sj.Mod, 0)).toBe('unknown');
  });
});

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Coverage of functions/special.ts. Expected values are str() results of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { impl } from '../src/core/nodes';
import {
  Float,
  LambertW,
  atan,
  pow,
  Max,
  Min,
  S,
  Sym,
  atan2,
  binomial,
  catalan,
  ceiling,
  erfc,
  erfcinv,
  expandFunc,
  factorial,
  harmonic,
  lowergamma,
  parse,
  rf,
  toComplex,
  uppergamma,
} from '../src';

const x = new Sym('x');
const y = new Sym('y');
const n = new Sym('n');

const cases: [string, string][] = [
  ['floor(sqrt(2)+2*I)', '1 + 2*I'],
  ['ceiling(sqrt(2)-3*I)', '2 - 3*I'],
  ['floor(sqrt(2)+I/2)', '1'],
  ['floor(sqrt(2)+2*I+x)', 'floor(x + sqrt(2)) + 2*I'],
];

describe('special functions', () => {
  it.each(cases)('%s', (src, want) => {
    expect(String(parse(src))).toBe(want);
  });
  it('constructors', () => {
    expect(String(rf(x, 2))).toBe('x*(x + 1)');
    expect(String(harmonic(n))).toBe('harmonic(n)');
    expect(String(lowergamma(x, y))).toBe('lowergamma(x, y)');
    expect(String(uppergamma(x, y))).toBe('uppergamma(x, y)');
    expect(String(LambertW(x))).toBe('LambertW(x)');
    expect(String(LambertW(x, -1))).toBe('LambertW(x, -1)');
    expect(String(ceiling(x))).toBe('ceiling(x)');
    // SymPy expand_func(binomial(x, y)) and expand_func(1 + gamma(x + 2))
    expect(String(expandFunc(parse('binomial(x, y)')))).toBe('binomial(x, y)');
    expect(String(expandFunc(parse('1 + gamma(x + 2)')))).toBe('x*(x + 1)*gamma(x) + 1');
  });
  it('special values', () => {
    expect(String(factorial(S.Infinity))).toBe('oo');
    expect(String(binomial(x, 0))).toBe('1');
    expect(String(erfcinv(2))).toBe('-oo');
    expect(String(catalan(new Sym('m', { integer: true, negative: true })))).toBe('catalan(m)');
    // harmonic numbers of a negative order are power sums: SymPy harmonic(3, -2) = 14
    expect(String(harmonic(3, -2))).toBe('14');
  });
  it('binomial with a very large k', () => {
    // SymPy binomial(-5, 100001), binomial(-5, 100002), binomial(100010, 100005)
    expect(String(binomial(-5, 100001))).toBe('-4167250029583975005');
    expect(String(binomial(-5, 100002))).toBe('4167416716251425015');
    expect(String(binomial(100010, 100005))).toBe('83366671958750016270252');
    // SymPy computes this ~60000-digit number; symjs keeps it unevaluated
    expect(String(binomial(-200001, 100001))).toBe('binomial(-200001, 100001)');
  });
  it('more special values', () => {
    // SymPy erfcinv(1/2), harmonic(oo, 1/2), atan2(1, 0.0), atan2(0.0, -1)
    expect(String(erfcinv(S.Half))).toBe('erfcinv(1/2)');
    expect(String(harmonic(S.Infinity, S.Half))).toBe('oo');
    expect(String(atan2(1, new Float(0)))).toBe('pi/2');
    expect(String(atan2(new Float(0), -1))).toBe('pi');
    // the value of 2**-2000 underflows to 0.0 in double precision; SymPy atan2(1, 2**-2000) = atan(2**2000)
    expect(String(atan2(1, pow(2, -2000)))).toBe(String(atan(pow(2, 2000))));
  });
  it('the lambertW hook of the core', () => {
    expect(String(impl.lambertW?.(x, -1))).toBe('LambertW(x, -1)');
  });
  it('atan2 in the left half-plane', () => {
    expect(String(atan2(-1, parse('-sqrt(2)')))).toBe('-pi + atan(sqrt(2)/2)');
    expect(String(atan2(1, parse('-sqrt(2)')))).toBe('pi - atan(sqrt(2)/2)');
  });
  it('Min and Max of numbers ordered numerically', () => {
    // pi - 3 < 1/7 is decided numerically
    expect(String(Min(parse('pi - 3'), parse('1/7'), x))).toBe('Min(x, -3 + pi)');
    expect(String(Max(parse('pi - 3'), parse('1/7'), x))).toBe('Max(1/7, x)');
  });
  it('floor when the imaginary part is numerically an integer but not decided', () => {
    // the imaginary part is 1 (sqrt(5 + 2*sqrt(6)) = sqrt(2) + sqrt(3)); SymPy gives
    // 1 + I*(-sqrt(2*sqrt(6) + 5) + 1 + sqrt(2) + sqrt(3)), symjs keeps floor unevaluated
    expect(String(parse('floor(sqrt(2) + I*(1 + sqrt(2)+sqrt(3)-sqrt(5+2*sqrt(6))))'))).toBe('floor(sqrt(2) + I*(-sqrt(2*sqrt(6) + 5) + 1 + sqrt(2) + sqrt(3)))');
  });
  it('erfc for large arguments (continued fraction)', () => {
    // mpmath erfc(3), erfc(6)
    expect(toComplex(erfc(x), { x: 3 }).re).toBeCloseTo(2.20904969985854e-5, 15);
    expect(toComplex(erfc(x), { x: 6 }).re / 2.15197367124989e-17).toBeCloseTo(1, 10);
  });
});

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Coverage of functions/combinatorial.ts. Expected values are str() results of SymPy 1.14
// (sympy.functions.combinatorial.numbers), errors where SymPy raises.

import { describe, expect, it } from 'vitest';
import { S, Sym, abs, add, bell, bernoulli, binomialMod, euler, fibonacci, frac, mobius, mul, multigamma } from '../src';

const x = new Sym('x');
const y = new Sym('y');
const z = new Sym('z');

describe('combinatorial numbers and polynomials', () => {
  it('incomplete Bell polynomials', () => {
    // SymPy bell(3, 2, (x, y)), bell(4, 2, (x, y, z)), bell(3, 4, (x,))
    expect(String(bell(3, 2, [x, y]))).toBe('3*x*y');
    expect(String(bell(4, 2, [x, y, z]))).toBe('4*x*z + 3*y**2');
    expect(String(bell(3, 4, [x]))).toBe('0');
    // SymPy: IndexError (too few symbols) and TypeError (symbolic k)
    expect(() => bell(3, 1, [x])).toThrow(RangeError);
    expect(() => bell(3, x, [y])).toThrow(TypeError);
  });
  it('domain errors like SymPy', () => {
    // SymPy raises ValueError for these
    expect(() => fibonacci(-1, x)).toThrow(RangeError);
    expect(() => mobius(0)).toThrow(RangeError);
    expect(() => mobius(-3)).toThrow(RangeError);
    expect(() => multigamma(x, 0)).toThrow(RangeError);
    expect(() => multigamma(x, S.Half)).toThrow(RangeError);
    expect(() => multigamma(x, -1)).toThrow(RangeError);
  });
  it('mobius of a product with a negative integer factor', () => {
    // SymPy leaves mobius(-4*n) unevaluated for a negative integer n; -4*n = 4*|n| has the
    // square factor 4, so 0 is the correct value
    const n = new Sym('n', { integer: true, negative: true });
    expect(String(mobius(mul(-4, n)))).toBe('0');
  });
  it('indices beyond the evaluation limit stay unevaluated', () => {
    // SymPy computes these (a degree-5001 polynomial and 5000-digit numbers); symjs keeps
    // indices above 5000 unevaluated. bernoulli of an odd index above 1 is 0 in both.
    expect(String(bernoulli(5001, x))).toBe('bernoulli(5001, x)');
    expect(String(bernoulli(5002))).toBe('bernoulli(5002)');
    expect(String(bernoulli(5003))).toBe('0');
    expect(String(euler(5001, x))).toBe('euler(5001, x)');
    expect(String(euler(5002))).toBe('euler(5002)');
  });
  it('frac of an imaginary term whose imaginary part contains I', () => {
    // SymPy frac(I*Abs(x + I))
    expect(String(frac(mul(S.I, abs(add(x, S.I)))))).toBe('frac(I*Abs(x + I))');
  });
  it('binomial coefficients modulo a composite modulus', () => {
    // Python math.comb(10, 4) % 12, comb(30, 7) % 60, comb(100, 50) % 1001
    expect(binomialMod(10n, 4n, 12n)).toBe(6n);
    expect(binomialMod(30n, 7n, 60n)).toBe(2035800n % 60n);
    expect(binomialMod(100n, 50n, 1001n)).toBe(100891344545564193334812497256n % 1001n);
  });
});

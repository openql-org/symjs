// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/ntheory/intutil.ts.

import { describe, expect, it } from 'vitest';
import { oo, Rational, Sym } from '../../src/core/nodes';
import { sqrt } from '../../src/core/ops';
import { asInt, asIntCeiling, bitLength, bitScan1, gcdext, invert, iroot, isqrt, isSquare, jacobi, powmod, product, pyLog, pyLog2, pyLogBase, pyRound, remove, truncInt } from '../../src/ntheory/intutil';

/**
 * Coverage of ntheory/intutil.ts, the integer helpers that stand in for
 * Python's int methods, math.isqrt/log/log2, round, pow and the gmpy
 * functions of sympy.external.ntheory; the expected values are those of
 * Python 3.12 with SymPy 1.14.
 */

describe('ntheory intutil: Python and gmpy semantics', () => {
  it('bit_length and bit_scan1', () => {
    expect(bitLength(0n)).toBe(0);
    expect(bitLength(-5n)).toBe(3);
    // gmpy bit_scan1(0) is None, represented by -1
    expect(bitScan1(0n)).toBe(-1);
    expect(bitScan1(-48n)).toBe(4);
    expect(bitScan1(1n << 70n)).toBe(70);
  });
  it('remove', () => {
    expect(remove(0n, 3n)).toEqual([0n, 0n]);
    expect(remove(3n ** 40n * 7n, 3n)).toEqual([7n, 40n]);
    expect(remove(5n ** 7n * 2n, 5n)).toEqual([2n, 7n]);
    expect(remove((1n << 70n) * 3n, 2n)).toEqual([3n, 70n]);
    expect(remove(-48n, 2n)).toEqual([-3n, 4n]);
    expect(() => remove(12n, 1n)).toThrow(RangeError);
  });
  it('isqrt, isSquare and iroot', () => {
    expect(() => isqrt(-1n)).toThrow(RangeError);
    const k = (1n << 26n) - 1n;
    expect(isqrt(k * k - 1n)).toBe(k - 1n);
    expect(isqrt(k * k)).toBe(k);
    expect(isqrt((1n << 52n) - 1n)).toBe((1n << 26n) - 1n);
    expect(isSquare(-4n)).toBe(false);
    expect(isSquare(49n)).toBe(true);
    expect(() => iroot(-1n, 3n)).toThrow(RangeError);
    expect(() => iroot(8n, 0n)).toThrow(RangeError);
    expect(iroot(0n, 3n)).toEqual([0n, true]);
    expect(iroot(1n, 5n)).toEqual([1n, true]);
    expect(iroot(7n, 1n)).toEqual([7n, true]);
    expect(iroot(1n << 64n, 64n)).toEqual([2n, true]);
    expect(iroot(3n ** 300n, 3n)).toEqual([515377520732011331036461129765621272702107522001n, true]);
    expect(iroot(3n ** 300n + 1n, 3n)).toEqual([515377520732011331036461129765621272702107522001n, false]);
    expect(iroot(10n ** 200n - 1n, 7n)).toEqual([37275937203149401661724906094n, false]);
    expect(iroot(1n << 200n, 2n)).toEqual([1267650600228229401496703205376n, true]);
  });
  it('gcdext, invert and pow', () => {
    expect(gcdext(0n, 0n)).toEqual([0n, 0n, 0n]);
    expect(gcdext(0n, -5n)).toEqual([5n, 0n, -1n]);
    expect(gcdext(-4n, 0n)).toEqual([4n, -1n, 0n]);
    expect(gcdext(12n, -18n)).toEqual([6n, -1n, -1n]);
    expect(gcdext(-12n, 18n)).toEqual([6n, 1n, 1n]);
    expect(gcdext(-12n, -18n)).toEqual([6n, 1n, -1n]);
    expect(invert(3n, 1n)).toBe(0n);
    expect(invert(3n, -1n)).toBe(0n);
    expect(() => invert(2n, 4n)).toThrow(RangeError);
    expect(powmod(5n, 3n, 1n)).toBe(0n);
    expect(powmod(5n, 3n, -1n)).toBe(0n);
    expect(powmod(3n, -2n, 7n)).toBe(4n);
    expect(powmod(-3n, 3n, -7n)).toBe(-6n);
  });
  it('jacobi', () => {
    expect(() => jacobi(1n, 0n)).toThrow(RangeError);
    expect(() => jacobi(1n, 4n)).toThrow(RangeError);
    expect([jacobi(0n, 1n), jacobi(0n, 3n), jacobi(1n, 9n), jacobi(6n, 9n), jacobi(1001n, 9907n), jacobi(-1n, 7n), jacobi(19n, 1n)]).toEqual([1, 0, 1, 0, -1, -1, 1]);
  });
  it('math.log, math.log2 and round', () => {
    expect(pyLog2(1n << 1500n)).toBe(1500);
    expect(pyLog2((1n << 1500n) + 1n)).toBe(1500);
    expect(pyLog(1n << 1500n)).toBe(1039.720770839918);
    expect(pyLog((1n << 1500n) + 1n)).toBe(1039.720770839918);
    expect(pyLog(3n ** 1000n)).toBe(1098.6122886681096);
    expect(pyLog2(3n ** 1000n)).toBe(1584.9625007211562);
    expect(pyLog2(10)).toBe(3.321928094887362);
    expect(pyLog(10)).toBe(2.302585092994046);
    expect(pyLogBase(10n ** 400n, 7n)).toBe(473.31786498197533);
    expect([2.3, 2.7, 2.5, 3.5, -2.5, -3.5, 0.5].map(pyRound)).toEqual([2, 3, 2, 4, -2, -4, 0]);
  });
  it('int(), as_int and _as_int_ceiling', () => {
    expect(() => asInt(2.5)).toThrow(TypeError);
    expect(() => asInt(Rational.of(1n, 2n))).toThrow(TypeError);
    expect(asInt(Rational.of(6n))).toBe(6n);
    expect(truncInt(sqrt(2).neg())).toBe(-1n);
    expect(truncInt(sqrt(2))).toBe(1n);
    expect(truncInt(Rational.of(-7n, 2n))).toBe(-3n);
    expect(truncInt(-2.5)).toBe(-2n);
    expect(() => truncInt(new Sym('x'))).toThrow(TypeError);
    expect(asIntCeiling(2.5)).toBe(3n);
    expect(asIntCeiling(7n)).toBe(7n);
    expect(asIntCeiling(sqrt(2))).toBe(2n);
    expect(asIntCeiling(Rational.of(5n, 2n))).toBe(3n);
    expect(asIntCeiling(Rational.of(-5n, 2n))).toBe(-2n);
    expect(() => asIntCeiling(oo)).toThrow(TypeError);
  });
  it('itertools.product', () => {
    expect([...product([])]).toEqual([[]]);
    expect([...product([[1, 2], []])]).toEqual([]);
    expect([...product([[1, 2], [3]])]).toEqual([
      [1, 3],
      [2, 3],
    ]);
  });
});

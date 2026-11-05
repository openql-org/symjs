// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Cases from SymPy 1.14 sympy/sets/tests/test_ordinals.py and the ordinals docstrings.
import { describe, expect, it } from 'vitest';
import { OmegaPower, OmegaPowerNode, Ordinal, convertOrdinal, omega, ord0 } from '../../src/sets';

const w = omega;
const eq = (a: { equals(b: never): boolean; toString(): string }, b: { toString(): string }) => expect(a.toString()).toBe(b.toString());

describe('ordinals', () => {
  it('prints like SymPy', () => {
    expect(String(omega)).toBe('w');
    expect(String(ord0)).toBe('ord0');
    expect(String(Ordinal(OmegaPower(5, 3), OmegaPower(3, 2)))).toBe('w**5*3 + w**3*2');
    expect(String(Ordinal(OmegaPower(5, 3), OmegaPower(0, 5)))).toBe('w**5*3 + 5');
    expect(String(Ordinal(OmegaPower(1, 3), OmegaPower(0, 5)))).toBe('w*3 + 5');
    expect(String(Ordinal(OmegaPower(omega.add(1), 1), OmegaPower(3, 2)))).toBe('w**(w + 1) + w**3*2');
    expect(String(Ordinal(OmegaPower(omega, 1)))).toBe('w**(w)');
    expect(String(OmegaPower(2, 3n))).toBe('OmegaPower(2, 3)');
  });

  it('adds integers and ordinals', () => {
    expect(convertOrdinal(3).add(Ordinal(OmegaPower(5, 3))).equals(Ordinal(OmegaPower(5, 3)))).toBe(true);
    expect(Ordinal(OmegaPower(5, 3)).add(3).equals(Ordinal(OmegaPower(5, 3), OmegaPower(0, 3)))).toBe(true);
    expect(Ordinal(OmegaPower(5, 3), OmegaPower(0, 2)).add(3).equals(Ordinal(OmegaPower(5, 3), OmegaPower(0, 5)))).toBe(true);
    expect(Ordinal(OmegaPower(5, 3), OmegaPower(3, 2)).add(Ordinal(OmegaPower(3, 3))).equals(Ordinal(OmegaPower(5, 3), OmegaPower(3, 5)))).toBe(true);
    expect(Ordinal(OmegaPower(5, 3), OmegaPower(3, 2)).add(Ordinal(OmegaPower(4, 2))).equals(Ordinal(OmegaPower(5, 3), OmegaPower(4, 2)))).toBe(true);
    expect(Ordinal(OmegaPower(omega, 2), OmegaPower(3, 2)).add(Ordinal(OmegaPower(4, 2))).equals(Ordinal(OmegaPower(omega, 2), OmegaPower(4, 2)))).toBe(true);
    eq(convertOrdinal(3).add(w), w);
    eq(w.add(w), 'w*2');
    eq(w.add(ord0), w);
    eq(w.add(0n), w);
  });

  it('compares', () => {
    expect(Ordinal(OmegaPower(5, 3)).gt(Ordinal(OmegaPower(4, 3), OmegaPower(2, 1)))).toBe(true);
    expect(Ordinal(OmegaPower(5, 3), OmegaPower(3, 2)).lt(Ordinal(OmegaPower(5, 4)))).toBe(true);
    expect(Ordinal(OmegaPower(5, 4)).lt(Ordinal(OmegaPower(5, 5), OmegaPower(4, 1)))).toBe(true);
    expect(Ordinal(OmegaPower(5, 3), OmegaPower(3, 2)).equals(Ordinal(OmegaPower(5, 3), OmegaPower(3, 2)))).toBe(true);
    expect(Ordinal(OmegaPower(5, 3), OmegaPower(3, 2)).equals(Ordinal(OmegaPower(5, 3)))).toBe(false);
    expect(Ordinal(OmegaPower(omega, 3)).gt(Ordinal(OmegaPower(5, 3)))).toBe(true);
    expect(Ordinal(OmegaPower(5, 3)).lt(Ordinal(OmegaPower(5, 3), OmegaPower(1, 1)))).toBe(true);
    expect(w.le(w)).toBe(true);
    expect(w.le(5)).toBe(false);
    expect(w.ge(5)).toBe(true);
    expect(convertOrdinal(5).ge(w)).toBe(false);
    const t = OmegaPower(omega.add(1), 1);
    expect(t.lt(5)).toBe(false);
    expect(OmegaPower(0, 2).lt(5)).toBe(true);
    expect(OmegaPower(0, 5).equals(5)).toBe(true);
    expect(t.equals(OmegaPower(omega.add(1), 1))).toBe(true);
    expect(() => t.lt(6.66)).toThrow(TypeError);
  });

  it('multiplies', () => {
    eq(convertOrdinal(3).mul(w), w);
    expect(w.mul(9).equals(Ordinal(OmegaPower(1, 9)))).toBe(true);
    expect(w.mul(w.add(1)).equals(w.mul(w).add(w))).toBe(true);
    expect(w.add(1).mul(w.add(1)).equals(w.mul(w).add(w).add(1))).toBe(true);
    expect(w.mul(1).equals(w)).toBe(true);
    expect(convertOrdinal(1).mul(w).equals(w)).toBe(true);
    expect(w.mul(ord0).equals(ord0)).toBe(true);
    expect(ord0.mul(w).equals(ord0)).toBe(true);
    expect(w.pow(w).equals(w.mul(w.pow(w)))).toBe(true);
    expect(w.pow(w).mul(w).mul(w).equals(w.pow(w.add(2)))).toBe(true);
    eq(w.add(1).mul(w), 'w**2');
  });

  it('exponentiates omega', () => {
    expect(w.pow(2).equals(w.mul(w))).toBe(true);
    expect(w.pow(3).equals(w.mul(w).mul(w))).toBe(true);
    expect(w.pow(w.add(1)).equals(Ordinal(OmegaPower(omega.add(1), 1)))).toBe(true);
    expect(w.pow(w).mul(w.pow(w)).equals(w.pow(w.mul(2)))).toBe(true);
    expect(() => convertOrdinal(2).pow(3)).toThrow(TypeError);
  });

  it('classifies successor and limit ordinals', () => {
    expect(w.isLimitOrdinal).toBe(true);
    expect(w.isSuccessorOrdinal).toBe(false);
    expect(Ordinal(OmegaPower(5, 1)).isSuccessorOrdinal).toBe(false);
    expect(w.add(1).isSuccessorOrdinal).toBe(true);
    expect(ord0.isLimitOrdinal).toBe(false);
    expect(ord0.isSuccessorOrdinal).toBe(false);
    expect(String(w.add(3).degree)).toBe('1');
    expect(String(w.add(3).trailingTerm)).toBe('OmegaPower(ord0, 3)');
    expect(() => ord0.leadingTerm).toThrow(RangeError);
    expect(() => ord0.trailingTerm).toThrow(RangeError);
  });

  it('validates its input', () => {
    expect(() => OmegaPower(1, 0)).toThrow(TypeError);
    expect(() => OmegaPower(1, 1.5)).toThrow(TypeError);
    expect(() => Ordinal(OmegaPower(1, 1), OmegaPower(2, 1))).toThrow(RangeError);
    expect(OmegaPower(w, 1)).toBeInstanceOf(OmegaPowerNode);
  });
});

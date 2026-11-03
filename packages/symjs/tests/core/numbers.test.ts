// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/numbers.ts.
// Number classes and integer helpers. Expected values are SymPy 1.14's (sympy.core.tests.test_numbers).

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { Rational } from '../../src/core/nodes';
import { factorInt, ipow, iroot, lcm } from '../../src/core/numbers';

describe('factorInt: a cofactor above the trial-division limit that is a perfect power', () => {
  it('65537**2', () => {
    expect([...factorInt(4295098369n)]).toEqual([[65537n, 2n]]);
  });
});

describe('numeric helpers', () => {
  it('computes bigint helpers', () => {
    expect(lcm(0n, 5n)).toBe(0n);
    expect(lcm(4n, -6n)).toBe(12n);
    expect(() => ipow(2n, -1n)).toThrow(RangeError);
    expect(() => iroot(-1n, 2n)).toThrow(RangeError);
    expect(iroot(1n, 3n)).toBe(1n);
    expect(iroot(10n, 1n)).toBe(10n);
    expect(iroot(3n, 64n)).toBe(1n);
    expect(iroot(26n, 3n)).toBe(2n);
    expect(iroot(27n, 3n)).toBe(3n);
    expect(() => factorInt(0n)).toThrow(RangeError);
  });

  it('takes integer roots beyond the double range', () => {
    // a floating-point first guess overflows beyond 2**1024
    const big = 2n ** 1100n;
    expect(iroot(big, 2n)).toBe(2n ** 550n);
    expect(iroot(big + 1n, 2n)).toBe(2n ** 550n);
    expect(iroot(big - 1n, 2n)).toBe(2n ** 550n - 1n);
    const c = 3n ** 700n;
    expect(iroot(c, 7n)).toBe(3n ** 100n);
    // SymPy: sqrt(2**1100) = 2**550
    expect(sj.sqrt(Rational.of(big)).equals(Rational.of(2n ** 550n))).toBe(true);
  });
});

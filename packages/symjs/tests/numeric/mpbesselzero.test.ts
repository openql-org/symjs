// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/numeric/mpbesselzero.ts.
//
// Zeros of the Bessel function J_v against mpmath 1.3 besseljzero (at the stated precision).

import { describe, expect, it } from 'vitest';
import '../../src';
import { InvariantError } from '../../src/core/errors';
import * as F from '../../src/numeric/mpf';
import { besselJZeros, isolate, mcmahon } from '../../src/numeric/mpbesselzero';

describe('besseljzero', () => {
  it("McMahon's estimate and its error (mpmath mcmahon)", () => {
    // mpmath mcmahon(mp, 1, 0, 0, 1) = (2.4064624433875701, 0.0045253413017980471), mcmahon(mp, 1, 0, 30, 1) = (37.129575218987966, 0.46418154142702039)
    const [r, err] = mcmahon(0, 1);
    expect(r).toBeCloseTo(2.4064624433875701, 12);
    expect(err).toBeCloseTo(0.0045253413017980471, 12);
    expect(mcmahon(30, 1)[0]).toBeCloseTo(37.129575218987966, 10);
    expect(mcmahon(30, 1)[1]).toBeCloseTo(0.46418154142702039, 12);
  });
  it('zeros at 113 bits', () => {
    // mpmath: with workprec(113): besseljzero(0, 1), besseljzero(20, 2)
    expect(F.toStr(besselJZeros(0, 1, 113)[0]!, 34)).toBe('2.404825557695772768621631879326455');
    expect(besselJZeros(20, 2, 113).map((r) => F.toStr(r, 34))).toEqual(['25.41714081407252358043161441456477', '29.96160379162515605990438912591038']);
  });
  it('invalid input and an isolation that does not succeed', () => {
    expect(() => besselJZeros(-1, 1, 53)).toThrow(RangeError);
    // [2.4, 3] holds one zero of J_0, not two
    expect(() => isolate(F.ZERO, 2.4, 3, 2, 8)).toThrow(InvariantError);
  });
});

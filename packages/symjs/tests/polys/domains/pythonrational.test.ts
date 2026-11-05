// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Expected values from SymPy 1.14.0 (sympy.external.pythonmpq.PythonMPQ).

import { describe, expect, it } from 'vitest';
import { PythonMPQ } from '../../../src/polys/domains/pythonrational';

const q = (p: number, d = 1): PythonMPQ => new PythonMPQ(p, d);

describe('PythonMPQ', () => {
  it('reduces, prints and compares', () => {
    expect([String(q(2, 4)), q(2, 4).repr(), String(q(4, 2)), String(q(1, -2)), String(new PythonMPQ(q(1, 2), 3))]).toEqual(['1/2', 'MPQ(1,2)', '2', '-1/2', '1/6']);
    expect(() => q(1, 0)).toThrow(RangeError);
    expect([q(0).isZero, q(1).isZero, q(0).sign, q(-1, 2).sign, q(3).sign]).toEqual([true, false, 0, -1, 1]);
    expect([q(1, 2).compare(q(1, 3)), q(1, 3).compare(1), q(2).compare(2n)]).toEqual([1, -1, 0]);
    expect([q(2).equals(2), q(2).equals(2n), q(1, 2).equals(0.5), q(2).equals(q(2)), q(2).equals('2')]).toEqual([true, true, false, true, false]);
  });
  it('arithmetic', () => {
    expect([q(1, 2).add(q(1, 3)), q(1, 2).sub(1), q(2, 3).mul(3n), q(2, 3).div(q(4)), q(1, 2).neg(), q(-1, 2).abs(), q(1, 2).abs(), q(2, 3).pow(2), q(2, 3).pow(-2)].map(String)).toEqual(['5/6', '-1/2', '2', '1/6', '-1/2', '1/2', '1/2', '4/9', '9/4']);
  });
});

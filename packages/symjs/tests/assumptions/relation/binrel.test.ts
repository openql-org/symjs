// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/assumptions/relation/binrel.ts; the BinaryRelation docstring of SymPy 1.14 and relations
// built the same way (expected values from SymPy).
import { describe, expect, it } from 'vitest';
import * as sj from '../../../src';

const { Q, ask } = sj;
const x = sj.symbol('x');

describe('BinaryRelation', () => {
  // class MyRel(BinaryRelation): name = "R"; is_reflexive = False, registered for (Number, Number)
  const R = sj.BinaryRelation('R', (n1, n2, a) => (sj.isNum(n1) && sj.isNum(n2) ? ask(Q.zero(sj.sub(sj.sub(n1, n2), 1)), a) : 'unknown'), { isReflexive: false });

  it('applies and asks like the SymPy docstring', () => {
    expect(String(R(2, 1))).toBe('Q.R(2, 1)');
    expect(Q['R']).toBe(R);
    expect(ask(R(2, 1))).toBe(true);
    expect(ask(R(1, 2))).toBe(false);
    expect(ask(R(x, x))).toBe(false);
    expect(ask(R(x, 1))).toBe('unknown');
    // reflexivity does not hold for nan
    expect(ask(R(1, sj.S.NaN))).toBe('unknown');
    expect(() => ask(R(1, 2, 3))).toThrow(RangeError);
  });

  it('tries the swapped arguments of a reflexive relation', () => {
    // x S y when y is a number and x = y + 1 (a handler for one order only)
    const S2 = sj.BinaryRelation('S2', (a, b) => (sj.isNum(b) && sj.isNum(a) ? sj.sub(a, b).equals(sj.S.One) : 'unknown'), { isReflexive: true });
    expect(ask(S2(x, x))).toBe(true);
    expect(ask(S2(2, 1))).toBe(true);
    expect(ask(S2(1, 2))).toBe(false);
    expect(ask(S2(x, 1))).toBe('unknown');
    const T = sj.BinaryRelation('T2', () => 'unknown');
    expect(ask(T(x, x))).toBe('unknown');
  });
});

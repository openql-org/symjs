// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/functions/mathieu.ts.
//
// The Mathieu functions: evaluation rules, derivatives, conjugate and LaTeX. Expected values are str()
// results of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { NotImplementedError, conjugate, diff, evalf, mathieuc, mathieucprime, mathieus, mathieusprime, neg, symbols } from '../../src';

const S = (e: unknown): string => String(e);
const [a, q, z] = symbols('a q z');

describe('Mathieu functions', () => {
  it('values at q = 0 and the parity in z', () => {
    expect(S(mathieus(a, q, z))).toBe('mathieus(a, q, z)');
    expect(S(mathieus(a, 0, z))).toBe('sin(sqrt(a)*z)');
    expect(S(mathieuc(a, 0, z))).toBe('cos(sqrt(a)*z)');
    expect(S(mathieusprime(a, 0, z))).toBe('sqrt(a)*cos(sqrt(a)*z)');
    expect(S(mathieucprime(a, 0, z))).toBe('-sqrt(a)*sin(sqrt(a)*z)');
    expect(S(mathieus(a, sj.float(0), z))).toBe('sin(sqrt(a)*z)');
    expect(S(mathieus(a, q, neg(z)))).toBe('-mathieus(a, q, z)');
    expect(S(mathieuc(a, q, neg(z)))).toBe('mathieuc(a, q, z)');
    expect(S(mathieusprime(a, q, neg(z)))).toBe('mathieusprime(a, q, z)');
    expect(S(mathieucprime(a, q, neg(z)))).toBe('-mathieucprime(a, q, z)');
    // no numerical evaluation (as in SymPy)
    expect(S(evalf(mathieuc(1, 2, 3)))).toBe('mathieuc(1, 2, 3)');
  });
  it('derivatives and conjugate', () => {
    expect(S(diff(mathieus(a, q, z), z))).toBe('mathieusprime(a, q, z)');
    expect(S(diff(mathieuc(a, q, z), z))).toBe('mathieucprime(a, q, z)');
    expect(S(diff(mathieusprime(a, q, z), z))).toBe('(-a + 2*q*cos(2*z))*mathieus(a, q, z)');
    expect(S(diff(mathieucprime(a, q, z), z))).toBe('(-a + 2*q*cos(2*z))*mathieuc(a, q, z)');
    expect(() => diff(mathieuc(a, q, z), a)).toThrow(NotImplementedError);
    expect(S(conjugate(mathieuc(a, q, z)))).toBe('mathieuc(conjugate(a), conjugate(q), conjugate(z))');
  });
  it('LaTeX', () => {
    expect(sj.latex(sj.pow(mathieucprime(a, q, z), 2))).toBe('C^{\\prime}\\left(a, q, z\\right)^{2}');
    expect(sj.latex(mathieus(a, q, z))).toBe('S\\left(a, q, z\\right)');
  });
});

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/polys/matrices/normalforms.ts. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Rational } from '../../../src/core';
import { DomainError } from '../../../src/core/errors';
import { QQ, ZZ } from '../../../src/polys/domains';
import { DM } from '../../../src/polys/matrices/domainmatrix';
import { DMDomainError, DMShapeError } from '../../../src/polys/matrices/exceptions';
import { hermiteNormalForm, invariantFactors, isSmithNormalForm, smithNormalDecomp, smithNormalForm } from '../../../src/polys/matrices/normalforms';

const s = (v: unknown): string => (Array.isArray(v) ? `[${v.map(s).join(', ')}]` : String(v));

describe('normal forms', () => {
  it('Smith normal form', () => {
    const M = DM([[2, 4, 4], [-6, 6, 12], [10, 4, 16]], ZZ);
    expect(String(smithNormalForm(M))).toBe('DomainMatrix({0: {0: 2}, 1: {1: 2}, 2: {2: 156}}, (3, 3), ZZ)');
    expect(s(invariantFactors(M))).toBe('[2, 2, 156]');
    expect(s(smithNormalDecomp(M))).toBe('[DomainMatrix([[2, 0, 0], [0, 2, 0], [0, 0, 156]], (3, 3), ZZ), DomainMatrix([[1, 0, 0], [-2, 1, 1], [-21, 8, 9]], (3, 3), ZZ), DomainMatrix([[1, -2, 18], [0, 1, -10], [0, 0, 1]], (3, 3), ZZ)]');
    expect([isSmithNormalForm(M), isSmithNormalForm(DM([[1, 0], [0, 2]], ZZ)), isSmithNormalForm(DM([[0, 0], [0, 2]], ZZ)), isSmithNormalForm(DM([[2, 0], [0, 3]], ZZ)), isSmithNormalForm(DM([[0, 0], [0, 0]], ZZ))]).toEqual([false, true, false, false, true]);
    expect(String(smithNormalForm(DM([[Rational.of(1n, 2n), 0], [0, 3]], QQ)))).toBe('DomainMatrix({0: {0: 1}, 1: {1: 1}}, (2, 2), QQ)');
    expect(s(invariantFactors(DM([[0, 2], [0, 3]], ZZ)))).toBe('[1, 0]');
    expect(s(smithNormalDecomp(DM([[0, 2], [0, 3]], ZZ)))).toBe('[DomainMatrix([[1, 0], [0, 0]], (2, 2), ZZ), DomainMatrix([[-1, 1], [3, -2]], (2, 2), ZZ), DomainMatrix([[0, 1], [1, 0]], (2, 2), ZZ)]');
    expect(s(smithNormalDecomp(DM([[0, 0], [0, 3]], ZZ)))).toBe('[DomainMatrix([[3, 0], [0, 0]], (2, 2), ZZ), DomainMatrix([[0, 1], [1, 0]], (2, 2), ZZ), DomainMatrix([[0, 1], [1, 0]], (2, 2), ZZ)]');
    expect(s(smithNormalDecomp(DM([[2, 0], [0, 3]], ZZ)))).toBe('[DomainMatrix([[1, 0], [0, 6]], (2, 2), ZZ), DomainMatrix([[-1, 1], [-3, 2]], (2, 2), ZZ), DomainMatrix([[1, -3], [1, -2]], (2, 2), ZZ)]');
    expect(s(invariantFactors(DM([[2, 0], [0, 3]], ZZ)))).toBe('[1, 6]');
    expect(s(smithNormalDecomp(DM([[1, 2]], ZZ)))).toBe('[DomainMatrix([[1, 0]], (1, 2), ZZ), DomainMatrix([[1]], (1, 1), ZZ), DomainMatrix([[1, -2], [0, 1]], (2, 2), ZZ)]');
    expect(s(smithNormalDecomp(DM([[1], [2]], ZZ)))).toBe('[DomainMatrix([[1], [0]], (2, 1), ZZ), DomainMatrix([[1, 0], [-2, 1]], (2, 2), ZZ), DomainMatrix([[1]], (1, 1), ZZ)]');
    expect(s(smithNormalDecomp(DM([[6, 4], [2, 8]], ZZ)))).toBe('[DomainMatrix([[2, 0], [0, 20]], (2, 2), ZZ), DomainMatrix([[0, 1], [-1, 3]], (2, 2), ZZ), DomainMatrix([[1, -4], [0, 1]], (2, 2), ZZ)]');
    expect(s(invariantFactors(DM([], ZZ)))).toBe('[]');
    expect(() => invariantFactors(DM([[1]], ZZ.polyRing()))).toThrow(DomainError);
  });
  it('Hermite normal form', () => {
    const H = DM([[2, 7, 17, 29, 41], [3, 11, 19, 31, 43], [5, 13, 23, 37, 47]], ZZ);
    const want = 'DomainMatrix([[1, 0, 0], [0, 2, 1], [0, 0, 1]], (3, 3), ZZ)';
    expect(String(hermiteNormalForm(H))).toBe(want);
    expect(String(hermiteNormalForm(H, { D: 2 }))).toBe(want);
    expect(String(hermiteNormalForm(H, { D: 2n, checkRank: true }))).toBe(want);
    expect(String(hermiteNormalForm(DM([[-2, 0], [0, 0]], ZZ)))).toBe('DomainMatrix([[2], [0]], (2, 1), ZZ)');
    expect(String(hermiteNormalForm(DM([[0, 0], [0, 0]], ZZ)))).toBe('DomainMatrix([[], []], (2, 0), ZZ)');
    expect(String(hermiteNormalForm(DM([[0, 2], [0, 3]], ZZ), { D: 6 }))).toBe('DomainMatrix([[2, 0], [0, 3]], (2, 2), ZZ)');
    expect(String(hermiteNormalForm(DM([[1, 0], [0, 0]], ZZ), { D: 6, checkRank: true }))).toBe('DomainMatrix([[1], [0]], (2, 1), ZZ)');
    expect(() => hermiteNormalForm(DM([[1]], QQ))).toThrow(DMDomainError);
    expect(() => hermiteNormalForm(DM([[1]], ZZ), { D: 0 })).toThrow(DMDomainError);
    expect(() => hermiteNormalForm(DM([[1], [2]], ZZ), { D: 1 })).toThrow(DMShapeError);
  });
  it('covers the remaining branches', () => {
    expect(s(smithNormalDecomp(DM([[2, 3], [0, 5], [4, 1]], ZZ)))).toBe('[DomainMatrix([[1, 0], [0, 10], [0, 0]], (3, 2), ZZ), DomainMatrix([[1, 0, 0], [5, -1, 0], [-2, 1, 1]], (3, 3), ZZ), DomainMatrix([[-1, 3], [1, -2]], (2, 2), ZZ)]');
    expect(s(invariantFactors(DM([[2, 3], [0, 5], [4, 1]], ZZ)))).toBe('[1, 10]');
    expect(s(smithNormalDecomp(DM([[2, 3]], ZZ)))).toBe('[DomainMatrix([[1, 0]], (1, 2), ZZ), DomainMatrix([[1]], (1, 1), ZZ), DomainMatrix([[-1, 3], [1, -2]], (2, 2), ZZ)]');
    expect(s(smithNormalDecomp(DM([[0, 1], [2, 3]], ZZ)))).toBe('[DomainMatrix([[1, 0], [0, 2]], (2, 2), ZZ), DomainMatrix([[0, 1], [-1, 1]], (2, 2), ZZ), DomainMatrix([[-1, 3], [1, -2]], (2, 2), ZZ)]');
    expect(s(invariantFactors(DM([[0, 1], [2, 3]], ZZ)))).toBe('[1, 2]');
    expect(String(hermiteNormalForm(DM([[2, 4]], ZZ)))).toBe('DomainMatrix([[2]], (1, 1), ZZ)');
    expect(String(hermiteNormalForm(DM([[1], [2], [3]], ZZ)))).toBe('DomainMatrix([[1], [2], [3]], (3, 1), ZZ)');
    expect(String(hermiteNormalForm(DM([[0, -3]], ZZ)))).toBe('DomainMatrix([[3]], (1, 1), ZZ)');
    expect(String(hermiteNormalForm(DM([[4, 2]], ZZ)))).toBe('DomainMatrix([[2]], (1, 1), ZZ)');
    expect(String(hermiteNormalForm(DM([[4, -2]], ZZ)))).toBe('DomainMatrix([[2]], (1, 1), ZZ)');
  });
});

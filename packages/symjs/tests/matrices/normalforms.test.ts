// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/matrices/normalforms.ts. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Rational } from '../../src/core';
import { Matrix } from '../../src/matrices/matrix';
import { hermiteNormalForm, invariantFactors, isSmithNormalForm, smithNormalDecomp, smithNormalForm } from '../../src/matrices/normalforms';
import { QQ, ZZ } from '../../src/polys/domains';
import { DM } from '../../src/polys/matrices/domainmatrix';

const s = (v: unknown): string => (Array.isArray(v) ? `[${v.map(s).join(', ')}]` : String(v));
const m = () => Matrix.of([[2, 4, 4], [-6, 6, 12], [10, 4, 16]]);

describe('matrices/normalforms', () => {
  it('works on Matrices', () => {
    expect(String(smithNormalForm(m(), ZZ))).toBe('Matrix([[2, 0, 0], [0, 2, 0], [0, 0, 156]])');
    expect(isSmithNormalForm(m())).toBe(false);
    expect(s(invariantFactors(m()))).toBe('[2, 2, 156]');
    expect(String(smithNormalDecomp(m())[0])).toBe('Matrix([[2, 0, 0], [0, 2, 0], [0, 0, 156]])');
    const H = Matrix.of([[2, 7, 17, 29, 41], [3, 11, 19, 31, 43], [5, 13, 23, 37, 47]]);
    expect(String(hermiteNormalForm(H, { D: Rational.of(2n) }))).toBe('Matrix([[1, 0, 0], [0, 2, 1], [0, 0, 1]])');
    expect(String(hermiteNormalForm(H))).toBe('Matrix([[1, 0, 0], [0, 2, 1], [0, 0, 1]])');
    expect(s(invariantFactors(Matrix.of([[Rational.of(1n, 2n), 0], [0, 3]]), QQ))).toBe('[1, 1]');
  });
  it('works on DomainMatrices', () => {
    const M = DM([[2, 4, 4], [-6, 6, 12], [10, 4, 16]], ZZ);
    expect(String(smithNormalForm(M))).toBe('DomainMatrix({0: {0: 2}, 1: {1: 2}, 2: {2: 156}}, (3, 3), ZZ)');
    expect(isSmithNormalForm(M)).toBe(false);
    expect(s(invariantFactors(M))).toBe('[2, 2, 156]');
    expect(String(smithNormalDecomp(M)[0])).toBe('DomainMatrix([[2, 0, 0], [0, 2, 0], [0, 0, 156]], (3, 3), ZZ)');
    expect(String(hermiteNormalForm(DM([[-2, 0], [0, 0]], ZZ), { D: 2 }))).toBe('DomainMatrix([[1, 0], [0, 2]], (2, 2), ZZ)');
  });
});

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/functions/special/orthocoeffs.ts.
//
// The coefficient generators of SymPy polys/orthopolys.py (lowest power first). Expected values
// are the coefficients of SymPy 1.14 dup_chebyshevt, dup_legendre, ... reversed.

import { describe, expect, it } from 'vitest';
import * as sj from '../../../src';
import { chebyshevtCoeffs, chebyshevuCoeffs, coeffsExpr, gegenbauerCoeffs, hermiteCoeffs, hermiteProbCoeffs, jacobiCoeffs, laguerreCoeffs, legendreCoeffs } from '../../../src/functions/special/orthocoeffs';

const show = (cs: readonly sj.Expr[]): string[] => cs.map((c) => sj.str(c));

describe('orthogonal polynomial coefficients', () => {
  it('integer recurrences', () => {
    expect(show(chebyshevtCoeffs(0))).toEqual(['1']);
    expect(show(chebyshevtCoeffs(3))).toEqual(['0', '-3', '0', '4']);
    expect(show(chebyshevuCoeffs(2))).toEqual(['-1', '0', '4']);
    expect(show(hermiteCoeffs(3))).toEqual(['0', '-12', '0', '8']);
    expect(show(hermiteProbCoeffs(3))).toEqual(['0', '-3', '0', '1']);
    expect(show(legendreCoeffs(2))).toEqual(['-1/2', '0', '3/2']);
  });

  it('parametric families', () => {
    const [a, b] = sj.symbols('a b');
    expect(show(gegenbauerCoeffs(2, a))).toEqual(['-a', '0', '2*a**2 + 2*a']);
    expect(show(laguerreCoeffs(1, a))).toEqual(['a + 1', '-1']);
    expect(show(jacobiCoeffs(1, a, b))).toEqual(['a/2 - b/2', 'a/2 + b/2 + 1']);
  });

  it('coeffsExpr builds the polynomial', () => {
    const [x] = sj.symbols('x');
    expect(sj.str(coeffsExpr(chebyshevtCoeffs(2), x))).toBe('2*x**2 - 1');
  });
});

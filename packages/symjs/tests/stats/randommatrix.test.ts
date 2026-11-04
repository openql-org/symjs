// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/stats/randommatrix.ts (SymPy sympy/stats/random_matrix.py).
// Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { MatrixSymbol, Sym, str } from '../../src';
import { density } from '../../src/stats';
import { RandomMatrixSymbol } from '../../src/stats/rv';
import { RandomMatrixPSpace } from '../../src/stats/randommatrix';
import { GaussianUnitaryEnsemble } from '../../src/stats/randommatrixmodels';

describe('RandomMatrixPSpace', () => {
  it('model and density', () => {
    const U = GaussianUnitaryEnsemble('U', 2);
    const ps = U.pspace as RandomMatrixPSpace;
    expect(ps.hasModel).toBe(true);
    expect(ps.hasValueDensity).toBe(true);
    expect(ps.valueDensity).toBe(ps.model);
    expect(str(ps.computeDensity(U) as never)).toBe('exp(-Trace(U**2))/(2*pi**2)');
    // SymPy: NotImplementedError for an expression of random matrices
    expect(() => ps.computeDensity(U.mul(2))).toThrow('Currently, no algorithm has been implemented');
  });
  it('a space without a model', () => {
    const ps = new RandomMatrixPSpace([new Sym('P')]);
    expect(str(ps)).toBe('RandomMatrixPSpace(P)');
    expect(ps.symbol.name).toBe('P');
    expect(ps.hasModel).toBe(false);
    expect(ps.hasValueDensity).toBe(false);
    const H = new RandomMatrixSymbol('H', 2, 2, ps);
    // SymPy: AttributeError ('NoneType' object has no attribute 'density')
    expect(() => density(H)).toThrow();
    const bad = new RandomMatrixPSpace([new Sym('P'), new Sym('x')]);
    expect(() => bad.model).toThrow('x is not a random matrix ensemble model');
    void MatrixSymbol;
  });
});

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/vector/scalar.ts (SymPy sympy/vector/scalar.py and the base
// scalar cases of sympy/vector/tests/test_coordsysrect.py, test_printing.py).
// Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { add, diff, integrate, latex, mul, pow, pretty, solve, str, symbol } from '../../src';
import { BaseScalar, CoordSys3D, Vector } from '../../src/vector';

describe('BaseScalar', () => {
  const A = CoordSys3D('A');
  it('is a coordinate symbol', () => {
    expect(str(A.x)).toBe('A.x');
    expect(latex(A.x)).toBe('\\mathbf{{x}_{A}}');
    expect(pretty(A.x)).toBe('x_A');
    expect(A.x.system).toBe(A);
    expect(A.x.index).toBe(0);
    expect(BaseScalar(1, A).key).toBe(A.y.key);
    expect(BaseScalar(1, A).prettyForm).toBe('x1');
    expect(BaseScalar(1, A, symbol('p'), symbol('q')).latexForm).toBe('q');
    expect(BaseScalar(0, A).key).not.toBe(BaseScalar(0, A.locateNew('A', A.i)).key);
    expect(diff(mul(A.x, A.y), A.x)).toBe(A.y);
    expect(str(integrate(pow(A.x, 2), A.x))).toBe('A.x**3/3');
    expect(solve(add(A.x, -2), A.x).map(str)).toEqual(['2']);
    // SymPy orders BaseScalars before Symbols: C.x + c, C.x*c
    const c = symbol('c');
    expect(str(add(A.x, c))).toBe('A.x + c');
    expect(str(mul(A.x, c, symbol('B')))).toBe('A.x*B*c');
  });
  it('checks its arguments', () => {
    expect(() => BaseScalar(3, A)).toThrow('Invalid index specified.');
    expect(() => BaseScalar(0, Vector.zero as never)).toThrow('system should be a CoordSys3D');
  });
});

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/compare.ts. Expected values from SymPy 1.14 (type(e).__name__, e.args, Basic.compare).

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { Dummy, Float, S, Sym, Wild } from '../../src/core/nodes';
import { basicCompare, sympyArgs, sympyClassName } from '../../src/core/compare';

const [x, y] = sj.symbols('x y') as [Sym, Sym];

describe('SymPy class names', () => {
  it('numbers, constants and symbols', () => {
    const names = [S.Zero, S.One, S.NegOne, S.Half, sj.Rational.of(2n), sj.Rational.of(1n, 3n), new Float(1.5), sj.pi, sj.E, sj.I, S.EulerGamma, S.Infinity, S.NegativeInfinity, S.ComplexInfinity, S.NaN, x, new Dummy('d'), new Wild('w'), S.true, S.false].map(sympyClassName);
    expect(names).toEqual(['Zero', 'One', 'NegativeOne', 'Half', 'Integer', 'Rational', 'Float', 'Pi', 'Exp1', 'ImaginaryUnit', 'EulerGamma', 'Infinity', 'NegativeInfinity', 'ComplexInfinity', 'NaN', 'Symbol', 'Dummy', 'Wild', 'BooleanTrue', 'BooleanFalse']);
  });
  it('compound nodes', () => {
    const f = sj.SymFunction('f');
    const names = [sj.add(x, 1), sj.mul(2, x), sj.pow(x, 2), sj.exp(x), sj.sin(x), sj.Abs(x), f(x), sj.Eq(x, 1), sj.Lt(x, 1), sj.Tuple(x), new sj.Integral([x, x])].map(sympyClassName);
    expect(names).toEqual(['Add', 'Mul', 'Pow', 'exp', 'sin', 'Abs', 'f', 'Equality', 'StrictLessThan', 'Tuple', 'Integral']);
  });
});

describe('SymPy args and Basic.compare', () => {
  it('exp(x) has the argument x; sums and products in Basic.compare order', () => {
    expect(sympyArgs(sj.exp(x)).map(String)).toEqual(['x']);
    expect(sympyArgs(sj.add(y, x, 2)).map(String)).toEqual(['2', 'x', 'y']);
    const A = new Sym('A', { commutative: false });
    expect(sympyArgs(sj.mul(y, x, A)).map(String)).toEqual(['x', 'y', 'A']);
    expect(sympyArgs(sj.sin(x)).map(String)).toEqual(['x']);
  });
  it('compare', () => {
    expect(basicCompare(x, x)).toBe(0);
    expect(basicCompare(sj.Rational.of(2n), x)).toBe(-1);
    expect(basicCompare(x, y)).toBe(-1);
    expect(basicCompare(sj.sin(x), sj.sin(y))).toBe(-1);
    expect(basicCompare(sj.sin(x), sj.cos(x))).toBe(1);
    expect(basicCompare(sj.add(x, 1), sj.add(x, y, 1))).toBe(-1);
    expect(basicCompare(new Float(1.5), new Float(2.5))).toBe(-1);
    expect(basicCompare(sj.MatrixSymbol('A', 2, 2).args[0]!, sj.MatrixSymbol('B', 2, 2).args[0]!)).toBe(-1);
  });
});

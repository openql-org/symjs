// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { describe, it, expect } from 'vitest';
import { ExtensionExpr, ImmutableMatrix, Matrix, S, Tuple, add, latex, mul, pow, sin, str, symbol } from '@symjs/symjs';
import { Tr } from '../src';

describe('quantum trace', () => {
  const A = symbol('A', { commutative: false }), B = symbol('B', { commutative: false }), x = symbol('x');
  it('keeps partial indices and prints the operator in its original order', () => {
    const t = Tr(mul(A, B), 2);
    expect(str(t)).toBe('Tr(A*B)');
    expect(latex(t)).toBe('\\operatorname{tr}\\left(A B\\right)');
    expect(t.isNumber).toBe(true);
    expect(t.equals(Tr(mul(B, A), [2]))).toBe(true);
    expect(t.equals(Tr(mul(B, A)))).toBe(false);
    expect(Tr(mul(A, B, A)).equals(Tr(mul(pow(A, 2), B)))).toBe(true);
    expect(Tr(mul(A, B, pow(A, -1))).equals(Tr(B))).toBe(true);
    if (!(t instanceof ExtensionExpr)) throw new TypeError('expected a trace node');
    expect(t.withArgs([B, Tuple(2)]).equals(Tr(B, 2))).toBe(true);
    expect(() => t.withArgs([])).toThrow(TypeError);
    expect(() => t.withArgs([B, A])).toThrow(TypeError);
  });
  it('is linear and evaluates scalars and explicit matrices', () => {
    expect(str(Tr(add(A, B)))).toBe('Tr(A) + Tr(B)');
    expect(str(Tr(mul(x, A)))).toBe('x*Tr(A)');
    expect(str(Tr(mul(x, sin(x))))).toBe('x*sin(x)');
    expect(str(Tr(pow(x, 2)))).toBe('x**2');
    expect(str(Tr(pow(A, 2)))).toBe('Tr(A**2)');
    expect(str(Tr(3))).toBe('3');
    for (const s of [S.Infinity, S.NegativeInfinity, S.NaN]) expect(Tr(s)).toBe(s);
    expect(str(Tr(S.ComplexInfinity))).toBe('Tr(zoo)');
    expect(str(Tr(ImmutableMatrix([[1, 2], [3, 4]])))).toBe('5');
    expect(str(Tr(Matrix.of([[1, 2], [3, 4]])))).toBe('5');
  });
});

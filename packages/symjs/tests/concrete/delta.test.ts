// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/concrete/delta.ts.
// Sums and products of Kronecker deltas. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { deltaproduct, deltasummation } from '../../src/calculus';

const [k, n, x] = sj.symbols('k n x') as sj.Sym[];
const i = sj.symbol('i', { integer: true });
const j = sj.symbol('j', { integer: true });
const P = (s: string): sj.Expr => sj.parse(s, { symbols: [k!, n!, x!, i, j], locals: { KroneckerDelta: sj.KroneckerDelta } });
const oo = sj.S.Infinity;
const ds = (f: string, l: [sj.Sym, sj.ExprLike, sj.ExprLike]): string => sj.str(deltasummation(P(f), l));
const dp = (f: string, l: [sj.Sym, sj.ExprLike, sj.ExprLike]): string => sj.str(deltaproduct(P(f), l));

describe('deltasummation', () => {
  it('picks the term of the delta', () => {
    expect(ds('KroneckerDelta(i, k)', [k!, sj.S.NegativeInfinity, oo])).toBe('1');
    expect(ds('KroneckerDelta(i, k)', [k!, 0, oo])).toBe('Piecewise((1, i >= 0), (0, True))');
    expect(ds('KroneckerDelta(i, k)', [k!, 1, 3])).toBe('Piecewise((1, (i >= 1) & (i <= 3)), (0, True))');
    expect(ds('k*KroneckerDelta(i, j)*KroneckerDelta(j, k)', [k!, sj.S.NegativeInfinity, oo])).toBe('j*KroneckerDelta(i, j)');
    expect(ds('j*KroneckerDelta(i, j)', [j, sj.S.NegativeInfinity, oo])).toBe('i');
    expect(ds('i*KroneckerDelta(i, j)', [i, sj.S.NegativeInfinity, oo])).toBe('j');
    expect(sj.str(deltasummation(P('k*KroneckerDelta(i, k)'), [k!, 1, 3], true))).toBe('i');
    expect(ds('x*KroneckerDelta(k, 0)', [k!, -2, 2])).toBe('x');
  });
  it('sums without a simple delta and empty ranges', () => {
    expect(ds('k', [k!, 1, n!])).toBe('n**2/2 + n/2');
    expect(ds('KroneckerDelta(i, k)', [k!, 3, 1])).toBe('0');
    expect(ds('x*(KroneckerDelta(i, k) + 1)', [k!, 1, 3])).toBe('Piecewise((4*x, (i >= 1) & (i <= 3)), (3*x, True))');
    expect(ds('k + KroneckerDelta(i, k)', [k!, 1, n!])).toBe('Piecewise((n**2/2 + n/2 + 1, (i >= 1) & (i <= n)), (n**2/2 + n/2, True))');
    expect(ds('KroneckerDelta(i, k**2)', [k!, 1, n!])).toBe('Sum(KroneckerDelta(i, k**2), (k, 1, n))');
    expect(ds('KroneckerDelta(i, j)*KroneckerDelta(i, k)', [k!, 1, n!])).toBe('Piecewise((KroneckerDelta(i, j), (i >= 1) & (i <= n)), (0, True))');
  });
});

describe('deltaproduct', () => {
  it('products of deltas', () => {
    expect(dp('k', [k!, 1, n!])).toBe('factorial(n)');
    expect(dp('KroneckerDelta(i, k)', [k!, 1, n!])).toBe('KroneckerDelta(0, n) + KroneckerDelta(1, i)*KroneckerDelta(1, n)');
    expect(dp('KroneckerDelta(i, k)', [k!, 3, 1])).toBe('1');
    expect(dp('x + KroneckerDelta(i, k)', [k!, 1, 3])).toBe('x**3 + x**2*KroneckerDelta(1, i) + x**2*KroneckerDelta(2, i) + x**2*KroneckerDelta(3, i)');
    expect(dp('x + KroneckerDelta(i, k)', [k!, 1, n!])).toBe('x**n + Piecewise((x**(-i + n)*x**(i - 1), (i >= 1) & (i <= n)), (0, True))');
    expect(dp('x*(KroneckerDelta(i, k) + 1)', [k!, 1, n!])).toBe('x**n + Piecewise((x*x**(-i + n)*x**(i - 1), (i >= 1) & (i <= n)), (0, True))');
    expect(dp('x*KroneckerDelta(i, k**2)', [k!, 1, 2])).toBe('x**2*KroneckerDelta(1, i)*KroneckerDelta(4, i)');
    expect(dp('k*KroneckerDelta(i, j)', [k!, 1, 3])).toBe('6*KroneckerDelta(i, j)');
    expect(dp('KroneckerDelta(i, k)', [k!, 1, 3])).toBe('0');
    expect(dp('KroneckerDelta(i, k)', [k!, 1, P('n**2')])).toBe('KroneckerDelta(0, n) + KroneckerDelta(1, i)*KroneckerDelta(1, n**2)');
    expect(dp('KroneckerDelta(i, k)', [k!, 1, P('n**2 - 1')])).toBe('KroneckerDelta(0, n**2 - 1) + KroneckerDelta(1, i)*KroneckerDelta(1, n**2 - 1)');
    expect(dp('2*x + KroneckerDelta(i, k)', [k!, 1, 2])).toBe('4*x**2 + 2*x*KroneckerDelta(1, i) + 2*x*KroneckerDelta(2, i)');
    expect(dp('KroneckerDelta(i, k)*KroneckerDelta(k, j) + x', [k!, 1, 2])).toBe('x**2 + x*KroneckerDelta(1, i)*KroneckerDelta(1, j) + x*KroneckerDelta(2, i)*KroneckerDelta(2, j)');
    expect(dp('KroneckerDelta(k, 1)*KroneckerDelta(k, 2) + x', [k!, 1, 2])).toBe('x**2');
    expect(dp('KroneckerDelta(i, k)*KroneckerDelta(i, 2)', [k!, 1, n!])).toBe('KroneckerDelta(0, n)');
    expect(dp('KroneckerDelta(i, k)*KroneckerDelta(i, j)', [k!, 1, n!])).toBe('KroneckerDelta(0, n) + KroneckerDelta(1, i)*KroneckerDelta(1, j)*KroneckerDelta(1, n)');
    const m = sj.symbol('m');
    expect(sj.str(deltaproduct(P('KroneckerDelta(i, k)'), [k!, 1, sj.add(n!, m)]))).toBe('KroneckerDelta(1, i)*KroneckerDelta(m, 1 - n) + KroneckerDelta(m, -n)');
    // (SymPy solves m*n = 1 as well: KroneckerDelta(m, 1/n))
    expect(sj.str(deltaproduct(P('KroneckerDelta(i, k)'), [k!, 1, sj.mul(n!, m)]))).toBe('KroneckerDelta(0, m*n) + KroneckerDelta(1, i)*KroneckerDelta(1, m*n)');
    // (SymPy recurses without end)
    expect(() => deltaproduct(P('KroneckerDelta(i, j) + x'), [k!, 1, 3])).toThrow(sj.NotImplementedError);
    expect(dp('KroneckerDelta(i, k)*KroneckerDelta(j, k)', [k!, 1, n!])).toBe('KroneckerDelta(0, n) + KroneckerDelta(1, i)*KroneckerDelta(1, j)*KroneckerDelta(1, n)');
  });
});

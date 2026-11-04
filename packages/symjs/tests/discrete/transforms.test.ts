// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/discrete/transforms.ts: SymPy's sympy/discrete/tests/test_transforms.py and
// the doctests of sympy/discrete/transforms.py; expected values from SymPy 1.14.

import { describe, expect, it } from 'vitest';
import type { Expr } from '../../src/core/nodes';
import { Sym } from '../../src/core/nodes';
import { parseExpr } from '../../src/index';
import { fft, fwht, ifft, ifwht, intt, inverseMobiusTransform, mobiusTransform, ntt } from '../../src/discrete/index';
import { padLength } from '../../src/discrete/transforms';

/** A list of expressions written with `;` separators. */
const L = (s: string): Expr[] => s.split(';').map((t) => parseExpr(t));
/** Python's printed form of a list. */
const str = (v: readonly unknown[]): string => `[${v.map(String).join(', ')}]`;
const range = (n: number): number[] => Array.from({ length: n }, (_, i) => i);

const x = new Sym('x');
const y = new Sym('y');

describe('fft, ifft', () => {
  it('leaves short sequences unchanged', () => {
    for (const tf of [fft, ifft]) {
      expect(tf([])).toEqual([]);
      expect(str(tf(L('5/3')))).toBe('[5/3]');
    }
  });

  it('transforms exactly', () => {
    const fls = '[15, -7*sqrt(2)/2 - 4 - sqrt(2)*I/2 + 2*I, 2 + 3*I, -4 + 7*sqrt(2)/2 - 2*I - sqrt(2)*I/2, -3, -4 + 7*sqrt(2)/2 + sqrt(2)*I/2 + 2*I, 2 - 3*I, -7*sqrt(2)/2 - 4 - 2*I + sqrt(2)*I/2]';
    const f = fft(range(6));
    expect(str(f)).toBe(fls);
    expect(str(ifft(f))).toBe('[0, 1, 2, 3, 4, 5, 0, 0]');
    const ifls = ifft(L('1 + 2*I; 3 + 4*I; 5 + 6*I'));
    expect(str(ifls)).toBe('[9/4 + 3*I, -7*I/4, 3/4 + I, -2 - I/4]');
    expect(str(fft(ifls))).toBe('[1 + 2*I, 3 + 4*I, 5 + 6*I, 0]');
    expect(str(fft([1, 2, 3, 4, 5]))).toBe(
      '[15, -4 - sqrt(2) + 3*I + 3*sqrt(2)*I, 3 - 2*I, -4 + sqrt(2) - 3*I + 3*sqrt(2)*I, 3, -4 + sqrt(2) - 3*sqrt(2)*I + 3*I, 3 + 2*I, -4 - sqrt(2) - 3*sqrt(2)*I - 3*I]',
    );
  });

  it('doctests', () => {
    const f = fft([1, 2, 3, 4]);
    expect(str(f)).toBe('[10, -2 - 2*I, -2, -2 + 2*I]');
    expect(str(ifft(f))).toBe('[1, 2, 3, 4]');
    const i = ifft([1, 2, 3, 4]);
    expect(str(i)).toBe('[5/2, -1/2 + I/2, -1/2, -1/2 - I/2]');
    expect(str(fft(i))).toBe('[1, 2, 3, 4]');
    // the docstring shows 3.75, ...; SymPy 1.14 prints the 15 digits below
    const n = ifft([1, 7, 3, 4], { dps: 15 });
    expect(str(n)).toBe('[3.75000000000000, -0.5 - 0.75*I, -1.75000000000000, -0.5 + 0.75*I]');
    expect(str(fft(n))).toBe('[1.00000000000000, 7.00000000000000, 3.00000000000000, 4.00000000000000]');
  });

  it('transforms numerically with dps', () => {
    expect(str(fft([1, 2, 3, 4, 5], { dps: 10 }))).toBe(
      '[15, -5.41421356237 + 7.24264068712*I, 3.0 - 2.0*I, -2.58578643763 + 1.24264068712*I, 3, -2.58578643763 - 1.24264068712*I, 3.0 + 2.0*I, -5.41421356237 - 7.24264068712*I]',
    );
    expect(str(ifft(L('pi; E'), { dps: 20 }))).toBe('[2.9299372410244192369, 0.21165541256537400155]');
  });

  it('rejects non-sequences and symbolic coefficients', () => {
    const xr = new Sym('x', { real: true });
    // @ts-expect-error: not a sequence (SymPy raises TypeError)
    expect(() => fft(xr)).toThrow(TypeError);
    expect(() => ifft([xr, xr.mul(2), xr.pow(2).mul(3), xr.pow(3).mul(4)])).toThrow('Expected non-symbolic coefficients');
    // SymPy checks the coefficients before the length
    expect(() => fft([x])).toThrow(RangeError);
  });
});

describe('ntt, intt', () => {
  const p = 7 * 17 * 2 ** 23 + 1;
  const q = 2 * 500000003 + 1; // only for sequences of length 1 or 2
  const r = 2 * 3 * 5 * 7; // composite modulus

  it('leaves short sequences unchanged', () => {
    for (const tf of [ntt, intt]) {
      expect(tf([], p)).toEqual([]);
      expect(tf([5], p)).toEqual([5n]);
    }
  });

  it('transforms modulo a prime', () => {
    const nls = [15n, 801133602n, 738493201n, 334102277n, 998244350n, 849020224n, 259751156n, 12232587n];
    expect(ntt(range(6), p)).toEqual(nls);
    expect(intt(nls, p)).toEqual([0n, 1n, 2n, 3n, 4n, 5n, 0n, 0n]);
    expect(ntt([-3, 5n, parseExpr('7')], 17)).toEqual([9n, 4n, 16n, 10n]);
  });

  it('doctests', () => {
    const P = 3 * 2 ** 8 + 1;
    expect(ntt([1, 2, 3, 4], P)).toEqual([10n, 643n, 767n, 122n]);
    expect(intt([10n, 643n, 767n, 122n], P)).toEqual([1n, 2n, 3n, 4n]);
    expect(intt([1, 2, 3, 4], P)).toEqual([387n, 415n, 384n, 353n]);
    expect(ntt([387n, 415n, 384n, 353n], P)).toEqual([1n, 2n, 3n, 4n]);
  });

  it('rejects invalid input', () => {
    const xi = new Sym('x', { integer: true });
    // @ts-expect-error: not a sequence
    expect(() => ntt(xi, p)).toThrow(TypeError);
    // SymPy's as_int raises ValueError (RangeError in symjs)
    expect(() => intt([xi, xi.mul(2)], p)).toThrow(new RangeError('x is not an integer'));
    expect(() => intt(L('1 + 2*I; 3 + 4*I; 5 + 6*I'), p)).toThrow(new RangeError('1 + 2*I is not an integer'));
    expect(() => ntt([1.2, 2.1, 3.5], p)).toThrow(new RangeError('1.2 is not an integer'));
    expect(() => ntt([1], parseExpr('17/2'))).toThrow(new RangeError('17/2 is not an integer'));
    expect(() => ntt([3, 5, 6], q)).toThrow('Expected prime modulus of the form (m*2**k + 1)');
    expect(() => ntt([4, 5, 7], r)).toThrow('Expected prime modulus for Number Theoretic Transform');
    expect(() => ntt([], 15)).toThrow(RangeError);
  });
});

describe('fwht, ifwht', () => {
  it('leaves short sequences unchanged', () => {
    for (const tf of [fwht, ifwht]) {
      expect(tf([])).toEqual([]);
      expect(str(tf(L('7/4')))).toBe('[7/4]');
    }
  });

  it('transforms', () => {
    const fls = '[49459, 38061, -47661, -37759, 48729, 37543, -48391, -38277]';
    const f = fwht([213, 321, 43235, 5325, 312, 53]);
    expect(str(f)).toBe(fls);
    expect(str(ifwht(f))).toBe('[213, 321, 43235, 5325, 312, 53, 0, 0]');

    const ifls = ifwht(L('1/2 + 2*I; 3/7 + 4*I; 5/6 + 6*I; 7/3; 9/4'));
    expect(str(ifls)).toBe('[533/672 + 3*I/2, 23/224 + I/2, 1/672, 107/224 - I, 155/672 + 3*I/2, -103/224 + I/2, -377/672, -19/224 - I]');
    expect(str(fwht(ifls))).toBe('[1/2 + 2*I, 3/7 + 4*I, 5/6 + 6*I, 7/3, 9/4, 0, 0, 0]');

    const ls = L('x; 2*x; 3*x**2; 4*x**3');
    const i2 = ifwht(ls);
    expect(str(i2)).toBe('[x**3 + 3*x**2/4 + 3*x/4, -x**3 + 3*x**2/4 - x/4, -x**3 - 3*x**2/4 + 3*x/4, x**3 - 3*x**2/4 - x/4]');
    expect(str(fwht(i2))).toBe(str(ls));

    const f3 = fwht(L('x; y; x**2; y**2; x*y'));
    expect(str(f3)).toBe(
      '[x**2 + x*y + x + y**2 + y, x**2 + x*y + x - y**2 - y, -x**2 + x*y + x - y**2 + y, -x**2 + x*y + x + y**2 - y, x**2 - x*y + x + y**2 + y, x**2 - x*y + x - y**2 - y, -x**2 - x*y + x - y**2 + y, -x**2 - x*y + x + y**2 - y]',
    );
    expect(str(ifwht(f3))).toBe('[x, y, x**2, y**2, x*y, 0, 0, 0]');

    expect(str(fwht(range(6)))).toBe(str(ifwht(range(6)).map((e) => e.mul(8))));
    // @ts-expect-error: not a sequence
    expect(() => fwht(x)).toThrow(TypeError);
  });

  it('doctests', () => {
    expect(str(fwht([4, 2, 2, 0, 0, 2, -2, 0]))).toBe('[8, 0, 8, 0, 8, 8, 0, 0]');
    expect(str(ifwht([8, 0, 8, 0, 8, 8, 0, 0]))).toBe('[4, 2, 2, 0, 0, 2, -2, 0]');
    expect(str(ifwht([19, -1, 11, -9, -7, 13, -15, 5]))).toBe('[2, 0, 4, 0, 3, 10, 0, 0]');
    expect(str(fwht([2, 0, 4, 0, 3, 10, 0, 0]))).toBe('[19, -1, 11, -9, -7, 13, -15, 5]');
  });
});

describe('mobiusTransform, inverseMobiusTransform', () => {
  it('leaves short sequences unchanged', () => {
    for (const subset of [true, false]) {
      for (const tf of [mobiusTransform, inverseMobiusTransform]) {
        expect(tf([], { subset })).toEqual([]);
        expect(str(tf(L('7/4'), { subset }))).toBe('[7/4]');
      }
    }
  });

  it('transforms over subsets and supersets', () => {
    expect(str(mobiusTransform(L('x; y')))).toBe('[x, x + y]');
    expect(str(inverseMobiusTransform(L('x; x + y')))).toBe('[x, y]');
    expect(str(mobiusTransform(L('x; y'), { subset: false }))).toBe('[x + y, y]');
    expect(str(inverseMobiusTransform(L('x + y; y'), { subset: false }))).toBe('[x, y]');

    expect(str(mobiusTransform(L('w; x; y; z')))).toBe('[w, w + x, w + y, w + x + y + z]');
    expect(str(inverseMobiusTransform(L('w; w + x; w + y; w + x + y + z')))).toBe('[w, x, y, z]');
    expect(str(mobiusTransform(L('w; x; y; z'), { subset: false }))).toBe('[w + x + y + z, x + z, y + z, z]');
    expect(str(inverseMobiusTransform(L('w + x + y + z; x + z; y + z; z'), { subset: false }))).toBe('[w, x, y, z]');

    const ls = L('2/3; 6/7; 5/8; 9; 5/3 + 7*I');
    const mls = mobiusTransform(ls);
    expect(str(mls)).toBe('[2/3, 32/21, 31/24, 1873/168, 7/3 + 7*I, 67/21 + 7*I, 71/24 + 7*I, 2153/168 + 7*I]');
    expect(str(inverseMobiusTransform(mls))).toBe('[2/3, 6/7, 5/8, 9, 5/3 + 7*I, 0, 0, 0]');
    const sup = mobiusTransform(ls, { subset: false });
    expect(str(sup)).toBe('[2153/168 + 7*I, 69/7, 77/8, 9, 5/3 + 7*I, 0, 0, 0]');
    expect(str(inverseMobiusTransform(sup, { subset: false }))).toBe('[2/3, 6/7, 5/8, 9, 5/3 + 7*I, 0, 0, 0]');

    const ls4 = ls.slice(0, -1);
    expect(str(mobiusTransform(ls4))).toBe('[2/3, 32/21, 31/24, 1873/168]');
    expect(str(inverseMobiusTransform(L('2/3; 32/21; 31/24; 1873/168')))).toBe('[2/3, 6/7, 5/8, 9]');
    expect(str(mobiusTransform(ls4, { subset: false }))).toBe('[1873/168, 69/7, 77/8, 9]');
    expect(str(inverseMobiusTransform(L('1873/168; 69/7; 77/8; 9'), { subset: false }))).toBe('[2/3, 6/7, 5/8, 9]');

    // @ts-expect-error: not a sequence
    expect(() => mobiusTransform(x, { subset: true })).toThrow(TypeError);
    // @ts-expect-error: not a sequence
    expect(() => inverseMobiusTransform(y, { subset: false })).toThrow(TypeError);
  });

  it('doctests', () => {
    const m = mobiusTransform(L('x; y; z'));
    expect(str(m)).toBe('[x, x + y, x + z, x + y + z]');
    expect(str(inverseMobiusTransform(m))).toBe('[x, y, z, 0]');
    const s = mobiusTransform(L('x; y; z'), { subset: false });
    expect(str(s)).toBe('[x + y + z, y, z, 0]');
    expect(str(inverseMobiusTransform(s, { subset: false }))).toBe('[x, y, z, 0]');
    expect(str(mobiusTransform([1, 2, 3, 4]))).toBe('[1, 3, 4, 10]');
    expect(str(inverseMobiusTransform([1, 3, 4, 10]))).toBe('[1, 2, 3, 4]');
    expect(str(mobiusTransform([1, 2, 3, 4], { subset: false }))).toBe('[10, 6, 7, 4]');
    expect(str(inverseMobiusTransform([10, 6, 7, 4], { subset: false }))).toBe('[1, 2, 3, 4]');
  });
});

describe('padLength', () => {
  it('rounds up to a power of 2', () => {
    expect([0, 1, 2, 3, 4, 5, 8, 9].map(padLength)).toEqual([1, 1, 2, 4, 4, 8, 8, 16]);
  });
});

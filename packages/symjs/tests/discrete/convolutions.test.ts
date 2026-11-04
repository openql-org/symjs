// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/discrete/convolutions.ts: SymPy's sympy/discrete/tests/test_convolutions.py and
// the doctests of sympy/discrete/convolutions.py; expected values from SymPy 1.14.

import { describe, expect, it } from 'vitest';
import type { Expr } from '../../src/core/nodes';
import { Sym } from '../../src/core/nodes';
import { parseExpr } from '../../src/index';
import { convolution, convolutionFft, convolutionFwht, convolutionNtt, convolutionSubset, coveringProduct, intersectingProduct } from '../../src/discrete/index';

/** A list of expressions written with `;` separators. */
const L = (s: string): Expr[] => s.split(';').map((t) => parseExpr(t));
/** Python's printed form of a list. */
const str = (v: readonly unknown[]): string => `[${v.map(String).join(', ')}]`;

const [u, v, w, x, y, z] = [new Sym('u'), new Sym('v'), new Sym('w'), new Sym('x'), new Sym('y'), new Sym('z')];
const syms = (s: string): Expr[] => s.split(' ').map((n) => new Sym(n));

const p = 7 * 17 * 2 ** 23 + 1;
const q = 19 * 2 ** 10 + 1;

describe('convolution', () => {
  const a = L('1; 5/3; sqrt(3); 7/5');
  const b = [9, 5, 5, 4, 3, 2];
  const c = [3, 5, 3, 7, 8];
  const d = [1422, 6572, 3213, 5552];
  const e = L('-1; 5/3; 7/5');

  it('by fft', () => {
    expect(str(convolution(a, b))).toBe(str(convolutionFft(a, b)));
    expect(str(convolution(a, b, { dps: 9 }))).toBe(str(convolutionFft(a, b, { dps: 9 })));
    expect(str(convolution(a, d, { dps: 7 }))).toBe(str(convolutionFft(d, a, { dps: 7 })));
    expect(str(convolution(a, d.slice(1), { dps: 3 }))).toBe(str(convolutionFft(d.slice(1), a, { dps: 3 })));
    // Integer expressions go to the FFT (numeric with dps), JavaScript integers to the exact integer convolution
    expect(str(convolution(L('1; 2'), L('3; 4'), { dps: 3 }))).toBe('[3.0 - 7.63e-6*I, 10.0 + 2.52e-6*I, 8.0 + 7.63e-6*I]');
    expect(str(convolution([1, 2], [3, 4], { dps: 3 }))).toBe('[3, 10, 8]');
    expect(str(convolution([1, 2.5], [3, 4]))).toBe('[3.00000000000000, 11.5000000000000, 10.0000000000000]');
  });

  it('by ntt', () => {
    expect(convolution(d, b, { prime: q })).toEqual(convolutionNtt(b, d, q));
    expect(convolution(c, b, { prime: p })).toEqual(convolutionNtt(b, c, p));
    expect(convolution(d, c, { prime: p })).toEqual(convolutionNtt(c, d, p));
    expect(convolution(d, b, { prime: q })).toEqual([12798n, 7887n, 10516n, 7296n, 16008n, 4801n, 6077n, 3625n, 11104n]);
    expect(() => convolution(b, d, { dps: 5, prime: q })).toThrow(TypeError);
    expect(() => convolution(b, d, { dps: 6, prime: q })).toThrow('Ambiguity in determining the type of convolution');
  });

  it('by fwht', () => {
    expect(str(convolution(a, b, { dyadic: true }))).toBe(str(convolutionFwht(a, b)));
    expect(str(convolution(a, b, { dyadic: true }))).toBe('[5*sqrt(3) + 344/15, 4*sqrt(3) + 27, 9*sqrt(3) + 56/3, 5*sqrt(3) + 374/15, 19/3, 7, 14/5 + 3*sqrt(3), 2*sqrt(3) + 21/5]');
    expect(str(convolution(a, b, { dyadic: false }))).toBe(str(convolution(a, b)));
    expect(() => convolution(b, d, { dps: 2, dyadic: true })).toThrow(TypeError);
    expect(() => convolution(b, d, { prime: p, dyadic: true })).toThrow(TypeError);
    expect(() => convolution(a, b, { dps: 2, dyadic: true })).toThrow(TypeError);
    expect(() => convolution(b, c, { prime: p, dyadic: true })).toThrow(TypeError);
  });

  it('subset', () => {
    const s = str(convolution(a, b, { subset: true }));
    expect(s).toBe('[9, 20, 5 + 9*sqrt(3), 5*sqrt(3) + 374/15, 3, 7, 3*sqrt(3), 2*sqrt(3) + 21/5]');
    expect(str(convolutionSubset(a, b))).toBe(s);
    expect(str(convolution(a, b, { subset: true, dyadic: false }))).toBe(s);
    expect(str(convolution(a, b, { subset: false }))).toBe(str(convolution(a, b)));
    expect(() => convolution(a, b, { subset: true, dyadic: true })).toThrow(TypeError);
    expect(() => convolution(c, d, { subset: true, dps: 6 })).toThrow(TypeError);
    expect(() => convolution(a, c, { subset: true, prime: q })).toThrow(TypeError);
  });

  it('of integers and rationals', () => {
    expect(str(convolution([0], [0]))).toBe('[0]');
    expect(str(convolution(b, c))).toBe('[27, 60, 67, 115, 151, 108, 87, 59, 38, 16]');
    expect(str(convolution(L('1/2'), L('1/2')))).toBe('[1/4]');
    expect(str(convolution(b, e))).toBe('[-9, 10, 239/15, 34/3, 32/3, 43/5, 113/15, 14/5]');
    expect(str(convolution([10n, -5, 1, 3], [-5, 6, 7]))).toBe('[-50, 85, 35, -44, 25, 21]');
    // like SymPy: the integer convolution (JavaScript integers and non-integer Rationals) ends at
    // the last nonzero term and fails on an empty list; Integer expressions go to the FFT
    expect(str(convolution([1, 0], [1, 0]))).toBe('[1]');
    expect(str(convolution([1, 0], [1, 0], { cycle: 3 }))).toBe('[1, 0, 0]');
    expect(str(convolution([1, 0], [parseExpr('1/2'), 0]))).toBe('[1/2]');
    expect(str(convolution([0, 0], [1]))).toBe('[0]');
    expect(str(convolution([1, -1], [1, 1]))).toBe('[1, 0, -1]');
    expect(str(convolution(L('1; 0'), [1, 0]))).toBe('[1, 0, 0]');
    expect(() => convolution([], [])).toThrow(new RangeError('max() iterable argument is empty'));
    expect(() => convolution([1], [])).toThrow(new RangeError('max() iterable argument is empty'));
    expect(() => convolution(L('1/2'), [])).toThrow(new RangeError('max() iterable argument is empty'));
    expect(convolution([], L('1'))).toEqual([]);
    expect(() => convolution([1, 2], [3, 4], { cycle: 1.5 })).toThrow(new RangeError('1.5 is not an integer'));
  });

  it('doctests', () => {
    expect(str(convolution(L('1 + 2*I; 4 + 3*I'), L('5/4; 6'), { dps: 3 }))).toBe('[1.25 + 2.5*I, 11.0 + 15.8*I, 24.0 + 18.0*I]');
    expect(str(convolution([1, 2, 3], [4, 5, 6], { cycle: 3 }))).toBe('[31, 31, 28]');
    expect(convolution([111, 777], [888, 444], { prime: q })).toEqual([1283n, 19351n, 14219n]);
    expect(convolution([111, 777], [888, 444], { prime: q, cycle: 2 })).toEqual([15502n, 19351n]);
    expect(str(convolution([u, v], [x, y, z], { dyadic: true }))).toBe('[u*x + v*y, u*y + v*x, u*z, v*z]');
    expect(str(convolution([u, v], [x, y, z], { dyadic: true, cycle: 2 }))).toBe('[u*x + u*z + v*y, u*y + v*x + v*z]');
    expect(str(convolution([u, v, w], [x, y, z], { subset: true }))).toBe('[u*x, u*y + v*x, u*z + w*x, v*z + w*y]');
    expect(str(convolution([u, v, w], [x, y, z], { subset: true, cycle: 3 }))).toBe('[u*x + v*z + w*y, u*y + v*x, u*z + w*x]');
  });
});

describe('cyclic convolution', () => {
  it('by fft', () => {
    const lin = str(convolution([1, 2, 3], [4, 5, 6]));
    expect(str(convolution([1, 2, 3], [4, 5, 6], { cycle: 0 }))).toBe(lin);
    expect(str(convolution([1, 2, 3], [4, 5, 6], { cycle: 5 }))).toBe(lin);
    expect(str(convolution([1, 2, 3], [4, 5, 6], { cycle: 3 }))).toBe('[31, 31, 28]');

    const a = L('1/3; 7/3; 5/9; 2/7; 5/8');
    const b = L('3/5; 4/7; 7/8; 8/9');
    expect(str(convolution(a, b, { cycle: 0 }))).toBe(str(convolution(a, b, { cycle: a.length + b.length - 1 })));
    expect(str(convolution(a, b, { cycle: 4 }))).toBe('[87277/26460, 30521/11340, 11125/4032, 3653/1080]');
    expect(str(convolution(a, b, { cycle: 6 }))).toBe('[20177/20160, 676/315, 47/24, 3053/1080, 16397/5292, 2497/2268]');
    expect(str(convolution(a, b, { cycle: 9 }))).toBe(str([...convolution(a, b, { cycle: 0 }), 0]));
    expect(() => convolution([1, 2, 3], [4, 5, 6], { cycle: -1 })).toThrow(RangeError);
  });

  it('by ntt', () => {
    const a = [2313, 5323532, parseExpr('3232'), 42142, 42242421];
    const b = [parseExpr('33456'), 56757, 45754, 432423];
    const lin = convolution(a, b, { prime: q });
    expect(convolution(a, b, { prime: q, cycle: 0 })).toEqual(lin);
    expect(convolution(a, b, { prime: q, cycle: 8 })).toEqual(lin);
    expect(convolution(a, b, { prime: q, cycle: 5 })).toEqual([96n, 17146n, 2664n, 15534n, 3517n]);
    expect(convolution(a, b, { prime: q, cycle: 7 })).toEqual([4643n, 3458n, 1260n, 15534n, 3517n, 16314n, 13688n]);
    expect(convolution(a, b, { prime: q, cycle: 9 })).toEqual([...lin, 0n]);
  });

  it('by fwht and subset', () => {
    const a = [2313, 5323532, parseExpr('3232'), 42142, 42242421];
    const b = [parseExpr('33456'), 56757, 45754, 432423];
    const c = [u, v, w, x, y];
    const d = syms('p q r s t');
    expect(str(convolution(a, b, { dyadic: true, cycle: 3 }))).toBe('[2499522285783, 19861417974796, 4702176579021]');
    expect(str(convolution(a, b, { dyadic: true, cycle: 5 }))).toBe('[2718149225143, 2114320852171, 20571217906407, 246166418903, 1413262436976]');
    expect(str(convolution(c, d, { dyadic: true, cycle: 4 }))).toBe(
      '[p*u + p*y + q*v + r*w + s*x + t*u + t*y, p*v + q*u + q*y + r*x + s*w + t*v, p*w + q*x + r*u + r*y + s*v + t*w, p*x + q*w + r*v + s*u + s*y + t*x]',
    );
    expect(str(convolution(c, d, { dyadic: true, cycle: 6 }))).toBe(
      '[p*u + q*v + r*w + r*y + s*x + t*w + t*y, p*v + q*u + r*x + s*w + s*y + t*x, p*w + q*x + r*u + s*v, p*x + q*w + r*v + s*u, p*y + t*u, q*y + t*v]',
    );

    expect(str(convolution(a, b, { subset: true, cycle: 7 }))).toBe(
      '[18266671799811, 178235365533, 213958794, 246166418903, 1413262436976, 2397553088697, 1932759730434]',
    );
    expect(str(convolution(a.slice(1), b, { subset: true, cycle: 4 }))).toBe('[178104086592, 302255835516, 244982785880, 3717819845434]');
    expect(str(convolution(a, b.slice(0, -1), { subset: true, cycle: 6 }))).toBe(
      '[1932837114162, 178235365533, 213958794, 245166224504, 1413262436976, 2397553088697]',
    );
    expect(str(convolution(c, d, { subset: true, cycle: 3 }))).toBe(
      '[p*u + p*x + q*w + r*v + r*y + s*u + t*w, p*v + p*y + q*u + s*y + t*u + t*x, p*w + q*y + r*u + t*v]',
    );
    expect(str(convolution(c, d, { subset: true, cycle: 5 }))).toBe('[p*u + q*y + t*v, p*v + q*u + r*y + t*w, p*w + r*u + s*y + t*x, p*x + q*w + r*v + s*u, p*y + t*u]');
  });
});

describe('convolutionFft', () => {
  it('convolves', () => {
    for (const s of [[], [1]]) for (const dps of [undefined, 3]) expect(convolutionFft([], s, { dps })).toEqual([]);
    expect(str(convolutionFft([1, 2, 3], [4, 5, 6]))).toBe('[4, 13, 28, 27, 18]');
    expect(str(convolutionFft([1], [5, 6, 7]))).toBe('[5, 6, 7]');
    expect(str(convolutionFft([1, 3], [5, 6, 7]))).toBe('[5, 21, 25, 21]');
    expect(str(convolutionFft(L('1 + 2*I'), L('2 + 3*I')))).toBe('[-4 + 7*I]');
    expect(str(convolutionFft(L('1 + 2*I; 3 + 4*I; 5 + 3*I/5'), L('2/5 + 4*I/7')))).toBe('[-26/35 + 48*I/35, -38/35 + 116*I/35, 58/35 + 542*I/175]');
    expect(str(convolutionFft(L('3/4; 5/6'), L('7/8; 1/3; 2/5')))).toBe('[21/32, 47/48, 26/45, 1/3]');
    expect(str(convolutionFft(L('1/9; 2/3; 3/5'), L('2/5; 3/7; 4/9')))).toBe('[2/45, 11/35, 8152/14175, 523/945, 4/15]');
    expect(str(convolutionFft(L('pi; E; sqrt(2)'), L('sqrt(3); 1/pi; 1/E')))).toBe('[sqrt(3)*pi, 1 + sqrt(3)*E, E/pi + pi*exp(-1) + sqrt(6), sqrt(2)/pi + 1, sqrt(2)*exp(-1)]');
    expect(str(convolutionFft([2321, 33123], [5321, 6321, 71323]))).toBe('[12350041, 190918524, 374911166, 2362431729]');
    expect(str(convolutionFft([312313, 31278232], [32139631, 319631]))).toBe('[10037624576503, 1005370659728895, 9997492572392]');
    // @ts-expect-error: not sequences
    expect(() => convolutionFft(x, y)).toThrow(TypeError);
    expect(() => convolutionFft([x, y], [y, x])).toThrow(RangeError);
  });

  it('doctests', () => {
    expect(str(convolutionFft([2, 3], [4, 5]))).toBe('[8, 22, 15]');
    expect(str(convolutionFft([2, 5], [6, 7, 3]))).toBe('[12, 44, 41, 15]');
    expect(str(convolutionFft(L('1 + 2*I; 4 + 3*I'), L('5/4; 6')))).toBe('[5/4 + 5*I/2, 11 + 63*I/4, 24 + 18*I]');
  });
});

describe('convolutionNtt', () => {
  const r = 2 * 500000003 + 1; // only for sequences of length 1 or 2

  it('convolves modulo a prime', () => {
    for (const s of [[], [1]]) for (const m of [p, q, r]) expect(convolutionNtt([], s, m)).toEqual([]);
    expect(convolutionNtt([2], [3], r)).toEqual([6n]);
    expect(convolutionNtt([2, 3], [4], r)).toEqual([8n, 12n]);
    expect(convolutionNtt([32121, 42144, 4214, 4241], [32132, 3232, 87242], p)).toEqual([33867619n, 459741727n, 79180879n, 831885249n, 381344700n, 369993322n]);
    expect(convolutionNtt([121913, 3171831, 31888131, 12], [17882, 21292, 29921, 312], q)).toEqual([8158n, 3065n, 3682n, 7090n, 1239n, 2232n, 3744n]);
    expect(convolutionNtt([12, 19, 21, 98, 67], [2, 6, 7, 8, 9], p)).toEqual(convolutionNtt([12, 19, 21, 98, 67], [2, 6, 7, 8, 9], q));
    expect(convolutionNtt([12, 19, 21, 98, 67], [21, 76, 17, 78, 69], p)).toEqual(convolutionNtt([12, 19, 21, 98, 67], [21, 76, 17, 78, 69], q));
    expect(() => convolutionNtt([2, 3], [4, 5], r)).toThrow(RangeError);
    // SymPy's as_int raises ValueError (RangeError in symjs)
    expect(() => convolutionNtt([x, y], [y, x], q)).toThrow(new RangeError('x is not an integer'));
    // @ts-expect-error: not sequences
    expect(() => convolutionNtt(x, y, p)).toThrow(TypeError);
  });

  it('doctests', () => {
    expect(convolutionNtt([2, 3], [4, 5], q)).toEqual([8n, 22n, 15n]);
    expect(convolutionNtt([2, 5], [6, 7, 3], q)).toEqual([12n, 44n, 41n, 15n]);
    expect(convolutionNtt([333, 555], [222, 666], q)).toEqual([15555n, 14219n, 19404n]);
  });
});

describe('convolutionFwht', () => {
  it('convolves', () => {
    expect(convolutionFwht([], [])).toEqual([]);
    expect(convolutionFwht([], [1])).toEqual([]);
    expect(str(convolutionFwht([1, 2, 3], [4, 5, 6]))).toBe('[32, 13, 18, 27]');
    expect(str(convolutionFwht(L('5/7; 6/8; 7/3'), L('2; 4; 6/7')))).toBe('[45/7, 61/14, 776/147, 419/42]');

    const a = L('1; 5/3; sqrt(3); 7/5; 4 + 5*I');
    const b = [94, 51, 53, 45, 31, 27, 13];
    const c = L('3 + 4*I; 5 + 7*I; 3; 7/6; 8');
    expect(str(convolutionFwht(a, b))).toBe(
      '[53*sqrt(3) + 366 + 155*I, 45*sqrt(3) + 5848/15 + 135*I, 94*sqrt(3) + 1257/5 + 65*I, 51*sqrt(3) + 3974/15, 13*sqrt(3) + 452 + 470*I, 4513/15 + 255*I, 31*sqrt(3) + 1314/5 + 265*I, 27*sqrt(3) + 3676/15 + 225*I]',
    );
    expect(str(convolutionFwht(b, c))).toBe(
      '[1993/2 + 733*I, 6215/6 + 862*I, 1659/2 + 527*I, 1988/3 + 551*I, 1019 + 313*I, 3955/6 + 325*I, 1175/2 + 52*I, 3253/6 + 91*I]',
    );
    expect(str(convolutionFwht(a.slice(3), c))).toBe('[-54/5 + 293*I/5, -1 + 204*I/5, 133/15 + 35*I/6, 409/30 + 15*I, 56/5, 32 + 40*I, 0, 0]');

    expect(str(convolutionFwht([u, v], [x, y]))).toBe('[u*x + v*y, u*y + v*x]');
    expect(str(convolutionFwht([u, v, w], [x, y]))).toBe('[u*x + v*y, u*y + v*x, w*x, w*y]');
    expect(str(convolutionFwht([u, v, w], [x, y, z]))).toBe('[u*x + v*y + w*z, u*y + v*x, u*z + w*x, v*z + w*y]');
    // @ts-expect-error: not sequences
    expect(() => convolutionFwht(x, y)).toThrow(TypeError);
    // @ts-expect-error: not sequences
    expect(() => convolutionFwht(x.mul(y), u.add(v))).toThrow(TypeError);
  });

  it('doctests', () => {
    expect(str(convolutionFwht([2, 3], [4, 5]))).toBe('[23, 22]');
    expect(str(convolutionFwht(L('2; 5 + 4*I; 7'), L('6*I; 7; 3 + 4*I')))).toBe('[56 + 68*I, -10 + 30*I, 6 + 50*I, 48 + 32*I]');
    expect(str(convolutionFwht(L('33/7; 55/6; 7/4'), L('2/3; 5')))).toBe('[2057/42, 1870/63, 7/6, 35/4]');
  });
});

describe('convolutionSubset', () => {
  it('convolves', () => {
    expect(convolutionSubset([], [])).toEqual([]);
    expect(convolutionSubset([], L('1/3'))).toEqual([]);
    expect(str(convolutionSubset(L('6 + 3*I/7'), L('2/3')))).toBe('[4 + 2*I/7]');

    const a = L('1; 5/3; sqrt(3); 4 + 5*I');
    const b = [64, 71, 55, 47, 33, 29, 15];
    const c = L('3 + 2*I/3; 5 + 7*I; 7; 7/5; 9');
    expect(str(convolutionSubset(a, b))).toBe('[64, 533/3, 55 + 64*sqrt(3), 71*sqrt(3) + 1184/3 + 320*I, 33, 84, 15 + 33*sqrt(3), 29*sqrt(3) + 157 + 165*I]');
    expect(str(convolutionSubset(b, c))).toBe('[192 + 128*I/3, 533 + 1486*I/3, 613 + 110*I/3, 5013/5 + 1249*I/3, 675 + 22*I, 891 + 751*I/3, 771 + 10*I, 3736/5 + 105*I]');
    expect(str(convolutionSubset(a, c))).toBe(str(convolutionSubset(c, a)));
    expect(str(convolutionSubset(a.slice(0, 2), b))).toBe('[64, 533/3, 55, 416/3, 33, 84, 15, 25]');
    expect(str(convolutionSubset(a.slice(0, 2), c))).toBe('[3 + 2*I/3, 10 + 73*I/9, 7, 196/15, 9, 15, 0, 0]');

    expect(str(convolutionSubset([u, v, w], [x, y]))).toBe('[u*x, u*y + v*x, w*x, w*y]');
    expect(str(convolutionSubset([u, v, w, x], [y, z]))).toBe('[u*y, u*z + v*y, w*y, w*z + x*y]');
    expect(str(convolutionSubset([u, v], [x, y, z]))).toBe(str(convolutionSubset([x, y, z], [u, v])));
    // @ts-expect-error: not sequences
    expect(() => convolutionSubset(x, z)).toThrow(TypeError);
    // @ts-expect-error: not sequences
    expect(() => convolutionSubset(parseExpr('7/3'), u)).toThrow(TypeError);
  });

  it('doctests', () => {
    expect(str(convolutionSubset([u, v], [x, y]))).toBe('[u*x, u*y + v*x]');
    expect(str(convolutionSubset([u, v, x], [y, z]))).toBe('[u*y, u*z + v*y, x*y, x*z]');
    expect(str(convolutionSubset(L('1; 2/3'), [3, 4]))).toBe('[3, 6]');
    expect(str(convolutionSubset(L('1; 3; 5/7'), [7]))).toBe('[7, 21, 5, 0]');
  });
});

describe('coveringProduct', () => {
  it('multiplies', () => {
    expect(coveringProduct([], [])).toEqual([]);
    expect(coveringProduct([], L('1/3'))).toEqual([]);
    expect(str(coveringProduct(L('6 + 3*I/7'), L('2/3')))).toBe('[4 + 2*I/7]');

    const a = L('1; 5/8; sqrt(7); 4 + 9*I');
    const b = [66, 81, 95, 49, 37, 89, 17];
    const c = L('3 + 2*I/3; 51 + 72*I; 7; 7/15; 91');
    expect(str(coveringProduct(a, b))).toBe('[66, 1383/8, 95 + 161*sqrt(7), 130*sqrt(7) + 1303 + 2619*I, 37, 671/4, 17 + 54*sqrt(7), 89*sqrt(7) + 4661/8 + 1287*I]');
    expect(str(coveringProduct(b, c))).toBe('[198 + 44*I, 7740 + 10638*I, 1412 + 190*I/3, 42684/5 + 31202*I/3, 9484 + 74*I/3, 22163 + 27394*I/3, 10621 + 34*I/3, 90236/15 + 1224*I]');
    expect(str(coveringProduct(a, c))).toBe(str(coveringProduct(c, a)));
    expect(str(coveringProduct(b, c.slice(0, -1)))).toBe('[198 + 44*I, 7740 + 10638*I, 1412 + 190*I/3, 42684/5 + 31202*I/3, 111 + 74*I/3, 6693 + 27394*I/3, 429 + 34*I/3, 23351/15 + 1224*I]');
    expect(str(coveringProduct(a, c.slice(0, -1)))).toBe('[3 + 2*I/3, 339/4 + 1409*I/12, 7 + 10*sqrt(7) + 2*sqrt(7)*I/3, -403 + 772*sqrt(7)/15 + 72*sqrt(7)*I + 12658*I/15]');

    expect(str(coveringProduct([u, v, w], [x, y]))).toBe('[u*x, u*y + v*x + v*y, w*x, w*y]');
    expect(str(coveringProduct([u, v, w, x], [y, z]))).toBe('[u*y, u*z + v*y + v*z, w*y, w*z + x*y + x*z]');
    expect(str(coveringProduct([u, v], [x, y, z]))).toBe(str(coveringProduct([x, y, z], [u, v])));
    // @ts-expect-error: not sequences
    expect(() => coveringProduct(x, z)).toThrow(TypeError);
    // @ts-expect-error: not sequences
    expect(() => coveringProduct(parseExpr('7/3'), u)).toThrow(TypeError);
  });

  it('doctests', () => {
    expect(str(coveringProduct([u, v], [x, y]))).toBe('[u*x, u*y + v*x + v*y]');
    expect(str(coveringProduct([u, v, x], [y, z]))).toBe('[u*y, u*z + v*y + v*z, x*y, x*z]');
    expect(str(coveringProduct(L('1; 2/3'), L('3; 4 + 5*I')))).toBe('[3, 26/3 + 25*I/3]');
    expect(str(coveringProduct(L('1; 3; 5/7'), [7, 8]))).toBe('[7, 53, 5, 40/7]');
  });
});

describe('intersectingProduct', () => {
  it('multiplies', () => {
    expect(intersectingProduct([], [])).toEqual([]);
    expect(intersectingProduct([], L('1/3'))).toEqual([]);
    expect(str(intersectingProduct(L('6 + 3*I/7'), L('2/3')))).toBe('[4 + 2*I/7]');

    const a = L('1; sqrt(5); 3/8 + 5*I; 4 + 7*I');
    const b = [67, 51, 65, 48, 36, 79, 27];
    const c = L('3 + 2*I/5; 5 + 9*I; 7; 7/19; 13');
    expect(str(intersectingProduct(a, b))).toBe('[195*sqrt(5) + 6979/8 + 1886*I, 178*sqrt(5) + 520 + 910*I, 841/2 + 1344*I, 192 + 336*I, 0, 0, 0, 0]');
    expect(str(intersectingProduct(b, c))).toBe('[128553/19 + 9521*I/5, 17820/19 + 1602*I, 19264/19, 336/19, 1846, 0, 0, 0]');
    expect(str(intersectingProduct(a, c))).toBe(str(intersectingProduct(c, a)));
    expect(str(intersectingProduct(b.slice(1), c.slice(0, -1)))).toBe('[64788/19 + 8622*I/5, 12804/19 + 1152*I, 11508/19, 252/19, 0, 0, 0, 0]');
    expect(str(intersectingProduct(a, c.slice(0, -2)))).toBe('[-99/5 + 10*sqrt(5) + 2*sqrt(5)*I/5 + 3021*I/40, -43 + 5*sqrt(5) + 9*sqrt(5)*I + 71*I, 245/8 + 84*I, 0]');

    expect(str(intersectingProduct([u, v, w], [x, y]))).toBe('[u*x + u*y + v*x + w*x + w*y, v*y, 0, 0]');
    expect(str(intersectingProduct([u, v, w, x], [y, z]))).toBe('[u*y + u*z + v*y + w*y + w*z + x*y, v*z + x*z, 0, 0]');
    expect(str(intersectingProduct([u, v], [x, y, z]))).toBe(str(intersectingProduct([x, y, z], [u, v])));
    // @ts-expect-error: not sequences
    expect(() => intersectingProduct(x, z)).toThrow(TypeError);
    // @ts-expect-error: not sequences
    expect(() => intersectingProduct(u, parseExpr('8/3'))).toThrow(TypeError);
  });

  it('doctests', () => {
    expect(str(intersectingProduct([u, v], [x, y]))).toBe('[u*x + u*y + v*x, v*y]');
    expect(str(intersectingProduct([u, v, x], [y, z]))).toBe('[u*y + u*z + v*y + x*y + x*z, v*z, 0, 0]');
    expect(str(intersectingProduct(L('1; 2/3'), L('3; 4 + 5*I')))).toBe('[9 + 5*I, 8/3 + 10*I/3]');
    expect(str(intersectingProduct(L('1; 3; 5/7'), [7, 8]))).toBe('[327/7, 24, 0, 0]');
  });
});

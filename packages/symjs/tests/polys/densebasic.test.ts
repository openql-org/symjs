// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Expected values from SymPy 1.14.0 (sympy.polys.densebasic doctests and tests/test_densebasic.py).

import { describe, expect, it } from 'vitest';
import { Rational, Sym, add, sstr } from '../../src/index';
import { Float } from '../../src/core/nodes';
import { InvariantError } from '../../src/core/errors';
import { EX, QQ, ZZ } from '../../src/polys/domains';
import { PythonMPQ } from '../../src/polys/domains/pythonrational';
import { GF } from '../../src/polys/domains/finitefield';
import * as D from '../../src/polys/densebasic';

const x = new Sym('x');
const y = new Sym('y');
const show = (v: unknown): string => JSON.stringify(v, (_k, w: unknown) => (typeof w === 'bigint' ? Number(w) : w instanceof Rational || w instanceof PythonMPQ ? String(w) : w === -Infinity ? '-inf' : w));
const dict = (m: Map<number[] | number, unknown>): string => show([...m]);

describe('coefficients', () => {
  it('Python truth value and equality', () => {
    expect([[], 0, 0n, Rational.of(0n), new Float(0), null, undefined, false, new PythonMPQ(0n), GF(5).new(5)].map(D.groundIsZero)).toEqual(Array(10).fill(true));
    expect([[1], 1, 1n, x, new PythonMPQ(1n), 'a'].map(D.groundIsZero)).toEqual(Array(6).fill(false));
    expect(D.groundEquals(1, 1n)).toBe(true);
    expect(D.groundEquals(Rational.of(1n, 2n), new PythonMPQ(1n, 2n))).toBe(true);
    expect(D.groundEquals(x, x)).toBe(true);
    expect(D.groundEquals(GF(5).new(2), 7)).toBe(true);
    expect(D.groundEquals('a', 'a')).toBe(true);
  });
});

describe('leading terms and degrees', () => {
  const f = [[2, 3], [1, 2, 3]];
  it('LC, TC, ground LC/TC and LT', () => {
    expect([D.polyLC([], ZZ), D.polyLC([1, 2, 3], ZZ), D.polyTC([], ZZ), D.polyTC([1, 2, 3], ZZ)].map(String)).toEqual(['0', '1', '0', '3']);
    expect(D.dmpGroundLC([[[1], [2, 3]]], 2, ZZ)).toBe(1);
    expect(D.dmpGroundTC([[[1], [2, 3]]], 2, ZZ)).toBe(3);
    expect(show(D.dmpTrueLT([[4, 0], [2, 0]], 1, ZZ))).toBe('[[1,1],4]');
    expect(show(D.dmpTrueLT([[[]]], 2, ZZ))).toBe('[[0,0,0],"0"]');
  });
  it('degrees', () => {
    expect(D.dupDegree([])).toBe(-Infinity);
    expect(D.dupDegree([1, 2, 0, 3])).toBe(3);
    expect(D.dmpDegree([[[]]], 2)).toBe(-Infinity);
    expect(D.dmpDegree(f, 1)).toBe(1);
    expect([D.dmpDegreeIn(f, 0, 1), D.dmpDegreeIn(f, 1, 1)]).toEqual([1, 2]);
    expect(() => D.dmpDegreeIn(f, 2, 1)).toThrow(RangeError);
    expect(D.dmpDegreeList(f, 1)).toEqual([1, 2]);
  });
  it('rejects a non-integer level', () => {
    expect(() => D.dmpDegreeIn(f, Rational.of(1n, 2n) as unknown as number, 1)).toThrow(TypeError);
  });
});

describe('strip, validate, copy, convert', () => {
  it('strip and validate', () => {
    expect(D.dupStrip([0, 0, 1, 2, 3, 0])).toEqual([1, 2, 3, 0]);
    expect(D.dmpStrip([[], [0, 1, 2], [1]], 1)).toEqual([[0, 1, 2], [1]]);
    expect(D.dmpStrip([[]], 1)).toEqual([[]]);
    expect(D.dmpStrip([0, 1], 0)).toEqual([1]);
    expect(D.dmpStrip([[], []], 1)).toEqual([[]]);
    expect(D.dmpValidate([[], [0, 1, 2], [1]])).toEqual([[[1, 2], [1]], 1]);
    expect(D.dmpValidate([[[]]])).toEqual([[[[]]], 2]);
    expect(() => D.dmpValidate([[1], 2])).toThrow(RangeError);
    expect(D.dmpValidate([1n, 2n], ZZ)).toEqual([[1n, 2n], 0]);
    expect(() => D.dmpValidate([1, 2], ZZ)).toThrow(TypeError);
    expect(() => D.dmpStrip([1, [2]], 1)).toThrow(InvariantError);
  });
  it('copies and tuples', () => {
    expect(D.dupReverse([1, 2, 3, 0])).toEqual([3, 2, 1]);
    expect(D.dupCopy([1, 2, 3, 0])).toEqual([1, 2, 3, 0]);
    expect(D.dmpCopy([[1], [1, 2]], 1)).toEqual([[1], [1, 2]]);
    expect(D.dupToTuple([1, 2])).toEqual([1, 2]);
    expect(D.dmpToTuple([[1], [1, 2]], 1)).toEqual([[1], [1, 2]]);
  });
  it('normal, convert and from_sympy', () => {
    expect(D.dupNormal([0, 1, 2, 3], ZZ)).toEqual([1n, 2n, 3n]);
    expect(D.dmpNormal([[], [0, 1, 2]], 1, ZZ)).toEqual([[1n, 2n]]);
    expect(D.dupConvert([1, 2], ZZ, ZZ)).toEqual([1, 2]);
    expect(D.dupConvert([1, 2], null, QQ).map(String)).toEqual(['1', '2']);
    expect(D.dmpConvert([[1], [2]], 1, ZZ, ZZ)).toEqual([[1], [2]]);
    const R = ZZ.polyRing(x);
    expect(sstr(D.dmpConvert([[1], [2]], 1, ZZ, R).flat()[1] as Rational)).toBe('2');
    expect(D.dmpConvert([[new Map([[[0], 1]])], [new Map([[[0], 2]])]], 1, R, ZZ)).toEqual([[1n], [2n]]);
    expect(D.dupFromSympy([Rational.of(1n), Rational.of(0n)], ZZ)).toEqual([1n, 0n]);
    expect(D.dmpFromSympy([[Rational.of(1n)], []], 1, ZZ)).toEqual([[1n], []]);
  });
});

describe('coefficients by degree, zero, one, ground', () => {
  const f = [[1, 2], [3], [4, 5]];
  it('nth', () => {
    expect([D.dupNth([1, 2, 3], 0, ZZ), D.dupNth([1, 2, 3], 4, ZZ)].map(String)).toEqual(['3', '0']);
    expect(() => D.dupNth([1], -1, ZZ)).toThrow(RangeError);
    expect([D.dmpNth(f, 0, 1, ZZ), D.dmpNth(f, 4, 1, ZZ)]).toEqual([[4, 5], []]);
    expect(() => D.dmpNth(f, -1, 1, ZZ)).toThrow(RangeError);
    expect(D.dmpGroundNth([[1], [2, 3]], [0, 1], 1, ZZ)).toBe(2);
    expect(String(D.dmpGroundNth([[1], [2, 3]], [5, 1], 1, ZZ))).toBe('0');
    expect(String(D.dmpGroundNth([[]], [0, 0], 1, ZZ))).toBe('0');
    expect(() => D.dmpGroundNth(f, [-1], 1, ZZ)).toThrow(RangeError);
  });
  it('zero, one and ground', () => {
    expect([D.dmpZeroP([[[[[]]]]], 4), D.dmpZeroP([[[[[1]]]]], 4), D.dmpZeroP([[], []], 1)]).toEqual([true, false, false]);
    expect(D.dmpZero(4)).toEqual([[[[[]]]]]);
    expect(D.dmpOneP([[[1n]]], 2, ZZ)).toBe(true);
    expect(show(D.dmpOne(2, ZZ))).toBe('[[["1"]]]');
    expect([D.dmpGroundP([[[3]]], 3, 2), D.dmpGroundP([[[4]]], null, 2), D.dmpGroundP([[]], 0, 1), D.dmpGroundP([[1], [2]], 1, 1), D.dmpGroundP([[1]], 2, 1)]).toEqual([true, true, true, false, false]);
    expect(D.dmpGround(3, 5)).toEqual([[[[[[3]]]]]]);
    expect(D.dmpGround(1, -1)).toBe(1);
    expect(D.dmpGround(0, 1)).toEqual([[]]);
    expect(show(D.dmpZeros(3, -1, ZZ))).toBe('["0","0","0"]');
    expect(D.dmpZeros(3, 2, ZZ)).toEqual([[[[]]], [[[]]], [[[]]]]);
    expect(D.dmpGrounds(4, 3, 2)).toEqual([[[[4]]], [[[4]]], [[[4]]]]);
    expect(D.dmpGrounds(4, 3, -1)).toEqual([4, 4, 4]);
    expect([D.dmpNegativeP([[1], [-1]], 1, ZZ), D.dmpNegativeP([[-1], [1]], 1, ZZ), D.dmpPositiveP([[1], [-1]], 1, ZZ), D.dmpPositiveP([[-1], [1]], 1, ZZ)]).toEqual([false, true, true, false]);
  });
});

describe('dicts', () => {
  it('from and to dicts', () => {
    expect(D.dupFromDict(new Map([[[0], 7], [[2], 5], [[4], 1]]), ZZ).map(String)).toEqual(['1', '0', '5', '0', '7']);
    expect(D.dupFromDict(new Map(), ZZ)).toEqual([]);
    expect(D.dupFromDict(new Map([[1, 7]]), ZZ)).toEqual([7, Rational.of(0n)]);
    expect(D.dupFromRawDict(new Map([[0, 7], [2, 5], [4, 1]]), ZZ).map(String)).toEqual(['1', '0', '5', '0', '7']);
    expect(D.dupFromRawDict(new Map(), ZZ)).toEqual([]);
    expect(D.dmpFromDict(new Map([[[0, 0], 3], [[0, 1], 2], [[2, 1], 1]]), 1, ZZ)).toEqual([[1, Rational.of(0n)], [], [2, 3]]);
    expect(D.dmpFromDict(new Map(), 1, ZZ)).toEqual([[]]);
    expect(dict(D.dupToDict([1, 0, 5, 0, 7]))).toBe('[[[0],7],[[2],5],[[4],1]]');
    expect(dict(D.dupToDict([], ZZ, true))).toBe('[[[0],"0"]]');
    expect(dict(D.dupToRawDict([1, 0, 5, 0, 7]))).toBe('[[0,7],[2,5],[4,1]]');
    expect(dict(D.dupToRawDict([], ZZ, true))).toBe('[[0,"0"]]');
    expect(dict(D.dmpToDict([[1, 0], [], [2, 3]], 1))).toBe('[[[0,0],3],[[0,1],2],[[2,1],1]]');
    expect(dict(D.dmpToDict([[]], 1, ZZ, true))).toBe('[[[0,0],"0"]]');
    expect(dict(D.dmpToDict([[]], 1))).toBe('[]');
  });
});

describe('variables', () => {
  const f = [[[2], [1, 0]], []];
  it('swap and permute', () => {
    expect(show(D.dmpSwap(f, 0, 1, 2, ZZ))).toBe('[[[2],[]],[[1,"0"],[]]]');
    expect(show(D.dmpSwap(f, 1, 2, 2, ZZ))).toBe('[[[1],[2,"0"]],[[]]]');
    expect(D.dmpSwap(f, 1, 1, 2, ZZ)).toEqual(f);
    expect(() => D.dmpSwap(f, 0, 3, 2, ZZ)).toThrow(RangeError);
    expect(() => D.dmpSwap(f, -1, 1, 2, ZZ)).toThrow(RangeError);
    expect(show(D.dmpPermute(f, [1, 0, 2], 2, ZZ))).toBe('[[[2],[]],[[1,"0"],[]]]');
    expect(show(D.dmpPermute(f, [1, 2, 0], 2, ZZ))).toBe('[[[1],[]],[[2,"0"],[]]]');
    expect(show(D.dmpPermute(f, [1, 0], 2, ZZ))).toBe('[[[2],[]],[[1],[]]]');
  });
  it('nest and raise', () => {
    expect(D.dmpNest([[1]], 2, ZZ)).toEqual([[[[1]]]]);
    expect(D.dmpNest(1, 2, ZZ)).toEqual([[[1]]]);
    expect(D.dmpRaise([[], [1, 2]], 2, 1, ZZ)).toEqual([[[[]]], [[[1]], [[2]]]]);
    expect(D.dmpRaise([1], 0, 0, ZZ)).toEqual([1]);
    expect(D.dmpRaise([], 2, 0, ZZ)).toEqual([[[]]]);
  });
  it('deflate and inflate', () => {
    expect(D.dupDeflate([1, 0, 0, 1, 0, 0, 1], ZZ)).toEqual([3, [1, 1, 1]]);
    expect(D.dupDeflate([1], ZZ)).toEqual([1, [1]]);
    expect(D.dupDeflate([1, 1, 0], ZZ)).toEqual([1, [1, 1, 0]]);
    expect(D.dmpDeflate([[1, 0, 0, 2], [], [3, 0, 0, 4]], 1, ZZ)).toEqual([[2, 3], [[1, 2], [3, 4]]]);
    expect(D.dmpDeflate([[]], 1, ZZ)).toEqual([[1, 1], [[]]]);
    expect(D.dmpDeflate([[1, 1]], 1, ZZ)).toEqual([[1, 1], [[1, 1]]]);
    expect(D.dupMultiDeflate([[1, 0, 2, 0, 3], [4, 0, 0]], ZZ)).toEqual([2, [[1, 2, 3], [4, 0]]]);
    expect(D.dupMultiDeflate([[1, 0, 2], [3]], ZZ)).toEqual([1, [[1, 0, 2], [3]]]);
    expect(D.dupMultiDeflate([[1, 1]], ZZ)).toEqual([1, [[1, 1]]]);
    expect(show(D.dmpMultiDeflate([[[1, 0, 0, 2], [], [3, 0, 0, 4]], [[1, 0, 2], [], [3, 0, 4]]], 1, ZZ))).toBe('[[2,1],[[[1,"0","0",2],[3,"0","0",4]],[[1,"0",2],[3,"0",4]]]]');
    expect(D.dmpMultiDeflate([[1, 0, 1]], 0, ZZ)).toEqual([[2], [[1, 1]]]);
    expect(D.dmpMultiDeflate([[[1, 1]], [[]]], 1, ZZ)).toEqual([[1, 1], [[[1, 1]], [[]]]]);
    expect(show(D.dupInflate([1, 1, 1], 3, ZZ))).toBe('[1,"0","0",1,"0","0",1]');
    expect(D.dupInflate([1], 1, ZZ)).toEqual([1]);
    expect(() => D.dupInflate([1], 0, ZZ)).toThrow(RangeError);
    expect(show(D.dmpInflate([[1, 2], [3, 4]], [2, 3], 1, ZZ))).toBe('[[1,"0","0",2],[],[3,"0","0",4]]');
    expect(D.dmpInflate([[1]], [1, 1], 1, ZZ)).toEqual([[1]]);
    expect(D.dmpInflate([1, 1], [2], 0, ZZ)).toEqual([1, Rational.of(0n), 1]);
    expect(() => D.dmpInflate([[1]], [0, 2], 1, ZZ)).toThrow(RangeError);
  });
  it('exclude and include', () => {
    expect(D.dmpExclude([[[1]], [[1], [2]]], 2, ZZ)).toEqual([[2], [[1], [1, 2]], 1]);
    expect(D.dmpExclude([[1]], 1, ZZ)).toEqual([[], [[1]], 1]);
    expect(D.dmpExclude([[1, 0], [1]], 1, ZZ)).toEqual([[], [[1, 0], [1]], 1]);
    expect(D.dmpInclude([[1], [1, 2]], [2], 1, ZZ)).toEqual([[[1]], [[1], [2]]]);
    expect(D.dmpInclude([[1]], [], 1, ZZ)).toEqual([[1]]);
  });
  it('inject and eject over ZZ[x, y]', () => {
    const R = ZZ.polyRing(x, y);
    const [g, w] = D.dmpInject([1, add(x, 2)], 0, ZZ.polyRing(x));
    expect([show(g), w]).toEqual(['[[1],[1,2]]', 1]);
    expect(show(D.dmpInject([1, add(x, 2)], 0, ZZ.polyRing(x), true)[0])).toBe('[[1],[1,2]]');
    expect(D.dmpEject([[[1]], [[1], [2]]], 2, R).map((e) => sstr(e as Rational))).toEqual(['1', 'x + 2']);
    expect(D.dmpEject([[[1]], [[1], [2]]], 2, R, true).map((e) => sstr(e as Rational))).toEqual(['x + y + 2']);
  });
});

describe('terms', () => {
  it('terms gcd and list terms', () => {
    expect(D.dupTermsGcd([1, 0, 1, 0, 0], ZZ)).toEqual([2, [1, 0, 1]]);
    expect(D.dupTermsGcd([1, 1], ZZ)).toEqual([0, [1, 1]]);
    expect(D.dupTermsGcd([], ZZ)).toEqual([0, []]);
    expect(show(D.dmpTermsGcd([[1, 0], [1, 0, 0], [], []], 1, ZZ))).toBe('[[2,1],[[1],[1,"0"]]]');
    expect(D.dmpTermsGcd([[1]], 1, ZZ)).toEqual([[0, 0], [[1]]]);
    expect(D.dmpTermsGcd([[]], 1, ZZ)).toEqual([[0, 0], [[]]]);
    expect(D.dmpTermsGcd([[1], [1, 0]], 1, ZZ)).toEqual([[0, 0], [[1], [1, 0]]]);
    expect(D.dmpTermsGcd([[1, 0], [1]], 1, ZZ)).toEqual([[0, 0], [[1, 0], [1]]]);
    const f = [[1, 1], [2, 3]];
    expect(show(D.dmpListTerms(f, 1, ZZ))).toBe('[[[1,1],1],[[1,0],1],[[0,1],2],[[0,0],3]]');
    expect(show(D.dmpListTerms(f, 1, ZZ, 'grevlex'))).toBe('[[[1,1],1],[[1,0],1],[[0,1],2],[[0,0],3]]');
    expect(show(D.dmpListTerms([[]], 1, ZZ))).toBe('[[[0,0],"0"]]');
    expect(show(D.dmpListTerms([0, 1], 0, ZZ))).toBe('[[[0],1]]');
  });
  it('apply pairs', () => {
    const h = (a: unknown, b: unknown, c: unknown): unknown => Number(a) * 2 + Number(b) + Number(c);
    expect(D.dupApplyPairs([1, 2, 3], [3, 2, 1], h, [1], ZZ)).toEqual([6, 7, 8]);
    expect(D.dupApplyPairs([1, 2, 3], [1], h, [0], ZZ)).toEqual([2, 4, 7]);
    expect(D.dmpApplyPairs([[1], [2, 3]], [[3], [2, 1]], (a, b) => Number(a) + Number(b), [], 1, ZZ)).toEqual([[4], [4, 4]]);
    expect(D.dmpApplyPairs([[1]], [[3], [2, 1]], (a, b) => Number(a) + Number(b), [], 1, ZZ)).toEqual([[3], [2, 2]]);
  });
  it('slices', () => {
    expect(show(D.dupSlice([1, 2, 3, 4], 1, 3, ZZ))).toBe('[2,3,"0"]');
    expect(D.dupSlice([1, 2], 3, 5, ZZ)).toEqual([]);
    expect(D.dupSlice([1, 2, 3, 4], 0, 1, ZZ)).toEqual([4]);
    expect(show(D.dmpSlice([[1n, 2n], [3n, 4n]], 0, 1, 1, ZZ))).toBe('[[4,6]]');
    expect(show(D.dmpSliceIn([[1, 2], [3, 4]], 1, 2, 1, 1, ZZ))).toBe('[[1,2],[3,4]]');
    expect(show(D.dmpSliceIn([[1n, 2n], [3n, 4n]], 0, 1, 1, 1, ZZ))).toBe('[[3],[7]]');
    expect(show(D.dmpSliceIn([[1n, 2n], [3n, 4n]], 1, 2, 0, 1, ZZ))).toBe('[[1,2],[3,4]]');
    expect(show(D.dmpSliceIn([3n, 4n], 1, 2, 0, 0, ZZ))).toBe('[3,"0"]');
    expect(() => D.dmpSliceIn([[1]], 0, 1, 2, 1, ZZ)).toThrow(RangeError);
  });
  it('random polynomials', () => {
    const vals = [0, 0, 0.5, 0.99];
    let i = 0;
    const r = (): number => vals[i++ % vals.length] ?? 0;
    expect(D.dupRandom(2, 0, 3, ZZ, r)).toEqual([3n, 0n, 2n]);
    expect(D.dupRandom(1, 0, 1, ZZ).length).toBe(2);
    expect(D.dupRandom(1, 1, 2, EX).length).toBe(2);
  });
});

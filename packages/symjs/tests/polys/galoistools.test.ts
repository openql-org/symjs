// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { describe, expect, it } from 'vitest';
import { ExactQuotientFailed, NotInvertible } from '../../src/core/errors';
import { Rational } from '../../src/core/nodes';
import { ZZ } from '../../src/polys/domains';
import {
  gfCrt, gfCrt1, gfCrt2, gfInt, gfDegree, gfLC, gfTC, gfStrip, gfTrunc, gfNormal, gfFromDict, gfToDict, gfFromIntPoly, gfToIntPoly, gfNeg, gfAddGround, gfSubGround, gfMulGround, gfQuoGround, gfAdd, gfSub, gfMul, gfSqr, gfAddMul, gfSubMul, gfExpand, gfDiv, gfRem, gfQuo, gfExquo, gfLshift, gfRshift, gfPow, gfFrobeniusMonomialBase, gfFrobeniusMap, gfPowMod, gfGcd, gfLcm, gfCofactors, gfGcdex, gfMonic, gfDiff, gfEval, gfMultiEval, gfCompose, gfComposeMod, gfTraceMap, gfRandom, gfIrreducible, gfIrredPBenOr, gfIrredPRabin, gfIrreducibleP, gfSqfP, gfSqfPart, gfSqfList, gfQmatrix, gfQbasis, gfBerlekamp, gfDdfZassenhaus, gfEdfZassenhaus, gfDdfShoup, gfEdfShoup, gfZassenhaus, gfShoup, gfFactorSqf, gfFactor, gfValue,
} from '../../src/polys/galoistools';

/** Numbers (degrees, multiplicities, dict keys) as bigints, to compare with SymPy's integers. */
const B = (v: unknown): unknown =>
  typeof v === 'number' ? BigInt(v) : Array.isArray(v) ? v.map(B) : v instanceof Map ? new Map([...v].map(([k, x]) => [B(k), B(x)])) : v;

// expected values computed with SymPy 1.14 (sympy.polys.galoistools)
describe('galoistools', () => {
  it('agrees with SymPy', () => {
    expect(B(gfCrt([49, 76, 65], [99, 97, 95], ZZ))).toEqual(639985n);
    expect(B(gfCrt([-3, 2], [7, 11], ZZ))).toEqual(46n);
    expect(B(gfCrt1([99, 97, 95], ZZ))).toEqual([912285n, [9215n, 9405n, 9603n], [62n, 24n, 12n]]);
    expect(B(gfCrt2([49, 76, 65], [99, 97, 95], 912285, [9215, 9405, 9603], [62, 24, 12], ZZ))).toEqual(639985n);
    expect(B(gfInt(2, 7))).toEqual(2n);
    expect(B(gfInt(5, 7))).toEqual(-2n);
    expect(B(gfInt(3, 7))).toEqual(3n);
    expect(B(gfInt(4, 7))).toEqual(-3n);
    expect(B(gfDegree([1, 1, 2, 0]))).toEqual(3n);
    expect(B(gfDegree([]))).toEqual(-1n);
    expect(B(gfLC([3, 0, 1], ZZ))).toEqual(3n);
    expect(B(gfLC([], ZZ))).toEqual(0n);
    expect(B(gfTC([3, 0, 1], ZZ))).toEqual(1n);
    expect(B(gfTC([], ZZ))).toEqual(0n);
    expect(B(gfStrip([0, 0, 0, 3, 0, 1]))).toEqual([3n, 0n, 1n]);
    expect(B(gfStrip([3, 0]))).toEqual([3n, 0n]);
    expect(B(gfStrip([]))).toEqual([]);
    expect(B(gfStrip([0, 0]))).toEqual([]);
    expect(B(gfTrunc([7, -2, 3], 5))).toEqual([2n, 3n, 3n]);
    expect(B(gfNormal([5, 10, 21, -3], 5, ZZ))).toEqual([1n, 2n]);
    expect(B(gfFromDict(new Map([[10, 4], [4, 33], [0, -1]]), 5, ZZ))).toEqual([4n, 0n, 0n, 0n, 0n, 0n, 3n, 0n, 0n, 0n, 4n]);
    expect(B(gfFromDict(new Map([[[2], 3], [[0], 1]]), 5, ZZ))).toEqual([3n, 0n, 1n]);
    expect(B(gfToDict([4, 0, 0, 0, 0, 0, 3, 0, 0, 0, 4], 5))).toEqual(new Map([[0n, -1n], [4n, -2n], [10n, -1n]]));
    expect(B(gfToDict([4, 0, 0, 0, 0, 0, 3, 0, 0, 0, 4], 5, false))).toEqual(new Map([[0n, 4n], [4n, 3n], [10n, 4n]]));
    expect(B(gfFromIntPoly([7, -2, 3], 5))).toEqual([2n, 3n, 3n]);
    expect(B(gfToIntPoly([2, 3, 3], 5))).toEqual([2n, -2n, -2n]);
    expect(B(gfToIntPoly([2, 3, 3], 5, false))).toEqual([2n, 3n, 3n]);
    expect(B(gfNeg([3, 2, 1, 0], 5, ZZ))).toEqual([2n, 3n, 4n, 0n]);
    expect(B(gfAddGround([3, 2, 4], 2, 5, ZZ))).toEqual([3n, 2n, 1n]);
    expect(B(gfAddGround([], 7, 5, ZZ))).toEqual([2n]);
    expect(B(gfAddGround([], 5, 5, ZZ))).toEqual([]);
    expect(B(gfAddGround([3], 2, 5, ZZ))).toEqual([]);
    expect(B(gfAddGround([2], 3, 5, ZZ))).toEqual([]);
    expect(B(gfSubGround([3, 2, 4], 2, 5, ZZ))).toEqual([3n, 2n, 2n]);
    expect(B(gfSubGround([], 2, 5, ZZ))).toEqual([3n]);
    expect(B(gfSubGround([2], 2, 5, ZZ))).toEqual([]);
    expect(B(gfMulGround([3, 2, 4], 2, 5, ZZ))).toEqual([1n, 4n, 3n]);
    expect(B(gfMulGround([3, 2, 4], 0, 5, ZZ))).toEqual([]);
    expect(B(gfQuoGround([3, 2, 4], 2, 5, ZZ))).toEqual([4n, 1n, 2n]);
    expect(B(gfAdd([3, 2, 4], [2, 2, 2], 5, ZZ))).toEqual([4n, 1n]);
    expect(B(gfAdd([], [1, 2], 5, ZZ))).toEqual([1n, 2n]);
    expect(B(gfAdd([1, 2], [], 5, ZZ))).toEqual([1n, 2n]);
    expect(B(gfAdd([1, 2, 3], [4, 4], 5, ZZ))).toEqual([1n, 1n, 2n]);
    expect(B(gfAdd([4, 4], [1, 2, 3], 5, ZZ))).toEqual([1n, 1n, 2n]);
    expect(B(gfSub([3, 2, 4], [2, 2, 2], 5, ZZ))).toEqual([1n, 0n, 2n]);
    expect(B(gfSub([], [1, 2], 5, ZZ))).toEqual([4n, 3n]);
    expect(B(gfSub([1, 2], [], 5, ZZ))).toEqual([1n, 2n]);
    expect(B(gfSub([1, 2, 3], [4, 4], 5, ZZ))).toEqual([1n, 3n, 4n]);
    expect(B(gfSub([4, 4], [1, 2, 3], 5, ZZ))).toEqual([4n, 2n, 1n]);
    expect(B(gfSub([1, 2], [1, 2], 5, ZZ))).toEqual([]);
    expect(B(gfMul([3, 2, 4], [2, 2, 2], 5, ZZ))).toEqual([1n, 0n, 3n, 2n, 3n]);
    expect(B(gfMul([], [2, 2, 2], 5, ZZ))).toEqual([]);
    expect(B(gfSqr([3, 2, 4], 5, ZZ))).toEqual([4n, 2n, 3n, 1n, 1n]);
    expect(B(gfAddMul([3, 2, 4], [2, 2, 2], [1, 4], 5, ZZ))).toEqual([2n, 3n, 2n, 2n]);
    expect(B(gfSubMul([3, 2, 4], [2, 2, 2], [1, 4], 5, ZZ))).toEqual([3n, 3n, 2n, 1n]);
    expect(B(gfExpand([[[3, 2, 4], 1], [[2, 2], 2], [[3, 1], 3]], 5, ZZ))).toEqual([4n, 3n, 0n, 3n, 0n, 1n, 4n, 1n]);
    expect(B(gfExpand([2, [[[1, 1], 2]]], 5, ZZ))).toEqual([2n, 4n, 2n]);
    expect(B(gfDiv([1, 0, 1, 1], [1, 1, 0], 2, ZZ))).toEqual([[1n, 1n], [1n]]);
    expect(B(gfDiv([1, 1], [1, 1, 0], 2, ZZ))).toEqual([[], [1n, 1n]]);
    expect(B(gfDiv([1, 0, 3, 2, 3], [2, 2, 2], 5, ZZ))).toEqual([[3n, 2n, 4n], []]);
    expect(B(gfRem([1, 0, 1, 1], [1, 1, 0], 2, ZZ))).toEqual([1n]);
    expect(B(gfQuo([1, 0, 3, 2, 3], [2, 2, 2], 5, ZZ))).toEqual([3n, 2n, 4n]);
    expect(B(gfExquo([1, 0, 3, 2, 3], [2, 2, 2], 5, ZZ))).toEqual([3n, 2n, 4n]);
    expect(B(gfLshift([3, 2, 4], 4, ZZ))).toEqual([3n, 2n, 4n, 0n, 0n, 0n, 0n]);
    expect(B(gfLshift([], 4, ZZ))).toEqual([]);
    expect(B(gfRshift([1, 2, 3, 4, 0], 3, ZZ))).toEqual([[1n, 2n], [3n, 4n, 0n]]);
    expect(B(gfRshift([1, 2, 3], 0, ZZ))).toEqual([[1n, 2n, 3n], []]);
    expect(B(gfPow([3, 2, 4], 3, 5, ZZ))).toEqual([2n, 4n, 4n, 2n, 2n, 1n, 4n]);
    expect(B(gfPow([3, 2, 4], 0, 5, ZZ))).toEqual([1n]);
    expect(B(gfPow([3, 2, 4], 1, 5, ZZ))).toEqual([3n, 2n, 4n]);
    expect(B(gfPow([3, 2, 4], 2, 5, ZZ))).toEqual([4n, 2n, 3n, 1n, 1n]);
    expect(B(gfFrobeniusMonomialBase([1, 0, 2, 1], 5, ZZ))).toEqual([[1n], [4n, 4n, 2n], [1n, 2n]]);
    expect(B(gfFrobeniusMonomialBase([1, 0, 0, 0, 0, 1, 1], 3, ZZ))).toEqual([[1n], [1n, 0n, 0n, 0n], [2n, 2n], [2n, 2n, 0n, 0n, 0n], [1n, 2n, 1n], [1n, 2n, 1n, 0n, 0n, 0n]]);
    expect(B(gfFrobeniusMonomialBase([3], 5, ZZ))).toEqual([]);
    expect(B(gfFrobeniusMonomialBase([1, 1], 5, ZZ))).toEqual([[1n]]);
    expect(B(gfFrobeniusMap([2, 1, 0, 1], [1, 0, 2, 1], [[1], [4, 4, 2], [1, 2]], 5, ZZ))).toEqual([4n, 0n, 3n]);
    expect(B(gfFrobeniusMap([1, 0, 2, 1], [1, 0, 2, 1], [[1], [4, 4, 2], [1, 2]], 5, ZZ))).toEqual([]);
    expect(B(gfFrobeniusMap([1, 1], [1, 0, 2, 1], [[1], [4, 4, 2], [1, 2]], 5, ZZ))).toEqual([4n, 4n, 3n]);
    expect(B(gfPowMod([3, 2, 4], 3, [1, 1], 5, ZZ))).toEqual([]);
    expect(B(gfPowMod([3, 2, 4], 0, [1, 1], 5, ZZ))).toEqual([1n]);
    expect(B(gfPowMod([3, 2, 4], 1, [1, 1, 1], 5, ZZ))).toEqual([4n, 1n]);
    expect(B(gfPowMod([3, 2, 4], 2, [1, 1, 1], 5, ZZ))).toEqual([2n, 0n]);
    expect(B(gfPowMod([1, 2], 10, [1, 0, 0, 1], 7, ZZ))).toEqual([3n, 3n, 1n]);
    expect(B(gfGcd([3, 2, 4], [2, 2, 3], 5, ZZ))).toEqual([1n, 3n]);
    expect(B(gfLcm([3, 2, 4], [2, 2, 3], 5, ZZ))).toEqual([1n, 2n, 0n, 4n]);
    expect(B(gfLcm([], [2, 2, 3], 5, ZZ))).toEqual([]);
    expect(B(gfCofactors([3, 2, 4], [2, 2, 3], 5, ZZ))).toEqual([[1n, 3n], [3n, 3n], [2n, 1n]]);
    expect(B(gfCofactors([], [], 5, ZZ))).toEqual([[], [], []]);
    expect(B(gfGcdex([1, 8, 7], [1, 7, 1, 7], 11, ZZ))).toEqual([[5n, 6n], [6n], [1n, 7n]]);
    expect(B(gfGcdex([], [], 11, ZZ))).toEqual([[1n], [], []]);
    expect(B(gfGcdex([], [2, 1], 11, ZZ))).toEqual([[], [6n], [1n, 6n]]);
    expect(B(gfGcdex([3, 1], [], 11, ZZ))).toEqual([[4n], [], [1n, 4n]]);
    expect(B(gfMonic([3, 2, 4], 5, ZZ))).toEqual([3n, [1n, 4n, 3n]]);
    expect(B(gfMonic([1, 2, 4], 5, ZZ))).toEqual([1n, [1n, 2n, 4n]]);
    expect(B(gfMonic([], 5, ZZ))).toEqual([0n, []]);
    expect(B(gfDiff([3, 2, 4], 5, ZZ))).toEqual([1n, 2n]);
    expect(B(gfDiff([1, 0, 0, 0, 0, 1], 5, ZZ))).toEqual([]);
    expect(B(gfDiff([], 5, ZZ))).toEqual([]);
    expect(B(gfEval([3, 2, 4], 2, 5, ZZ))).toEqual(0n);
    expect(B(gfMultiEval([3, 2, 4], [0, 1, 2, 3, 4], 5, ZZ))).toEqual([4n, 4n, 0n, 2n, 0n]);
    expect(B(gfCompose([3, 2, 4], [2, 2, 2], 5, ZZ))).toEqual([2n, 4n, 0n, 3n, 0n]);
    expect(B(gfCompose([3, 2, 4], [2], 5, ZZ))).toEqual([]);
    expect(B(gfCompose([3, 2, 4], [], 5, ZZ))).toEqual([4n]);
    expect(B(gfCompose([], [1, 2], 5, ZZ))).toEqual([]);
    expect(B(gfComposeMod([3, 2, 4], [2, 2, 2], [4, 3], 5, ZZ))).toEqual([4n]);
    expect(B(gfComposeMod([], [2, 2, 2], [4, 3], 5, ZZ))).toEqual([]);
    expect(B(gfTraceMap([1, 2], [4, 4], [1, 1], 4, [3, 2, 4], 5, ZZ))).toEqual([[1n, 3n], [1n, 3n]]);
    expect(B(gfTraceMap([1, 2], [4, 4], [1, 1], 3, [3, 2, 4], 5, ZZ))).toEqual([[4n, 1n], [1n]]);
    expect(B(gfIrredPBenOr([1, 4, 2, 2, 3, 2, 4, 1, 4, 0, 4], 5, ZZ))).toEqual(true);
    expect(B(gfIrredPBenOr([3, 2, 4], 5, ZZ))).toEqual(false);
    expect(B(gfIrredPBenOr([1, 0, 1, 1], 2, ZZ))).toEqual(true);
    expect(B(gfIrredPBenOr([2, 1], 5, ZZ))).toEqual(true);
    expect(B(gfIrredPBenOr([1, 0, 0, 0, 0, 0, 1], 5, ZZ))).toEqual(false);
    expect(B(gfIrredPRabin([1, 4, 2, 2, 3, 2, 4, 1, 4, 0, 4], 5, ZZ))).toEqual(true);
    expect(B(gfIrredPRabin([3, 2, 4], 5, ZZ))).toEqual(false);
    expect(B(gfIrredPRabin([1, 1], 5, ZZ))).toEqual(true);
    expect(B(gfIrredPRabin([2, 0, 1], 3, ZZ))).toEqual(false);
    expect(B(gfIrreducibleP([1, 4, 2, 2, 3, 2, 4, 1, 4, 0, 4], 5, ZZ))).toEqual(true);
    expect(B(gfSqfP([3, 2, 4], 5, ZZ))).toEqual(true);
    expect(B(gfSqfP([2, 4, 4, 2, 2, 1, 4], 5, ZZ))).toEqual(false);
    expect(B(gfSqfP([], 5, ZZ))).toEqual(true);
    expect(B(gfSqfPart([1, 1, 3, 0, 1, 0, 2, 2, 1], 5, ZZ))).toEqual([1n, 4n, 3n]);
    expect(B(gfSqfList([1, 1, 3, 0, 1, 0, 2, 2, 1], 5, ZZ))).toEqual([1n, [[[1n, 4n, 3n], 4n]]]);
    expect(B(gfSqfList([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 11, ZZ))).toEqual([1n, [[[1n, 1n], 11n]]]);
    expect(B(gfSqfList([3], 5, ZZ))).toEqual([3n, []]);
    expect(B(gfSqfList([1, 0, 2, 0, 1, 0, 0, 0, 0], 3, ZZ))).toEqual([1n, [[[1n, 0n, 1n], 2n], [[1n, 0n], 4n]]]);
    expect(B(gfQmatrix([3, 2, 4], 5, ZZ))).toEqual([[1n, 0n], [3n, 4n]]);
    expect(B(gfQmatrix([1, 0, 0, 0, 1], 5, ZZ))).toEqual([[1n, 0n, 0n, 0n], [0n, 4n, 0n, 0n], [0n, 0n, 1n, 0n], [0n, 0n, 0n, 4n]]);
    expect(B(gfQbasis([[1, 0], [3, 4]], 5, ZZ))).toEqual([[1n, 0n]]);
    expect(B(gfQbasis([[1, 0, 0, 0], [0, 4, 0, 0], [0, 0, 1, 0], [0, 0, 0, 4]], 5, ZZ))).toEqual([[1n, 0n, 0n, 0n], [0n, 0n, 1n, 0n]]);
    expect(B(gfBerlekamp([1, 0, 0, 0, 1], 5, ZZ))).toEqual([[1n, 0n, 2n], [1n, 0n, 3n]]);
    expect(B(gfBerlekamp([1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], 3, ZZ))).toEqual([[1n, 1n, 1n], [1n, 2n, 1n], [1n, 0n, 2n, 0n, 0n, 0n, 1n]]);
    expect(B(gfBerlekamp([1, 2, 3, 2, 3, 0, 1], 7, ZZ))).toEqual([[1n, 4n], [1n, 0n, 1n], [1n, 5n, 3n, 2n]]);
    expect(B(gfDdfZassenhaus([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0], 11, ZZ))).toEqual([[[1n, 0n], 1n], [[1n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 1n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 1n], 7n]]);
    expect(B(gfDdfZassenhaus([1, 1, 1], 2, ZZ))).toEqual([[[1n, 1n, 1n], 2n]]);
    expect(B(gfEdfZassenhaus([1, 1, 1, 1], 1, 5, ZZ))).toEqual([[1n, 1n], [1n, 2n], [1n, 3n]]);
    expect(B(gfEdfZassenhaus([1, 1, 1], 2, 5, ZZ))).toEqual([[1n, 1n, 1n]]);
    expect(B(gfEdfZassenhaus([1, 1, 0], 1, 2, ZZ))).toEqual([[1n, 0n], [1n, 1n]]);
    expect(B(gfEdfZassenhaus([1, 1, 1, 1, 1, 1, 1], 3, 2, ZZ))).toEqual([[1n, 0n, 1n, 1n], [1n, 1n, 0n, 1n]]);
    expect(B(gfDdfShoup([1, 2, 0, 1, 0, 0, 0, 1], 3, ZZ))).toEqual([[[1n, 0n, 0n, 1n], 1n], [[1n, 1n], 2n], [[1n, 1n, 2n, 1n], 3n]]);
    expect(B(gfDdfShoup([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1], 2, ZZ))).toEqual([[[1n, 1n, 1n], 2n], [[1n, 1n, 0n, 1n, 1n, 0n, 1n, 1n, 0n, 1n], 9n]]);
    expect(B(gfEdfShoup([1, 2837, 2277], 1, 2917, ZZ))).toEqual([[1n, 852n], [1n, 1985n]]);
    expect(B(gfEdfShoup([1, 1, 1], 2, 5, ZZ))).toEqual([[1n, 1n, 1n]]);
    expect(B(gfEdfShoup([1], 1, 5, ZZ))).toEqual([]);
    expect(B(gfEdfShoup([1, 1, 1, 1, 1, 1, 1], 3, 2, ZZ))).toEqual([[1n, 0n, 1n, 1n], [1n, 1n, 0n, 1n]]);
    expect(B(gfEdfShoup([1, 1, 0], 1, 2, ZZ))).toEqual([[1n, 0n], [1n, 1n]]);
    expect(B(gfZassenhaus([1, 4, 3], 5, ZZ))).toEqual([[1n, 1n], [1n, 3n]]);
    expect(B(gfShoup([1, 4, 3], 5, ZZ))).toEqual([[1n, 1n], [1n, 3n]]);
    expect(B(gfZassenhaus([1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], 3, ZZ))).toEqual([[1n, 1n], [1n, 2n], [1n, 0n, 2n], [1n, 0n, 2n, 0n, 0n, 0n, 1n]]);
    expect(B(gfShoup([1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1], 3, ZZ))).toEqual([[1n, 1n], [1n, 1n], [1n, 2n], [1n, 2n], [1n, 0n, 2n, 0n, 0n, 0n, 1n]]);
    expect(B(gfFactorSqf([3, 2, 4], 5, ZZ))).toEqual([3n, [[1n, 1n], [1n, 3n]]]);
    expect(B(gfFactorSqf([3], 5, ZZ))).toEqual([3n, []]);
    expect(B(gfFactorSqf([1, 4, 3], 5, ZZ, 'berlekamp'))).toEqual([1n, [[1n, 1n], [1n, 3n]]]);
    expect(B(gfFactorSqf([1, 4, 3], 5, ZZ, 'shoup'))).toEqual([1n, [[1n, 1n], [1n, 3n]]]);
    expect(B(gfFactor([5, 2, 7, 2], 11, ZZ))).toEqual([5n, [[[1n, 2n], 1n], [[1n, 8n], 2n]]]);
    expect(B(gfFactor([5], 11, ZZ))).toEqual([5n, []]);
    expect(B(gfFactor([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], 11, ZZ))).toEqual([1n, [[[1n, 1n], 11n]]]);
    expect(B(gfFactor([1, 1, 3, 0, 1, 0, 2, 2, 1], 5, ZZ))).toEqual([1n, [[[1n, 1n], 4n], [[1n, 3n], 4n]]]);
    expect(B(gfValue([1, 7, 2, 4], 11))).toEqual(2204n);
  });

  it('covers the remaining algorithm paths', () => {
    // (x + 1)**5*(x + 2) modulo 5: a p-th power besides a square-free part
    expect(B(gfSqfList([1, 2, 0, 0, 0, 1, 2], 5, ZZ))).toEqual([1n, [[[1n, 2n], 1n], [[1n, 1n], 5n]]]);
    expect(gfEdfZassenhaus([1, 0, 0, 0, 1], 2, 5, ZZ)).toEqual([[1n, 0n, 2n], [1n, 0n, 3n]]);
    expect(gfEdfShoup([1, 0, 0, 0, 1], 2, 5, ZZ)).toEqual([[1n, 0n, 2n], [1n, 0n, 3n]]);
    expect(gfBerlekamp([1, 0, 2], 5, ZZ)).toEqual([[1n, 0n, 2n]]);
    expect(B(gfDdfShoup([1, 0, 0, 1, 0, 1], 2, ZZ))).toEqual([[[1n, 0n, 0n, 1n, 0n, 1n], 5n]]);
  });

  it('accepts integers as Rational expressions and bigints', () => {
    expect(B(gfAdd([Rational.of(3n), 2n], [1], Rational.of(5n)))).toEqual([3n, 3n]);
    expect(gfInt(3n, 7n)).toBe(3n);
  });

  it('throws like SymPy', () => {
    expect(() => gfDiv([1, 2], [], 5, ZZ)).toThrow(RangeError);
    expect(() => gfExquo([1, 0, 1], [1, 1], 5, ZZ)).toThrow(ExactQuotientFailed);
    expect(() => gfQuoGround([1, 1], 2, 4, ZZ)).toThrow(NotInvertible);
    expect(() => gfSqfList([1, 0, 1], 5, ZZ, { all: true })).toThrow(RangeError);
    expect(B(gfSqfList([1, 0, 1], 5, ZZ, { all: false }))).toEqual([1n, [[[1n, 0n, 1n], 1n]]]);
  });

  it('draws random polynomials', () => {
    const f = gfRandom(4, 5, ZZ);
    expect(f).toHaveLength(5);
    expect(f[0]).toBe(1n);
    expect(f.every((c) => c >= 0n && c < 5n)).toBe(true);
    expect(gfRandom(2, 7)).toHaveLength(3);
    // x**2 (reducible) first, then x**2 + 2 (irreducible modulo 5)
    const seq = [0n, 0n, 0n, 2n];
    let i = 0;
    expect(B(gfIrreducible(2, 5, ZZ, () => seq[i++] ?? 0n))).toEqual([1n, 0n, 2n]);
    const g = gfIrreducible(3, 2);
    expect(gfIrreducibleP(g, 2)).toBe(true);
  });

  it('uses the default domain', () => {
    expect(gfLC([3, 1])).toBe(3n);
    expect(gfTC([3, 1])).toBe(1n);
    expect(B(gfNormal([6, 1], 5))).toEqual([1n, 1n]);
    expect(gfCrt([1, 2], [3, 5])).toBe(7n);
    expect(B(gfCrt1([3, 5]))).toEqual([15n, [5n, 3n], [2n, 2n]]);
    expect(gfCrt2([1, 2], [3, 5], 15, [5, 3], [2, 2])).toBe(7n);
    expect(B(gfFromDict(new Map([[1n, 1]]), 5))).toEqual([1n, 0n]);
  });
});

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { describe, expect, it } from 'vitest';
import * as F from '../src/numeric/mpf';
import * as M from '../src/numeric/mpfun';

const P = F.dpsToPrec(50);
const s = (v: F.Mpf) => F.toStr(v, 50);

describe('mpf arbitrary precision (values from mpmath, dps=50)', () => {
  it('constants', () => {
    expect(s(M.mpPi(P))).toBe('3.1415926535897932384626433832795028841971693993751');
    expect(s(M.mpE(P))).toBe('2.7182818284590452353602874713526624977572470937');
    expect(s(M.mpEuler(P))).toBe('0.57721566490153286060651209008240243104215933593992');
    expect(s(M.mpCatalan(P))).toBe('0.91596559417721901505460351493238411077414937428167');
    expect(s(M.mpLn2(P))).toBe('0.69314718055994530941723212145817656807550013436025');
  });
  it('functions', () => {
    expect(s(M.exp(F.fromInt(10n), P))).toBe('22026.465794806716516957900645284244366353512618557');
    expect(s(M.log(F.fromInt(3n), P))).toBe('1.0986122886681096913952452369225257046474905578227');
    expect(s(M.sin(F.fromInt(100n), P))).toBe('-0.50636564110975879365655761045978543206503272129066');
    expect(s(M.cos(F.fromInt(1n), P))).toBe('0.54030230586813971740093660744297660373231042061792');
    expect(s(M.atan(F.fromInt(3n), P))).toBe('1.2490457723982544258299170772810901230778294041299');
    expect(s(F.sqrt(F.fromInt(2n), P))).toBe('1.4142135623730950488016887242096980785696718753769');
  });
  it('to_str', () => {
    expect(F.floatToString(F.fromNumber(3.5), 53, false)).toBe('3.50000000000000');
    expect(F.floatToString(F.fromNumber(1e20), 53, false)).toBe('1.00000000000000e+20');
    expect(F.floatToString(F.fromStr('1e-3', F.dpsToPrec(3)), F.dpsToPrec(3), false)).toBe('0.00100');
    expect(F.floatToString(F.fromNumber(0.3), F.dpsToPrec(20), false)).toBe('0.29999999999999998890');
  });
});

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/numeric/mpquad.ts. Expected values from mpmath 1.3.0 quad at mp.dps = 15 and 50.

import { describe, expect, it } from 'vitest';
import * as F from '../../src/numeric/mpf';
import * as M from '../../src/numeric/mpfun';
import type { Mpc } from '../../src/numeric/mpfun';
import { quadZeroInf } from '../../src/numeric/mpquad';

const toStr = (z: Mpc, d: number): [string, string] => [F.toStr(z[0], d), F.toStr(z[1], d)];

describe('quadZeroInf integrates over (0, oo) like mpmath quad', () => {
  it('exp(-t) cos(t) and 1/(1 + t^2)^2', () => {
    const f1 = (x: F.Mpf, w: number): Mpc => M.cmul(M.cexp([F.neg(x), F.ZERO], w), M.ccos([x, F.ZERO], w), w);
    const f2 = (x: F.Mpf, w: number): Mpc => [F.div(F.ONE, F.powInt(F.add(F.ONE, F.mul(x, x, w), w), 2n, w), w), F.ZERO];
    // mpmath quad(lambda t: exp(-t)*cos(t), [0, inf]) = 0.5; quad(lambda t: 1/(1+t*t)**2, [0, inf]) = pi/4
    expect(toStr(quadZeroInf(f1, F.dpsToPrec(15)), 15)).toEqual(['0.5', '0.0']);
    expect(toStr(quadZeroInf(f1, F.dpsToPrec(50)), 50)).toEqual(['0.5', '0.0']);
    expect(toStr(quadZeroInf(f2, F.dpsToPrec(15)), 15)).toEqual(['0.785398163397448', '0.0']);
    expect(toStr(quadZeroInf(f2, F.dpsToPrec(50)), 50)).toEqual(['0.78539816339744830961566084581987572104929234984378', '0.0']);
  });
  it('returns the last estimate after maxLevel halvings', () => {
    const f = (x: F.Mpf, w: number): Mpc => [M.exp(F.neg(x), w), F.ZERO];
    // one halving (h = 1/2) is far from the 53 bits of int exp(-t) = 1
    const v = F.toNumber(quadZeroInf(f, 53, 1)[0]);
    expect(Math.abs(v - 1)).toBeGreaterThan(1e-12);
    expect(Math.abs(v - 1)).toBeLessThan(1e-2);
  });
});

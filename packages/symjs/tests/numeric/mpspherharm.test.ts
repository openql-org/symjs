// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/numeric/mpspherharm.ts.
//
// The spherical harmonic kernel against mpmath 1.3 spherharm and hyp2f1 (values at 53 bits).

import { describe, expect, it } from 'vitest';
import * as F from '../../src/numeric/mpf';
import type { Mpc } from '../../src/numeric/mpfun';
import { MpSpecialValue } from '../../src/numeric/mpeval';
import { addPart, hyp2f1Regularized, mpSpherharm, mulPart, mulX, negPart } from '../../src/numeric/mpspherharm';

const c = (re: number, im = 0): Mpc => [F.fromNumber(re), F.fromNumber(im)];
const num = (v: Mpc): [number, number] => [F.toNumber(v[0]), F.toNumber(v[1])];

describe('mpSpherharm', () => {
  it('negative orders (Ynm itself makes an integer order nonnegative)', () => {
    // mpmath: spherharm(2, -1, 1, 1) = 0.18977477584258449931 - 0.29555670184189363134j, spherharm(1, -1, 1j, 0) = 0.40602513685566341131j
    const [re, im] = num(mpSpherharm([c(2), c(-1), c(1), c(1)], 53));
    expect(re).toBeCloseTo(0.1897747758425845, 14);
    expect(im).toBeCloseTo(-0.29555670184189364, 14);
    const [re2, im2] = num(mpSpherharm([c(1), c(-1), c(0, 1), c(0)], 53));
    expect(re2).toBe(0);
    expect(im2).toBeCloseTo(0.4060251368556634, 14);
    expect(num(mpSpherharm([c(1), c(-1), c(0), c(0)], 53))).toEqual([0, 0]);
    // a non-integer degree with a negative integer order at theta = 0: mpmath spherharm(0.5, -1, 0, 1) = 0
    expect(num(mpSpherharm([c(0.5), c(-1), c(0), c(1)], 53))).toEqual([0, 0]);
    // mpmath: spherharm(2.5, -1, 1, 1) = 0.144903355685259 - 0.22567360547264j
    const [re3, im3] = num(mpSpherharm([c(2.5), c(-1), c(1), c(1)], 53));
    expect(re3).toBeCloseTo(0.144903355685259, 13);
    expect(im3).toBeCloseTo(-0.22567360547264, 13);
  });
  it('the regularized 2F1', () => {
    // mpmath at 60 digits: hyp2f1(0.5, 1.5, -1 + e, 0.25)/gamma(-1 + e) with e = 1e-25 -> 0.20388431797142563
    const [re] = num(hyp2f1Regularized(c(0.5), c(1.5), c(-1), c(0.25), 60));
    expect(re).toBeCloseTo(0.20388431797142564, 12);
    // near z = 1 (the 1 - z transformation): mpmath hyp2f1(0.25, 0.5, 1.2, 0.95)/gamma(1.2) = 1.3386078748156236
    const [re2] = num(hyp2f1Regularized(c(0.25), c(0.5), c(1.2), c(0.95), 60));
    expect(re2).toBeCloseTo(1.3386078748156236, 12);
    // a terminating series near z = 1: mpmath hyp2f1(-1, 0.5, 1.2, 0.95)/gamma(1.2) = 0.6580126710560781
    const [re3] = num(hyp2f1Regularized(c(-1), c(0.5), c(1.2), c(0.95), 60));
    expect(re3).toBeCloseTo(0.6580126710560781, 12);
    // an integer c - a - b at z = 0.95: the perturbed limit, mpmath hyp2f1(0.25, 0.75, 1, 0.95) = 1.618623452857967
    const [re4] = num(hyp2f1Regularized(c(0.25), c(0.75), c(1), c(0.95), 60));
    expect(re4).toBeCloseTo(1.618623452857967, 12);
    // at z = 1 with Re(c - a - b) < 0 the value is infinite: (1 - z)**(c - a - b) raises
    expect(() => hyp2f1Regularized(c(0.25), c(0.5), c(0.5), c(1), 60)).toThrow(RangeError);
  });
  it('special values the kernel raises', () => {
    const thrown = (args: Mpc[]): [unknown, unknown] => {
      try {
        mpSpherharm(args, 53);
      } catch (err) {
        if (err instanceof MpSpecialValue) return [err.re, err.im];
        throw err;
      }
      throw new TypeError('no special value');
    };
    const pi = F.fromNumber(Math.PI);
    // Re(m) < 0 at theta = pi (Ynm itself makes such an order positive): the power of cos(theta/2)**2 = 0 is inf
    expect(thrown([c(0.5), c(-0.3), [pi, F.ZERO], c(1)])).toEqual(['-inf', 'inf']);
    // a complex order at theta = 0 is not evaluated (NotImplementedError)
    expect(() => mpSpherharm([c(0.5), c(0.3, 0.25), c(0), c(1)], 53)).toThrow(/complex order/);
  });
  it("mpmath's arithmetic with inf and nan", () => {
    const one = F.ONE;
    expect(mulPart('nan', one, 53)).toBe('nan');
    expect(mulPart('inf', F.ZERO, 53)).toBe('nan');
    expect(mulPart('inf', F.neg(one), 53)).toBe('-inf');
    expect(mulPart('-inf', '-inf', 53)).toBe('inf');
    expect(addPart(one, one, 53)).toEqual(F.fromInt(2n));
    expect(addPart('inf', '-inf', 53)).toBe('nan');
    expect(addPart('nan', one, 53)).toBe('nan');
    expect(addPart(one, '-inf', 53)).toBe('-inf');
    expect([negPart('inf'), negPart('-inf'), negPart('nan'), negPart(one)]).toEqual(['-inf', 'inf', 'nan', F.neg(one)]);
    // an mpc times an mpf, and two mpc: (inf + inf*j)*(0 + 1j) = (nan, nan)
    expect(mulX({ re: 'inf', im: one }, { re: one }, 53)).toEqual({ re: 'inf', im: one });
    expect(mulX({ re: 'inf', im: 'inf' }, { re: F.ZERO, im: one }, 53)).toEqual({ re: 'nan', im: 'nan' });
  });
});

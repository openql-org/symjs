// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Double-precision complex helpers; expected values from Python cmath and
// mpmath.lambertw (asin(2) on the branch cut as SymPy's asin(2).evalf()).

import { describe, expect, it } from 'vitest';
import * as X from '../src/numeric/complex';
import type { ComplexValue as C } from '../src/core/nodes';

const close = (got: C, re: number, im: number) => {
  expect(got.re).toBeCloseTo(re, 12);
  expect(got.im).toBeCloseTo(im, 12);
};
const z12 = X.c(1, 2);

describe('double-precision complex functions', () => {
  it('arithmetic and powers', () => {
    expect(() => X.cdiv(X.c(1), X.c(0))).toThrow(RangeError);
    expect(X.cconj(z12)).toEqual(X.c(1, -2));
    expect(() => X.clog(X.c(0))).toThrow(RangeError);
    expect(X.cpow(X.c(0), X.c(0.5))).toEqual(X.c(0));
    expect(() => X.cpow(X.c(0), X.c(-0.5))).toThrow(RangeError);
    close(X.cpow(X.c(1, 1), X.c(2.5)), -0.9101797211244547, 2.19736822693562);
    close(X.cpow(X.c(1, 1), X.c(-3)), -0.25, -0.25);
  });
  it('trigonometric functions', () => {
    close(X.ctan(z12), 0.0338128260798967, 1.0147936161466333);
    close(X.ctanh(z12), 1.16673625724092, -0.24345820118572534);
    close(X.casin(z12), 0.4270785863924761, 1.5285709194809982);
    close(X.cacos(z12), 1.1437177404024204, -1.5285709194809982);
    close(X.catan(z12), 1.3389725222944935, 0.40235947810852507);
    // SymPy: asin(2).evalf() = 1.5707963267949 - 1.31695789692482*I
    close(X.casin(X.c(2)), 1.5707963267948966, -1.3169578969248166);
    close(X.casin(X.c(0.5)), Math.asin(0.5), 0);
    close(X.cacos(X.c(0.5)), Math.acos(0.5), 0);
    close(X.catan(X.c(2)), Math.atan(2), 0);
    close(X.cacos(X.c(2)), 0, 1.3169578969248166);
  });
  it('Lambert W branches', () => {
    close(X.cLambertW(X.c(-0.3), 0), -0.4894022271802149, 0);
    close(X.cLambertW(X.c(-0.3), -1), -1.7813370234216277, 0);
    close(X.cLambertW(X.c(1, 1), 0), 0.6569660692304364, 0.32545033941341506);
    close(X.cLambertW(X.c(10), 0), 1.7455280027406994, 0);
    close(X.cLambertW(X.c(2, 3), 1), -0.4462717121285748, 5.615883357759838);
  });
});

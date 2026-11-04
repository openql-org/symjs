// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/polys/specialpolys.ts: Swinnerton-Dyer, cyclotomic, symmetric, random and interpolating
// polynomials; expected values from SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';

const [x, y, a] = sj.symbols('x y a');

describe('swinnertonDyerPoly', () => {
  it('orders 1 to 4', () => {
    expect(String(sj.swinnertonDyerPoly(1, x))).toBe('x**2 - 2');
    expect(String(sj.swinnertonDyerPoly(2, x))).toBe('x**4 - 10*x**2 + 1');
    expect(String(sj.swinnertonDyerPoly(3, x))).toBe('x**8 - 40*x**6 + 352*x**4 - 960*x**2 + 576');
    expect(String(sj.swinnertonDyerPoly(4, x))).toBe(
      'x**16 - 136*x**14 + 6476*x**12 - 141912*x**10 + 1513334*x**8 - 7453176*x**6 + 13950764*x**4 - 5596840*x**2 + 46225',
    );
    expect(String(sj.swinnertonDyerPoly(1, undefined, { polys: true }))).toBe("PurePoly(_x**2 - 2, _x, domain='ZZ')");
    expect(() => sj.swinnertonDyerPoly(0, x)).toThrow('Cannot generate Swinnerton-Dyer polynomial of order 0');
  });
});

describe('cyclotomicPoly', () => {
  it('values, Poly objects and the order check', () => {
    expect(String(sj.cyclotomicPoly(1, x))).toBe('x - 1');
    expect(String(sj.cyclotomicPoly(12, x))).toBe('x**4 - x**2 + 1');
    expect(String(sj.cyclotomicPoly(9, x))).toBe('x**6 + x**3 + 1');
    expect(String(sj.cyclotomicPoly(6, undefined, { polys: true }))).toBe("PurePoly(_x**2 - _x + 1, _x, domain='ZZ')");
    expect(String(sj.cyclotomicPoly(6, x, { polys: true }))).toBe("Poly(x**2 - x + 1, x, domain='ZZ')");
    expect(() => sj.cyclotomicPoly(0, x)).toThrow('Cannot generate cyclotomic polynomial of order 0');
  });
});

describe('symmetricPoly', () => {
  it('elementary symmetric polynomials', () => {
    expect(String(sj.symmetricPoly(3, x, y, a))).toBe('a*x*y');
    expect(String(sj.symmetricPoly(1, [x, y]))).toBe('x + y');
    expect(String(sj.symmetricPoly(2, x, y, { polys: true }))).toBe("Poly(x*y, x, y, domain='ZZ')");
    expect(String(sj.symmetricPoly(0, x))).toBe('1');
    expect(() => sj.symmetricPoly(3, x, y)).toThrow('Cannot generate symmetric polynomial of order 3 for (x, y)');
  });
});

describe('randomPoly', () => {
  it('degree and coefficient range, with a given generator', () => {
    // a generator drawing 0 first: the leading coefficient is drawn again until it is nonzero
    const seq = [0.5, 0.5, 0.9, 0.0, 0.25];
    let i = 0;
    const random = () => seq[i++ % seq.length] as number;
    expect(String(sj.randomPoly(x, 3, -2, 2, { random }))).toBe('2*x**3 - 2*x**2 - x');
    const p = sj.randomPoly(x, 4, -5, 5, { polys: true });
    expect(p.degree()).toBe(4);
    expect(p.allCoeffs().every((c) => c instanceof sj.Rational && Math.abs(Number(c.p)) <= 5)).toBe(true);
    expect(() => sj.randomPoly(x, -1, 0, 1)).toThrow(RangeError);
    expect(() => sj.randomPoly(x, 2, 0, 0)).toThrow(RangeError);
    expect(() => sj.randomPoly(x, 2, 3, 1)).toThrow(RangeError);
  });
});

describe('interpolatingPoly', () => {
  it('Lagrange polynomials', () => {
    expect(String(sj.interpolatingPoly(2, x))).toBe('y0*(x - x1)/(x0 - x1) + y1*(x - x0)/(-x0 + x1)');
    expect(String(sj.interpolatingPoly(3, x, [1, 2, 3], [1, 4, 9]))).toBe('(x - 3)*(x - 2)/2 - 4*(x - 3)*(x - 1) + 9*(x - 2)*(x - 1)/2');
    expect(String(sj.interpolatingPoly(2, x, 'a', 'b'))).toBe('b0*(-a1 + x)/(a0 - a1) + b1*(-a0 + x)/(-a0 + a1)');
  });
  it('x must be a symbol outside X and Y', () => {
    expect(() => sj.interpolatingPoly(2, a, [a, 1], 'y')).toThrow('Expecting symbol for x');
    expect(() => sj.interpolatingPoly(2, a, 'x', [a, 1])).toThrow('Expecting symbol for x');
    expect(() => sj.interpolatingPoly(2, 1)).toThrow('Expecting symbol for x');
  });
});

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/functions/sphericalbessel.ts.
//
// The spherical Hankel functions hn1 and hn2, the rewrites and expand_func of the spherical Bessel
// functions, jn_zeros and the Airy functions as hypergeometric functions. Expected values are str()
// results of SymPy 1.14 (mpmath 1.3 for the numbers).

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { NotImplementedError, Rational, Sym, add, diff, evalf, expandFunc, hn1, hn2, jn, jnZeros, rewrite, sphericalBesselFn, symbols, yn } from '../../src';

const S = (e: unknown): string => String(e);
const [z, n] = symbols('z n');
const nu = new Sym('nu', { integer: true });

describe('spherical_bessel_fn and expand_func', () => {
  it('the coefficient polynomials in 1/z', () => {
    expect(Array.from({ length: 10 }, (_, i) => S(sphericalBesselFn(i - 5, z)))).toEqual([
      '-10/z**2 + 105/z**4',
      '1/z - 15/z**3',
      '3/z**2',
      '-1/z',
      '0',
      '1/z',
      'z**(-2)',
      '-1/z + 3/z**3',
      '-6/z**2 + 15/z**4',
      '1/z - 45/z**3 + 105/z**5',
    ]);
  });
  it('jn, yn, hn1 and hn2 of an integer order in sin and cos', () => {
    expect(S(expandFunc(jn(0, z)))).toBe('sin(z)/z');
    expect(S(expandFunc(jn(2, z)))).toBe('(-1/z + 3/z**3)*sin(z) - 3*cos(z)/z**2');
    expect(S(expandFunc(jn(3, z)))).toBe('(-6/z**2 + 15/z**4)*sin(z) + (1/z - 15/z**3)*cos(z)');
    expect(S(expandFunc(yn(2, z)))).toBe('-(-1/z + 3/z**3)*cos(z) - 3*sin(z)/z**2');
    expect(S(expandFunc(yn(0, z)))).toBe('-cos(z)/z');
    expect(S(expandFunc(yn(-2, z)))).toBe('cos(z)/z - sin(z)/z**2');
    expect(S(expandFunc(jn(nu, z)))).toBe('jn(nu, z)');
    expect(S(expandFunc(yn(nu, z)))).toBe('yn(nu, z)');
    expect(S(expandFunc(hn1(nu, z)))).toBe('jn(nu, z) + I*yn(nu, z)');
    expect(S(expandFunc(hn2(nu, z)))).toBe('jn(nu, z) - I*yn(nu, z)');
    expect(S(expandFunc(hn1(0, z)))).toBe('sin(z)/z - I*cos(z)/z');
    expect(S(expandFunc(hn1(1, z)))).toBe('-I*sin(z)/z - cos(z)/z + sin(z)/z**2 - I*cos(z)/z**2');
    expect(S(expandFunc(hn2(1, z)))).toBe('I*sin(z)/z - cos(z)/z + sin(z)/z**2 + I*cos(z)/z**2');
  });
});

describe('rewrites', () => {
  const RW = (e: sj.Expr, t: string) => S(rewrite(e, t));
  it('jn and yn', () => {
    expect(RW(jn(nu, z), 'besselj')).toBe('sqrt(2)*sqrt(pi)*sqrt(1/z)*besselj(nu + 1/2, z)/2');
    expect(RW(jn(nu, z), 'bessely')).toBe('(-1)**nu*sqrt(2)*sqrt(pi)*sqrt(1/z)*bessely(-nu - 1/2, z)/2');
    expect(RW(jn(nu, z), 'yn')).toBe('(-1)**nu*yn(-nu - 1, z)');
    expect(RW(yn(nu, z), 'besselj')).toBe('(-1)**(nu + 1)*sqrt(2)*sqrt(pi)*sqrt(1/z)*besselj(-nu - 1/2, z)/2');
    expect(RW(yn(nu, z), 'bessely')).toBe('sqrt(2)*sqrt(pi)*sqrt(1/z)*bessely(nu + 1/2, z)/2');
    expect(RW(yn(n, z), 'besselj')).toBe('yn(n, z)');
    expect(RW(yn(n, z), 'bessely')).toBe('yn(n, z)');
    expect(RW(yn(nu, z), 'jn')).toBe('(-1)**(nu + 1)*jn(-nu - 1, z)');
  });
  it('hn1 and hn2', () => {
    expect(RW(hn1(nu, z), 'jn')).toBe('(-1)**(nu + 1)*I*jn(-nu - 1, z) + jn(nu, z)');
    expect(RW(hn2(nu, z), 'jn')).toBe('-(-1)**(nu + 1)*I*jn(-nu - 1, z) + jn(nu, z)');
    expect(RW(hn1(nu, z), 'yn')).toBe('(-1)**nu*yn(-nu - 1, z) + I*yn(nu, z)');
    expect(RW(hn2(nu, z), 'yn')).toBe('(-1)**nu*yn(-nu - 1, z) - I*yn(nu, z)');
    expect(RW(hn1(nu, z), 'besselj')).toBe('sqrt(2)*sqrt(pi)*((-1)**(nu + 1)*I*besselj(-nu - 1/2, z) + besselj(nu + 1/2, z))*sqrt(1/z)/2');
    expect(RW(hn2(nu, z), 'besselj')).toBe('sqrt(2)*sqrt(pi)*(-(-1)**(nu + 1)*I*besselj(-nu - 1/2, z) + besselj(nu + 1/2, z))*sqrt(1/z)/2');
    expect(RW(hn1(nu, z), 'bessely')).toBe('sqrt(2)*sqrt(pi)*((-1)**nu*bessely(-nu - 1/2, z) + I*bessely(nu + 1/2, z))*sqrt(1/z)/2');
    expect(RW(hn2(nu, z), 'bessely')).toBe('sqrt(2)*sqrt(pi)*((-1)**nu*bessely(-nu - 1/2, z) - I*bessely(nu + 1/2, z))*sqrt(1/z)/2');
    expect(RW(hn1(nu, z), 'hankel1')).toBe('sqrt(2)*sqrt(pi)*sqrt(1/z)*hankel1(nu, z)/2');
    expect(RW(hn2(nu, z), 'hankel2')).toBe('sqrt(2)*sqrt(pi)*sqrt(1/z)*hankel2(nu, z)/2');
    expect(RW(hn1(n, z), 'hankel1')).toBe('hn1(n, z)');
  });
  it('the Airy functions as hyper', () => {
    expect(RW(sj.airyai(z), 'hyper')).toBe('-3**(2/3)*z*hyper((), (4/3,), z**3/9)/(3*gamma(1/3)) + 3**(1/3)*hyper((), (2/3,), z**3/9)/(3*gamma(2/3))');
    expect(RW(sj.airybi(z), 'hyper')).toBe('3**(1/6)*z*hyper((), (4/3,), z**3/9)/gamma(1/3) + 3**(5/6)*hyper((), (2/3,), z**3/9)/(3*gamma(2/3))');
    expect(RW(sj.airyaiprime(z), 'hyper')).toBe('3**(1/3)*z**2*hyper((), (5/3,), z**3/9)/(6*gamma(2/3)) - 3**(2/3)*hyper((), (1/3,), z**3/9)/(3*gamma(1/3))');
    expect(RW(sj.airybiprime(z), 'hyper')).toBe('3**(5/6)*z**2*hyper((), (5/3,), z**3/9)/(6*gamma(2/3)) + 3**(1/6)*hyper((), (1/3,), z**3/9)/gamma(1/3)');
  });
});

describe('hn1 and hn2: derivatives, values and LaTeX', () => {
  it('derivatives', () => {
    expect(S(diff(hn1(n, z), z))).toBe('hn1(n - 1, z) - (n + 1)*hn1(n, z)/z');
    expect(S(diff(hn2(n, z), z))).toBe('hn2(n - 1, z) - (n + 1)*hn2(n, z)/z');
    expect(() => diff(hn1(n, 1), n)).toThrow(NotImplementedError);
  });
  it('values of integer orders', () => {
    expect(S(evalf(hn1(2, 3), 20))).toBe('0.29863749707573354751 - 0.26703833526449917565*I');
    expect(S(evalf(hn2(1, 2), 20))).toBe('0.43539777497999161735 + 0.35061200427605525095*I');
    expect(S(evalf(hn1(1, add(Rational.of(1, 2), sj.I)), 20))).toBe('-0.56151298875607522291 + 0.2298154343420090274*I');
    // SymPy: hn1(1/2, 2) is not evaluated
    expect(S(evalf(hn1(Rational.of(1, 2), 2), 20))).toBe('hn1(1/2, 2)');
    expect(S(hn2(1, sj.float(2)))).toBe('hn2(1, 2.0)');
    // hn2(1, 2) = 0.435397774979992 + 0.350612004276055*I in double precision
    const v = sj.toComplex(hn2(1, 2));
    expect(v.re).toBeCloseTo(0.435397774979992, 12);
    expect(v.im).toBeCloseTo(0.350612004276055, 12);
    expect(() => sj.toComplex(hn1(0.5, 2))).toThrow(NotImplementedError);
  });
  it('LaTeX', () => {
    expect(sj.latex(hn2(n, z))).toBe('h^{(2)}_{n}\\left(z\\right)');
  });
});

describe('jn_zeros', () => {
  it('the zeros of jn(n, z) at dps digits', () => {
    expect(S(jnZeros(2, 4, { dps: 5 }))).toBe('5.7635,9.0950,12.323,15.515');
    // SymPy prints [6.987932000500520324237641, 10.41711854737936526760222, ...]: its besseljzero runs at
    // mpmath's default 53 bits, so only 15 digits are right. These are mpmath besseljzero at 86 bits.
    expect(jnZeros(3, 5, { dps: 25 }).map(S)).toEqual([
      '6.987932000500519959015333',
      '10.41711854737936476325043',
      '13.69802315324924899950309',
      '16.92362128521383957885418',
      '20.12180617445381828564965',
    ]);
    expect(jnZeros(10, 3).map(S)).toEqual(['15.0334693037434', '19.0258535361278', '22.6627206581361']);
    expect(jnZeros(0, 2).map(S)).toEqual(['3.14159265358979', '6.28318530717959']);
    // (SymPy: [36.628378589713435076, 41.643008631132495623], again correct to 15 digits only)
    expect(jnZeros(30, 2, { dps: 20 }).map(S)).toEqual(['36.628378589713436836', '41.643008631132493502']);
  });
  it('invalid arguments', () => {
    expect(() => jnZeros(2, 4, { method: 'scipy' })).toThrow(NotImplementedError);
    expect(() => jnZeros(Rational.of(1, 2), 2)).toThrow(TypeError);
  });
});

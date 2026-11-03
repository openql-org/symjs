// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/** Top-level polynomial functions of polys/sympoly (gcd, degree, div, terms_gcd, horner, factor, ...); expected values from SymPy 1.14. */

import { describe, expect, it } from 'vitest';
import * as sj from '../src';

const [x, y, z] = sj.symbols('x y z') as [sj.Sym, sj.Sym, sj.Sym];
const E = sj.parse;
const show = (r: unknown): string => (Array.isArray(r) ? `[${r.map(show).join(', ')}]` : String(r));
const F = (e: string, opts: Parameters<typeof sj.factor>[1] = {}) => String(sj.factor(E(e), opts));

describe('gcd, lcm, degree, div', () => {
  it('on expressions', () => {
    expect(String(sj.gcd(E('x**2 - 1'), E('x**2 + 2*x + 1')))).toBe('x + 1');
    expect(String(sj.gcd(sj.Poly.from(E('x**2 - 1'), [x]), E('x**2 + 2*x + 1')))).toBe('x + 1');
    expect(String(sj.lcm(E('x**2 - 1'), E('x*y + y')))).toBe('x**2*y - y');
    expect(sj.degree(E('x**3*y + y**2'), x)).toBe(3);
    expect(sj.degree(E('x**3*y + y**2'), y)).toBe(2);
    expect(sj.degree(E('x**3*y + y**2'), z)).toBe(0);
    expect(sj.degree(0, x)).toBe(-Infinity);
    expect(sj.degree(5, x)).toBe(0);
    expect(sj.degree(sj.Poly.from(E('x**2 + 1'), [x]))).toBe(2);
    expect(show(sj.div(E('x**3 + 2*x + 1'), E('x**2 + 1')))).toBe('[x, x + 1]');
    // SymPy divides multivariate polynomials, (y, 1 - y**2); symjs supports univariate division only
    expect(() => sj.div(E('x*y + 1'), E('x + y'))).toThrow(sj.PolynomialError);
  });
});

describe('horner, interpolate, resultant, discriminant', () => {
  it('horner', () => {
    expect(String(sj.horner(E('x**4 + 2*x**3 + 3*x + 5')))).toBe('x*(x**2*(x + 2) + 3) + 5');
    expect(String(sj.horner(E('x**2*y + x*y**2 + x + 1')))).toBe('x*(x*y + y**2 + 1) + 1');
    expect(String(sj.horner(E('x**2*y + x*y**2 + x + 1'), y))).toBe('x + y*(x**2 + x*y) + 1');
    expect(String(sj.horner(5))).toBe('5');
  });
  it('interpolate', () => {
    expect(String(sj.interpolate([[1, 1], [2, 4], [3, 9]], x))).toBe('x**2');
    expect(String(sj.interpolate([1, 4, 9, 16], x))).toBe('x**2');
  });
  it('resultant and discriminant', () => {
    expect(String(sj.resultant(E('x**2 + 1'), E('x**2 - 2*x + 5'), x))).toBe('20');
    expect(String(sj.resultant(E('x**2 - 1'), E('x - 1'), x))).toBe('0');
    expect(String(sj.resultant(E('x**2 - 1'), 0, x))).toBe('0');
    expect(String(sj.resultant(E('x**2 - 1'), 3, x))).toBe('9');
    expect(String(sj.resultant(E('x**3 + x + 1'), E('x**2 + 2'), x))).toBe('3');
    expect(String(sj.resultant(E('x**2 + y'), E('y*x + 1'), x))).toBe('y**3 + 1');
    expect(String(sj.discriminant(E('a*x**2 + b*x + 1'), x))).toBe('-4*a + b**2');
    expect(String(sj.discriminant(E('x**3 - x + 1'), x))).toBe('-23');
  });
});

describe('terms_gcd', () => {
  it('content and common monomial', () => {
    const T = (e: string, ...rest: (sj.Sym | { expand?: boolean; deep?: boolean; clear?: boolean })[]) => String(sj.termsGcd(E(e), ...rest));
    expect(T('x**3*y + x*y**3')).toBe('x*y*(x**2 + y**2)');
    expect(T('4*x**2 + 6*x')).toBe('2*x*(2*x + 3)');
    expect(T('x/2 + x**2/3')).toBe('x*(2*x + 3)/6');
    expect(T('x/2 + x**2/3', { clear: false })).toBe('x*(2*x + 3)/6');
    expect(T('2*x + 4*x**2', { clear: false })).toBe('2*x*(2*x + 1)');
    expect(T('x/3 + x*y/3 + x*z/3', { clear: false })).toBe('x*(y + z + 1)/3');
    expect(T('sin(x**2*y + x*y**2) + x', { deep: true })).toBe('x + sin(x*y*(x + y))');
    expect(T('(x + 1)*x + x', { expand: false })).toBe('x*(x + 2)');
    expect(T('x + 1')).toBe('x + 1');
    expect(T('3')).toBe('3');
    expect(T('sqrt(2)*x + sqrt(2)')).toBe('sqrt(2)*(x + 1)');
    expect(T('pi*x + pi')).toBe('pi*(x + 1)');
    expect(T('x/y + x**2/y**2')).toBe('x*(x/y + 1)/y');
    expect(T('x - x')).toBe('0');
    // SymPy works over RR, x*(1.0*x + 2.5); symjs leaves an expression with Float coefficients unchanged
    expect(String(sj.termsGcd(sj.add(sj.mul(new sj.Float(2.5), x), sj.pow(x, 2))))).toBe('x**2 + 2.5*x');
  });
});

describe('factor options', () => {
  it('modulus', () => {
    expect(F('x**4 + 1', { modulus: 2 })).toBe('(x + 1)**4');
    expect(F('2*x**3 + x + 1', { modulus: 5 })).toBe('2*(x**3 - 2*x - 2)');
    // SymPy: NotImplementedError (multivariate) and (x - 1)/2 (rational coefficients); not supported here
    expect(() => F('x*y + 1', { modulus: 2 })).toThrow(sj.PolynomialError);
    expect(() => F('x/2 + 1', { modulus: 3 })).toThrow(sj.DomainError);
    expect(() => F('sin(x) + 1', { modulus: 3 })).toThrow(sj.DomainError);
  });
  it('gaussian and extension', () => {
    expect(F('x**2 + 1', { gaussian: true })).toBe('(x - I)*(x + I)');
    expect(F('x**2 + x + 1', { gaussian: true })).toBe('x**2 + x + 1');
    const s2 = [E('sqrt(2)')];
    expect(F('x**2 - 2', { extension: s2 })).toBe('(x - sqrt(2))*(x + sqrt(2))');
    expect(F('(x**2 - 2)*(x**2 + 1)', { extension: s2 })).toBe('(x - sqrt(2))*(x + sqrt(2))*(x**2 + 1)');
    expect(F('x*y - 2', { extension: s2 })).toBe('x*y - 2');
    expect(F('x**2 - 3', { extension: s2 })).toBe('x**2 - 3');
    expect(F('x**2 + 1', { extension: s2 })).toBe('x**2 + 1');
    expect(F('x**2 - 2*x - 1', { extension: s2 })).toBe('(x - 1 + sqrt(2))*(x - sqrt(2) - 1)');
  });
  it('deep and fraction', () => {
    expect(F('sin(x**2 + 2*x + 1)', { deep: true })).toBe('sin((x + 1)**2)');
    expect(F('exp(x - y)*(x + 1)', { deep: true })).toBe('(x + 1)*exp(x)*exp(-y)');
    expect(F('exp(x - y)*(x + 1)', { deep: true, fraction: false })).toBe('(x + 1)*exp(x)*exp(-y)');
    expect(F('sin(x**2 + 2*x + 1)', { deep: true, fraction: false })).toBe('sin((x + 1)**2)');
  });
  it('rational functions, powers and generators', () => {
    expect(F('6')).toBe('6');
    expect(F('(x**2 - 1)/(x**2 + 2*x + 1)')).toBe('(x - 1)/(x + 1)');
    expect(F('-x/(1 - y)')).toBe('x/(y - 1)');
    expect(F('(x**2 - 1)**3')).toBe('(x - 1)**3*(x + 1)**3');
    expect(F('sqrt(x**2 - 1)')).toBe('sqrt((x - 1)*(x + 1))');
    expect(F('x*(x**2 - 1)**2')).toBe('x*(x - 1)**2*(x + 1)**2');
    expect(F('sin(x)**2 - 1')).toBe('(sin(x) - 1)*(sin(x) + 1)');
    expect(F('sin(x)')).toBe('sin(x)');
    expect(F('-x - 1')).toBe('-x - 1');
    expect(F('2*x + 2')).toBe('2*(x + 1)');
    expect(F('-2*x**2 + 2')).toBe('-2*(x - 1)*(x + 1)');
    expect(String(sj.factor(sj.add(sj.mul(x, E('x + 1')), sj.mul(-1, sj.pow(x, 2)), sj.mul(-1, x), 3)))).toBe('3');
  });
  it('factorNc, factorList, sqfNorm, minimalPolynomial', () => {
    const [A, B] = [new sj.Sym('A', { commutative: false }), new sj.Sym('B', { commutative: false })];
    expect(String(sj.factorNc(sj.add(sj.mul(A, x), sj.mul(A, y))))).toBe('(x + y)*A');
    expect(String(sj.factorNc(E('x**2 - 1')))).toBe('(x - 1)*(x + 1)');
    expect(String(sj.factorNc(sj.add(sj.mul(A, B), sj.mul(B, A))))).toBe('A*B + B*A');
    expect(show(sj.factorList(E('2*x**2 - 2')))).toBe('[2, [[x - 1, 1], [x + 1, 1]]]');
    expect(show(sj.factorList(E('6')))).toBe('[6, []]');
    expect(show(sj.sqfNorm(E('x**2 - 2'), x, [E('sqrt(3)')]))).toBe('[[1], x**2 - 2*sqrt(3)*x + 1, x**4 - 10*x**2 + 1]');
    expect(show(sj.sqfNorm(E('x**2 + 1'), x, [sj.I]))).toBe('[[2], x**2 - 4*I*x - 3, x**4 + 10*x**2 + 9]');
    expect(String(sj.minimalPolynomial(E('sqrt(2) + sqrt(3)'), x))).toBe('x**4 - 10*x**2 + 1');
    expect(String(sj.minimalPolynomial(E('3/4'), x))).toBe('4*x - 3');
    expect(String(sj.minimalPolynomial(E('-sqrt(2)/2'), x))).toBe('2*x**2 - 1');
    expect(() => sj.minimalPolynomial(E('2**(1/3)'), x)).toThrow(sj.NotImplementedError);
  });
});

describe('further cases', () => {
  it('terms_gcd, discriminant, factor', () => {
    expect(String(sj.termsGcd(E('x**2 + x'), { clear: false }))).toBe('x*(x + 1)');
    expect(String(sj.termsGcd(sj.add(sj.pow(E('x + 1'), 2), E('-x**2 - 2*x - 1'))))).toBe('0');
    expect(String(sj.discriminant(E('x**4 + 1'), x))).toBe('256');
    expect(String(sj.minimalPolynomial(E('1 - sqrt(2)'), x))).toBe('x**2 - 2*x - 1');
    const s2 = [E('sqrt(2)')];
    expect(F('x**2 - a', { extension: s2 })).toBe('-a + x**2');
    // SymPy factors over Q(2**(1/3)) and with sin(x) as a generator:
    // (x - 2**(1/3))*(x**2 + 2**(1/3)*x + 2**(2/3)) and (sin(x) - sqrt(2))*(sin(x) + sqrt(2))
    expect(F('x**3 - 2', { extension: [E('2**(1/3)')] })).toBe('x**3 - 2');
    expect(F('sin(x)**2 - 2', { extension: s2 })).toBe('sin(x)**2 - 2');
    // SymPy splits exp(x + y) into exp(x)*exp(y)
    expect(F('exp(x + y)*(x**2 - 1)', { deep: true })).toBe('(x - 1)*(x + 1)*exp(x + y)');
  });
});

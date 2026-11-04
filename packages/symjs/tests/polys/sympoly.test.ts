// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/polys/sympoly.ts: Poly methods and the top-level polynomial functions (gcd, degree, div, terms_gcd, horner, factor, ...); expected values from SymPy 1.14 (tuples written as [...]).

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { add, expand, factorNc, mul, parse, pow, sstr, str, Sym, symbols } from '../../src';
import { factorListInt } from '../../src/polys/sympoly';

const { Poly } = sj;
const [x, y, z] = symbols('x y z');
const E = sj.parse;
const show = (r: unknown): string => (Array.isArray(r) ? `[${r.map(show).join(', ')}]` : String(r));
const F = (e: string, opts: Parameters<typeof sj.factor>[1] = {}) => String(sj.factor(E(e), opts));
const P = (e: string, ...g: sj.Expr[]) => Poly.from(parse(e), g);
const R = (p: number, q = 1) => sj.Rational.of(BigInt(p), BigInt(q));
const f = P('2*x**3 - 3*x + 1', x);
const A = new Sym('A', { commutative: false });
const B = new Sym('B', { commutative: false });
const P2 = (s: string) => parse(s, { symbols: { x: x!, y: y! } });

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
    expect(String(sj.minimalPolynomial(E('2**(1/3)'), x))).toBe('x**3 - 2');
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
    expect(F('x**3 - 2', { extension: [E('2**(1/3)')] })).toBe('(x - 2**(1/3))*(x**2 + 2**(1/3)*x + 2**(2/3))');
    // SymPy factors with sin(x) as a generator: (sin(x) - sqrt(2))*(sin(x) + sqrt(2))
    expect(F('sin(x)**2 - 2', { extension: s2 })).toBe('sin(x)**2 - 2');
    // SymPy splits exp(x + y) into exp(x)*exp(y)
    expect(F('exp(x + y)*(x**2 - 1)', { deep: true })).toBe('(x - 1)*(x + 1)*exp(x)*exp(y)');
  });
});

describe('terms, leading terms and arithmetic', () => {
  it('monoms, LM, LT, EC, TC, nth, length, norms', () => {
    const p = P('x**2*y + 3*y + 1', x, y);
    expect(show(p.monoms())).toBe('[[2, 1], [0, 1], [0, 0]]');
    expect(show(P('0', x, y).monoms())).toBe('[[0, 0]]');
    expect(String(p.LM())).toBe('x**2*y');
    expect(String(P('0', x).LM())).toBe('1');
    expect(show(p.LT())).toBe('[[2, 1], 1]');
    expect(show(P('0', x, y).LT())).toBe('[[0, 0], 0]');
    expect(String(P('x**3 + 2*x + 5', x).EC())).toBe('5');
    expect(String(P('0', x).EC())).toBe('0');
    expect(String(P('x**3 + 2*x + 5', x).TC())).toBe('5');
    expect(String(P('x*y + 2', x, y).TC())).toBe('2');
    expect(String(P('x**2*y + 3*x*y', x, y).nth(1, 1))).toBe('3');
    expect(P('x**3 + 2*x + 5', x).length()).toBe(3);
    expect(String(P('-x**3 + 2*x - 5', x).l1Norm())).toBe('8');
    expect(String(P('-x**3 + 2*x - 5', x).maxNorm())).toBe('5');
    expect(String(P('0', x).maxNorm())).toBe('0');
    expect(show(P('x**3 + 1', x).allMonoms())).toBe('[[3], [2], [1], [0]]');
    expect(show(P('x**3 + 2', x).allTerms())).toBe('[[[3], 1], [[2], 0], [[1], 0], [[0], 2]]');
    expect(show(P('0', x).allTerms())).toBe('[[[0], 0]]');
    expect(show(P('x**2*y + 3', x, y).asDict())).toBe('[[[2, 1], 1], [[0, 0], 3]]');
    expect(String(P('x**2*y + 3', x, y).asExprAt([2, 3]))).toBe('15');
    expect(String(P('x**2*y + 3', x, y).asExprAt([[y, 3]]))).toBe('3*x**2 + 3');
  });
  it('add, neg, ground operations', () => {
    expect(String(f.add(P('x**2 - 1', x)))).toBe("Poly(2*x**3 + x**2 - 3*x, x, domain='ZZ')");
    expect(String(f.add(x))).toBe("Poly(2*x**3 - 2*x + 1, x, domain='ZZ')");
    expect(String(f.neg())).toBe("Poly(-2*x**3 + 3*x - 1, x, domain='ZZ')");
    expect(String(P('-2*x**2 + x - 3', x).abs())).toBe("Poly(2*x**2 + x + 3, x, domain='ZZ')");
    expect(String(P('x + 1', x).sqr())).toBe("Poly(x**2 + 2*x + 1, x, domain='ZZ')");
    expect(String(P('x + 1', x).addGround(2))).toBe("Poly(x + 3, x, domain='ZZ')");
    expect(String(P('x + 1', x).subGround(2))).toBe("Poly(x - 1, x, domain='ZZ')");
    expect(String(P('x + 1', x).mulGround(3))).toBe("Poly(3*x + 3, x, domain='ZZ')");
    expect(String(P('3*x + 7', x).quoGround(2))).toBe("Poly(x + 3, x, domain='ZZ')");
    expect(String(P('-3*x - 7', x).quoGround(2))).toBe("Poly(-2*x - 4, x, domain='ZZ')");
    expect(String(P('3*x + 7', x).quoGround(-2))).toBe("Poly(-2*x - 4, x, domain='ZZ')");
    expect(String(P('3*x + 7/2', x).quoGround(2))).toBe("Poly(3/2*x + 7/4, x, domain='QQ')");
    expect(String(P('4*x + 6', x).exquoGround(2))).toBe("Poly(2*x + 3, x, domain='ZZ')");
    expect(() => P('3*x + 7', x).exquoGround(2)).toThrow(sj.ExactQuotientFailed);
    expect(String(P('x/2 + 1', x).exquoGround(3))).toBe("Poly(1/6*x + 1/3, x, domain='QQ')");
  });
});

describe('pseudo-division and subresultants', () => {
  it('prem, pquo, pdiv, pexquo (SymPy dup_prem scaling)', () => {
    const g = P('2*x - 1', x);
    expect(String(f.prem(g))).toBe("Poly(-2, x, domain='ZZ')");
    expect(String(f.pquo(g))).toBe("Poly(8*x**2 + 4*x - 10, x, domain='ZZ')");
    expect(show(f.pdiv(g))).toBe("[Poly(8*x**2 + 4*x - 10, x, domain='ZZ'), Poly(-2, x, domain='ZZ')]");
    expect(String(P('x**3 + 1', x).prem(P('2*x**2', x)))).toBe("Poly(4, x, domain='ZZ')");
    expect(String(P('x', x).prem(P('2*x**3', x)))).toBe("Poly(x, x, domain='ZZ')");
    expect(String(P('x', x).pquo(P('2*x**3', x)))).toBe("Poly(0, x, domain='ZZ')");
    expect(String(P('x**2 - 1', x).pexquo(P('2*x - 2', x)))).toBe("Poly(2*x + 2, x, domain='ZZ')");
    expect(() => f.pexquo(g)).toThrow(sj.ExactQuotientFailed);
    expect(() => f.prem(P('0', x))).toThrow(RangeError);
  });
  it('subresultant PRS', () => {
    expect(show(P('x**2 + 1', x).subresultants(P('x**2 - 1', x)))).toBe(
      "[Poly(x**2 + 1, x, domain='ZZ'), Poly(x**2 - 1, x, domain='ZZ'), Poly(-2, x, domain='ZZ')]",
    );
    expect(show(P('x**3 - x + 1', x).subresultants(P('x', x)))).toBe("[Poly(x**3 - x + 1, x, domain='ZZ'), Poly(x, x, domain='ZZ'), Poly(-1, x, domain='ZZ')]");
    expect(show(P('x**4 + x**2 + 1', x).subresultants(P('x**2 - x + 1', x)))).toBe("[Poly(x**4 + x**2 + 1, x, domain='ZZ'), Poly(x**2 - x + 1, x, domain='ZZ')]");
    expect(show(P('x', x).subresultants(P('x**3 + 2', x)))).toBe("[Poly(x**3 + 2, x, domain='ZZ'), Poly(x, x, domain='ZZ'), Poly(-2, x, domain='ZZ')]");
    expect(show(P('x**5 + x + 3', x).subresultants(P('3*x**2 + 2', x)))).toBe(
      "[Poly(x**5 + x + 3, x, domain='ZZ'), Poly(3*x**2 + 2, x, domain='ZZ'), Poly(117*x + 243, x, domain='ZZ'), Poly(2525, x, domain='ZZ')]",
    );
    expect(P('0', x).subresultants(P('0', x))).toEqual([]);
    expect(show(P('x + 1', x).subresultants(P('0', x)))).toBe("[Poly(x + 1, x, domain='ZZ')]");
  });
  it('lcm, cofactors, gcdex, invert', () => {
    expect(String(P('x**2 - 1', x).lcm(P('x**2 + 2*x + 1', x)))).toBe("Poly(x**3 + x**2 - x - 1, x, domain='ZZ')");
    expect(show(P('x**2 - 1', x).cofactors(P('x**2 - 3*x + 2', x)))).toBe(
      "[Poly(x - 1, x, domain='ZZ'), Poly(x + 1, x, domain='ZZ'), Poly(x - 2, x, domain='ZZ')]",
    );
    const F = P('x**4 - 2*x**3 - 6*x**2 + 12*x + 15', x);
    const G = P('x**3 + x**2 - 4*x - 4', x);
    expect(show(F.gcdex(G))).toBe("[Poly(-1/5*x + 3/5, x, domain='QQ'), Poly(1/5*x**2 - 6/5*x + 2, x, domain='QQ'), Poly(x + 1, x, domain='QQ')]");
    expect(show(F.halfGcdex(G))).toBe("[Poly(-1/5*x + 3/5, x, domain='QQ'), Poly(x + 1, x, domain='QQ')]");
    expect(String(P('x**2 - 1', x).invert(P('2*x - 1', x)))).toBe("Poly(-4/3, x, domain='QQ')");
    expect(() => P('x**2 - 1', x).invert(P('x - 1', x))).toThrow(sj.NotInvertible);
  });
});

describe('calculus, evaluation and substitution', () => {
  it('integrate and eval', () => {
    expect(String(P('3*x**2 + 2*x*y', x, y).integrate(x))).toBe("Poly(x**3 + x**2*y, x, y, domain='QQ')");
    expect(String(P('3*x**2 + 2*x*y', x, y).integrate(y))).toBe("Poly(3*x**2*y + x*y**2, x, y, domain='QQ')");
    expect(String(P('4*x**3 + 1', x).integrate())).toBe("Poly(x**4 + x, x, domain='QQ')");
    // y is not a generator (SymPy PolynomialError)
    expect(() => P('x**2 + 1', x).integrate(y)).toThrow('a valid generator expected, got y');
    expect(() => P('y*x**2 + 1', x).integrate(y)).toThrow(sj.PolynomialError);
    expect(String(P('x**2*y + y + 1', x, y).eval(2))).toBe("Poly(5*y + 1, y, domain='ZZ')");
    expect(String(P('x**2*y + y + 1', x, y).eval(3, y))).toBe("Poly(3*x**2 + 4, x, domain='ZZ')");
    expect(String(P('x**2 + 1', x).eval(3))).toBe('10');
    expect(String(P('x*y + z', x, y, z).evalMany([[x, 1], [y, 2]]))).toBe("Poly(z + 2, z, domain='ZZ')");
    expect(String(P('x*y + z', x, y, z).evalMany([[x, 1], [y, 2], [z, 3]]))).toBe('5');
    expect(show(P('x**3 - x', x).roots())).toBe('[-1, 0, 1]');
  });
  it('compose, transform, shift, revert, discriminant, resultant', () => {
    expect(String(P('x**2 + x', x).compose(P('x - 1', x)))).toBe("Poly(x**2 - x, x, domain='ZZ')");
    expect(String(P('x**2 - 2*x + 1', x).transform(P('x + 1', x), P('x - 1', x)))).toBe("Poly(4, x, domain='ZZ')");
    expect(String(P('1 + x + x**2', x).revert(4))).toBe("Poly(x**3 - x + 1, x, domain='ZZ')");
    expect(String(P('x**2 + 3*x + 1', x).discriminant())).toBe('5');
    expect(String(P('x**3 + a*x + b', x).discriminant())).toBe('-4*a**3 - 27*b**2');
    expect(String(P('x**2 + 1', x).resultant(P('x**2 - 1', x)))).toBe('4');
  });
  it('nth_power_roots_poly is the resultant of f(y) and y**n - x', () => {
    expect(String(P('x**2 - 3*x + 1', x).nthPowerRootsPoly(2))).toBe("Poly(x**2 - 7*x + 1, x, domain='ZZ')");
    expect(String(P('2*x**2 - 3*x + 1', x).nthPowerRootsPoly(2))).toBe("Poly(4*x**2 - 5*x + 1, x, domain='ZZ')");
    expect(String(P('x**3 - x - 1', x).nthPowerRootsPoly(3))).toBe("Poly(-x**3 + 3*x**2 - 2*x + 1, x, domain='ZZ')");
    expect(String(P('-x**3 + x + 1', x).nthPowerRootsPoly(2))).toBe("Poly(-x**3 + 2*x**2 - x + 1, x, domain='ZZ')");
    expect(String(P('x**2 - 2', x).nthPowerRootsPoly(3))).toBe("Poly(x**2 - 8, x, domain='ZZ')");
    // SymPy prints Poly(x - 8, ...): its resultant(x - 2, x**3 - t, x) has the wrong sign
    // (t - 8; the Sylvester determinant is 8 - t), so the correct value is kept
    expect(String(P('x - 2', x).nthPowerRootsPoly(3))).toBe("Poly(-x + 8, x, domain='ZZ')");
  });
});

describe('generators and domains', () => {
  it('exclude, hasOnlyGens, homogenize, ltrim, reorder, replace', () => {
    expect(String(P('x + z', x, y, z).exclude())).toBe("Poly(x + z, x, z, domain='ZZ')");
    expect(String(P('3', x, y).exclude())).toBe("Poly(3, x, y, domain='ZZ')");
    expect(P('x*y + 1', x, y, z).hasOnlyGens(x, y)).toBe(true);
    expect(P('x*y + z', x, y, z).hasOnlyGens(x, y)).toBe(false);
    expect(String(P('x**3 + x*y + 1', x, y).homogenize(z))).toBe("Poly(x**3 + x*y*z + z**3, x, y, z, domain='ZZ')");
    expect(String(P('x**3 + x*y + 1', x, y).homogenize(y))).toBe("Poly(x**3 + x*y**2 + y**3, x, y, domain='ZZ')");
    expect(P('0', x).homogeneousOrder()).toBe(-Infinity);
    expect(P('x*y + x**2', x, y).homogeneousOrder()).toBe(2);
    for (const g of [y, 1, -2]) expect(String(P('y**2 + y*z**2', x, y, z).ltrim(g))).toBe("Poly(y**2 + y*z**2, y, z, domain='ZZ')");
    expect(String(P('x**2 + y', x, y).reorder(y, x))).toBe("Poly(y + x**2, y, x, domain='ZZ')");
    expect(String(P('x**2 + 1', x).replace(x, y))).toBe("Poly(y**2 + 1, y, domain='ZZ')");
  });
  it('termsGcd, deflate, toRing, toExact, retract, trunc, clearDenoms', () => {
    expect(show(P('x**6*y**2 + x**3*y', x, y).termsGcd())).toBe("[[3, 1], Poly(x**3*y + 1, x, y, domain='ZZ')]");
    expect(show(P('x**6*y**2 + x**3 + 1', x, y).deflate())).toBe("[[3, 2], Poly(x**2*y + x + 1, x, y, domain='ZZ')]");
    expect(show(P('5', x).deflate())).toBe("[[1], Poly(5, x, domain='ZZ')]");
    expect(String(Poly.from(parse('x + 2'), [x], { domain: 'QQ' }).toRing())).toBe("Poly(x + 2, x, domain='ZZ')");
    expect(String(P('1.5*x', x).toRing())).toBe("Poly(1.5*x, x, domain='RR')");
    expect(String(P('0.5*x + 2', x).toExact())).toBe("Poly(1/2*x + 2, x, domain='QQ')");
    expect(String(P('x + 2', x).toExact())).toBe("Poly(x + 2, x, domain='ZZ')");
    expect(String(Poly.from(parse('x + 1'), [x], { domain: 'QQ' }).retract())).toBe("Poly(x + 1, x, domain='ZZ')");
    expect(String(P('x + 1', x).retract(true))).toBe("Poly(x + 1, x, domain='QQ')");
    expect(String(P('x**3 + 3*x**2 + 5*x + 7', x).trunc(3))).toBe("Poly(x**3 - x + 1, x, domain='ZZ')");
    expect(String(P('-x**3 - 4*x + 7', x).trunc(5))).toBe("Poly(-x**3 + x + 2, x, domain='ZZ')");
    expect(show(P('x/2 + 1/3', x).clearDenoms())).toBe("[6, Poly(3*x + 2, x, domain='QQ')]");
    expect(show(P('x/2 + 1/3', x).clearDenoms(true))).toBe("[6, Poly(3*x + 2, x, domain='ZZ')]");
  });
  it('modulus, eject, inject, norm, lift', () => {
    expect(P('x**2 + 1', x).setModulus(5).getModulus()).toBe(5n);
    expect(() => P('x**2 + 1', x).getModulus()).toThrow(sj.DomainError);
    expect(String(P('x**2 + 7*x - 6', x).setModulus(5))).toBe('Poly(x**2 + 2*x - 1, x, modulus=5)');
    expect(() => P('x/2', x).setModulus(5)).toThrow(sj.DomainError);
    const e = P('x**2*y + x*y**3 + x*y + 1', x, y).eject(y);
    expect(String(e)).toBe("Poly(y*x**2 + (y**3 + y)*x + 1, x, domain='ZZ[y]')");
    expect(String(e.inject())).toBe("Poly(x**2*y + x*y**3 + x*y + 1, x, y, domain='ZZ')");
    expect(String(e.inject({ front: true }))).toBe("Poly(y**3*x + y*x**2 + y*x + 1, y, x, domain='ZZ')");
    expect(String(P('x + 1', x).inject())).toBe("Poly(x + 1, x, domain='ZZ')");
    // the norm needs an algebraic field QQ<a>: over EX and ZZ_I SymPy raises DomainError
    expect(() => P('x**2 - sqrt(2)*x + 1', x).norm()).toThrow('ground domain must be algebraic');
    expect(() => P('x - I', x).norm()).toThrow(sj.DomainError);
    expect(String(P('x - I', x).lift())).toBe("Poly(x**2 + 1, x, domain='ZZ')");
    expect(String(P('x - I/2', x).lift())).toBe("Poly(x**2 + 1/4, x, domain='QQ')");
    // SymPy raises NotImplementedError (z is neither a leading nor a trailing generator) and DomainError
    expect(() => P('x*y', x, y).eject(z)).toThrow('can only eject front or back generators');
    expect(() => P('x*y*z', x, y, z).eject(y)).toThrow(sj.NotImplementedError);
    expect(() => P('x*y*z', x, y, z).eject(z, y)).toThrow(sj.NotImplementedError);
    expect(String(P('x*y*z', x, y, z).eject(y, z))).toBe("Poly(y*z*x, x, domain='ZZ[y,z]')");
    expect(String(P('x*y', x, y).eject())).toBe("Poly(x*y, x, y, domain='ZZ')");
    expect(() => P('x - 1', x).lift()).toThrow('computation can be done only in an algebraic domain');
    expect(() => P('x - sqrt(2)', x).lift()).toThrow(sj.DomainError);
    expect(() => P('x - 1', x).norm()).toThrow(sj.DomainError);
    // not implemented: more than three square roots (SymPy gives (x - 1)**16 expanded)
    expect(() => Poly.from(parse('x - 1'), [x], { domain: 'QQ<sqrt(2) + sqrt(3) + sqrt(5) + sqrt(7)>' }).norm()).toThrow('norm: unsupported coefficient field');
    expect(String(P('x/2', x).integrate())).toBe("Poly(1/4*x**2, x, domain='QQ')");
    expect(show(P('2*x**2 + 3*x + 1/2', x).makeMonicOverIntegersByScalingRoots())).toBe("[Poly(x**2 + 6*x + 4, x, domain='ZZ'), 4]");
    expect(() => P('a*x**2 + 1', x).makeMonicOverIntegersByScalingRoots()).toThrow(sj.DomainError);
  });
  it('termwise', () => {
    const p = P('x**2 + 20*x + 400', x);
    const q = (c: sj.Expr) => (c instanceof sj.Rational ? c.p : 0n);
    expect(String(p.termwise((m, c) => [m, q(c) % 10n === 0n ? sj.Rational.of(q(c) / 10n) : c]))).toBe("Poly(x**2 + 2*x + 40, x, domain='ZZ')");
    expect(String(p.termwise((_m, c) => sj.Rational.of(q(c) / 10n)))).toBe("Poly(2*x + 40, x, domain='ZZ')");
  });
});

describe('factorization, roots and decomposition', () => {
  it('sqfPart, gffList, decompose', () => {
    expect(String(P('x**3 - 3*x - 2', x).sqfPart())).toBe("Poly(x**2 - x - 2, x, domain='ZZ')");
    expect(String(P('-x**3 + 3*x + 2', x).sqfPart())).toBe("Poly(x**2 - x - 2, x, domain='ZZ')");
    expect(show(P('x**5 + 2*x**4 - x**3 - 2*x**2', x).gffList())).toBe("[[Poly(x, x, domain='ZZ'), 1], [Poly(x + 2, x, domain='ZZ'), 4]]");
    expect(show(P('2*x**2 + 2*x', x).gffList())).toBe("[[Poly(x + 1, x, domain='ZZ'), 2]]");
    expect(show(P('x**2/2 + x/2', x).gffList())).toBe("[[Poly(x + 1, x, domain='QQ'), 2]]");
    expect(() => P('0', x).gffList()).toThrow(sj.PolynomialError);
    expect(show(P('x**4 + 2*x**3 - x - 1', x).decompose())).toBe("[Poly(x**2 - x - 1, x, domain='ZZ'), Poly(x**2 + x, x, domain='ZZ')]");
    expect(show(P('x**6 + 2*x**3 + 3', x).decompose())).toBe("[Poly(x**2 + 2*x + 3, x, domain='ZZ'), Poly(x**3, x, domain='ZZ')]");
    expect(show(P('x**4 - 2*x**2 + x', x).decompose())).toBe("[Poly(x**4 - 2*x**2 + x, x, domain='ZZ')]");
    expect(show(P('x**4 + x**2/2 + 1', x).decompose())).toBe("[Poly(x**2 + 1/2*x + 1, x, domain='QQ'), Poly(x**2, x, domain='QQ')]");
  });
  it('factor and square-free lists', () => {
    expect(show(P('2*x**2 - 2', x).factorListInclude())).toBe("[[Poly(2*x - 2, x, domain='ZZ'), 1], [Poly(x + 1, x, domain='ZZ'), 1]]");
    expect(show(P('x**2 - 1', x).factorListInclude())).toBe("[[Poly(x - 1, x, domain='ZZ'), 1], [Poly(x + 1, x, domain='ZZ'), 1]]");
    expect(show(P('6', x).factorListInclude())).toBe("[[Poly(6, x, domain='ZZ'), 1]]");
    expect(show(P('2*(x - 1)**2*(x + 1)', x).sqfListInclude())).toBe("[[Poly(2*x + 2, x, domain='ZZ'), 1], [Poly(x - 1, x, domain='ZZ'), 2]]");
    expect(show(P('2*(x - 1)**3', x).sqfListInclude(true))).toBe("[[Poly(2, x, domain='ZZ'), 1], [Poly(1, x, domain='ZZ'), 2], [Poly(x - 1, x, domain='ZZ'), 3]]");
    expect(show(P('2*(x - 1)*(x + 1)**2', x).sqfListInclude())).toBe("[[Poly(2*x - 2, x, domain='ZZ'), 1], [Poly(x + 1, x, domain='ZZ'), 2]]");
    expect(show(P('(x - 1)**3*(x + 2)', x).sqfListAll(true))).toBe(
      "[1, [[Poly(x + 2, x, domain='ZZ'), 1], [Poly(1, x, domain='ZZ'), 2], [Poly(x - 1, x, domain='ZZ'), 3]]]",
    );
    expect(show(P('x**2 + a', x).sqfList())).toBe("[1, [[Poly(x**2 + a, x, domain='ZZ[a]'), 1]]]");
    expect(show(P('2*x**2 + 2*a', x).sqfList())).toBe("[2, [[Poly(x**2 + a, x, domain='ZZ[a]'), 1]]]");
    // a symbolic square (Yun's algorithm over ZZ[a])
    expect(show(P('x**2 + 2*a*x + a**2', x).sqfList())).toBe("[1, [[Poly(x + a, x, domain='ZZ[a]'), 2]]]");
  });
  it('Sturm sequences and real root counting', () => {
    expect(show(P('x**3 - 2*x**2 + x - 3', x).sturm())).toBe(
      "[Poly(x**3 - 2*x**2 + x - 3, x, domain='QQ'), Poly(3*x**2 - 4*x + 1, x, domain='QQ'), Poly(2/9*x + 25/9, x, domain='QQ'), Poly(-2079/4, x, domain='QQ')]",
    );
    expect(P('x**4 - 4', x).countRoots()).toBe(2);
    expect(P('x**4 - 4', x).countRoots(0, 2)).toBe(1);
    expect(P('x**4 - 4', x).countRoots(-1)).toBe(1);
    expect(P('x**3 - x', x).countRoots(undefined, 0)).toBe(2);
    expect(P('x**3 - x', x).countRoots(1, 3)).toBe(1);
    expect(P('(x - 1)**2*(x + 2)', x).countRoots()).toBe(2);
  });
  it('ground roots', () => {
    expect(show(P('x**2*(x - 1)**2*(x**2 + 1)', x).groundRoots())).toBe('[[1, 2], [0, 2]]');
    expect(show(P('x**3 - x**2', x).groundRoots())).toBe('[[1, 1], [0, 2]]');
    expect(show(P('x**2 - a**2', x).groundRoots())).toBe('[[a, 1], [-a, 1]]');
    expect(show(P('x**2 - 2', x).groundRoots())).toBe('[]');
    expect(show(P('x**2 - 2', x).groundRoots({ extension: true }))).toBe('[[-sqrt(2), 1], [sqrt(2), 1]]');
    expect(show(P('(x**2 - 2)**2', x).groundRoots({ extension: true }))).toBe('[[-sqrt(2), 2], [sqrt(2), 2]]');
  });
  it('roots with algebraic coefficients, root(i), which roots', () => {
    expect(show(P('x**2 - 2*sqrt(2)*x + 1', x).allRoots({ extension: true }))).toBe('[-1 + sqrt(2), 1 + sqrt(2)]');
    expect(show(P('x**2 - 2*sqrt(2)*x + 1', x).realRoots({ extension: true }))).toBe('[-1 + sqrt(2), 1 + sqrt(2)]');
    // roots(Poly(x**2 - sqrt(2)*x - 4)) = {-sqrt(2): 1, 2*sqrt(2): 1}
    expect(show(Poly.from(parse('x**2 - sqrt(2)*x - 4')).allRoots({ extension: true }))).toBe('[-sqrt(2), 2*sqrt(2)]');
    expect(show(P('x**2 - 4', x).allRoots({ extension: true }))).toBe('[-2, 2]');
    expect(show(P('x**2 - 2*I*x - 2', x).allRoots({ extension: true }))).toBe('[-1 + I, 1 + I]');
    expect(show(P('x**2 + 1', x).realRoots({ extension: true }))).toBe('[]');
    expect(String(P('x**3 - x', x).root(1))).toBe('0');
    const cands = [parse('-1'), parse('1'), sj.I, parse('2'), parse('1')];
    // SymPy raises OverflowError (which_real_roots) and keeps the non-root 2 (which_all_roots);
    // the exact roots among the candidates are returned
    expect(show(P('x**4 - 1', x).whichRealRoots(cands))).toBe('[-1, 1]');
    expect(show(P('x**4 - 1', x).whichAllRoots(cands))).toBe('[-1, 1, I]');
    const r = sj.rootof(parse('x**3 - x - 1'), 0);
    expect(show(P('x**3 - x - 1', x).whichRealRoots([r, parse('1')]))).toBe(show([r]));
  });
});

describe('isolating intervals', () => {
  it('Poly.intervals', () => {
    expect(show(P('(x**2 - 2)*(x - 1)**2*x', x).intervals())).toBe('[[[-2, -1], 1], [[0, 0], 1], [[1, 1], 2], [[1, 2], 1]]');
    expect(show(P('x**3 - 3*x + 1', x).intervals())).toBe('[[[-2, -1], 1], [[0, 1], 1], [[1, 2], 1]]');
    expect(show(P('x**2 - 2', x).intervals(R(1, 100)))).toBe('[[[-17/12, -24/17], 1], [[24/17, 17/12], 1]]');
    expect(show(P('(x - 1)*(x - 2)*(x - 3)*(x - 1/2)*(x + 5/3)', x).intervals())).toBe(
      '[[[-2, -1], 1], [[0, 1], 1], [[1, 1], 1], [[2, 2], 1], [[3, 3], 1]]',
    );
    expect(show(P('(x**2 - 2)*(x**2 - 201/100)', x).intervals())).toBe('[[[-10/7, -17/12], 1], [[-17/12, -7/5], 1], [[7/5, 17/12], 1], [[17/12, 10/7], 1]]');
    expect(show(P('(x**2 - 2)*(x**2 - 3)*(10*x - 14)**2', x).intervals())).toBe(
      '[[[-2, -3/2], 1], [[-3/2, -1], 1], [[7/5, 7/5], 2], [[7/5, 10/7], 1], [[3/2, 2], 1]]',
    );
  });
  it('Poly.refineRoot', () => {
    const p = P('x**2 - 2', x);
    expect(show(p.refineRoot(R(1), R(2), R(1, 100)))).toBe('[24/17, 17/12]');
    expect(show(p.refineRoot(R(-2), R(-1), R(1, 100)))).toBe('[-17/12, -24/17]');
    expect(show(p.refineRoot(R(1), R(2), undefined, 3))).toBe('[7/5, 3/2]');
    expect(show(p.refineRoot(R(1), R(2), R(1, 100), 2))).toBe('[4/3, 3/2]');
    expect(show(p.refineRoot(R(2), R(1), undefined, 1))).toBe('[1, 3/2]');
    expect(show(P('x**2 - 1', x).refineRoot(R(1), R(1)))).toBe('[1, 1]');
    expect(() => p.refineRoot(R(-2), R(2))).toThrow('Cannot refine a real root in (-2, 2)');
    expect(() => p.refineRoot(R(2), R(3))).toThrow('there should be exactly one root in (2, 3) interval');
  });
});

describe('further Poly cases', () => {
  it('division without auto, exquo, accessors', () => {
    expect(show(P('x**2 + 1', x).divAuto(P('2*x - 4', x), false))).toBe("[Poly(0, x, domain='ZZ'), Poly(x**2 + 1, x, domain='ZZ')]");
    expect(show(P('2*x**2 + 2', x).divAuto(P('2*x - 4', x), false))).toBe("[Poly(x + 2, x, domain='ZZ'), Poly(10, x, domain='ZZ')]");
    expect(String(P('x**2 + 1', x).rem(P('2*x - 4', x), false))).toBe("Poly(x**2 + 1, x, domain='ZZ')");
    expect(String(P('x**2 + 1', x).quo(P('2*x - 4', x), false))).toBe("Poly(0, x, domain='ZZ')");
    expect(show(P('x**2 + 1', x).divAuto(P('2*x', x)))).toBe("[Poly(1/2*x, x, domain='QQ'), Poly(1, x, domain='QQ')]");
    expect(() => P('x**2 + 1', x).exquo(P('x + 1', x))).toThrow(sj.ExactQuotientFailed);
    expect(() => P('x*y', x, y).allCoeffs()).toThrow(sj.PolynomialError);
    expect(show(P('0', x).allCoeffs())).toBe('[0]');
    expect(show(P('0', x).coeffs())).toBe('[0]');
    expect(String(P('0', x).LC())).toBe('0');
    expect(P('x**2*y', x, y).degree(1)).toBe(1);
    // y is not a generator (SymPy PolynomialError; the function degree(x**2, y) is 0)
    expect(() => P('x**2', x).degree(y)).toThrow('a valid generator expected, got y');
    // SymPy total_degree() of zero is 0; symjs keeps -oo like degree()
    expect(P('0', x, y).totalDegree()).toBe(-Infinity);
    expect(String(P('x + 1', x).sub(P('x', x)))).toBe("Poly(1, x, domain='ZZ')");
    expect(String(P('x + 1', x).sub(1))).toBe("Poly(x, x, domain='ZZ')");
    expect(String(P('x + 1', x).mul(P('x', x)))).toBe("Poly(x**2 + x, x, domain='ZZ')");
    expect(String(P('x + 1', x).mul(2))).toBe("Poly(2*x + 2, x, domain='ZZ')");
    expect(String(P('x**2*y', x, y).diff(y))).toBe("Poly(x**2, x, y, domain='ZZ')");
    expect(() => P('x*y', x, y).div(P('x', x, y))).toThrow(sj.PolynomialError);
    expect(String(P('x + 1', x).replace(y, z))).toBe("Poly(x + 1, x, domain='ZZ')");
    expect(P('x**2 - 2', x).countRoots(new sj.Float(0.5), 2)).toBe(1);
  });
  it('per and termwise', () => {
    const p = P('x', x);
    expect(String(p.per([[1, 2], [3]], { gens: [x, y] }))).toBe("Poly(x*y + 2*x + 3, x, y, domain='ZZ')");
    expect(String(p.per([5], { remove: 0 }))).toBe('5');
    expect(String(p.per([], { remove: 0 }))).toBe('0');
    expect(() => P('x*y', x, y).per([1, 2])).toThrow(sj.PolynomialError);
    expect(() => p.per(['q'])).toThrow(sj.SympifyError);
    expect(String(P('x + 1', x).termwise(() => 0))).toBe("Poly(0, x, domain='ZZ')");
  });
  it('printing and domains', () => {
    expect(String(Poly.from(parse('sin(x)**2 + 1')))).toBe("Poly((sin(x))**2 + 1, sin(x), domain='ZZ')");
    expect(String(Poly.from(parse('(x + 1)**2 + 1'), [parse('x + 1')]))).toBe("Poly(x**2 + 2*x + 2, x + 1, domain='ZZ[x]')");
    expect(String(P('x + a + b', x))).toBe("Poly(x + a + b, x, domain='ZZ[a,b]')");
    expect(String(Poly.from(parse('x**2 + 1'), [x], { pure: true }))).toBe("PurePoly(x**2 + 1, x, domain='ZZ')");
    expect(String(Poly.from(parse('pi*x')))).toBe("Poly(x*pi, x, pi, domain='ZZ')");
    expect(String(P('x + I/2', x))).toBe("Poly(x + I/2, x, domain='QQ_I')");
  });
  it('decomposition, square-free lists and roots', () => {
    expect(show(P('x**4 + x**2', x).decompose())).toBe("[Poly(x**2 + x, x, domain='ZZ'), Poly(x**2, x, domain='ZZ')]");
    expect(show(P('x**4 + a*x**2', x).decompose())).toBe("[Poly(x**2 + a*x, x, domain='ZZ[a]'), Poly(x**2, x, domain='ZZ[a]')]");
    expect(show(P('2*(x - 1)**2', x).sqfListInclude())).toBe("[[Poly(2, x, domain='ZZ'), 1], [Poly(x - 1, x, domain='ZZ'), 2]]");
    expect(show(P('x - pi', x).allRoots())).toBe('[pi]');
    expect(show(P('x - pi*sqrt(2)', x).allRoots())).toBe('[sqrt(2)*pi]');
    // SymPy raises DomainError (the ground domain is not algebraic)
    expect(() => P('x - pi', x).norm()).toThrow(sj.DomainError);
    expect(() => P('x - pi*sqrt(2)', x).norm()).toThrow(sj.DomainError);
    // SymPy gives the roots as CRootOf of the degree-8 norm; symjs keeps the radicals
    // (the square root factored as SymPy's roots_quadratic does over EX: factor_terms(sqrt(2 - 4*I)/2) = sqrt(2)*sqrt(1 - 2*I)/2)
    expect(show(P('x**2 - sqrt(2)*x + I', x).allRoots({ extension: true }))).toBe(
      '[-sqrt(2)*re(sqrt(1 - 2*I))/2 + sqrt(2)/2 - sqrt(2)*I*im(sqrt(1 - 2*I))/2, sqrt(2)/2 + sqrt(2)*re(sqrt(1 - 2*I))/2 + sqrt(2)*I*im(sqrt(1 - 2*I))/2]',
    );
    const r = sj.rootof(parse('x**3 - x - 2'), 0);
    expect(show(P('x**3 - x - 1', x).whichAllRoots([r]))).toBe('[]');
  });
});

describe('square-free decomposition with symbolic coefficients (Yun over ZZ[a])', () => {
  it('contents and multiplicities', () => {
    // SymPy: (a, [(Poly(x**2 + 1, x, domain='ZZ[a]'), 1)]); symjs lists the symbolic content as a factor of degree 0
    expect(show(P('a*x**2 + a', x).sqfList())).toBe("[1, [[Poly(a, x, domain='ZZ[a]'), 1], [Poly(x**2 + 1, x, domain='ZZ[a]'), 1]]]");
    // SymPy: (1, [(Poly(x, x, domain='ZZ[a]'), 1), (Poly(x + a, x, domain='ZZ[a]'), 3)])
    expect(show(P('x*(x + a)**3', x).sqfList())).toBe("[1, [[Poly(x, x, domain='ZZ[a]'), 1], [Poly(x + a, x, domain='ZZ[a]'), 3]]]");
  });
});

describe('Poly methods', () => {
  it('diff with respect to the first generator', () => {
    expect(String(P('x**2*y', x, y).diff())).toBe("Poly(2*x*y, x, y, domain='ZZ')");
  });
});

describe('eject', () => {
  const z = new sj.Sym('z');
  it('generators into the ground domain', () => {
    expect(String(P('x*y*z + 1', x, y, z).eject(z))).toBe("Poly(z*x*y + 1, x, y, domain='ZZ[z]')");
    expect(String(P('x*y*z + 1', x, y, z).eject(y, z))).toBe("Poly(y*z*x + 1, x, domain='ZZ[y,z]')");
    // SymPy: DomainError Cannot eject generators over ZZ[z]
    expect(() => P('x*y*z + 1', x, y, z).eject(z).eject(y)).toThrow('Cannot eject generators over ZZ[z]');
  });
});

describe('norms, denominators, ground roots and root counting', () => {
  it('maxNorm and clearDenoms', () => {
    expect(String(P('x**2 + 3*x + 1', x).maxNorm())).toBe('3');
    // SymPy: (1, Poly(a/2*x + 1, x, domain='QQ[a]'))
    expect(show(P('a*x/2 + 1', x).clearDenoms())).toBe("[1, Poly(a/2*x + 1, x, domain='QQ[a]')]");
  });
  it('groundRoots with symbolic coefficients', () => {
    // SymPy: {0: 1} and {a: 1, -a: 1}
    expect(show(P('x**3 + a*x', x).groundRoots())).toBe('[[0, 1]]');
    expect(show(P('x**2 - a**2', x).groundRoots())).toBe('[[a, 1], [-a, 1]]');
  });
  it('countRoots bounds', () => {
    // SymPy converts the bounds to QQ: count_roots(1.0, 2.0) -> 1, count_roots(-2, 3/2) -> 2
    expect(P('x**2 - 2', x).countRoots(1.0, 2.0)).toBe(1);
    expect(P('x**2 - 2', x).countRoots(-2, parse('3/2'))).toBe(2);
    // SymPy: CoercionFailed expected `Rational` object, got pi
    expect(() => P('x**2 - 2', x).countRoots(parse('pi'), 4)).toThrow('expected a Rational, got pi');
    // over RR: SymPy Poly(x**2 - 2.0, x).count_roots() = 2
    expect(P('x**2 - 2.0', x).countRoots()).toBe(2);
    // SymPy raises TypeError with bounds over RR (mpf times PythonMPQ); the count of the exact polynomial is kept
    expect(P('x**2 - 2.0', x).countRoots(1.0, 2.0)).toBe(1);
    expect(P('x**2 - 2.0', x).countRoots(0, 3)).toBe(1);
  });
});

describe('factor and terms_gcd', () => {
  it('factor', () => {
    expect(String(sj.factor(parse('2*x**2 - 2')))).toBe('2*(x - 1)*(x + 1)');
    expect(String(sj.factor(parse('x/((x + 1)**2 - x**2 - 2*x)')))).toBe('x');
  });
  it.each([
    ['x*y**2/2 + x**2*y/2', 'x*y*(x + y)/2'],
    ['x/2 + 1', 'x/2 + 1'],
    ['x*y/2 + y**2', 'y*(x/2 + y)'],
    ['(x + 1)*(x*y/3 + y/6)', 'y*(2*x**2 + 3*x + 1)/6'],
    ['2*x*(x + 1) + 2*x*z', '2*x*(x + z + 1)'],
    ['x*z/2 + x*y/3', 'x*(2*y + 3*z)/6'],
  ])('terms_gcd(%s, clear=False)', (f, expected) => {
    expect(String(sj.termsGcd(parse(f), { clear: false }))).toBe(expected);
  });
});

describe('roots over extensions and generator order', () => {
  it('complex conjugate roots', () => {
    // Poly(x**2 + 1).all_roots() -> [-I, I]
    expect(show(P('x**2 + 1', x).allRoots({ extension: true }))).toBe('[-I, I]');
    expect(show(P('x**2 + 2*x + 5', x).allRoots({ extension: true }))).toBe('[-1 - 2*I, -1 + 2*I]');
    // roots(x**2 + sqrt(2)): {-2**(1/4)*I: 1, 2**(1/4)*I: 1}, ordered by the imaginary part
    expect(show(P('x**2 + sqrt(2)', x).allRoots({ extension: true }))).toBe('[-2**(1/4)*I, 2**(1/4)*I]');
  });
  it('generators with equal sort keys keep their order', () => {
    const d = new sj.Sym('x', { positive: true });
    expect(sj.sortGens([x, d])).toEqual([x, d]);
    expect(sj.sortGens([d, x])).toEqual([d, x]);
  });
});

describe('factor over an extension', () => {
  it.each([
    ['x**2 - sqrt(2)', 'sqrt(2)', 'x**2 - sqrt(2)'],
    ['x**3 - 2', '2**(1/3)', '(x - 2**(1/3))*(x**2 + 2**(1/3)*x + 2**(2/3))'],
    ['x**4 - 2', '2**(1/4)', '(x - 2**(1/4))*(x + 2**(1/4))*(x**2 + sqrt(2))'],
  ])('factor(%s, extension=%s)', (f, ext, expected) => {
    expect(String(sj.factor(parse(f), { extension: [parse(ext)] }))).toBe(expected);
  });
});

describe('factor_nc', () => {
  it('factors through commutative dummies when the expansion matches', () => {
    expect(String(factorNc(expand(pow(add(x, A), 2))))).toBe('(x + A)**2');
    expect(String(factorNc(expand(mul(add(x, A), add(x, B)))))).toBe('(x + A)*(x + B)');
  });
});

describe('factor keeps signs and content (regression)', () => {
  it('univariate and multivariate', async () => {
    const { factor } = await import('../../src');
    expect(str(factor(P2('-3*x**2 + x')))).toBe('-x*(3*x - 1)');
    expect(str(factor(P2('-3*x**2 + x*y + x')))).toBe('-x*(3*x - y - 1)');
    expect(str(factor(P2('-3*x + y + 1')))).toBe('-3*x + y + 1');
  });
});

describe('factor over GF(p)', () => {
  it('matches SymPy factor(f, modulus=p)', async () => {
    const { factor } = await import('../../src');
    const cases: [string, number, string][] = [
      ['x**2 + 1', 2, '(x + 1)**2'],
      ['x**4 + 1', 3, '(x**2 - x - 1)*(x**2 + x - 1)'],
      ['x**6 - 1', 7, '(x - 3)*(x - 2)*(x - 1)*(x + 1)*(x + 2)*(x + 3)'],
      ['x**5 + x + 1', 2, '(x**2 + x + 1)*(x**3 + x**2 + 1)'],
      ['3*x**3 + 2*x + 1', 5, '-2*(x**3 - x + 2)'],
      ['x**8 + x**4', 2, 'x**4*(x + 1)**4'],
      ['x**9 - x', 3, 'x*(x - 1)*(x + 1)*(x**2 + 1)*(x**2 - x - 1)*(x**2 + x - 1)'],
    ];
    for (const [f, p, want] of cases) expect(sstr(factor(parse(f), { modulus: p }))).toBe(want);
  });
});

describe('roots of polynomials with algebraic coefficients', () => {
  it('uses the norm polynomial like SymPy', async () => {
    const { Poly } = await import('../../src');
    const x = symbols('x')[0];
    expect(Poly.from(parse('x**2 + I*x - 1'), [x]).allRoots().map((e) => sstr(e))).toEqual(['CRootOf(x**4 - x**2 + 1, 0)', 'CRootOf(x**4 - x**2 + 1, 2)']);
    expect(Poly.from(parse('sqrt(2)*x**3 + x**2 - 1'), [x]).realRoots().map((e) => sstr(e))).toEqual(['sqrt(2)/2']);
  });
});

describe('Poly lift, eject and inject', () => {
  it('match SymPy', async () => {
    const { Poly, expand } = await import('../../src');
    const [x, y] = symbols('x y');
    const show = (p: { asExpr(): unknown; gens: readonly unknown[]; domain: string }) => `${sstr(expand(p.asExpr() as never))} | ${p.gens.map((g) => sstr(g as never)).join(',')} | ${p.domain}`;
    expect(show(Poly.from(parse('x**2 + I*x - 1'), [x]).lift())).toBe('x**4 - x**2 + 1 | x | ZZ');
    const f = Poly.from(parse('x**2*y + x*y**3 + x*y + 1'), [x, y]);
    expect(show(f.eject(x))).toBe('x**2*y + x*y**3 + x*y + 1 | y | ZZ[x]');
    expect(show(f.eject(x).inject())).toBe('x**2*y + x*y**3 + x*y + 1 | y,x | ZZ');
    expect(show(f.eject(x).inject({ front: true }))).toBe('x**2*y + x*y**3 + x*y + 1 | x,y | ZZ');
  });
});

describe('polynomial helpers and systems with irrational solutions', () => {
  it('match SymPy', async () => {
    const { Poly, sqfNorm, solvePolySystem, sqrt: rt } = await import('../../src');
    const [x, y, z] = symbols('x y z');
    expect(String(Poly.from(parse('x**2 + 2*x + sqrt(3)'), [], { domain: 'R' }))).toBe("Poly(1.0*x**2 + 2.0*x + 1.73205080756888, x, domain='RR')");
    expect(sqfNorm(parse('x**2+1'), x, [rt(3)]).map(String)).toEqual(['1', 'x**2 - 2*sqrt(3)*x + 4', 'x**4 - 4*x**2 + 16']);
    expect(String(Poly.from(parse('x - sqrt(2)'), [x], { domain: 'QQ<sqrt(2) + sqrt(3)>' }).norm())).toBe("Poly(x**4 - 4*x**2 + 4, x, domain='QQ')");
    const [g, s] = Poly.from(parse('x**2/2 + x/4 + 1/8'), [x]).makeMonicOverIntegersByScalingRoots();
    expect([String(g), sstr(s)]).toEqual(["Poly(x**2 + 2*x + 4, x, domain='ZZ')", '4']);
    const sols = solvePolySystem(['x**2+y+z-1', 'x+y**2+z-1', 'x+y+z**2-1'].map((e) => parse(e)), [x, y, z]).map((t) => t.map((e) => sstr(e)).join(','));
    expect(sols).toEqual(['0,0,1', '0,1,0', '1,0,0', '-1 + sqrt(2),-1 + sqrt(2),-1 + sqrt(2)', '-sqrt(2) - 1,-sqrt(2) - 1,-sqrt(2) - 1']);
  });
});

describe('minimal polynomials, line integrals and ITE conditions', () => {
  it('match SymPy', async () => {
    const { minimalPolynomial, Curve, lineIntegrate, Rational, Piecewise, Lt, Gt } = await import('../../src');
    const [x, y, t] = symbols('x y t');
    expect(['sqrt(2)-1', 'sqrt(2)+sqrt(3)', '1+I', '(1+sqrt(5))/2', 'sqrt(3)/2'].map((s) => sstr(minimalPolynomial(parse(s), x)))).toEqual([
      'x**2 + 2*x - 1', 'x**4 - 10*x**2 + 1', 'x**2 - 2*x + 2', 'x**2 - x - 1', '4*x**2 - 3',
    ]);
    const C = Curve([parse('exp(t) + 1'), parse('exp(t) - 1')], [t, Rational.of(0), parse('log(2)')]);
    expect(sstr(lineIntegrate(parse('x + y'), C, [x, y]))).toBe('3*sqrt(2)');
    const cond = Piecewise([Gt(y, 2), Lt(x, 0)], [Gt(y, 3), true]);
    expect(sstr(Piecewise([1, cond as never]))).toBe('Piecewise((1, ITE(x < 0, y > 2, y > 3)))');
  });
});

describe('factor on expressions (SymPy _symbolic_factor) and factor_list', () => {
  const p = new Sym('p', { positive: true });
  const G = (e: string, opts: Parameters<typeof sj.factor>[1] = {}) => String(sj.factor(parse(e, { symbols: { p } }), opts));
  it.each([
    ['1/x + 1/y', '(x + y)/(x*y)'],
    ['m + n*m', 'm*(n + 1)'],
    ['sqrt(2)*(x*y + x + y + 1)', 'sqrt(2)*(x + 1)*(y + 1)'],
    ['1/(x + 1) + 1/(x**2 - 1)', 'x/((x - 1)*(x + 1))'],
    ['x**2*exp(2*y) - 1', '(x*exp(y) - 1)*(x*exp(y) + 1)'],
    ['x**3 - x*exp(-2*y)', 'x*(x*exp(y) - 1)*(x*exp(y) + 1)*exp(-2*y)'],
    ['l**2 - (f(1) + 2)*l + 2*f(1)', '(l - 2)*(l - f(1))'],
    ['x**2 - 2*pi*x + pi**2', '(x - pi)**2'],
    ['x**2 - 2*sqrt(2)*x + 2', 'x**2 - 2*sqrt(2)*x + 2'],
    ['x*sqrt(2) + sqrt(2)*y + sqrt(3)*x + sqrt(3)*y', '(sqrt(2) + sqrt(3))*(x + y)'],
    ['I*x + I', 'I*(x + 1)'],
    ['sqrt(p**2*x + p**2)', 'p*sqrt(x + 1)'],
    ['sqrt(p*x + p)', 'sqrt(p)*sqrt(x + 1)'],
    ['x**2 + 2*x*y + y**2 - 2', 'x**2 + 2*x*y + y**2 - 2'],
    ['x**2 + 2*x*y + y**2 - 1', '(x + y - 1)*(x + y + 1)'],
    ['sqrt(-x - 1)', 'sqrt(-x - 1)'],
    ['sqrt(2*x + 2)', 'sqrt(2)*sqrt(x + 1)'],
    ['sqrt(-2*x - 2)', 'sqrt(2)*sqrt(-x - 1)'],
    ['(x**2 - 1)**y', '((x - 1)*(x + 1))**y'],
    ['(2*x + 2)**y', '2**y*(x + 1)**y'],
    ['2**x*(x**2 - 1)', '2**x*(x - 1)*(x + 1)'],
    ['-x**2*y - x*y', '-x*y*(x + 1)'],
    ['x**3 - a*x**2 - a**2*x + a**3', '(-a + x)**2*(a + x)'],
    ['sin(x)**2 - 2*sin(x) + 1', '(sin(x) - 1)**2'],
    ['exp(x - y)', 'exp(x)*exp(-y)'],
    ['sin((x + 1)**2)', 'sin(x**2 + 2*x + 1)'],
    ['x + exp(-y)', '(x*exp(y) + 1)*exp(-y)'],
  ])('factor(%s) = %s', (e, expected) => {
    expect(G(e)).toBe(expected);
  });
  it('options', () => {
    // SymPy factor(x + exp(-y), fraction=False)
    expect(G('x + exp(-y)', { fraction: false })).toBe('x + exp(-y)');
    expect(G('exp(x - y)*(x + 1)', { fraction: false })).toBe('(x + 1)*exp(x)*exp(-y)');
    // SymPy factor(sin(x**2 + 2*x + 1) + x, deep=True)
    expect(G('sin(x**2 + 2*x + 1) + x', { deep: true })).toBe('x + sin((x + 1)**2)');
    // Floats: SymPy factors over RR (2.0*(x + 1)); symjs leaves them
    expect(G('2.0*x + 2.0')).toBe('2.0*x + 2.0');
  });
  it('non-commutative expressions go to factor_nc', () => {
    const A = new Sym('A', { commutative: false });
    const B = new Sym('B', { commutative: false });
    // SymPy factor(A*B - B*A + x*A) = x*A + A*B - B*A
    expect(String(sj.factor(add(mul(A, B), mul(-1, B, A), mul(x!, A))))).toBe('x*A + A*B - B*A');
  });
  it('factor_list', () => {
    const fl = (e: string, ...g: sj.Expr[]) => show(sj.factorList(parse(e), g.length ? g : undefined));
    expect(fl('(x - sqrt(a))*(x - 1)', x!)).toBe('[1, [[x - 1, 1], [-sqrt(a) + x, 1]]]');
    expect(fl('x**2 - 2*sqrt(2)*x + 2', x!)).toBe('[1, [[x**2 - 2*sqrt(2)*x + 2, 1]]]');
    expect(fl('x**2 - 2*sqrt(2)*x + 2')).toBe('[1, [[x**2 - 2*sqrt(2)*x + 2, 1]]]');
    expect(fl('2*x*y + 2*y', x!)).toBe('[2*y, [[x + 1, 1]]]');
    expect(fl('y**2*(x - y)*(x + y)', x!)).toBe('[y**2, [[x - y, 1], [x + y, 1]]]');
    expect(fl('x*y + x')).toBe('[1, [[x, 1], [y + 1, 1]]]');
    // the domains ZZ, ZZ[sqrt(a)], ZZ[sqrt(b)] order the factors (SymPy _sorted_factors)
    expect(fl('(x - 1)*(x - sqrt(a))*(x - sqrt(b))', x!)).toBe('[1, [[x - 1, 1], [-sqrt(a) + x, 1], [-sqrt(b) + x, 1]]]');
    expect(fl('2*sqrt(2)*x - 2*sqrt(2)')).toBe('[2*sqrt(2), [[x - 1, 1]]]');
    expect(fl('x/2 + y/3')).toBe('[1/6, [[3*x + 2*y, 1]]]');
    expect(fl('(x**2 - 1)**3')).toBe('[1, [[x - 1, 3], [x + 1, 3]]]');
    expect(fl('x**2 - a**2', x!)).toBe('[1, [[-a + x, 1], [a + x, 1]]]');
    expect(fl('x**2 - a', x!)).toBe('[1, [[-a + x**2, 1]]]');
    expect(() => sj.factorList(parse('1/x'))).toThrow('a polynomial expected, got 1/x');
    // SymPy: PolynomialError: sin(x) contains an element of the set of generators.
    expect(() => sj.factorList(parse('sin(x) + x'), [x!])).toThrow('sin(x) contains an element of the set of generators.');
    expect(() => sj.factorList(parse('sin(x)*(x + 1)'), [x!])).toThrow('sin(x) contains an element of the set of generators.');
    expect(() => sj.factorList(parse('x*sin(x) + 1'), [x!])).toThrow('sin(x) contains an element of the set of generators.');
    // SymPy raises TypeError (a PolyElement product) for x + 2.5 with the generator x
    expect(() => sj.factorList(parse('x + 2.5'), [x!])).toThrow('x + 2.5 contains an element of the set of generators.');
  });
  it('factor_list with symbolic and fractional multiplicities (SymPy 1.14)', () => {
    const p = new Sym('p', { positive: true });
    const n = new Sym('n', { integer: true });
    const syms = { x: x!, y: y!, z: z!, p, n };
    const fl = (e: string, ...g: sj.Expr[]) => show(sj.factorList(parse(e, { symbols: syms }), g));
    expect(fl('(x + 1)**y')).toBe('[1, [[x + 1, y]]]');
    expect(fl('sqrt(x + 1)*(x - 2)**3')).toBe('[1, [[x + 1, 1/2], [x - 2, 3]]]');
    expect(fl('2*(x**2 - 1)**y')).toBe('[2, [[x**2 - 1, y]]]');
    expect(fl('(x + 1)**2*(x + 3)')).toBe('[1, [[x + 3, 1], [x + 1, 2]]]');
    expect(fl('exp(x)*(x + 1)')).toBe('[1, [[exp(x), 1], [x + 1, 1]]]');
    expect(fl('exp(2*x) - 1')).toBe('[1, [[exp(x) - 1, 1], [exp(x) + 1, 1]]]');
    expect(fl('(x**2 - 1)**(1/3)')).toBe('[1, [[x**2 - 1, 1/3]]]');
    expect(fl('(x*y)**z')).toBe('[1, [[x*y, z]]]');
    expect(fl('sqrt(2*x + 2)')).toBe('[sqrt(2), [[x + 1, 1/2]]]');
    expect(fl('(x + 1)**(2*y)')).toBe('[1, [[x + 1, 2*y]]]');
    expect(fl('(-x - 1)**y')).toBe('[1, [[-x - 1, y]]]');
    expect(fl('-(x + 1)**y')).toBe('[-1, [[x + 1, y]]]');
    expect(fl('(x - 1)**y*(x + 1)**y')).toBe('[1, [[x - 1, y], [x + 1, y]]]');
    expect(fl('4*(x**2 + 2*x + 1)**(1/2)')).toBe('[4, [[x**2 + 2*x + 1, 1/2]]]');
    expect(fl('(x*(x + 1))**(5/2)')).toBe('[1, [[x**2 + x, 5/2]]]');
    expect(fl('(exp(x) + 1)**y')).toBe('[1, [[exp(x) + 1, y]]]');
    expect(fl('(sin(x)**2 - 1)**y')).toBe('[1, [[sin(x)**2 - 1, y]]]');
    expect(fl('x**2*sqrt(y)')).toBe('[1, [[y, 1/2], [x, 2]]]');
    expect(fl('x**(1/3)*y')).toBe('[1, [[x, 1/3], [y, 1]]]');
    expect(fl('(x**2 - 1)**y*(x**3 + 1)**y')).toBe('[1, [[x**2 - 1, y], [x**3 + 1, y]]]');
    expect(fl('(x + 1)*(x**2 + x)**y')).toBe('[1, [[x + 1, 1], [x**2 + x, y]]]');
    expect(fl('sqrt(-2*x - 2)')).toBe('[sqrt(2), [[-x - 1, 1/2]]]');
    expect(fl('I*(x + 1)')).toBe('[I, [[x + 1, 1]]]');
    // positive factors get the exponent one by one; an integer symbol goes to every factor
    expect(fl('((p + 1)*(x + 1))**y')).toBe('[1, [[p + 1, y], [x + 1, y]]]');
    expect(fl('(p*(x + 1))**y')).toBe('[1, [[p, y], [x + 1, y]]]');
    expect(fl('(p*(x + 1))**y*(p*(x + 2))**y')).toBe('[1, [[p, 2*y], [x + 1, y], [x + 2, y]]]');
    expect(fl('(x**2 - 4)**n')).toBe('[1, [[x - 2, n], [x + 2, n]]]');
    expect(fl('(x**2 - 1)**(2*n)')).toBe('[1, [[x - 1, 2*n], [x + 1, 2*n]]]');
    // with gens: the parts free of them with an integer exponent are the content
    expect(fl('(x + 1)**y*(z + 1)', x!)).toBe('[z + 1, [[x + 1, y]]]');
    expect(fl('(z + 1)**y*(x + 1)', x!)).toBe('[1, [[z + 1, y], [x + 1, 1]]]');
    expect(fl('(2*z + 2)**y*(x + 1)', x!)).toBe('[1, [[2*z + 2, y], [x + 1, 1]]]');
    expect(fl('sqrt(z)*x', x!)).toBe('[1, [[z, 1/2], [x, 1]]]');
    expect(fl('exp(y)*(x + 1)/(y + 1)', x!)).toBe('[exp(y)/(y + 1), [[x + 1, 1]]]');
    expect(fl('((z + 1)*(x + 1))**y', x!)).toBe('[1, [[x*(z + 1) + z + 1, y]]]');
    expect(fl('((z + 1)*(x + 1)*(x - 1))**y', x!)).toBe('[1, [[x**2*(z + 1) - z - 1, y]]]');
    expect(fl('2**y*(x + 1)*(x - 1)*(x**2 + 1)**3', x!)).toBe('[1, [[2, y], [x - 1, 1], [x + 1, 1], [x**2 + 1, 3]]]');
    expect(fl('(x + 1)*(x*z + x + 1)', x!)).toBe('[1, [[x + 1, 1], [x*(z + 1) + 1, 1]]]');
    expect(fl('(x + 1)**y*(z + 1)**y', x!, z!)).toBe('[1, [[z + 1, y], [x + 1, y]]]');
    expect(fl('(z + 1)**n*(x + 1)', x!)).toBe('[1, [[z + 1, n], [x + 1, 1]]]');
  });
  it('factor_list where SymPy fails', () => {
    const p = new Sym('p', { positive: true });
    const n = new Sym('n', { integer: true });
    const fl = (e: string) => show(sj.factorList(parse(e, { symbols: { x: x!, y: y!, z: z!, p, n } })));
    // SymPy raises PolificationFailed (Cannot construct a polynomial from 2) for a number base
    expect(fl('2**x*(x**2 - 1)')).toBe('[1, [[2, x], [x - 1, 1], [x + 1, 1]]]');
    expect(fl('(2*x + 2)**n')).toBe('[1, [[2, n], [x + 1, n]]]');
    expect(fl('(-2*x - 2)**n')).toBe('[1, [[-2, n], [x + 1, n]]]');
    expect(fl('(2*p + 2)**y')).toBe('[1, [[2, y], [p + 1, y]]]');
    // SymPy appends the factor (1, y) when every factor is positive and fails on it
    expect(fl('(p + 1)**y*(x + 1)')).toBe('[1, [[x + 1, 1], [p + 1, y]]]');
    expect(fl('(p**2 + p)**y*p')).toBe('[1, [[p + 1, y], [p, y + 1]]]');
    // SymPy raises TypeError comparing the exponents (cannot determine truth value of Relational: y > 1)
    expect(fl('x**y*(x + 1)')).toBe('[1, [[x + 1, 1], [x, y]]]');
    expect(fl('(x - 1)**y*(x + 1)**y*(x + 2)**2')).toBe('[1, [[x + 2, 2], [x - 1, y], [x + 1, y]]]');
    expect(fl('(x + 1)**y*(x + 2)**z')).toBe('[1, [[x + 1, y], [x + 2, z]]]');
    expect(fl('exp(x)**y*exp(z)')).toBe('[1, [[exp(z), 1], [exp(x), y]]]');
    // SymPy raises PolificationFailed (Cannot construct a polynomial from 2.50000000000000)
    expect(fl('(x + 2.5)**y')).toBe('[1, [[x + 2.5, y]]]');
  });
  it('factor_list(frac=True)', () => {
    const fl = (e: string, ...g: sj.Expr[]) => show(sj.factorList(parse(e), g, { frac: true }));
    expect(fl('1/(x + 1)')).toBe('[1, [], [[x + 1, 1]]]');
    expect(fl('(x + 1)/(x - 1)**2')).toBe('[1, [[x + 1, 1]], [[x - 1, 2]]]');
    expect(fl('x/(2*y)')).toBe('[1/2, [[x, 1]], [[y, 1]]]');
    expect(fl('(x + 1)**y*exp(-x)/(x - 1)**2/2')).toBe('[1/2, [[x + 1, y]], [[exp(x), 1], [x - 1, 2]]]');
    expect(fl('sqrt(x)/(x + 1)**(3/2)')).toBe('[1, [[x, 1/2]], [[x + 1, 3/2]]]');
    expect(fl('1/(x + 1)**y')).toBe('[1, [], [[x + 1, y]]]');
    expect(fl('6/5')).toBe('[6/5, [], []]');
    expect(fl('(x + 1)**y/(z + 1)', x!)).toBe('[1/(z + 1), [[x + 1, y]], []]');
    // SymPy: PolynomialError: a polynomial expected, got (x + 1)**y/(x - 1)
    expect(() => sj.factorList(parse('(x + 1)**y/(x - 1)'), [], { frac: false })).toThrow('a polynomial expected, got (x + 1)**y/(x - 1)');
  });
  it('factorListInt keeps other exponents in the factor', () => {
    expect(show(factorListInt(parse('(x + 1)**y*(x - 1)**2')))).toBe('[1, [[x - 1, 2], [(x + 1)**y, 1]]]');
  });
  it('factor with an integer symbol exponent (SymPy 1.14)', () => {
    const n = new Sym('n', { integer: true });
    const Fn = (e: string) => String(sj.factor(parse(e, { symbols: { x: x!, n } })));
    expect(Fn('(x**2 - 4)**n')).toBe('(x - 2)**n*(x + 2)**n');
    expect(Fn('(2*x + 2)**n')).toBe('2**n*(x + 1)**n');
    expect(Fn('(-2*x - 2)**n')).toBe('(-2)**n*(x + 1)**n');
  });
});

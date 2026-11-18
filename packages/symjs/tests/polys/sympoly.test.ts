// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/polys/sympoly.ts: Poly methods and the top-level polynomial functions (gcd, degree, div, terms_gcd, horner, factor, ...); expected values from SymPy 1.14 (tuples written as [...]).

import { describe, expect, it, vi } from 'vitest';
import * as sj from '../../src';
import { add, expand, factorNc, mul, parse, pow, sstr, str, Sym, symbols } from '../../src';
import { factorListInt } from '../../src/polys/sympoly';

import algebraicRefs from './sympoly.algebraic.references.json';
import finitePseudoRefs from './finite-pseudo.references.json';

describe('finite-domain pseudo-division and resultants (SymPy 1.14)', () => {
  for (const row of finitePseudoRefs) it(`${row.f} by ${row.g} modulo ${row.modulus}`, () => {
    const gens = row.gens.map((s) => new Sym(s)), X = new Sym('x');
    const poly = (e: sj.ExprLike): sj.Poly => Poly.from(e, gens, { modulus: row.modulus });
    const f = poly(parse(row.f)), g = poly(parse(row.g)), [q, r] = f.pdiv(g);
    expect([String(q.asExpr()), String(r.asExpr())]).toEqual([row.q, row.r]);
    expect([q.domain, r.domain]).toEqual([f.domain, f.domain]);
    expect(f.pquo(g).equals(q)).toBe(true);
    expect(f.prem(g).equals(r)).toBe(true);
    const lc = Poly.from(g.asExpr(), [X]).LC();
    const scale = poly(pow(lc, Math.max(0, f.degree(X) - g.degree(X) + 1)));
    expect(f.mul(scale).equals(q.mul(g).add(r))).toBe(true);
    if (row.resultant !== undefined) expect(String(f.resultant(g))).toBe(row.resultant);
  });
  it('rejects a zero polynomial divisor and preserves exact quotient errors', () => {
    const f = Poly.from(parse('x**2+1'), [new Sym('x')], { modulus: 5 });
    expect(() => f.pdiv(f.sub(f))).toThrow(RangeError);
    expect(() => f.pexquo(f.add(1))).toThrow(sj.ExactQuotientFailed);
    expect(f.pexquo(f).asExpr().equals(1)).toBe(true);
  });
});

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
    // SymPy: (y, 1 - y**2)
    expect(show(sj.div(E('x*y + 1'), E('x + y')))).toBe('[y, 1 - y**2]');
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
    expect(F('sin(x)**2 - 2', { extension: s2 })).toBe('(sin(x) - sqrt(2))*(sin(x) + sqrt(2))');
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
    expect(String(P('x + y + z', x, y, z).reorder({ wrt: z }))).toBe("Poly(z + x + y, z, x, y, domain='ZZ')");
    expect(String(P('x + y + z', x, y, z).reorder({ wrt: [y, new Sym('w')] }))).toBe("Poly(y + x + z, y, x, z, domain='ZZ')");
    // SymPy PolynomialError: the generators can only be permuted; a left generator must not occur
    expect(() => P('x + y', x, y).reorder(x, z)).toThrow(sj.PolynomialError);
    expect(() => P('x + y', x, y).reorder(x)).toThrow(sj.PolynomialError);
    expect(() => P('x + y', x, y).reorder(x, x)).toThrow(sj.PolynomialError);
    expect(() => P('x*y**2 + y**2', x, y).ltrim(y)).toThrow(sj.PolynomialError);
    expect(() => P('x*y - x', x, y).ltrim(-1)).toThrow(sj.PolynomialError);
    for (const g of [2, -3, z]) expect(() => P('x*y', x, y).ltrim(g)).toThrow(sj.PolynomialError);
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
    expect(Poly.from(parse('x - 1'), [x], { domain: 'QQ<sqrt(2) + sqrt(3) + sqrt(5) + sqrt(7)>' }).norm().equals(P('(x-1)**16',x))).toBe(true);
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
    // SymPy: (Poly(y, x, y, domain='ZZ'), Poly(0, x, y, domain='ZZ')) (over QQ without auto)
    expect(String(P('x*y', x, y).div(P('x', x, y)))).toBe("Poly(y, x, y, domain='QQ'),Poly(0, x, y, domain='QQ')");
    // SymPy raises ValueError: univariate polynomial expected
    expect(() => P('x*y', x, y).sturm()).toThrow(sj.PolynomialError);
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
    expect(P('0', x).countRoots()).toBe(0);
    expect(P('7', x).countRoots()).toBe(0);
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

describe('multivariate division (SymPy dmp_ff_div)', () => {
  const P = (s: string) => sj.Poly.from(parse(s), [x, y]);
  it('divides recursively in the first generator', () => {
    const cases: [string, string, string][] = [
      ['x**2*y + x + y', 'x*y + 1', "[Poly(x, x, y, domain='ZZ'), Poly(y, x, y, domain='ZZ')]"],
      ['x**2 + y**2', 'x + y', "[Poly(x - y, x, y, domain='ZZ'), Poly(2*y**2, x, y, domain='ZZ')]"],
      ['x**2*y + 1', '2*x + y', "[Poly(1/2*x*y - 1/4*y**2, x, y, domain='QQ'), Poly(1/4*y**3 + 1, x, y, domain='QQ')]"],
      ['x*y**2 + 3', 'x*y', "[Poly(y, x, y, domain='ZZ'), Poly(3, x, y, domain='ZZ')]"],
      // the leading coefficient 3 of the remainder is not divisible by 2*y: the division stops
      ['2*x**2*y + 3*x', '2*x*y', "[Poly(x, x, y, domain='ZZ'), Poly(3*x, x, y, domain='ZZ')]"],
      ['x**2*y/2 + 1', 'x + y', "[Poly(1/2*x*y - 1/2*y**2, x, y, domain='QQ'), Poly(1/2*y**3 + 1, x, y, domain='QQ')]"],
    ];
    for (const [f, g, want] of cases) expect(`[${P(f).divAuto(P(g)).map(String).join(', ')}]`).toBe(want);
    expect(String(P('x**2*y/2 + 1').div(P('x/2 + y/3')))).toBe("Poly(x*y - 2/3*y**2, x, y, domain='QQ'),Poly(2/9*y**3 + 1, x, y, domain='QQ')");
    expect(() => P('x*y').div(P('0'))).toThrow(RangeError);
  });
  it('div of expressions, with the generators given', () => {
    // SymPy: div(x**2*y + 1, x*y + x, y, x) -> (x, 1 - x**2)
    expect(String(sj.polyDiv(parse('x**2*y + 1'), parse('x*y + x'), [y, x]))).toBe('x,1 - x**2');
    expect(String(sj.polyDiv(parse('x**2*y + x + y'), parse('x*y + 1')))).toBe('x,y');
    expect(() => sj.polyDiv(parse('3'), parse('2'))).toThrow(sj.PolynomialError);
  });
});

describe('PurePoly, asPoly, invert, gcdList, lcmList and sqf (SymPy polytools)', () => {
  it('PurePoly compares equal over other generators', () => {
    const p = sj.PurePoly(E('x**2 + 1'));
    expect(String(p)).toBe("PurePoly(x**2 + 1, x, domain='ZZ')");
    expect(p.equals(sj.PurePoly(E('y**2 + 1')))).toBe(true);
    expect(Poly.from(E('x**2 + 1')).equals(Poly.from(E('y**2 + 1')))).toBe(false);
    expect(Poly.from(E('x**2 + 1')).equals(Poly.from(E('x**2 + 1')))).toBe(true);
    expect(Poly.from(E('x**2 + 1')).equals(E('x**2 + 1'))).toBe(true);
    expect(Poly.from(E('x**2 + 1')).equals(E('x**2 + 2'))).toBe(false);
    expect(Poly.from(E('x**2 + 1')).equals(Poly.from(E('x**2 + y'), [x, y]))).toBe(false);
    expect(Poly.from(E('x**2 + 1')).equals(Poly.from(E('x**3 + 1')))).toBe(false);
    expect(Poly.from(E('x**2 + 1')).equals(Poly.from(E('x**2 + x + 1')))).toBe(false);
    expect(sj.PurePoly(E('x**2 + 1')).equals(Poly.from(E('x**2 + y'), [x, y]))).toBe(false);
    expect(Poly.from(E('x**2 + 1'), [x]).equals(sj.sin(x))).toBe(false);
    expect(String(sj.PurePoly(E('x**2 + y'), x))).toBe("PurePoly(x**2 + y, x, domain='ZZ[y]')");
    expect(String(sj.PurePoly(Poly.from(E('x**2*y + 1'), [x, y])))).toBe("PurePoly(x**2*y + 1, x, y, domain='ZZ')");
  });
  it('asPoly', () => {
    expect(String(sj.asPoly(E('x**2 + x*y')))).toBe("Poly(x**2 + x*y, x, y, domain='ZZ')");
    expect(String(sj.asPoly(E('x**2 + x*y'), x))).toBe("Poly(x**2 + y*x, x, domain='ZZ[y]')");
    // SymPy (x**2 + sin(y)).as_poly(x, y) is None
    expect(sj.asPoly(E('x**2 + sin(y)'), x, y)).toBe(sj.NoMatch);
    expect(sj.asPoly(mul(A, B))).toBe(sj.NoMatch);
  });
  it('invert', () => {
    expect(String(sj.invert(E('x**2 - 1'), E('2*x - 1')))).toBe('-4/3');
    expect(String(sj.invert(3, 7))).toBe('5');
    expect(String(sj.invert(E('x**2'), E('x + 1')))).toBe('1');
    expect(String(sj.invert(Poly.from(E('x**2 + 1')), E('x**3 + 2'), x))).toBe('-x**2/5 - 2*x/5 + 1/5');
    expect(() => sj.invert(E('x**2 - 1'), E('x - 1'))).toThrow(sj.NotInvertible);
    expect(() => sj.invert(E('x*y'), E('x + y'))).toThrow(sj.PolynomialError);
    expect(() => sj.invert(A, B)).toThrow('non-commutative expressions are not supported');
  });
  it('gcdList and lcmList', () => {
    const fs = [E('x**3 - 1'), E('x**2 - 1'), E('x**2 - 3*x + 2')];
    expect(String(sj.gcdList(fs))).toBe('x - 1');
    expect(String(sj.lcmList(fs))).toBe('x**5 - x**4 - 2*x**3 - x**2 + x + 2');
    expect([sj.gcdList([12, 18, 30]), sj.gcdList([]), sj.gcdList([R(1, 2), R(3, 4)]), sj.gcdList([E('x*y**2'), E('x**2*y')])].map(String)).toEqual(['6', '0', '1/4', 'x*y']);
    expect([sj.lcmList([4, 6, 10]), sj.lcmList([])].map(String)).toEqual(['60', '1']);
  });
  it('sqf', () => {
    expect(String(sj.sqf(E('2*x**5 + 16*x**4 + 50*x**3 + 76*x**2 + 56*x + 16')))).toBe('2*(x + 1)**2*(x + 2)**3');
    expect(String(sj.sqf(E('x**2 - 2*x + 1')))).toBe('(x - 1)**2');
    // the factors of one multiplicity are multiplied out: SymPy sqf(x**2 - 1) is x**2 - 1
    expect(String(sj.sqf(E('(x**2 - 1)/(x + 1)**2')))).toBe('(x**2 - 1)/(x + 1)**2');
    expect(String(sj.sqf(E('x**2*y**2 + 2*x*y + 1')))).toBe('(x*y + 1)**2');
    expect(String(sj.sqf(12))).toBe('12');
    expect(String(sj.sqf(E('x**3 - x**2')))).toBe('x**2*(x - 1)');
    // a polynomial gives a polynomial (SymPy sqf(Poly(x**3 - x**2)))
    expect(String(sj.sqf(Poly.from(E('x**3 - x**2'))))).toBe("Poly(x**3 - x**2, x, domain='ZZ')");
  });
});


describe('algebraic and Gaussian polynomial domains (SymPy 1.14)', () => {
  for (const row of algebraicRefs.construction) it(`Poly(${row.expr}, ${JSON.stringify(row.options)})`, () => {
    const options = row.options;
    const p = Poly.from(parse(row.expr), row.gens.map((g) => new Sym(g)), {
      ...('gaussian' in options ? { gaussian: options.gaussian } : {}),
      ...('domain' in options ? { domain: options.domain } : {}),
      ...('extension' in options ? { extension: typeof options.extension === 'string' ? parse(options.extension) : options.extension } : {}),
    });
    expect(String(p)).toBe(row.expected);
    if (row.norm !== null) expect(String(p.norm())).toBe(row.norm);
  });
  for (const row of algebraicRefs.factors) it(`factors ${row.expr} over QQ<${row.ext}>`, () => {
    const result=sj.factor(parse(row.expr),{extension:[parse(row.ext)]});
    expect(String(result)).toBe(row.expected);
    expect(sj.expand(sj.add(result,sj.mul(-1,parse(row.expr)))).equals(0)).toBe(true);
  });
  it('validates the coefficient domain and mutually exclusive options', () => {
    expect(() => Poly.from(parse('x**2+sqrt(3)'),[x],{extension:parse('sqrt(2)')})).toThrow(sj.CoercionFailed);
    expect(() => Poly.from(parse('x+sqrt(2)'),[x],{domain:'QQ_I'})).toThrow(sj.CoercionFailed);
    expect(() => Poly.from(parse('x**2'),[x],{extension:false})).toThrow(sj.OptionError);
    expect(() => Poly.from(parse('x**2'),[x],{gaussian:true,domain:'QQ'})).toThrow(sj.OptionError);
  });
});


it('preserves PurePoly construction and cancellation before monomial reduction', () => {
  expect(sj.factor(2, { extension: [sj.sqrt(2)] }).equals(2)).toBe(true);
  expect(String(Poly.from(parse('x+sqrt(2)'), [x], { extension: true, pure: true }))).toBe("PurePoly(x + sqrt(2), x, domain='QQ<sqrt(2)>')");
  const zero = new sj.Add([x, y, sj.mul(-1, x), sj.mul(-1, y)]);
  expect(sj.factor(zero, { extension: [sj.sqrt(2)] }).equals(0)).toBe(true);
});

describe('the field option (SymPy field=True)', () => {
  it('prefers QQ, QQ_I and fraction fields', () => {
    const [x, t] = sj.symbols('x t y');
    const dom = (e: string, gens: sj.Sym[], opts: sj.PolyConstructionOptions = {}): string => String(sj.Poly.from(sj.parse(e), gens, { field: true, ...opts }).domain);
    expect(dom('t**2 - x**3 - x + 1', [t])).toBe('ZZ(x)');
    expect(dom('t**2 - x/2', [t])).toBe('ZZ(x)');
    expect(dom('x + 1', [x])).toBe('QQ');
    expect(dom('t + I', [t])).toBe('QQ_I');
    expect(dom('t*x*y + 1', [t])).toBe('ZZ(x,y)');
    expect(dom('t + 2.5', [t])).toBe('RR');
    expect(dom('x + 1', [x], { domain: 'ZZ' })).toBe('ZZ');
  });
});

describe('gcd, lcm and cancel over an algebraic extension (SymPy 1.14 values)', () => {
  it('treats algebraic numbers as generators unless an extension is given', () => {
    const p = sj.parse;
    const got = [
      sj.gcd(p('x**2-2'), p('x-sqrt(2)')),
      sj.gcd(p('x**2-2'), p('x-sqrt(2)'), { extension: sj.sqrt(2) }),
      sj.lcm(p('x**2-2'), p('x-sqrt(2)'), { extension: sj.sqrt(2) }),
      sj.lcm(p('x**2-2'), p('x+sqrt(2)'), { extension: true }),
      sj.cancel(p('(x**2-2)/(x-sqrt(2))'), { extension: sj.sqrt(2) }),
      sj.cancel(p('(x**2-2)/(x-sqrt(2))'), { extension: true }),
      sj.gcd(p('x*pi'), p('pi')),
      sj.gcd(p('sqrt(2)*x'), p('2*x')),
    ].map(String);
    expect(got).toEqual(['1', 'x - sqrt(2)', 'x**2 - 2', 'x**2 - 2', 'x + sqrt(2)', 'x + sqrt(2)', 'pi', 'x']);
  });
});

it('exposes polynomial structural and factorization predicates', () => {
  expect(P('x**2+y', x).freeSymbolsInDomain).toEqual(new Set([y]));
  expect(P('x**2+y', x,y).freeSymbolsInDomain.size).toBe(0);
  expect(P('x',x).gen).toBe(x);
  expect(P('0',x).isGround).toBe(true);
  expect(P('y',x).isGround).toBe(true);
  expect(P('x',x).isGround).toBe(false);
  expect(P('x**2+x*y',x,y).isHomogeneous).toBe(true);
  expect(P('x**3+x*y',x,y).isHomogeneous).toBe(false);
  expect(P('x+y+1',x,y).isLinear).toBe(true);
  expect(P('x*y+1',x,y).isLinear).toBe(false);
  expect(P('x*y+1',x,y).isQuadratic).toBe(true);
  expect(P('x*y**2+1',x,y).isQuadratic).toBe(false);
  expect(P('x+1',x).isMonic).toBe(true);
  expect(P('2*x+1',x).isMonic).toBe(false);
  expect(P('2*x**2',x).isMonomial).toBe(true);
  expect(P('2*x**2+1',x).isMonomial).toBe(false);
  expect(P('x',x,y).isMultivariate).toBe(true);
  expect(P('x',x).isMultivariate).toBe(false);
  expect(P('x',x,y).isUnivariate).toBe(false);
  expect(P('x',x).isUnivariate).toBe(true);
  for (const [p, want] of [['0',false],['1',true],['x',false]] as const) expect(P(p,x).isOne).toBe(want);
  expect(P('2*x+2',x).isPrimitive).toBe(false);
  expect(P('x+2',x).isPrimitive).toBe(true);
  expect(P('x**2-1',x).isIrreducible).toBe(false);
  expect(P('(x+1)**2',x).isIrreducible).toBe(false);
  expect(P('x**2+1',x).isIrreducible).toBe(true);
  expect(Poly.from(E('x**2+x+1'),[x],{modulus:2}).isIrreducible).toBe(true);
  expect(Poly.from(E('x**2+1'),[x],{modulus:2}).isIrreducible).toBe(false);
  expect(P('0',x).isSqf).toBe(false);
  expect(P('(x-1)**2',x).isSqf).toBe(false);
  expect(P('x**2-1',x).isSqf).toBe(true);
  expect(P('x*y',x,y).isSqf).toBe(true);
  for (const [p, want] of [['x-1',true],['x+1',true],['x**2+1',true],['x**2+x+1',true],['x**4+1',true],['x**2-x+1',true],['x**2+2',false],['x**2-1',false],['2*x+2',false],['x+1/2',false],['x**2-3*x+1',false]] as const) expect(P(p,x).isCyclotomic, p).toBe(want);
  expect(P('x+y',x,y).isCyclotomic).toBe(false);
  expect(Poly.from(E('x+1'),[x],{modulus:2}).isCyclotomic).toBe(false);
});

it('excludes zero from square-free and irreducible polynomials', () => {
  // SymPy 1.14 returns true for both properties of zero. This is incorrect:
  // x**2 divides zero, and zero is neither a unit nor an irreducible element.
  expect(P('0',x).isSqf).toBe(false);
  expect(P('0',x).isIrreducible).toBe(false);
  expect(P('2',x).isIrreducible).toBe(true); // the predicate ignores scalar content
  expect(P('1',x).isCyclotomic).toBe(false);
});

it('polynomial symbols, unification, rational denominators and square-free norms', () => {
  const f = sj.Poly.from(E('x**2+y'),[x]);
  expect(f.freeSymbols()).toEqual(new Set([x,y]));
  expect(sj.Poly.from(E('x**2+y'),[x],{pure:true}).freeSymbols()).toEqual(new Set([y]));
  expect(sj.Poly.from(E('x**2+y'),[x,y],{pure:true}).freeSymbols().size).toBe(0);
  const [a,b] = sj.Poly.from(E('x/2+1'),[x]).unify(sj.Poly.from(E('2*x+1'),[x]));
  expect([a.domain,b.domain]).toEqual(['QQ','QQ']);
  expect(a.asExpr().equals(E('x/2+1'))).toBe(true);
  const [u,v] = sj.Poly.from(x,[x]).unify(sj.Poly.from(y,[y]));
  expect(u.gens).toEqual([x,y]); expect(v.gens).toEqual([x,y]);
  expect(sj.Poly.from(x,[x],{modulus:5}).unify(sj.Poly.from(2,[x],{modulus:5})).map(p=>p.domain)).toEqual(['GF(5)','GF(5)']);
  const F = sj.Poly.from(E('x**2/y+1'),[x]);
  const G = sj.Poly.from(E('x**3+y'),[x]);
  const [p,q] = F.ratClearDenoms(G);
  expect(p.toString()).toBe("Poly(x**2 + y, x, domain='ZZ[y]')");
  expect(q.toString()).toBe("Poly(y*x**3 + y**2, x, domain='ZZ[y]')");
  expect(p.mul(G).asExpr().equals(q.mul(F).asExpr())).toBe(true);
  expect(F.clearDenoms()[1].domain).toBe('ZZ(y)');
  const h = sj.Poly.from(E('x**2+1'),[x],{domain:'QQ<sqrt(3)>'});
  const [shift,translated,norm] = h.sqfNorm();
  expect(shift).toEqual([1]);
  expect(translated.asExpr().equals(E('x**2-2*sqrt(3)*x+4'))).toBe(true);
  expect(norm.asExpr().equals(E('x**4-4*x**2+16'))).toBe(true);
  expect(sj.Poly.from(E('x**2+1'),[x],{domain:'QQ_I'}).sqfNorm()[0]).toEqual([2]);
  expect(() => f.sqfNorm()).toThrow(sj.DomainError);
});

it('constructs polynomials from descending coefficient lists', () => {
  expect(sj.Poly.fromList([1,-5,-2],[x],{domain:'QQ'}).toString()).toBe("Poly(x**2 - 5*x - 2, x, domain='QQ')");
  expect(sj.Poly.fromList([], [x]).isZero).toBe(true);
  expect(() => sj.Poly.fromList([1],[])).toThrow(sj.PolynomialError);
  expect(() => sj.Poly.fromList([1],[x,y])).toThrow(sj.PolynomialError);
});

it('preserves coefficient fields under multiplication and prints large float coefficients', () => {
  const symbolic = Poly.from(sj.sin(y).mul(x), [x], { domain: 'EX' });
  expect(symbolic.mul(2).domain).toBe('EX');
  expect(symbolic.mul(2).asExpr().equals(E('2*x*sin(y)'))).toBe(true);
  expect(Poly.from(x, [x]).unify(Poly.from(add(x, y), [x, y])).map((p) => p.gens)).toEqual([[x, y], [x, y]]);
  for (const domain of ['QQ', 'CC']) {
    const f = Poly.from(E('x + 1'), [x], { domain });
    expect(f.mul(x).domain).toBe(domain);
    expect(f.mul(Poly.from(E('x/2'), [x])).domain).toBe(domain);
    expect(Poly.from(x, [x]).mul(f).domain).toBe(domain);
  }
  expect(Poly.from(E('93174668405225495165618337349632.0*x'), [x], { domain: 'RR' }).toString())
    .toBe("Poly(9.31746684052255e+31*x, x, domain='RR')");
});

it('unifies Gaussian and floating coefficient domains for multiplication', () => {
  const domains = ['ZZ', 'QQ', 'RR', 'CC', 'ZZ_I', 'QQ_I'];
  const expected = [
    ['ZZ', 'QQ', 'RR', 'CC', 'ZZ_I', 'QQ_I'],
    ['QQ', 'QQ', 'RR', 'CC', 'QQ_I', 'QQ_I'],
    ['RR', 'RR', 'RR', 'CC', 'CC', 'CC'],
    ['CC', 'CC', 'CC', 'CC', 'CC', 'CC'],
    ['ZZ_I', 'QQ_I', 'CC', 'CC', 'ZZ_I', 'QQ_I'],
    ['QQ_I', 'QQ_I', 'CC', 'CC', 'QQ_I', 'QQ_I'],
  ];
  domains.forEach((a, i) => domains.forEach((b, j) => {
    expect(Poly.from(x, [x], { domain: a }).mul(Poly.from(x, [x], { domain: b })).domain).toBe(expected[i]![j]);
  }));
  expect(Poly.from(x, [x]).mul(sj.I).domain).toBe('ZZ_I');
});

describe('gcd and lcm over fields are monic (SymPy dmp_ff_prs_gcd, dmp_ff_lcm)', () => {
  const g = (a: string, b: string): string => str(sj.gcd(parse(a), parse(b)));
  const l = (a: string, b: string): string => str(sj.lcm(parse(a), parse(b)));
  it('over QQ', () => {
    expect(g('2*x/3 + 2/3', '4*x + 4')).toBe('x + 1');
    expect(l('2*x/3 + 2/3', '4*x + 4')).toBe('x + 1');
    expect(l('x/2', '3*x + 3')).toBe('x**2 + x');
    expect(g('x/2 + y/2', '3*x + 3*y')).toBe('x + y');
    // over ZZ the leading coefficient is only made positive
    expect(g('4*x + 4', '-6*x - 6')).toBe('2*x + 2');
    expect(l('2*x', '3*x + 3')).toBe('6*x**2 + 6*x');
  });
  it('over RR through the exact rationals of the coefficients (SymPy dup_inner_gcd)', () => {
    expect(l('8.0089*x + 2.83', '1')).toBe('1.0*x + 0.353356890459364');
    expect(l('2.0*x + 1', '3*x')).toBe('1.0*x**2 + 0.5*x');
    expect(g('4.0*x + 2', '2.0*x + 1')).toBe('1.0*x + 0.5');
    expect(g('2.0*x**2 - 2', '4.0*x - 4')).toBe('1.0*x - 1.0');
    expect(g('-2.0*x + 1', '-4.0*x + 2')).toBe('1.0*x - 0.5');
    expect(g('2.0*x*y + y', '4.0*x + 2')).toBe('1.0*x + 0.5');
    expect(l('2.0*x*y + y', '4.0*x + 2')).toBe('1.0*x*y + 0.5*y');
    expect(l('2.0*x', '4.0*x**2')).toBe('1.0*x**2');
    expect(g('8.0089*x + 2.83', '0')).toBe('1.0*x + 0.353356890459364');
    expect(l('0', '2.0*x + 1')).toBe('0');
    // RR.to_rational of 8.0089 and 16.0178 are not proportional, as in SymPy
    expect(g('8.0089*x + 2.83', '16.0178*x + 5.66')).toBe('1.00000000000000');
    // numbers: RealField.gcd is one and RealField.lcm the product
    expect(g('2.0', '4.0')).toBe('1.00000000000000');
    expect(l('2.0', '3')).toBe('6.00000000000000');
    expect(g('2', '4')).toBe('2');
  });
  it('over CC', () => {
    expect(g('1.0*I*x + 1.0', '2.0*I*x + 2.0')).toBe('1.0*x - 1.0*I');
    expect(l('1.0*I*x + 1.0', '3*x')).toBe('1.0*x**2 - 1.0*I*x');
    expect(g('(2.0 + 1.0*I)*x + 1', '3.0*x + 1')).toBe('1.00000000000000');
  });
  it('keeps the other domains and rational functions', () => {
    expect(g('x/y', 'x')).toBe('x');
    expect(g('sqrt(2)*x', 'x')).toBe('x');
    const p = sj.Poly.from(parse('2.0*x + 1'), [new Sym('x')]);
    expect(str(p.gcd(sj.Poly.from(parse('x**2 + x'), [new Sym('x')])).asExpr())).toBe('1.00000000000000');
    expect(str(p.lcm(sj.Poly.from(parse('0'), [new Sym('x')], { domain: 'RR' })).asExpr())).toBe('0');
    const X = new Sym('x');
    expect(str(sj.Poly.from(parse('x/2'), [X]).gcd(sj.Poly.from(parse('x*y'), [X])).asExpr())).toBe('x/2');
    expect(str(sj.Poly.from(parse('0'), [new Sym('x')], { domain: 'QQ' }).gcd(sj.Poly.from(parse('0'), [new Sym('x')], { domain: 'QQ' })).asExpr())).toBe('0');
  });
  it('of irrational algebraic numbers with a rational ratio (SymPy Q[irrational])', () => {
    expect(g('6*(1 + sqrt(3))/5', '3*(1 + sqrt(3))/10')).toBe('3/10 + 3*sqrt(3)/10');
    expect(g('2*sqrt(3)/3', '5/(6*sqrt(3))')).toBe('sqrt(3)/18');
    expect(g('-sqrt(2)', '2*sqrt(2)')).toBe('sqrt(2)');
    expect(g('-sqrt(2)', '-2*sqrt(2)')).toBe('sqrt(2)');
    expect(l('3*sqrt(3)', '4/sqrt(3)')).toBe('12*sqrt(3)');
    expect(l('5*(1 + 2**(1/3))/6', '3*(1 + 2**(1/3))/8')).toBe('15/2 + 15*2**(1/3)/2');
    expect(g('sqrt(2)', 'sqrt(3)')).toBe('1');
    expect(l('sqrt(2)', 'sqrt(3)')).toBe('sqrt(6)');
    expect(g('sqrt(2)', '2')).toBe('1');
    // not real algebraic numbers: the polynomial gcd and lcm in the generators
    expect(g('pi', '2*pi')).toBe('pi');
    expect(g('2**sqrt(2)', '2*2**sqrt(2)')).toBe('2**(sqrt(2))');
    expect(g('sqrt(-2)', '2*sqrt(-2)')).toBe('sqrt(2)');
  });
  it('infers CC for complex floating-point coefficients', () => {
    expect(sj.Poly.from(parse('1.0*I*x + 1.0')).domain).toBe('CC');
    expect(sj.Poly.from(parse('2.0*I*x + 1')).domain).toBe('CC');
    expect(sj.Poly.from(parse('(2.0 + 1.0*I)*x + 1')).domain).toBe('CC');
    expect(sj.Poly.from(parse('I*x + 1/2')).domain).toBe('QQ_I');
    expect(str(sj.Poly.from(parse('I*x + 1'), [new Sym('x')], { domain: 'CC' }).asExpr())).toBe('1.0*I*x + 1.0');
  });
});


describe('explicit rational coefficient domains', () => {
  it('rejects coefficients outside the requested ground domain', () => {
    for (const domain of ['ZZ', 'QQ']) {
      expect(() => Poly.from(E('x + y'), [x], { domain })).toThrow(sj.CoercionFailed);
      expect(() => Poly.from(E('sqrt(2)*x + 1'), [x], { domain })).toThrow(sj.CoercionFailed);
      expect(Poly.from(E('2*x + 1'), [x], { domain }).domain).toBe(domain);
      expect(Poly.from(0, [x], { domain }).isZero).toBe(true);
    }
    expect(() => Poly.from(E('x/2 + 1'), [x], { domain: 'ZZ' })).toThrow(sj.CoercionFailed);
    expect(String(Poly.from(E('x/2 + 1'), [x], { domain: 'QQ', pure: true }))).toBe("PurePoly(1/2*x + 1, x, domain='QQ')");
  });
});


it('pseudo-divides in the first generator over the remaining polynomial variables', () => {
  const f = Poly.from(E('x**2 + x*y + 1'), [x, y]);
  const g = Poly.from(E('2*x + y'), [x, y]);
  const [q, r] = f.pdiv(g);
  expect(String(q.asExpr())).toBe('2*x + y');
  expect(String(r.asExpr())).toBe('4 - y**2');
  expect(q.domain).toBe('ZZ');
  expect(r.domain).toBe('ZZ');
  expect(q.mul(g).add(r).equals(f.mulGround(4))).toBe(true);
  expect(() => f.pexquo(g)).toThrow(sj.ExactQuotientFailed);
  expect(f.mul(g).pexquo(g).equals(f.mulGround(8))).toBe(true);
  expect(() => f.prem(Poly.from(0, [x, y]))).toThrow(RangeError);
});


it('preserves coefficient fields during extended Euclid and Sturm sequences', () => {
  const f = Poly.from(E('x**2 - 2'), [x], { domain: 'QQ<sqrt(2)>' });
  const g = Poly.from(E('x - sqrt(2)'), [x], { domain: 'QQ<sqrt(2)>' });
  const [s, t, h] = f.gcdex(g);
  expect(s.mul(f).add(t.mul(g)).equals(h)).toBe(true);
  const p = Poly.from(E('x**2 + 2*sqrt(2)*x + 1'), [x], { domain: 'QQ<sqrt(2)>' });
  expect(p.countRoots()).toBe(2);
  const mixed = Poly.from(E('x/2 + 1'), [x]);
  const [m, n, k] = mixed.gcdex(Poly.from(x, [x]));
  expect(m.mul(mixed).add(n.mul(Poly.from(x, [x]))).equals(k)).toBe(true);
  const a = Poly.from(E('x + y'), [x]);
  const b = Poly.from(E('x - y'), [x]);
  const [u, v, d] = a.gcdex(b);
  expect(u.mul(a).add(v.mul(b)).equals(d)).toBe(true);
});

import continuationRefs from './continuation.references.json';
for(const row of continuationRefs.algebraic) it(`Trager factorization: ${row.expr}`,()=>{
  const gens=row.gens.map((s)=>new Sym(s)),extension=row.extension.map((e)=>parse(e));
  const f=Poly.from(parse(row.expr),gens,{extension}),[c,fs]=f.factorList();
  expect(expand(add(c,mul(-1,parse(row.content))))).toEqual(sj.S.Zero);
  const remaining=[...fs];
  for(const [expr,k] of row.factors){
    const i=remaining.findIndex(([g,m])=>m===k&&g.equals(Poly.from(parse(String(expr)),gens,{extension})));
    expect(i).toBeGreaterThanOrEqual(0);remaining.splice(i,1);
  }
  expect(remaining).toHaveLength(0);
  expect(fs.reduce((p,[g,k])=>p.mul(g.pow(k)),Poly.from(c,gens,{extension})).equals(f)).toBe(true);
  expect(f.norm().equals(Poly.from(parse(row.norm),gens))).toBe(true);
});
for(const row of continuationRefs.finite) it(`multivariate finite PRS mod ${row.p}: ${row.a}, ${row.b}`,()=>{
  const gens=row.gens.map((s)=>new Sym(s)),P=(e:string)=>Poly.from(parse(e),gens,{modulus:row.p});
  const f=P(row.a),g=P(row.b),h=f.gcd(g);
  expect(h.equals(P(row.gcd))).toBe(true);
  expect(f.lcm(g).equals(P(row.lcm))).toBe(true);
  expect(f.subresultants(g).map((p)=>String(p.asExpr()))).toEqual(row.subresultants.map((e)=>String(P(e).asExpr())));
  expect(P(String(f.discriminant())).equals(P(row.discriminantExact))).toBe(true);
  if(!h.isZero){expect(f.exquo(h).mul(h).equals(f)).toBe(true);expect(g.exquo(h).mul(h).equals(g)).toBe(true);}
});
it('preserves nonsymmetric finite presentations and supports composite-modulus factorization when division is invertible',()=>{
  const x=new Sym('x'),P=(e:string)=>Poly.from(parse(e),[x],{modulus:5,symmetric:false});
  expect(String(P('4*x+3').asExpr())).toBe('4*x + 3');
  expect(String(P('4*x+3').add(P('x+1')).asExpr())).toBe('4');
  expect(P('4*x+3').equals(Poly.from(parse('-x-2'),[x],{modulus:5}))).toBe(true);
  expect(String(P('x+3').mul(P('x+3')).asExpr())).toBe('x**2 + x + 4');
  for(const modulus of [6,9]){
    const f=Poly.from(parse(modulus===6?'x+1':'x**2-1'),[x],{modulus}),[c,fs]=f.factorList();
    expect(fs).toHaveLength(modulus===6?1:2);
    expect(fs.reduce((r,[g,k])=>r.mul(g.pow(k)),Poly.from(c,[x],{modulus})).equals(f)).toBe(true);
  }
});

import finiteMethodRefs from './finite-methods.references.json';
for(const row of finiteMethodRefs) it(`further Poly methods on ${row.expr} mod ${row.p}`,()=>{
  const x=new Sym('x'),P=(e:string)=>Poly.from(parse(e),[x],{modulus:row.p}),f=P(row.expr);
  expect(f.sqfPart().equals(P(row.sqfPart))).toBe(true);
  expect(f.sturm().map((g)=>String(g.asExpr()))).toEqual(row.sturm.map((e)=>String(P(e).asExpr())));
  expect(f.groundRoots().map(([r,k])=>[String(r),k]).sort((a,b)=>String(a).localeCompare(String(b)))).toEqual([...row.groundRoots].sort((a,b)=>String(a).localeCompare(String(b))));
  if(row.decompose)expect(f.decompose().map((g)=>String(g.asExpr()))).toEqual(row.decompose.map((e)=>String(P(e).asExpr())));
  if(row.revert){const g=f.revert(5);expect(g.equals(P(row.revert))).toBe(true);expect(f.mul(g).rem(P('x**8')).equals(P('1'))).toBe(true);}
});

it('preprocesses indexed-root polynomials and removable symbolic coefficient scales',()=>{
  const x=new Sym('x'),y=new Sym('y');
  for(const [expr,scale,expected] of [['0','1','0'],['1','1','1'],['x**3-8*x+16','2','x**3-2*x+2'],['x**3/8-x+2','2','x**3-2*x+2'],['y**3*x**3+y**2*x**2+y*x+1','1/y','x**3+x**2+x+1']]){
    const [s,f]=sj.preprocessRoots(Poly.from(parse(String(expr)),[x]));
    expect(String(s)).toBe(String(scale));expect(f.equals(Poly.from(parse(String(expected)),[x]))).toBe(true);
  }
  expect(sj.cancel(parse('((x+y)*(x+1))/((x+y)*(y+1))'),{modulus:5}).equals(parse('(x+1)/(y+1)'))).toBe(true);
  const f=Poly.from(parse('4*x**2+4*y**2'),[x,y],{modulus:5,symmetric:false});
  for(const g of [f.reorder(y,x),f.deflate()[1],f.termsGcd()[1],f.homogenize(new Sym('z')),f.toExact(),f.toField(),f.toRing(),f.replace(x,new Sym('z'))]){
    expect(g.coeffs().every((c)=>c instanceof sj.Rational&&c.p>=0n)).toBe(true);
  }
  expect(String(f.evalMany([[x,2],[y,1]]))).toBe('0');
});

it('unifies distinct algebraic coefficient fields before arithmetic and GCD',()=>{
  const x=new Sym('x'),y=new Sym('y'),P=(e:string,r:string)=>Poly.from(parse(e),[x,y],{extension:parse(r)});
  const a=P('x+sqrt(2)','sqrt(2)'),b=P('x+sqrt(3)','sqrt(3)');
  expect(a.add(b).asExpr().equals(parse('2*x+sqrt(2)+sqrt(3)'))).toBe(true);
  expect(a.sub(b).asExpr().equals(parse('sqrt(2)-sqrt(3)'))).toBe(true);
  expect(a.mul(b).div(b)[1].isZero).toBe(true);
  const f=a.mul(y),g=b.mul(y);
  expect(f.gcd(g).asExpr().equals(y)).toBe(true);
});

it('rejects ordered-root operations over finite fields and reduces algebraic evaluation in its field',()=>{
  const x=new Sym('x'),f=Poly.from(parse('x**2-2'),[x],{modulus:5});
  expect(()=>f.intervals()).toThrow(sj.DomainError);
  expect(()=>f.refineRoot(sj.S.One,sj.S.Two)).toThrow(sj.DomainError);
  expect(()=>f.countRoots()).toThrow(sj.DomainError);
  const K=new sj.AlgebraicField(sj.QQ,parse('sqrt(2)')),g=Poly.from(parse('sqrt(2)*x'),[x],{domain:K});
  expect(g.content()).toEqual(sj.S.One);expect(g.primitive()[1]).toBe(g);
  expect(String(g.eval(parse('sqrt(2)')))).toBe('2');
  expect(g.integrate().domain).toBe(g.domain);
});
it('preserves inexact and multivariate preprocessing inputs as in SymPy',()=>{
  const x=new Sym('x'),y=new Sym('y');
  const rr=Poly.from(parse('2.0*x+4.0'),[x]),cc=Poly.from(x,[x],{domain:'CC'});
  expect(sj.preprocessRoots(rr)[1]).toBe(rr);expect(sj.preprocessRoots(cc)[1]).toBe(cc);
  const multi=Poly.from(parse('x*y+1'),[x,y]);
  expect(sj.preprocessRoots(multi)[1].equals(multi)).toBe(true);
  expect(sj.preprocessRoots(Poly.from(parse('x**2-4'),[x],{modulus:11})).map(String)).toEqual(['2',"Poly(x**2 - 1, x, domain='ZZ')"]);
});
it('factors over a supplied RootOf domain without parsing its generator name',()=>{
  const x=new Sym('x'),r=sj.CRootOf(parse('x**3-x-1'),0),K=new sj.AlgebraicField(sj.QQ,r);
  const f=Poly.from(parse('x**3-x-1'),[x],{domain:K}),[,fs]=f.factorList();
  expect(fs.map(([g])=>g.degree()).sort((a,b)=>a-b)).toEqual([1,2]);
  expect(String(f.eval(r))).toBe('0');
  expect(fs.some(([g])=>g.degree()===1&&String(g.eval(r))==='0')).toBe(true);
  expect(Poly.from(sj.factor(f.asExpr(),{domain:K}),[x],{domain:K}).equals(f)).toBe(true);
});

it('handles algebraic constants, zero norms and native subresultants',()=>{
  const x=new Sym('x'),P=(e:string)=>Poly.from(parse(e),[x],{extension:parse('sqrt(2)')});
  expect(P('0').factorList()).toEqual([sj.S.Zero,[]]);expect(P('sqrt(2)').factorList()[1]).toEqual([]);
  expect(P('0').sqfNorm().map(String)).toEqual(['0',String(P('0')),"Poly(0, x, domain='QQ')"]);
  expect(()=>P('(x+sqrt(2))**2').sqfNorm()).toThrow(sj.PolynomialError);
  expect(P('x**2-2').subresultants(P('x-sqrt(2)')).map((p)=>p.degree())).toEqual([2,1]);
  const r=sj.CRootOf(parse('x**3-x-1'),0),K=new sj.AlgebraicField(sj.QQ,r);
  expect(Poly.from(add(mul(add(pow(r,3),mul(-1,r),-1),x),1),[x],{domain:K}).asExpr().equals(sj.S.One)).toBe(true);
});

import * as intervalModule from '../../src/polys/numberfields/interval';
it('certifies lifted roots with small nonzero residuals and retries interval evaluation',()=>{
  const x=new Sym('x'),f=Poly.from(parse('x**3-x+sqrt(2)/10**15'),[x],{extension:parse('sqrt(2)')});
  expect(f.realRoots().map(String)).toEqual(continuationRefs.liftedRoots[0]?.roots);
  const original=intervalModule.algebraicEnclosure,spy=vi.spyOn(intervalModule,'algebraicEnclosure');
  let retried=false;
  try {
    spy.mockImplementation((e,bits)=>{
      if(!retried&&String(e).includes('CRootOf')&&String(e).includes('sqrt(2)')){retried=true;throw new RangeError('precision insufficient');}
      return original(e,bits);
    });
    expect(f.realRoots()).toHaveLength(3);expect(retried).toBe(true);
    spy.mockImplementation((e,bits)=>{if(String(e).includes('CRootOf')&&String(e).includes('sqrt(2)'))throw new TypeError('invalid residual');return original(e,bits);});
    expect(()=>f.realRoots()).toThrow(TypeError);
  } finally {spy.mockRestore();}
  expect(Poly.from(0,[x]).allRoots()).toEqual([]);
  expect(Poly.from(parse('x-I'),[x]).realRoots()).toEqual([]);
});

it('preserves dense finite/algebraic reconstruction and PurePoly preprocessing domains',()=>{
  const x=new Sym('x'),p=Poly.from(parse('4*x+3'),[x],{modulus:5,symmetric:false});
  expect(String(p.per([sj.GF(5).convert(4),sj.GF(5).convert(3)]))).toBe('Poly(4*x + 3, x, modulus=5)');
  expect(String(p.per([sj.GF(5).convert(4)],{remove:0}))).toBe('4');
  expect(String(p.termwise((_m,c)=>mul(2,c)))).toBe("Poly(8*x + 6, x, domain='ZZ')");
  const r=sj.CRootOf(parse('x**3-x-1'),0),K=new sj.AlgebraicField(sj.QQ,r),f=Poly.from(add(x,r),[x],{domain:K});
  const g=f.per([K.convert(1),K.convert(r)]);
  expect(g instanceof Poly&&g.equals(f)).toBe(true);
  expect(sj.preprocessRoots(Poly.from(0,[x],{domain:'QQ'}))[1].domain).toBe('ZZ');
  const pure=sj.PurePoly(parse('x**3-8*x+16'),x),[scale,normalized]=sj.preprocessRoots(pure);
  expect(String(scale)).toBe('2');expect(normalized.pure).toBe(true);
});
it('preserves RootOf coefficients during shifts, composition and generator replacement',()=>{
  const x=new Sym('x'),y=new Sym('y'),r=sj.CRootOf(parse('x**3-x-1'),0),K=new sj.AlgebraicField(sj.QQ,r),P=(e:sj.ExprLike)=>Poly.from(e,[x],{domain:K});
  const f=P(mul(add(x,mul(-1,r)),add(x,mul(-1,r),-3))),g=f.shift(-2);
  expect(g.shift(2).equals(f)).toBe(true);
  expect(f.compose(P(add(x,2))).equals(f.shift(2))).toBe(true);
  expect(f.replace(x,y).replace(y,x).equals(f)).toBe(true);
  expect(f.compose(Poly.from(parse('x+sqrt(2)'),[x],{extension:parse('sqrt(2)')})).degree()).toBe(2);
  const multi=Poly.from(add(x,y),[x,y],{domain:K}),evaluated=multi.eval(r);
  expect(evaluated instanceof Poly&&evaluated.domain===multi.domain).toBe(true);
  expect(String(Poly.from(mul(parse('sqrt(2)'),x),[x],{extension:parse('sqrt(2)')}).eval(parse('sqrt(3)')))).toBe('sqrt(6)');
});
it('covers degenerate finite discriminants, indecomposable polynomials and algebraic zero LCMs',()=>{
  const x=new Sym('x'),y=new Sym('y'),p=Poly.from(parse('x**5+y**5'),[x,y],{modulus:5});
  expect(String(p.discriminant())).toBe('0');
  const q=Poly.from(parse('x**4+x+1'),[x],{modulus:5});expect(q.decompose()).toHaveLength(1);
  const P=(e:number|sj.Expr)=>Poly.from(e,[x],{extension:parse('sqrt(2)')});
  expect(P(0).lcm(P(x)).isZero).toBe(true);expect(P(x).lcm(P(0)).isZero).toBe(true);
  expect(String(sj.factor(parse('x**2-1'),{modulus:9}))).toBe('(x - 1)*(x + 1)');
});
it('supports automatic, single-generator and deep algebraic factor options',()=>{
  const x=new Sym('x');
  expect(String(sj.factor(parse('x**2+2*sqrt(2)*x+2'),{extension:true}))).toBe('(x + sqrt(2))**2');
  expect(String(sj.factor(parse('x**2-2'),{extension:parse('sqrt(2)')}))).toBe('(x - sqrt(2))*(x + sqrt(2))');
  expect(String(sj.factor(parse('x**2-2'),{extension:false}))).toBe('x**2 - 2');
  expect(String(sj.factor(parse('sin(x**2-2)'),{extension:parse('sqrt(2)'),deep:true}))).toBe('sin((x - sqrt(2))*(x + sqrt(2)))');
  expect(Poly.from(sj.factor(parse('(x**2-2)/(x-sqrt(2))'),{extension:true}),[x],{extension:parse('sqrt(2)')}).equals(Poly.from(parse('x+sqrt(2)'),[x],{extension:parse('sqrt(2)')}))).toBe(true);
});
it('preserves coefficient-domain errors during algebraic evaluation',()=>{
  const x=new Sym('x'),K=new sj.AlgebraicField(sj.QQ,parse('sqrt(2)')),f=Poly.from(x,[x],{domain:K}),spy=vi.spyOn(K,'convert').mockImplementation(()=>{throw new TypeError('coefficient conversion failed');});
  try {expect(()=>f.eval(1)).toThrow(TypeError);}
  finally {spy.mockRestore();}
});
it('recognizes indexed algebraic coefficients when choosing formal factorization generators',()=>{
  const x=new Sym('x'),r=sj.CRootOf(parse('x**3-x-1'),0),K=new sj.AlgebraicField(sj.QQ,r),expression=pow(add(x,mul(-1,r)),2);
  expect(Poly.from(sj.factor(expression,{extension:true}),[x],{domain:K}).equals(Poly.from(expression,[x],{domain:K}))).toBe(true);
});
it('keeps an algebraic domain alias out of the polynomial generators',()=>{
  const x=new Sym('x'),theta=new Sym('theta'),K=new sj.AlgebraicField(sj.QQ,new sj.AlgebraicNumber(theta,[1,0],{minpoly:Poly.from(parse('x**2-2'),[x])}));
  const result=sj.factor(add(pow(x,2),pow(theta,2),-4),{domain:K});
  expect(String(result)).toBe(String(mul(add(x,mul(-1,theta)),add(x,theta))));
});
it('validates unary and binary generator replacement',()=>{
  const x=new Sym('x'),y=new Sym('y'),z=new Sym('z'),f=Poly.from(add(x,1),[x]),g=Poly.from(add(x,y),[x,y]);
  expect(f.replace(y).asExpr().equals(add(y,1))).toBe(true);expect(f.replace(x)).toBe(f);
  expect(()=>g.replace(z)).toThrow(sj.PolynomialError);
  expect(f.replace(z,y)).toBe(f);
  expect(()=>g.replace(x,y)).toThrow(sj.PolynomialError);
});
it('recovers algebraic root multiplicities without multiplying by unused field conjugates',()=>{
  const x=new Sym('x'),P=(e:string)=>Poly.from(parse(e),[x],{extension:[parse('sqrt(2)'),parse('sqrt(3)')]});
  expect(P('x**2-2').realRoots().map(String)).toEqual(['-sqrt(2)','sqrt(2)']);
  expect(P('x**2-sqrt(2)*x+1').allRoots().map(String)).toEqual(['sqrt(2)/2 - sqrt(2)*I/2','sqrt(2)/2 + sqrt(2)*I/2']);
  expect(Poly.from(parse('x**2+1'),[x],{domain:'QQ_I'}).allRoots().map(String)).toEqual(['-I','I']);
  expect(P('(x-sqrt(2))**2*(x+sqrt(2))**3').realRoots().map(String)).toEqual(['-sqrt(2)','-sqrt(2)','-sqrt(2)','sqrt(2)','sqrt(2)']);
  expect(Poly.from(parse('x**2+1'),[x],{modulus:5}).allRoots().map(String)).toEqual(['-I','I']);
  expect(Poly.from(parse('4*x+3'),[x],{modulus:5,symmetric:false}).allRoots().map(String)).toEqual(['-3/4']);
});
it('preserves nonsymmetric representatives in top-level finite factorization and cancellation',()=>{
  expect(String(sj.factor(parse('x**2+1'),{modulus:5,symmetric:false}))).toBe('(x + 2)*(x + 3)');
  expect(String(sj.factor(parse('x**2-1'),{modulus:9,symmetric:false}))).toBe('(x + 1)*(x + 8)');
  expect(String(sj.factor(parse('x**2+1'),{domain:sj.GF(5,false)}))).toBe('(x + 2)*(x + 3)');
  expect(String(sj.cancel(parse('(4*x+3)/(x+1)'),{modulus:5,symmetric:false}))).toBe('(4*x + 3)/(x + 1)');
});

it('rejects multivariate Taylor shifts like SymPy 1.14',()=>{
  const x=new Sym('x'),y=new Sym('y');
  expect(()=>Poly.from(add(mul(x,y),pow(y,2)),[x,y],{modulus:5}).shift(2)).toThrow('univariate polynomial expected');
});

describe('polynomial construction and comparison options', () => {
  const X = new Sym('x'), Y = new Sym('y');
  it('constructs from exponent dictionaries and checks their dimensions', () => {
    expect(Poly.fromDict(new Map([[[2], 3], [[0], 1]]), [X]).asExpr().equals(parse('3*x**2+1'))).toBe(true);
    expect(Poly.fromDict(new Map([[[1], Y]]), [X], { composite: false }).domain).toBe('EX');
    expect(Poly.fromDict(new Map([[[1], 2]]), [X], { composite: false }).domain).toBe('ZZ');
    expect(Poly.fromDict(new Map([[[1], 2]]), [X], { composite: false, modulus: 3 }).domain).toBe('GF(3)');
    for (const m of [[1, 0], [-1], [0.5]]) expect(() => Poly.fromDict(new Map([[m, 1]]), [X])).toThrow(sj.PolynomialError);
    expect(() => Poly.fromExpr(1)).toThrow(sj.GeneratorsNeeded);
    expect(() => Poly.fromDict(new Map(), [])).toThrow(sj.GeneratorsNeeded);
    expect(Poly.fromExpr(X).gen).toBe(X);
    expect(Poly.fromExpr(1, [X]).degree()).toBe(0);
  });
  it('converts domains and rejects incompatible generators or characteristic', () => {
    const p = Poly.from(X);
    expect(p.setDomain('QQ').domain).toBe('QQ');
    expect(p.setDomain(sj.QQ).domain).toBe('QQ');
    expect(() => p.setDomain(sj.ZZ.polyRing(X))).toThrow(sj.GeneratorsError);
    const f = Poly.from(X, [X], { modulus: 3 });
    expect(f.setDomain('GF(3)').domain).toBe('GF(3)');
    expect(() => f.setDomain('QQ')).toThrow(sj.CoercionFailed);
  });
  it('compares domains strictly and keeps PurePoly generators as placeholders', () => {
    const p = Poly.from(X), q = p.setDomain('QQ');
    expect(p.eq(q)).toBe(false);
    expect(p.eq(q, { strict: false })).toBe(false);
    expect(p.ne(q)).toBe(true);
    expect(p.eq(X)).toBe(true);
    expect(p.eq(X, { strict: true })).toBe(false);
    const pure = Poly.from(X, [X], { pure: true });
    const other = Poly.from(Y, [Y], { domain: 'QQ', pure: true });
    expect(pure.eq(other)).toBe(true);
    expect(pure.eq(p, { strict: true })).toBe(false);
    expect(pure.eq(other, { strict: true })).toBe(false);
    expect(pure.ne(other, { strict: false })).toBe(false);
  });
  it('slices exponents in either generator and preserves the coefficient domain', () => {
    const p = Poly.from(parse('x**3+2*x*y+3*y**2+4'), [X, Y], { domain: 'QQ' });
    expect(p.slice(0, 2).asExpr().equals(parse('2*x*y+3*y**2+4'))).toBe(true);
    expect(p.slice(1, 2, Y).asExpr().equals(parse('2*x*y'))).toBe(true);
    expect(p.slice(2, 2).isZero).toBe(true);
    expect(p.slice(0, 2).domain).toBe('QQ');
  });
  it('isolates constants and counts roots with infinite and algebraic bounds', () => {
    expect(Poly.from(1).intervals()).toEqual([]);
    expect(Poly.from(0).intervals(undefined, { all: true })).toEqual([[], []]);
    const p = Poly.from(parse('x**2-2'), [X]);
    expect(p.countRoots(sj.S.NegativeInfinity, sj.S.Infinity)).toBe(2);
    expect(p.countRoots(-2, 2)).toBe(2);
    const a = Poly.from(parse('x**2+2*sqrt(2)*x+1'), [X], { extension: parse('sqrt(2)') });
    expect(a.countRoots(-3, 0)).toBe(2);
  });
});

it('validates sparse term transforms and finite-domain isolation', () => {
  const X = new Sym('x'), Y = new Sym('y');
  expect(() => Poly.from(parse('x+1'), [X]).termwise(() => [[0], 1])).toThrow('generated twice');
  const finite = Poly.from(parse('x+y'), [X, Y], { modulus: 3 });
  expect(() => finite.sqfPart()).toThrow(sj.NotImplementedError);
  const f = Poly.from(X, [X], { modulus: 3 });
  expect(() => f.intervals()).toThrow(sj.DomainError);
  expect(() => f.refineRoot(R(0), R(1))).toThrow(sj.DomainError);
  const names = ['a10', 'a2', 'a1', 'a1'].map((n) => new Sym(n));
  expect(sj.sortGens(names).map(String)).toEqual(['a1', 'a1', 'a2', 'a10']);
  expect(sj.sortGens([new Sym('bb'), new Sym('aa')]).map(String)).toEqual(['aa', 'bb']);
});

it('selects leading and trailing terms with graded monomial orders', () => {
  const X = new Sym('x'), Y = new Sym('y'), Z = new Sym('z');
  const p = Poly.from(parse('2*x**2*y**3+x*y**7'), [X, Y]);
  expect(String(p.LM({ order: 'grlex' }))).toBe('x*y**7');
  expect(String(p.EM({ order: 'grlex' }))).toBe('x**2*y**3');
  expect(p.LC({ order: 'grlex' }).equals(1)).toBe(true);
  expect(p.EC({ order: 'grlex' }).equals(2)).toBe(true);
  expect(p.LT({ order: 'grlex' })[0]).toEqual([1, 7]);
  const q = Poly.from(parse('x*y**2+x**2*z+y**4'), [X, Y, Z]);
  expect(q.LT({ order: 'grevlex' })[0]).toEqual([0, 4, 0]);
  expect(q.ET({ order: 'grevlex' })[0]).toEqual([2, 0, 1]);
  expect(q.ET({ order: 'grlex' })[0]).toEqual([1, 2, 0]);
  expect(Poly.from(0, [X]).ET()).toEqual([[0], sj.S.Zero]);
});

it('preserves sparse domains and handles unsupported algebraic root domains explicitly', () => {
  const X = new Sym('x');
  expect(sj.sortGens([new Sym('a1'), new Sym('a2')]).map(String)).toEqual(['a1', 'a2']);
  const p = Poly.from(X, [X]).termwise((_m, c) => mul(c, sj.S.I, R(1, 2)));
  expect(p.toField().domain).toBe('QQ_I');
  for (const e of ['x**2+pi', 'x**2+sqrt(2)+sqrt(3)+sqrt(5)+sqrt(7)', 'x**2+sqrt(2)*pi']) {
    expect(() => Poly.from(parse(e), [X]).allRoots()).toThrow(sj.DomainError);
  }
  expect(() => sj.lcm(parse('sin(x)'), parse('1.0*x'))).toThrow(sj.PolynomialError);
  const q = sj.Quaternion(parse('x**2-1'), 0, 0, 0);
  expect(String(sj.factorNc(q))).toBe(String(sj.Quaternion(parse('(x-1)*(x+1)'), 0, 0, 0)));
});

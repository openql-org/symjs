// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/** Poly methods (polys/sympoly); expected values from SymPy 1.14 (tuples written as [...]). */

import { describe, expect, it } from 'vitest';
import * as sj from '../src';

const { Poly, parse } = sj;
const [x, y, z] = sj.symbols('x y z') as [sj.Sym, sj.Sym, sj.Sym];
const P = (e: string, ...g: sj.Expr[]) => Poly.from(parse(e), g);
const R = (p: number, q = 1) => sj.Rational.of(BigInt(p), BigInt(q));
const show = (r: unknown): string => (Array.isArray(r) ? `[${r.map(show).join(', ')}]` : String(r));
const f = P('2*x**3 - 3*x + 1', x);

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
    // SymPy raises PolynomialError (y is not a generator); symjs integrates the coefficients
    expect(String(P('x**2 + 1', x).integrate(y))).toBe("Poly(y*x**2 + y, x, domain='ZZ[y]')");
    expect(() => P('y*x**2 + 1', x).integrate(y)).toThrow(sj.NotImplementedError);
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
    expect(String(P('x**2 - sqrt(2)*x + 1', x).norm())).toBe("Poly(x**4 + 1, x, domain='QQ')");
    expect(String(P('x - I', x).lift())).toBe("Poly(x**2 + 1, x, domain='ZZ')");
    expect(String(P('x - I/2', x).lift())).toBe("Poly(x**2 + 1/4, x, domain='QQ')");
    // SymPy raises NotImplementedError / DomainError here; symjs returns the polynomial unchanged
    expect(String(P('x*y', x, y).eject(z))).toBe("Poly(x*y, x, y, domain='ZZ')");
    expect(String(P('x - 1', x).lift())).toBe("Poly(x - 1, x, domain='ZZ')");
    expect(String(P('x - 1', x).norm())).toBe("Poly(x - 1, x, domain='ZZ')");
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
    // SymPy raises PolynomialError for a non-generator; symjs gives degree 0
    expect(P('x**2', x).degree(y)).toBe(0);
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
    expect(() => P('x - pi', x).norm()).toThrow(sj.NotImplementedError);
    expect(() => P('x - pi*sqrt(2)', x).norm()).toThrow(sj.NotImplementedError);
    // SymPy gives the roots as CRootOf of the degree-8 norm; symjs keeps the radicals
    expect(show(P('x**2 - sqrt(2)*x + I', x).allRoots({ extension: true }))).toBe(
      '[-re(sqrt(2 - 4*I))/2 + sqrt(2)/2 - I*im(sqrt(2 - 4*I))/2, sqrt(2)/2 + re(sqrt(2 - 4*I))/2 + I*im(sqrt(2 - 4*I))/2]',
    );
    const r = sj.rootof(parse('x**3 - x - 2'), 0);
    expect(show(P('x**3 - x - 1', x).whichAllRoots([r]))).toBe('[]');
  });
});

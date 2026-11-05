// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Expected values from SymPy 1.14.0 (polys/domains, old_poly_ring, DMP, DMF).

import { afterEach, describe, expect, it } from 'vitest';
import { Float, Rational, Sym, parseExpr as P, sstr } from '../../src/index';
import { ExactQuotientFailed, NotImplementedError } from '../../src/core/errors';
import { CoercionFailed, DMF, DMP, EX, Expression, ExpressionDomain, FractionField, IntegerRing, PolynomialRing, QQ, RR, RationalField, RealField, ZZ, domainArith, domainNeg, gcdSettings, groundRational, groundToSympy, isDomainElement } from '../../src/polys/domains';
import { PythonMPQ } from '../../src/polys/domains/pythonrational';
import '../../src/polys/domains/algebraicfield';

const x = new Sym('x');
const a = new Sym('a');
const b = new Sym('b');
const s = (e: Parameters<typeof sstr>[0]) => sstr(e);

describe('ground domains', () => {
  it('names, fields and unification (SymPy unify)', () => {
    expect([ZZ, QQ, RR].map(String)).toEqual(['ZZ', 'QQ', 'RR']);
    expect(String(QQ.polyRing(a, b))).toBe('QQ[a,b]');
    expect(String(QQ.fracField(a))).toBe('QQ(a)');
    expect(String(ZZ.polyRing(a).getField())).toBe('ZZ(a)');
    expect(String(ZZ.fracField(a))).toBe('ZZ(a)');
    expect(String(QQ.polyRing(a).fracField(b))).toBe('QQ(a,b)');
    expect([ZZ.isField, QQ.isField, RR.isField, QQ.polyRing(a).isField]).toEqual([false, true, true, false]);
    expect(ZZ.getField()).toBe(QQ);
    expect(RR.getField()).toBe(RR);
    expect(QQ.fracField(a).getField().equals(QQ.fracField(a))).toBe(true);
    expect(ZZ.unify(ZZ)).toBe(ZZ);
    expect(ZZ.unify(QQ)).toBe(QQ);
    expect(RR.unify(QQ)).toBe(RR);
    expect(QQ.unify(ZZ)).toBe(QQ);
    expect(String(QQ.fracField(a).unify(RR))).toBe('RR(a)');
    expect(String(QQ.polyRing(a).unify(ZZ.polyRing(a, b)))).toBe('QQ[a,b]');
    expect(String(QQ.polyRing(a).unify(QQ.fracField(b)))).toBe('QQ(a,b)');
    expect(() => QQ.oldPolyRing(x, a)).toThrow(NotImplementedError);
  });
  it('conversions (from_sympy)', () => {
    expect(s(ZZ.fromSympy(3))).toBe('3');
    expect(s(ZZ.fromSympy(new Float(2)))).toBe('2');
    expect(() => ZZ.fromSympy(Rational.of(1n, 2n))).toThrow(CoercionFailed);
    expect(() => ZZ.fromSympy(new Float(2.5))).toThrow(CoercionFailed);
    expect(s(QQ.fromSympy(new Float(1.4)))).toBe('7/5');
    expect(() => QQ.fromSympy(P('sqrt(2)'))).toThrow(CoercionFailed);
    expect(s(RR.fromSympy(Rational.of(1n, 4n)))).toBe('0.250000000000000');
    expect(s(RR.fromSympy(P('pi')))).toBe('3.14159265358979');
    expect(s(RR.fromSympy(new Float(1.5, 80)))).toBe('1.50000000000000');
    expect(() => RR.fromSympy(x)).toThrow(CoercionFailed);
    expect(() => RR.fromSympy(P('I'))).toThrow(CoercionFailed);
    const F = QQ.fracField(a);
    expect(s(F.fromSympy(P('(a**2 - 1)/(a + 1)')))).toBe('a - 1');
    expect(() => F.fromSympy(P('sin(a)'))).toThrow(CoercionFailed);
    expect(() => F.fromSympy(P('b'))).toThrow(CoercionFailed);
    expect(() => F.fromSympy(new Float(1.5))).toThrow(CoercionFailed);
    expect(s(F.fromSympy(a))).toBe('a');
    expect(s(RR.fracField(a).fromSympy(P('1.5*a')))).toBe('1.5*a');
    const Pa = QQ.polyRing(a);
    expect(s(Pa.fromSympy(P('(a + 1)**2')))).toBe('a**2 + 2*a + 1');
    expect(() => Pa.fromSympy(P('1/a'))).toThrow(CoercionFailed);
    expect(() => ZZ.polyRing(a).fromSympy(P('a/2'))).toThrow(CoercionFailed);
    expect(() => Pa.fromSympy(P('a**(1/2)'))).toThrow(CoercionFailed);
    expect(Pa).toBeInstanceOf(PolynomialRing);
    expect(F).toBeInstanceOf(FractionField);
  });
  it('arithmetic', () => {
    expect(s(QQ.sub(Rational.of(1n, 2n), Rational.of(1n, 3n)))).toBe('1/6');
    expect(s(ZZ.quo(Rational.of(1n), Rational.of(3n)))).toBe('1/3');
    expect(s(RR.quo(Rational.of(1n), new Float(3)))).toBe('0.333333333333333');
    expect(QQ.isNegative(Rational.of(-1n))).toBe(true);
    expect(RR.isNegative(new Float(-1))).toBe(true);
    expect(QQ.fracField(a).isZero(a)).toBe(false);
  });
  it('EX: expressions (SymPy ExpressionDomain)', () => {
    expect([String(EX), EX.isField]).toEqual(['EX', true]);
    expect(EX.getField()).toBe(EX);
    expect(EX.unify(QQ)).toBe(EX);
    expect(QQ.fracField(a).unify(EX)).toBe(EX);
    // SymPy keeps EX(sqrt(2)*(x + sqrt(2))) until an operation, which simplifies with cancel and expand
    expect(s(EX.fromSympy(P('sqrt(2)*(sqrt(2) + x)')))).toBe('sqrt(2)*x + 2');
    expect(s(EX.fromSympy(P('(x**2 - 1)/(x + 1)')))).toBe('x - 1');
    expect(s(EX.mul(P('sqrt(2)*I'), P('sqrt(2)*I')))).toBe('-2');
    expect(EX.isZero(EX.sub(P('(sqrt(2) + 1)*(sqrt(2) - 1)'), Rational.of(1n)))).toBe(true);
  });
});

describe('old polynomial rings (DMP) and their fraction fields (DMF)', () => {
  afterEach(() => {
    gcdSettings.heuristicTries = 6;
  });
  const R = ZZ.oldPolyRing(x);
  const RQ = QQ.oldPolyRing(x);
  it('the ring', () => {
    expect(String(R)).toBe('ZZ[x]');
    expect(R.gens).toEqual([x]);
    expect(String(R.fromList([1, 0, -1]))).toBe('DMP(x**2 - 1, ZZ)');
    expect(() => R.fromSympy(P('1/x'))).toThrow(CoercionFailed);
    expect(R.zero.degree()).toBe(-Infinity);
    expect(s(R.zero.LC())).toBe('0');
    expect(R.zero.allCoeffs().map(s)).toEqual(['0']);
    expect(R.fromSympy(P('x**2')).toList().map(s)).toEqual(['1', '0', '0']);
  });
  it('gcd and lcm (SymPy: ZZ keeps the content, QQ is monic)', () => {
    const f = R.fromSympy(P('6*x + 6'));
    const g = R.fromSympy(P('4*x**2 - 4'));
    expect(s(f.gcd(g).toSympy())).toBe('2*x + 2');
    expect(s(R.fromSympy(P('2*x + 2')).lcm(g).toSympy())).toBe('4*x**2 - 4');
    expect(s(RQ.fromSympy(P('6*x + 6')).gcd(RQ.fromSympy(P('4*x**2 - 4'))).toSympy())).toBe('x + 1');
    expect(s(RQ.fromSympy(P('2*x + 2')).lcm(RQ.fromSympy(P('4*x**2 - 4'))).toSympy())).toBe('x**2 - 1');
    expect(s(R.zero.gcd(g).toSympy())).toBe('4*x**2 - 4');
    expect(s(g.gcd(R.zero).toSympy())).toBe('4*x**2 - 4');
    expect(R.zero.gcd(R.zero).isZero).toBe(true);
    expect(R.zero.lcm(g).isZero).toBe(true);
    expect(g.lcm(R.zero).isZero).toBe(true);
    expect(R.zero.exquo(g).isZero).toBe(true);
    expect(s(R.fromSympy(3).gcd(g).toSympy())).toBe('1');
    // the Euclidean algorithm after the heuristic
    gcdSettings.heuristicTries = 0;
    expect(s(R.fromSympy(P('(x + 1)*(x**2 + 3)')).gcd(R.fromSympy(P('(x + 1)*(x - 5)'))).toSympy())).toBe('x + 1');
    expect(s(R.fromSympy(P('x - 5')).gcd(R.fromSympy(P('(x + 1)*(x**2 + 3)'))).toSympy())).toBe('1');
  });
  it('the heuristic gcd through the cofactors', () => {
    const f = R.fromSympy(P('(x**3 + 7*x - 1)*(2*x**2 + 1)'));
    const g = R.fromSympy(P('(x**3 + 7*x - 1)*(5*x + 3)'));
    expect(s(f.gcd(g).toSympy())).toBe('x**3 + 7*x - 1');
    expect(s(g.gcd(f).toSympy())).toBe('x**3 + 7*x - 1');
  });
  it('exact division', () => {
    expect(s(R.fromSympy(P('x**2 - 1')).exquo(R.fromSympy(P('x - 1'))).toSympy())).toBe('x + 1');
    expect(() => R.fromSympy(P('x**2')).exquo(R.fromSympy(P('2*x')))).toThrow(ExactQuotientFailed);
    expect(() => R.fromSympy(P('x**2')).exquo(R.fromSympy(P('x + 1')))).toThrow(ExactQuotientFailed);
    expect(() => R.fromSympy(P('x')).exquo(R.zero)).toThrow(RangeError);
    expect(() => R.fromSympy(P('x')).exquo(R.fromSympy(P('x**2')))).toThrow(ExactQuotientFailed);
    const RA = QQ.fracField(a).oldPolyRing(x);
    expect(s(RA.fromSympy(P('x**2 - a**2')).exquo(RA.fromSympy(P('x - a'))).toSympy())).toBe('a + x');
    expect(() => RA.fromSympy(P('x**2')).exquo(RA.fromSympy(P('x - a')))).toThrow(ExactQuotientFailed);
    expect(() => RA.fromSympy(P('x')).exquo(RA.zero)).toThrow(RangeError);
  });
  it('polynomials over fraction fields, polynomial rings and RR', () => {
    const RA = QQ.fracField(a).oldPolyRing(x);
    expect(s(RA.fromSympy(P('a*x + a')).gcd(RA.fromSympy(P('x**2 - 1'))).toSympy())).toBe('x + 1');
    expect(s(RA.fromSympy(P('a*x + a')).lcm(RA.fromSympy(P('x - 1'))).toSympy())).toBe('x**2 - 1');
    const RP = ZZ.polyRing(a).oldPolyRing(x);
    expect(s(RP.fromSympy(P('a*x + a')).gcd(RP.fromSympy(P('x**2 - 1'))).toSympy())).toBe('x + 1');
    const RF = RR.oldPolyRing(x);
    expect(s(RF.fromSympy(P('2.0*x + 2.0')).gcd(RF.fromSympy(P('x**2 - 1'))).toSympy())).toBe('1.0*x + 1.0');
    expect(s(RF.fromSympy(P('2.0*x + 2.0')).lcm(RF.fromSympy(P('x - 1'))).toSympy())).toBe('1.0*x**2 - 1.0');
    expect(s(RF.fromSympy(P('x**2 - 1')).exquo(RF.fromSympy(P('2.0*x + 2.0'))).toSympy())).toBe('0.5*x - 0.5');
  });
  it('shift, derivative and equality', () => {
    const p = R.fromSympy(P('x**2'));
    expect(s(p.shift(1).toSympy())).toBe('x**2 + 2*x + 1');
    expect(s(p.diff().toSympy())).toBe('2*x');
    expect(s(p.mulGround(3).toSympy())).toBe('3*x**2');
    expect(p.equals(P('x**2'))).toBe(true);
    expect(p.equals(P('1/x'))).toBe(false);
    expect(p.equals(P('x'))).toBe(false);
  });
  it('fractions (DMF, SymPy dmp_cancel)', () => {
    const K = R.getField();
    expect(String(K)).toBe('ZZ(x)');
    const f = K.fromSympy(P('(2*x + 2)/(-4*x**2 + 4)'));
    expect(s(f.numer().toSympy())).toBe('-1');
    expect(s(f.denom().toSympy())).toBe('2*x - 2');
    expect(String(f)).toBe('DMF(-1/(2*x - 2), ZZ)');
    expect(s(f.toSympy())).toBe('-1/(2*x - 2)');
    expect(f.add(f.neg()).isZero).toBe(true);
    expect(s(f.add(R.one).toSympy())).toBe('(2*x - 3)/(2*x - 2)');
    expect(s(f.sub(1).toSympy())).toBe('(1 - 2*x)/(2*x - 2)');
    expect(s(f.mul(P('x - 1')).toSympy())).toBe('-1/2');
    expect(s(f.div(f).toSympy())).toBe('1');
    expect(s(f.diff().toSympy())).toBe('1/(2*x**2 - 4*x + 2)');
    expect(f.equals(P('-1/(2*x - 2)'))).toBe(true);
    expect(f.equals(R.one)).toBe(false);
    expect(K.zero.isZero).toBe(true);
    expect(K.one.equals(1)).toBe(true);
    expect(() => K.frac(R.one, R.zero)).toThrow(RangeError);
    const KQ = RQ.getField();
    expect(s(KQ.fromSympy(P('x/2')).toSympy())).toBe('x/2');
    expect(s(KQ.fromSympy(P('(x/2)/(3*x + 1)')).toSympy())).toBe('x/(6*(x + 1/3))');
    const KR = RR.oldPolyRing(x).getField();
    expect(s(KR.fromSympy(P('(2.0*x + 2.0)/(x**2 - 1)')).toSympy())).toBe('2.0/(1.0*x - 1.0)');
    expect(f).toBeInstanceOf(DMF);
    expect(f.numer()).toBeInstanceOf(DMP);
  });
  it('polynomials and fractions over EX', () => {
    const RE = EX.oldPolyRing(x);
    const KE = RE.getField();
    expect(String(KE)).toBe('EX(x)');
    // SymPy: DMF(([EX(sqrt(2)*I), EX(0)], [EX(2)]), EX) and its square DMF(([EX(-2), EX(0), EX(0)], [EX(4)]), EX)
    const f = KE.fromSympy(P('sqrt(2)*I*x/2'));
    expect(s(f.toSympy())).toBe('sqrt(2)*I*x/2');
    expect(s(f.mul(f).toSympy())).toBe('-x**2/2');
    // SymPy: DMF(([EX(1), EX(-sqrt(2))], [EX(sqrt(2))]), EX) = (x - sqrt(2))/sqrt(2)
    expect(s(KE.fromSympy(P('(x**2 - 2)/(sqrt(2)*x + 2)')).toSympy())).toBe('sqrt(2)*x/2 - 1');
    const p = RE.fromSympy(P('x**2 - 2'));
    const q = RE.fromSympy(P('sqrt(2)*x + 2'));
    expect(s(p.gcd(q).toSympy())).toBe('x + sqrt(2)');
    expect(s(p.lcm(q).toSympy())).toBe('x**2 - 2');
    expect(s(p.exquo(RE.fromSympy(P('x - sqrt(2)'))).toSympy())).toBe('x + sqrt(2)');
    expect(() => p.exquo(RE.fromSympy(P('x - 1')))).toThrow(ExactQuotientFailed);
  });
});

describe('domain classes', () => {
  it('are exported with SymPy names', () => {
    expect(ZZ).toBeInstanceOf(IntegerRing);
    expect(QQ).toBeInstanceOf(RationalField);
    expect(RR).toBeInstanceOf(RealField);
    expect(EX).toBeInstanceOf(ExpressionDomain);
  });
});

describe('SymPy ground elements (bigint ZZ, PythonMPQ QQ)', () => {
  it('ZZ', () => {
    expect([ZZ.new(2), ZZ.convert(Rational.of(4n)), ZZ.convert(new PythonMPQ(6n, 3n)), ZZ.convert(3, QQ), ZZ.convert(new Float(2))]).toEqual([2n, 4n, 2n, 3n, 2n]);
    expect(() => ZZ.convert(Rational.of(1n, 2n))).toThrow(CoercionFailed);
    expect(() => ZZ.convert('a')).toThrow(CoercionFailed);
    expect([ZZ.ofType(1n), ZZ.ofType(1), ZZ.gcd(4, 6), ZZ.lcm(4, 6), ZZ.div(-7, 2), ZZ.rem(-7, 2), ZZ.exquo(-6, 3), ZZ.log(8, 2), ZZ.log(9, 2), ZZ.log(1000, 10)]).toEqual([true, false, 2n, 12n, [-4n, 1n], 1n, -2n, 3n, 3n, 2n]);
    expect(() => ZZ.exquo(5, 2)).toThrow(ExactQuotientFailed);
    expect(() => ZZ.div(5, 0)).toThrow(RangeError);
    expect([ZZ.getRing(), ZZ.dom, ZZ.ngens]).toEqual([ZZ, ZZ, 0]);
    expect([ZZ.isPositive(2n), ZZ.isPositive(x), ZZ.isNegative(-1), ZZ.isNegative(x), ZZ.isNonnegative(0), ZZ.isNonnegative(x), ZZ.isNonpositive(0), ZZ.isNonpositive(x), ZZ.isOne(1n), ZZ.isZero(0)]).toEqual([true, false, true, false, true, false, true, false, true, true]);
    expect([ZZ.toSympy(3n), ZZ.toSympy(1.5), ZZ.toSympy(new PythonMPQ(1n, 2n))].map(s)).toEqual(['3', '1.50000000000000', '1/2']);
    expect(() => ZZ.toSympy('a')).toThrow(CoercionFailed);
    expect(() => ZZ.toDict(1)).toThrow(NotImplementedError);
  });
  it('QQ', () => {
    expect([QQ.new(1, 2), QQ.new(3), QQ.convert(new Float(0.5)), QQ.convert(2n, ZZ)].map(String)).toEqual(['1/2', '3', '1/2', '2']);
    expect(() => QQ.convert('a')).toThrow(CoercionFailed);
    expect([QQ.ofType(QQ.new(1)), QQ.ofType(1), QQ.getRing() === ZZ].map(String)).toEqual(['true', 'false', 'true']);
    expect([QQ.gcd(Rational.of(2n, 3n), Rational.of(4n, 9n)), QQ.lcm(Rational.of(2n, 3n), Rational.of(4n, 9n)), QQ.exquo(5, 2), QQ.rem(5, 2)].map(String)).toEqual(['2/9', '4/3', '5/2', '0']);
    expect(QQ.div(5, 2).map((e) => e.repr())).toEqual(['MPQ(5,2)', 'MPQ(0,1)']);
    expect(String(QQ.algebraicField(P('sqrt(2)')))).toBe('QQ<sqrt(2)>');
  });
  it('base domain defaults', () => {
    for (const f of ['gcd', 'lcm', 'div', 'exquo', 'rem'] as const) expect(() => RR[f](1, 2)).toThrow(NotImplementedError);
    expect([RR.ofType(new Float(1)), String(RR.new(2)), RR.getRing()]).toEqual([true, '2.00000000000000', RR]);
    expect(() => RR.convert({})).toThrow(CoercionFailed);
    expect(String(QQ.fracField(a).getRing())).toBe('QQ[a]');
  });
  it('arithmetic on elements of any representation', () => {
    expect([domainArith(ZZ, 'add', 2, 3), domainArith(ZZ, 'sub', 2, 3), domainArith(ZZ, 'mul', 2, 3), domainArith(ZZ, 'quo', -7, 2), domainNeg(ZZ, 2)]).toEqual([5n, -1n, 6n, -4n, -2n]);
    expect([domainArith(QQ, 'add', 1, 2), domainArith(QQ, 'quo', 1, 2)].map(String)).toEqual(['3', '1/2']);
    expect([domainArith(RR, 'add', 1, 2), domainArith(RR, 'sub', 1, 2), domainArith(RR, 'mul', 2, 3), domainArith(RR, 'quo', 1, 4)].map(String)).toEqual(['3.00000000000000', '-1.00000000000000', '6.00000000000000', '0.250000000000000']);
    expect([isDomainElement(QQ.new(1)), isDomainElement(x), isDomainElement(null), groundToSympy('a')]).toEqual([true, false, false, 'a']);
    expect(groundRational(x)).toBeUndefined();
  });
  it('EX elements (SymPy ExpressionDomain.Expression)', () => {
    const e = EX.convert(P('sqrt(2)'));
    expect([e.add(1), e.mul(e), e.div(2), e.neg(), e.pow(2), e.sub(1), EX.convert(3), EX.convert(e), EX.convert(QQ.new(1, 2), QQ), new Expression(P('x*(x + 1)'))].map(String)).toEqual(['EX(1 + sqrt(2))', 'EX(2)', 'EX(sqrt(2)/2)', 'EX(-sqrt(2))', 'EX(2)', 'EX(-1 + sqrt(2))', 'EX(3)', 'EX(sqrt(2))', 'EX(1/2)', 'EX(x**2 + x)']);
    expect([e.repr(), e.equals(P('sqrt(2)')), e.equals(e), e.isZero, EX.convert(0).isZero]).toEqual(['EX(sqrt(2))', true, true, false, true]);
    expect([s(EX.toSympy(e)), s(EX.toSympy(2)), EX.ofType(e), EX.ofType(x), EX.isZero(EX.convert(0)), EX.isZero(0)]).toEqual(['sqrt(2)', '2', true, false, true, true]);
  });
  it('polynomial-ring elements from dicts (SymPy PolyElement is a dict)', () => {
    const R = ZZ.polyRing(a, b);
    expect([R.new(new Map([[[1, 0], 2n], [[0, 2], 3n]])), R.new(a), R.convert(new Map([[1, 1]])), R.toSympy(new Map([[[0, 1], 2]]))].map(String)).toEqual(['2*a + 3*b**2', 'a', 'a', '2*b']);
    expect([...R.toDict(P('2*a*b + 3*a*b + a**2 + 0*b'))].map(([m, c]) => `${m.join(',')}:${String(c)}`)).toEqual(['1,1:5', '2,0:1']);
    expect([...R.toDict(new Map([[[1, 0], 2]]))].map(([m, c]) => `${m.join(',')}:${String(c)}`)).toEqual(['1,0:2']);
    expect([R.ngens, R.dom]).toEqual([2, ZZ]);
  });
});

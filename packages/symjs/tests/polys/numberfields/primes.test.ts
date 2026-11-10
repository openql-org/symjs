// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// References from SymPy 1.14.0 (scripts/gen_numberfields.py): prime decompositions, prime ideals in
// two-element form, their test factors, powers, sums, reductions and valuations.
import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import { Rational, Sym, parseExpr as P, sqrt } from '../../../src';
import { AlgebraicField } from '../../../src/polys/domains/algebraicfield';
import { QQ, ZZ } from '../../../src/polys/domains';
import { DomainMatrix } from '../../../src/polys/matrices/domainmatrix';
import { AlgebraicNumber } from '../../../src/polys/numberfields';
import { roundTwo } from '../../../src/polys/numberfields/basis';
import { StructureError } from '../../../src/polys/numberfields/exceptions';
import { PowerBasis, toCol } from '../../../src/polys/numberfields/modules';
import { PrimeIdeal, primeDecomp, primeValuation } from '../../../src/polys/numberfields/primes';
import { Poly } from '../../../src/polys/sympoly';

const ref = JSON.parse(readFileSync(new URL('./numberfields.references.json', import.meta.url), 'utf8'));
const x = new Sym('x');
const theta = new Sym('theta');
const poly = (s: string): Poly => Poly.from(P(s), [x]);
const s = (v: unknown): string => String(v);

describe('primeDecomp', () => {
  for (const r of ref.fields) {
    it(`primes of ${r.T}`, () => {
      const T = poly(r.T);
      const [ZK, dK] = roundTwo(T);
      const pb = ZK.powerBasisAncestor();
      for (const { p, ideals } of r.primes) {
        const P = primeDecomp(p, { T });
        expect(P.map((Q) => Q.repr()), `p = ${p}`).toEqual(ideals.map((i: { repr: string }) => i.repr));
        // the decomposition of p: sum of e*f over the primes is the degree
        expect(P.reduce((a, Q) => a + Q.e * Q.f, 0)).toBe(T.degree());
        P.forEach((Q, k) => {
          const i = ideals[k];
          expect([s(Q), Q.repr(theta, true), Q.e, Q.f, Q.isInert], `p = ${p}`).toEqual([i.str, i.gens, i.e, i.f, i.inert]);
          expect([Q.alpha.coeffs.map(String), s(Q.alpha.denom)]).toEqual(i.alpha);
          expect([Q.testFactor().coeffs.map(String), s(Q.testFactor().denom)]).toEqual(i.test_factor);
          expect([s(Q.asSubmodule()), s(Q.pow(2)), s(Q.add(ZK.mul(p)))]).toEqual([i.submodule, i.square, i.sum]);
          expect(P.map((R) => primeValuation(R.asSubmodule(), Q))).toEqual(i.valuations);
          expect(primeValuation(ZK.mul(p * p), Q)).toBe(i.valuation_p2);
          expect(s(Q.reduceElement(pb.call(toCol(Array.from({ length: ZK.n }, (_, j) => 3 + j)))))).toBe(i.reduce);
        });
        // with the maximal order and the discriminant given
        expect(primeDecomp(p, { ZK, dK }).map((Q) => Q.repr())).toEqual(P.map((Q) => Q.repr()));
      }
    });
  }
  it('takes the polynomial of the maximal order', () => {
    const [ZK] = roundTwo(poly('x**3 + x**2 - 2*x + 8'));
    expect(primeDecomp(2, { ZK }).map((Q) => Q.repr())).toEqual(ref.fields[0].primes[0].ideals.map((i: { repr: string }) => i.repr));
    expect(primeDecomp(2, { ZK, dK: Rational.of(-503) }).length).toBe(3);
    expect(primeDecomp(2, { ZK, dK: -503n }).length).toBe(3);
    expect(() => primeDecomp(2)).toThrow(RangeError);
  });
  it('uses the polynomial of the maximal order for the index (T not monic)', () => {
    // 2*x**2 - 3: theta' = 2*theta is a root of x**2 - 6, ZK = ZZ[sqrt(6)]; 2 and 3 ramify
    const P2 = primeDecomp(2, { T: poly('2*x**2 - 3') });
    const P3 = primeDecomp(3, { T: poly('2*x**2 - 3') });
    expect([P2.map((Q) => Q.repr()), P3.map((Q) => Q.repr())]).toEqual([['[ (2, x) e=2, f=1 ]'], ['[ (3, x) e=2, f=1 ]']]);
  });
  it('splits with an element outside the prime field', () => {
    // x**2 - 588 = (14*sqrt(3))**2 - 588: 7 divides the index and is inert in QQ(sqrt(3)) (SymPy's assertion fails)
    expect(primeDecomp(7, { T: poly('x**2 - 588') }).map((Q) => Q.repr())).toEqual(['[ (7, 0) e=1, f=2 ]']);
  });
});

describe('PrimeIdeal', () => {
  const T = poly('x**6 + x**5 + x**4 + x**3 + x**2 + x + 1');
  const [ZK] = roundTwo(T);
  const P7 = primeDecomp(7, { T })[0]!;
  it('works with powers, sums and products', () => {
    expect(P7.pow(6).equals(ZK.mul(7))).toBe(true);
    expect(P7.add(ZK.mul(7)).equals(P7.asSubmodule())).toBe(true);
    expect(P7.add(P7).equals(P7.asSubmodule())).toBe(true);
    expect(P7.mul(P7).equals(P7.pow(2))).toBe(true);
    expect(P7.mul(7).equals(P7.asSubmodule().mul(7))).toBe(true);
    expect(primeValuation(ZK.mul(2), P7)).toBe(0);
    expect(P7.pow(0)).toBe(P7.ZK);
    expect(P7.pow(1)).toBe(P7);
    expect(() => P7.pow(-1)).toThrow(TypeError);
    expect(P7.equals(primeDecomp(7, { T })[0])).toBe(true);
    expect(P7.equals(ZK)).toBe(false);
    expect(P7.valuation(ZK.mul(49))).toBe(12);
    // the zero ideal has infinite valuation (SymPy loops forever)
    expect(primeValuation(ZK.mul(0), P7)).toBe(Infinity);
    expect(() => primeValuation(ZK.submoduleFromMatrix(DomainMatrix.diag([1, 1, 1, 1, 1, 0].map((v) => Rational.of(v)), ZZ)), P7)).toThrow(RangeError);
    const inert = primeDecomp(3, { T })[0]!;
    expect([s(inert), inert.isInert, s(P7), P7.isInert]).toEqual(['(3)', true, '(7, x - 1)', false]);
    expect(s(primeDecomp(5, { T: poly('x**2 - 2') })[0])).toBe('(5)');
  });
  it('reduces field elements', () => {
    const K = new AlgebraicField(QQ, new AlgebraicNumber(theta, [1, 0], { minpoly: T }));
    const Q = K.primesAbove(7)[0]!;
    // Q = (7, theta - 1): theta = 1 in the residue field GF(7), so a = 1 + 2 + 3 + 4 + 5 + 7 = 1 modulo Q
    // (SymPy gives the same for reduce_ANP; its to_alg_num fails for this field)
    const a = K.new([1, 2, 3, 4, 5, 7]);
    expect(s(Q.reduceANP(a))).toBe('ANP([MPQ(1,1)], [MPQ(1,1), MPQ(1,1), MPQ(1,1), MPQ(1,1), MPQ(1,1), MPQ(1,1), MPQ(1,1)], QQ)');
    expect(s(Q.reduceAlgNum(K.toAlgNum(a)).coeffs())).toBe('1');
  });
  it('checks the maximal order', () => {
    const pb = new PowerBasis(poly('x**2 + 1'));
    const ZK1 = pb.wholeSubmodule();
    expect(() => new PrimeIdeal(ZK1.mul(2), 2, pb.call(1), 1)).toThrow(new StructureError('The submodule representing the maximal order should have 1 as its first generator.'));
    expect(() => new PrimeIdeal(ZK1.submoduleFromMatrix(DomainMatrix.eye(2, ZZ)), 2, pb.call(1), 1)).toThrow(StructureError);
    const notHNF = pb.submoduleFromMatrix(DomainMatrix.eye(2, ZZ).hstack(DomainMatrix.eye(2, ZZ)));
    expect(() => new PrimeIdeal(notHNF, 2, pb.call(1), 1)).toThrow(StructureError);
    expect(new PrimeIdeal(ZK1, 2, pb.call(0).add(pb.call(1)).overPowerBasis(), 1).e).toBe(2);
  });
  it('lies above the primes of an algebraic field', () => {
    for (const r of ref.algebraic) {
      if (r.name !== 'sqrt5') continue;
      const K = new AlgebraicField(QQ, sqrt(5));
      for (const [p, reprs] of Object.entries(r.primes)) expect(K.primesAbove(Number(p)).map((Q) => Q.repr())).toEqual(reprs);
    }
  });
});

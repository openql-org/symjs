// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Expected values from SymPy 1.14.0 (sympy.polys.domains.algebraicfield, polyclasses.ANP).

import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import { Dummy, Rational, Sym, parseExpr as P, sqrt } from '../../../src/index';
import type { Expr } from '../../../src/index';
import { Poly } from '../../../src/polys/sympoly';
import '../../../src/polys/numberfields/primes';
import { DomainError, NotInvertible } from '../../../src/core/errors';
import { CoercionFailed, QQ, ZZ } from '../../../src/polys/domains';
import { ANP, AlgebraicField } from '../../../src/polys/domains/algebraicfield';
import { PythonMPQ } from '../../../src/polys/domains/pythonrational';
import { AlgebraicNumber } from '../../../src/polys/numberfields';

const K = QQ.algebraicField(sqrt(2)) as AlgebraicField;

describe('AlgebraicField', () => {
  it('names and elements', () => {
    expect([String(K), String(ZZ.algebraicField(sqrt(2))), String(QQ.algebraicField(sqrt(2), sqrt(3))), String(K.algebraicField(sqrt(3)))]).toEqual(['QQ<sqrt(2)>', 'QQ<sqrt(2)>', 'QQ<sqrt(2) + sqrt(3)>', 'QQ<sqrt(2) + sqrt(3)>']);
    expect(String(K.new([1, 2]))).toBe('ANP([MPQ(1,1), MPQ(2,1)], [MPQ(1,1), MPQ(0,1), MPQ(-2,1)], QQ)');
    expect(() => new AlgebraicField(ZZ, sqrt(2))).toThrow(DomainError);
    expect(String(new AlgebraicField(QQ, new AlgebraicNumber(sqrt(2))))).toBe('QQ<sqrt(2)>');
    expect([String(K.dom), String(K.domain), K.origExt.map(String), K.characteristic()]).toEqual(['QQ', 'QQ', ['sqrt(2)'], 0n]);
  });
  it('arithmetic (SymPy doctests)', () => {
    const [a, b] = [K.new([1, 2]), K.new([3, 4])];
    const xk = K.convert(P('3 + 4*sqrt(2)'));
    const yk = K.convert(P('2 + sqrt(2)'));
    expect([xk.mul(yk), xk.add(yk), xk.pow(2), xk.div(yk)].map((e) => String(K.toSympy(e)))).toEqual(['14 + 11*sqrt(2)', '5 + 5*sqrt(2)', '24*sqrt(2) + 41', '-1 + 5*sqrt(2)/2']);
    expect([a.mul(b), a.div(b), a.pow(-2), a.sub(b), a.neg(), a.add(1)].map((e) => String(K.toSympy(e)))).toEqual(['14 + 10*sqrt(2)', '-1 + sqrt(2)', '3/2 - sqrt(2)', '-2*sqrt(2) - 2', '-2 - sqrt(2)', 'sqrt(2) + 3']);
    expect(() => a.div(K.new([]))).toThrow(NotInvertible);
    expect([K.new([]).mul(a).isZero, a.mul(0).isZero]).toEqual([true, true]);
    expect(() => a.add(QQ.algebraicField(sqrt(3)).new([1, 0]))).toThrow(CoercionFailed);
    expect([a.LC().toString(), a.toList().map(String), new ANP(5, [1, 0, -2]).toList().map(String), a.repr() === String(a), K.new([]).LC().toString()]).toEqual(['1', ['1', '2'], ['5'], true, '0']);
    expect([a.equals(K.new([1, 2])), a.equals(b), K.new([3]).equals(3), a.equals(3), K.new([3]).equals('x'), K.new([]).isZero]).toEqual([true, false, true, false, false, true]);
    expect([a.equals(new ANP([1, 2], [1, 0, 0, -2])), a.equals(new ANP([1, 3], [1, 0, -2]))]).toEqual([false, false]);
  });
  it('domain methods', () => {
    expect([K.convert(P('sqrt(2) + 3')), K.convert(Rational.of(1n, 2n)), K.convert(new PythonMPQ(2n)), K.convert(2, ZZ)].map(String)).toEqual([
      'ANP([MPQ(1,1), MPQ(3,1)], [MPQ(1,1), MPQ(0,1), MPQ(-2,1)], QQ)',
      'ANP([MPQ(1,2)], [MPQ(1,1), MPQ(0,1), MPQ(-2,1)], QQ)',
      'ANP([MPQ(2,1)], [MPQ(1,1), MPQ(0,1), MPQ(-2,1)], QQ)',
      'ANP([MPQ(2,1)], [MPQ(1,1), MPQ(0,1), MPQ(-2,1)], QQ)',
    ]);
    const a = K.new([1, 2]);
    expect(K.convert(a)).toBe(a);
    expect(() => K.convert(sqrt(3))).toThrow(CoercionFailed);
    expect(() => K.convert('x')).toThrow(CoercionFailed);
    expect([K.toSympy(2), K.canon(P('(1 + sqrt(2))**2')), K.fromSympy(P('sqrt(8)'))].map(String)).toEqual(['2', '2*sqrt(2) + 3', '2*sqrt(2)']);
    expect([K.ofType(a), K.ofType(1), K.isZero(K.new([])), K.isZero(0), K.isPositive(a), K.isNegative(K.new([-1, 2])), K.isNegative(-1), K.getField() === K]).toEqual([true, false, true, true, true, true, true, true]);
    expect(() => K.getRing()).toThrow(DomainError);
    expect([K.exquo(a, 2), K.rem(a, 2), K.gcd(a, 2), K.gcd(0, 0), K.lcm(a, 2)].map((e) => String(K.toSympy(e)))).toEqual(['sqrt(2)/2 + 1', '0', '1', '0', '2*sqrt(2) + 4']);
    expect(K.div(a, 2).map((e) => String(K.toSympy(e)))).toEqual(['sqrt(2)/2 + 1', '0']);
    expect([K.equals(QQ.algebraicField(sqrt(2))), K.equals(QQ)]).toEqual([true, false]);
    expect(String(K.toAlgNum(a).asExpr())).toBe('sqrt(2) + 2');
  });
});

// maximal orders, integral bases, discriminants and prime ideals (references from tools/sympy-reference/generators/gen_numberfields.py)
describe('AlgebraicField number-field methods', () => {
  const nf = JSON.parse(readFileSync(new URL('../numberfields/numberfields.references.json', import.meta.url), 'utf8')).algebraic;
  const x = new Sym('x'), theta = new Sym('theta'), zeta = new Sym('zeta');
  const poly = (s: string, g: Expr = x): Poly => Poly.from(P(s).subs(x, g), [g]);
  const fields: Record<string, () => AlgebraicField> = {
    sqrt5: () => new AlgebraicField(QQ, sqrt(5)),
    sqrt2_sqrt3: () => new AlgebraicField(QQ, sqrt(2), sqrt(3)),
    alpha: () => new AlgebraicField(QQ, new AlgebraicNumber(sqrt(5), [1, 0], { alias: 'alpha' })),
    theta: () => new AlgebraicField(QQ, new AlgebraicNumber(theta, [1, 0], { minpoly: poly('x**3 + x**2 - 2*x + 8') })),
    zeta7: () => new AlgebraicField(QQ, new AlgebraicNumber(zeta, [1, 0], { minpoly: poly('x**6 + x**5 + x**4 + x**3 + x**2 + x + 1') })),
    cyc5: () => {
      const d = new Dummy('x');
      return new AlgebraicField(QQ, new AlgebraicNumber(zeta, [1, 0], { minpoly: Poly.from(P('x**4 + x**3 + x**2 + x + 1').subs(x, d), [d], { pure: true }), alias: zeta }));
    },
  };
  const unMPQ = (s: string): string => s.replace(/MPQ\((-?\d+),1\)/g, '$1');
  for (const r of nf) {
    it(`computes the maximal order of ${r.name}`, () => {
      const K = fields[r.name]!();
      expect([String(K), String(K.maximalOrder()), String(K.discriminant())]).toEqual([r.K, r.ZK, r.dK]);
      expect(K.integralBasis().map((b) => unMPQ(String(b)))).toEqual(r.basis.map(unMPQ));
      // compared after parsing: SymPy orders the terms of an alias (an AlgebraicNumber) otherwise (1/2 + alpha/2)
      const sympy = r.sympy.map((e: string) => String(P(e)));
      expect(K.integralBasis('sympy').map(String)).toEqual(sympy);
      expect(K.integralBasis('alg').map((a) => String(K.toSympy(K.new(a.coeffs()))))).toEqual(sympy);
      for (const [p, reprs] of Object.entries(r.primes)) expect(K.primesAbove(Number(p)).map((Q) => Q.repr()), `p = ${p}`).toEqual(reprs);
    });
  }
  it('converts polynomials in the symbol of the primitive element', () => {
    const K = fields.theta!();
    expect([String(K.convert(P('theta**3 + 1/2'))), String(K.toSympy(K.convert(P('theta**4'))))]).toEqual([
      'ANP([MPQ(-1,1), MPQ(2,1), MPQ(-15,2)], [MPQ(1,1), MPQ(1,1), MPQ(-2,1), MPQ(8,1)], QQ)',
      '3*theta**2 - 10*theta + 8',
    ]);
    expect(() => K.convert(P('sqrt(2)*theta'))).toThrow(CoercionFailed);
    expect(() => K.convert(P('1/theta'))).toThrow(CoercionFailed);
    expect(() => K.convert(P('sqrt(2)'))).toThrow(CoercionFailed);
    const Ka = fields.alpha!();
    expect([String(Ka), Ka.origExt.map(String), String(Ka.toSympy(Ka.convert(P('alpha**2 + alpha')))), String(Ka.toSympy(Ka.convert(P('sqrt(5) + 1'))))]).toEqual(['QQ<alpha>', ['alpha'], 'alpha + 5', 'alpha + 1']);
    // an alias given to a non-primitive algebraic number names the field's primitive element
    const Kb = new AlgebraicField(QQ, new AlgebraicNumber(sqrt(2), [1, 1], { alias: 'beta' }));
    expect([String(Kb), String(Kb.toSympy(Kb.new([1, 0]))), String(Kb.ext.root)]).toEqual(['QQ<beta>', 'beta', '1 + sqrt(2)']);
    expect(String(new AlgebraicField(QQ, new AlgebraicNumber(sqrt(2), [2, 0])).ext.root)).toBe('2*sqrt(2)');
  });
});
it('computes the Galois group of the defining polynomial', () => {
  const x = new Sym('x');
  const K = new AlgebraicField(QQ, new AlgebraicNumber(new Sym('a'), [1,0], {minpoly: Poly.from(P('x**4+1'), [x])}));
  expect(String(K.galoisGroup({byName:true})[0])).toBe('S4TransitiveSubgroups.V');
  expect(K.galoisGroup()[1]).toBe(true);
});

describe('AlgebraicField characteristic and unification (SymPy test_Domain_unify_algebraic)', () => {
  it('has characteristic zero and unifies the extensions', () => {
    expect(K.hasCharacteristicZero).toBe(true);
    expect(String(K.unify(QQ.algebraicField(sqrt(3))))).toBe('QQ<sqrt(2) + sqrt(3)>');
    expect(String(K.polyRing(new Sym('x')).unify(K))).toBe('QQ<sqrt(2)>[x]');
  });
});

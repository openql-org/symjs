// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * Monomial, AlgebraicNumber, CRootOf and Groebner bases (polys/monomial,
 * numberfields, rootof, groebner); expected values from SymPy 1.14.
 */

import { describe, expect, it } from 'vitest';
import * as sj from '../src';
import { leadingMonomial } from '../src/polys/groebner';

const { parse } = sj;
const [x, y, z] = sj.symbols('x y z') as [sj.Sym, sj.Sym, sj.Sym];
const show = (r: unknown): string => (Array.isArray(r) ? `[${r.map(show).join(', ')}]` : String(r));

describe('Monomial', () => {
  it('operations zip the exponent tuples like SymPy', () => {
    const m = new sj.Monomial([1, 2]);
    expect(String(m.asExpr(x, y))).toBe('x*y**2');
    expect(String(m.mul(new sj.Monomial([1, 0])))).toBe('Monomial((2, 2))');
    expect(String(m.gcd(new sj.Monomial([0, 3])))).toBe('Monomial((0, 2))');
    expect(String(m.lcm(new sj.Monomial([3, 0])))).toBe('Monomial((3, 2))');
    // Monomial((1, 2))*(1,), .gcd((5,)), .lcm((0,)) -> Monomial((2,)), Monomial((1,)), Monomial((1,))
    expect(String(m.mul([1]))).toBe('Monomial((2,))');
    expect(String(m.gcd([5]))).toBe('Monomial((1,))');
    expect(String(m.lcm([0]))).toBe('Monomial((1,))');
    expect(String(m.asExpr(x))).toBe('x');
    expect(String(new sj.Monomial([1], [x, y]).asExpr())).toBe('x');
    expect(String(new sj.Monomial([1, 2], [x, y]))).toBe('x**1*y**2');
    expect(String(new sj.Monomial([1, 2], [x, y]).mul(new sj.Monomial([1, 1])).asExpr())).toBe('x**2*y**3');
    expect(String(new sj.Monomial([2], [x]))).toBe('x**2');
    expect(String(new sj.Monomial([2]))).toBe('Monomial((2,))');
    expect(() => m.asExpr()).toThrow('Cannot convert Monomial((1, 2)) to an expression without generators');
  });
});

describe('AlgebraicNumber', () => {
  it('values, coefficients and elements of elements', () => {
    const a = new sj.AlgebraicNumber(parse('sqrt(2)'), [1, 3]);
    expect(show(a.coeffs())).toBe('[1, 3]');
    expect(String(a.asExpr())).toBe('sqrt(2) + 3');
    expect(String(a.toRoot())).toBe('sqrt(2) + 3');
    expect(String(a.primitiveElement())).toBe('sqrt(2)');
    expect(String(a.evalf(10))).toBe('4.414213562');
    expect(String(new sj.AlgebraicNumber(parse('sqrt(2)')).asExpr())).toBe('sqrt(2)');
    const b = new sj.AlgebraicNumber(a, [2, 1]);
    expect(show(b.coeffs())).toBe('[2, 7]');
    expect(String(b.asExpr())).toBe('2*sqrt(2) + 7');
    expect(String(b.root)).toBe('sqrt(2)');
    expect(show(new sj.AlgebraicNumber(a, [1, 0, 0]).coeffs())).toBe('[6, 11]');
    // AlgebraicNumber(AlgebraicNumber(sqrt(2), [1, 0, 0]), [1, 0]).coeffs() -> [2]
    expect(show(new sj.AlgebraicNumber(new sj.AlgebraicNumber(parse('sqrt(2)'), [1, 0, 0]), [1, 0]).coeffs())).toBe('[2]');
    // AlgebraicNumber(AlgebraicNumber(sqrt(2), [1, 0, 5]), [1, 0]).coeffs() -> [7]
    expect(show(new sj.AlgebraicNumber(new sj.AlgebraicNumber(parse('sqrt(2)'), [1, 0, 5]), [1, 0]).coeffs())).toBe('[7]');
    const c = new sj.AlgebraicNumber(parse('2**(1/3)'), [1, 0, 0]);
    expect(String(c.asExpr())).toBe('2**(2/3)');
    // AlgebraicNumber(AlgebraicNumber(cbrt(2), [1, 0, 0]), [1, 0, 0]): [2, 0], 2*2**(1/3)
    const d = new sj.AlgebraicNumber(c, [1, 0, 0]);
    expect(show(d.coeffs())).toBe('[2, 0]');
    expect(String(d.asExpr())).toBe('2*2**(1/3)');
    expect(show(new sj.AlgebraicNumber(c, [1, 0]).coeffs())).toBe('[1, 0, 0]');
  });
  it('reduction modulo the minimal polynomial', () => {
    expect(show(new sj.AlgebraicNumber(parse('sqrt(2)'), [1, 0, 0]).coeffs())).toBe('[2]');
    expect(show(new sj.AlgebraicNumber(parse('sqrt(2)'), [1, 0, -2]).coeffs())).toBe('[0]');
    expect(show(new sj.AlgebraicNumber(parse('3'), [1, 3]).coeffs())).toBe('[6]');
    const s = new sj.AlgebraicNumber(parse('sqrt(2) + sqrt(3)'), [1, 0, 0]);
    expect(show(s.coeffs())).toBe('[1, 0, 0]');
    expect(show(new sj.AlgebraicNumber(s, [1, 0]).coeffs())).toBe('[1, 0, 0]');
    const s2 = new sj.AlgebraicNumber(s, [1, 0, 0]);
    expect(show(s2.coeffs())).toBe('[10, 0, -1]');
    expect(String(s2.asExpr())).toBe('20*sqrt(6) + 49');
    // SymPy reduces modulo minimal_polynomial(cos(pi/7)) = 8*x**3 - 4*x**2 - 4*x + 1, giving
    // [3/4, 1/8, -1/16]; symjs has no minimal polynomial for cos(pi/7) and keeps the composition
    const c = new sj.AlgebraicNumber(parse('cos(pi/7)'), [1, 0, 0]);
    expect(show(new sj.AlgebraicNumber(c, [1, 0, 0]).coeffs())).toBe('[1, 0, 0, 0, 0]');
  });
  it('minimal polynomials of radicals', () => {
    const X = new sj.Sym('x');
    expect(String(sj.minimalPolynomial(parse('2**(1/3)'), X))).toBe('x**3 - 2');
    expect(String(sj.minimalPolynomial(parse('2**(2/3)'), X))).toBe('x**3 - 4');
    expect(String(sj.minimalPolynomial(parse('sqrt(2) + sqrt(3)'), X))).toBe('x**4 - 10*x**2 + 1');
    expect(String(sj.minimalPolynomial(3, X))).toBe('x - 3');
    // SymPy: x**4 - 2*x**2 - 1 and NotAlgebraic for 2**pi; symjs handles rational radicals and square-root towers over QQ only
    expect(() => sj.minimalPolynomial(parse('sqrt(1 + sqrt(2))'), X)).toThrow(sj.NotImplementedError);
    expect(() => sj.minimalPolynomial(parse('2**pi'), X)).toThrow(sj.NotImplementedError);
  });
});

describe('CRootOf', () => {
  const f = parse('x**3 - x - 1');
  it('indices, printing and values', () => {
    const r = sj.rootof(f, 0);
    expect(String(r)).toBe('CRootOf(x**3 - x - 1, 0)');
    expect(sj.latex(r)).toBe('\\operatorname{CRootOf} {\\left(x^{3} - x - 1, 0\\right)}');
    expect(String(sj.rootof(f, -1))).toBe('CRootOf(x**3 - x - 1, 2)');
    expect(String(sj.rootof(sj.Poly.from(f, [x]), 1))).toBe('CRootOf(x**3 - x - 1, 1)');
    // SymPy raises IndexError: root index out of [-3, 2] range, got 3
    expect(() => sj.rootof(f, 3)).toThrow(RangeError);
    expect(() => sj.rootof(f, -4)).toThrow(RangeError);
    expect(String(r.evalf(20))).toBe('1.3247179572447460260');
    expect(String(sj.rootof(f, 1).evalf(15))).toBe('-0.662358978622373 - 0.562279512062301*I');
    expect(String(sj.rootof(f, 2).evalf(15))).toBe('-0.662358978622373 + 0.562279512062301*I');
    const c = new sj.CRootOf(f, sj.Rational.of(1n));
    expect(c.index).toBe(1);
    expect(c.isRealRoot).toBe(false);
    expect(new sj.CRootOf(f, 0).isRealRoot).toBe(true);
    // the root 0 of x**3 - x: CRootOf(x**3 - x, 1).is_real -> True
    expect(new sj.CRootOf(parse('x**3 - x'), 1).isRealRoot).toBe(true);
    expect(String(c.gen)).toBe('x');
    expect(String(c.poly)).toBe('x**3 - x - 1');
    expect(String(c.withArgs([f, sj.Rational.of(2n)]))).toBe('CRootOf(x**3 - x - 1, 2)');
    expect(() => c.withArgs([f, x])).toThrow('CRootOf index is not a Rational');
  });
});

describe('Groebner bases', () => {
  const F = [parse('x**3 - 2*x*y'), parse('x**2*y - 2*y**2 + x')];
  it('orders and domains', () => {
    expect(String(sj.groebner(F, [x, y], 'lex'))).toBe("GroebnerBasis([x - 2*y**2, y**3], x, y, domain='ZZ', order='lex')");
    expect(String(sj.groebner(F, [x, y], 'grlex'))).toBe("GroebnerBasis([x**2, x*y, 2*y**2 - x], x, y, domain='ZZ', order='grlex')");
    expect(String(sj.groebner(F, [x, y], 'grevlex'))).toBe("GroebnerBasis([x**2, x*y, 2*y**2 - x], x, y, domain='ZZ', order='grevlex')");
    expect(String(sj.groebner([parse('x/2 + y'), parse('y**2 - 1/3')], [x, y]))).toBe("GroebnerBasis([x + 2*y, y**2 - 1/3], x, y, domain='QQ', order='lex')");
    expect(String(sj.groebner([parse('x*y - 1'), parse('x**2 + y**2')], [x, y], 'grevlex'))).toBe(
      "GroebnerBasis([y**3 + x, x**2 + y**2, x*y - 1], x, y, domain='ZZ', order='grevlex')",
    );
    expect(String(sj.groebner([parse('x**2*y**3 - x*y**4'), parse('x**3*y - x*y**3'), parse('x*z - y*z')], [x, y, z], 'grevlex'))).toBe(
      "GroebnerBasis([x**2*y**3 - x*y**4, x**3*y - x*y**3, x*z - y*z], x, y, z, domain='ZZ', order='grevlex')",
    );
    // the terms are printed in the basis order over the sorted generators
    expect(String(sj.groebner([parse('x - y**2'), parse('x*y - 1')], [y, x]))).toBe("GroebnerBasis([-x**2 + y, x**3 - 1], y, x, domain='ZZ', order='lex')");
    expect(String(sj.groebner([parse('x - y**2'), parse('x*y - 1')], [y, x], 'grlex'))).toBe("GroebnerBasis([y**2 - x, x*y - 1, x**2 - y], y, x, domain='ZZ', order='grlex')");
    expect(String(sj.groebner([parse('x**3 - y'), parse('x*y - 1')], [y, x], 'grevlex'))).toBe("GroebnerBasis([x**3 - y, -x**2 + y**2, x*y - 1], y, x, domain='ZZ', order='grevlex')");
    expect(String(sj.groebner([parse('x**3 - y'), parse('x*y - 1')], [x, y], 'grevlex'))).toBe("GroebnerBasis([y**3 - x, x**2 - y**2, x*y - 1], x, y, domain='ZZ', order='grevlex')");
    expect(String(sj.groebner([0, x], [x]))).toBe("GroebnerBasis([x], x, domain='ZZ', order='lex')");
    expect(String(sj.groebner([parse('2*x + 4'), parse('6*y')], [x, y]))).toBe("GroebnerBasis([x + 2, y], x, y, domain='ZZ', order='lex')");
  });
  it('coefficients outside QQ and leading monomials', () => {
    // SymPy computes over ZZ[a]: GroebnerBasis([1], x, domain='ZZ[a]', order='lex');
    // symjs supports rational coefficients only
    expect(() => sj.groebner([parse('a*x - 1'), parse('x**2')], [x])).toThrow(sj.DomainError);
    expect(leadingMonomial(parse('x**2*y + y**3'), [x, y], 'grevlex')).toEqual([2, 1]);
    expect(leadingMonomial(parse('x**2*y + y**3'), [y, x], 'grevlex')).toEqual([3, 0]);
    expect(leadingMonomial(parse('x*y**2 + x**2*y'), [x, y], 'grevlex')).toEqual([2, 1]);
    expect(leadingMonomial(parse('x*y**2 + x**2*y'), [x, y])).toEqual([2, 1]);
    expect(() => leadingMonomial(0, [x, y])).toThrow(sj.PolynomialError);
  });
  it('membership and reduction', () => {
    const G = sj.groebner([parse('x**2 + y**2 - 1'), parse('x - y')], [x, y]);
    expect(G.contains(parse('x**2 - y**2 + x - y'))).toBe(true);
    expect(G.contains(parse('x + 1'))).toBe(false);
    expect(G.contains(5)).toBe(false);
    expect(G.contains(0)).toBe(true);
    expect(show(G.reduce(5))).toBe('[[0, 0], 5]');
    // SymPy: ([x**2 + x*y + y**2, y/2], 3*y/2)
    expect(show(G.reduce(parse('x**3 + y')))).toBe('[[x**2 + x*y + y**2, y/2], 3*y/2]');
    expect(show(sj.reduced(parse('x**2*y + x*y**2'), [parse('x*y - 1'), parse('y**2 - 1')], [x, y]))).toBe('[[x + y, 0], x + y]');
    expect(show(sj.reduced(parse('x**2*y + x*y**2'), [parse('x*y - 1'), parse('y**2 - 1')], [x, y], 'grevlex'))).toBe('[[x + y, 0], x + y]');
  });
});

describe('multivariate gcd, exact division and factorization (polys/mpoly)', () => {
  it('deprecated mgcd and divExact', () => {
    expect(String(sj.mgcd(parse('x*y'), parse('0'), [x, y]))).toBe('x*y');
    expect(String(sj.mgcd(parse('0'), parse('-x*y'), [x, y]))).toBe('x*y');
    expect(String(sj.mlcm(parse('x*y'), parse('x*z'), [x, y, z]))).toBe('x*y*z');
    expect(String(sj.divExact(parse('x**2 + x*y'), parse('x + y'), [x, y]))).toBe('x');
    expect(sj.divExact(parse('x*y + 1'), y, [x, y])).toBe(sj.NoMatch);
    expect(sj.divExact(parse('x*y'), parse('x*z'), [x, y, z])).toBe(sj.NoMatch);
    expect(() => sj.divExact(x, parse('0'), [x])).toThrow(RangeError);
  });
  it('factor', () => {
    expect(String(sj.factor(parse('x**2 - y**2')))).toBe('(x - y)*(x + y)');
    expect(String(sj.factor(parse('x**2 + 2*x*y + y**2 + 1')))).toBe('x**2 + 2*x*y + y**2 + 1');
    expect(String(sj.factor(parse('x**2*y + x*y**2 + x + y')))).toBe('(x + y)*(x*y + 1)');
    expect(show(sj.factorList(parse('2*x**2*y - 2*y**3')))).toBe('[2, [[y, 1], [x - y, 1], [x + y, 1]]]');
  });
  it('polyFromExpr with generators', () => {
    const [p, opts] = sj.polyFromExpr(parse('x*y + 1'), [y, x]);
    expect(String(p)).toBe("Poly(y*x + 1, y, x, domain='ZZ')");
    expect(show(opts.gens)).toBe('[y, x]');
    expect(opts.domain).toBe('ZZ');
    expect(String(sj.polyFromExpr(parse('x**2 + 1'))[0])).toBe("Poly(x**2 + 1, x, domain='ZZ')");
  });
});

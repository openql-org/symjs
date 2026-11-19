// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/polys/numberfields.ts: AlgebraicNumber and minimal polynomials; expected values from SymPy 1.14.

import { describe, expect, it, vi } from 'vitest';
import * as sj from '../../src';
import { add, AlgebraicNumber, Rational, sqrt } from '../../src';
import { chooseFactor, positiveRadicalMinpoly } from '../../src/polys/numberfields';

const { parse } = sj;
const show = (r: unknown): string => (Array.isArray(r) ? `[${r.map(show).join(', ')}]` : String(r));

describe('AlgebraicNumber', () => {
  it('minimal polynomials, aliases and field elements (SymPy minpoly, minpoly_of_element, field_element)', () => {
    const a = new sj.AlgebraicNumber(parse('sqrt(2)'), [1, 3]);
    expect([String(a.minpoly().asExpr().subs(a.minpoly().gens[0]!, parse('x'))), a.minpoly().pure, a.isAliased, a.alias]).toEqual(['x**2 - 2', true, false, undefined]);
    expect(String(a.minpolyOfElement().asExpr().subs(a.minpolyOfElement().gens[0]!, parse('x')))).toBe('x**2 - 6*x + 7');
    expect(a.minpolyOfElement()).toBe(a.minpolyOfElement());
    const t = new sj.Sym('t'), theta = new sj.Sym('theta');
    const T = sj.Poly.from(parse('t**3 - 2'), [t]);
    const b = new sj.AlgebraicNumber(theta, [1, 0, 0, 0], { minpoly: T, alias: 'beta' });
    expect([show(b.coeffs()), b.minpoly(), b.minpolyOfElement().degree(), b.isAliased, String(b.alias), String(b.asExpr())]).toEqual(['[2]', T, 1, true, 'beta', '2']);
    expect(new sj.AlgebraicNumber(theta, [1, 0], { minpoly: T }).minpolyOfElement()).toBe(T);
    const c = b.fieldElement([1, 1]);
    expect([show(c.coeffs()), c.minpoly(), String(c.alias), String(c.asExpr())]).toEqual(['[1, 1]', T, 'beta', 'theta + 1']);
    expect(new sj.AlgebraicNumber(theta, [1, 0], { minpoly: T, alias: theta }).alias).toBe(theta);
    expect(new sj.AlgebraicNumber(c, [1, 0]).minpoly()).toBe(T);
    expect(show(a.fieldElement([2, 0]).coeffs())).toBe('[2, 0]');
  });
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
    // reduced modulo minimal_polynomial(cos(pi/7)) = 8*x**3 - 4*x**2 - 4*x + 1
    const c = new sj.AlgebraicNumber(parse('cos(pi/7)'), [1, 0, 0]);
    expect(show(new sj.AlgebraicNumber(c, [1, 0, 0]).coeffs())).toBe('[3/4, 1/8, -1/16]');
    // SymPy raises NotAlgebraic for a transcendental primitive element
    expect(() => new sj.AlgebraicNumber(parse('2**pi'), [1, 0, 0])).toThrow('2 does not seem to be an algebraic element');
  });
  it('minimal polynomials of radicals', () => {
    const X = new sj.Sym('x');
    expect(String(sj.minimalPolynomial(parse('2**(1/3)'), X))).toBe('x**3 - 2');
    expect(String(sj.minimalPolynomial(parse('2**(2/3)'), X))).toBe('x**3 - 4');
    expect(String(sj.minimalPolynomial(parse('sqrt(2) + sqrt(3)'), X))).toBe('x**4 - 10*x**2 + 1');
    expect(String(sj.minimalPolynomial(3, X))).toBe('x - 3');
    expect(String(sj.minimalPolynomial(parse('sqrt(1 + sqrt(2))'), X))).toBe('x**4 - 2*x**2 - 1');
    // SymPy raises NotAlgebraic (a NotImplementedError)
    expect(() => sj.minimalPolynomial(parse('2**pi'), X)).toThrow(sj.NotImplementedError);
  });
});

describe('AlgebraicNumber (SymPy)', () => {
  it('elements as polynomials in a primitive element', () => {
    const a1 = new AlgebraicNumber(sqrt(2));
    expect(String(a1.evalf(10))).toBe('1.414213562');
    const a2 = new AlgebraicNumber(a1, [3, -5]);
    expect(String(a2.asExpr())).toBe('-5 + 3*sqrt(2)');
    expect(String(new AlgebraicNumber(a2, [2, -1]).asExpr())).toBe('-11 + 6*sqrt(2)');
  });
  it('an element of Q(sqrt(2) + sqrt(3))', () => {
    const a4 = new AlgebraicNumber(add(sqrt(2), sqrt(3)), [Rational.of(1, 2), 0, Rational.of(-9, 2), 0]);
    expect(String(a4.toRoot())).toBe('sqrt(2)');
    expect(String(a4.primitiveElement())).toBe('sqrt(2) + sqrt(3)');
    expect(a4.coeffs().map(String)).toEqual(['1/2', '0', '-9/2', '0']);
  });
});

describe('minimalPolynomial (SymPy minimal_polynomial by composition)', () => {
  const x = new sj.Sym('x');
  const mp = (src: string, opts?: sj.MinimalPolynomialOptions): string => String(sj.minimalPolynomial(parse(src), x, opts));
  // [SymPy source of the element, str() of minimal_polynomial(element, x) in SymPy 1.14]
  const CASES: [string, string][] = [
    ['sqrt(y)', 'x**2 - y'],
    ['y**(1/3)', 'x**3 - y'],
    ['sqrt(y) + 1/y', 'x**2*y**2 - 2*x*y - y**3 + 1'],
    ['1/y', '-x*y + 1'],
    ['sqrt(y)*sqrt(2)', 'x**2 - 2*y'],
    ['y*sqrt(2) + 1', 'x**2 - 2*x - 2*y**2 + 1'],
    ['sqrt(y) + y', 'x**2 - 2*x*y + y**2 - y'],
    ['cos(pi/7)', '8*x**3 - 4*x**2 - 4*x + 1'],
    ['cos(pi/9)', '8*x**3 - 6*x - 1'],
    ['cos(2*pi/7)', '8*x**3 + 4*x**2 - 4*x - 1'],
    ['cos(pi/5)', '4*x**2 - 2*x - 1'],
    ['cos(pi/12)', '16*x**4 - 16*x**2 + 1'],
    ['sin(pi/7)', '64*x**6 - 112*x**4 + 56*x**2 - 7'],
    ['sin(pi/9)', '64*x**6 - 96*x**4 + 36*x**2 - 3'],
    ['sin(pi/15)', '256*x**8 - 448*x**6 + 224*x**4 - 32*x**2 + 1'],
    ['sin(pi/12)', '16*x**4 - 16*x**2 + 1'],
    ['sin(pi/4)', '2*x**2 - 1'],
    ['tan(pi/8)', 'x**2 + 2*x - 1'],
    ['tan(pi/5)', 'x**4 - 10*x**2 + 5'],
    ['tan(pi/3)', 'x**2 - 3'],
    ['exp(I*pi/3)', 'x**2 - x + 1'],
    ['exp(I*pi/4)', 'x**4 + 1'],
    ['exp(I*pi/6)', 'x**4 - x**2 + 1'],
    ['exp(I*pi/8)', 'x**8 + 1'],
    ['exp(I*pi/9)', 'x**6 - x**3 + 1'],
    ['exp(I*pi/10)', 'x**8 - x**6 + x**4 - x**2 + 1'],
    ['exp(I*pi/5)', 'x**4 - x**3 + x**2 - x + 1'],
    ['exp(2*I*pi/5)', 'x**4 + x**3 + x**2 + x + 1'],
    ['exp(I*pi/12)', 'x**8 - x**4 + 1'],
    ['GoldenRatio', 'x**2 - x - 1'],
    ['TribonacciConstant', 'x**3 - x**2 - x - 1'],
    ['I', 'x**2 + 1'],
    ['I + 1', 'x**2 - 2*x + 2'],
    ['2**(1/3)*3**(1/2)', 'x**6 - 108'],
    ['-2**(1/3)*sqrt(3)*I', 'x**6 + 108'],
    ['2**(1/3)*(1 + sqrt(2))', 'x**6 - 28*x**3 - 4'],
    ['(1 + sqrt(2))**(1/3)', 'x**6 - 2*x**3 - 1'],
    ['(1 + sqrt(2))**(-2/3)', 'x**6 - 6*x**3 + 1'],
    ['1/(1 + sqrt(2))', 'x**2 + 2*x - 1'],
    ['3/4', '4*x - 3'],
    ['sqrt(2)*I*sqrt(3)', 'x**2 + 6'],
    ['cos(pi/11)', '32*x**5 - 16*x**4 - 32*x**3 + 12*x**2 + 6*x - 1'],
    ['cos(2*pi/11)', '32*x**5 + 16*x**4 - 32*x**3 - 12*x**2 + 6*x + 1'],
    ['cos(3*pi/11)', '32*x**5 - 16*x**4 - 32*x**3 + 12*x**2 + 6*x - 1'],
    ['sin(pi/11)', '1024*x**10 - 2816*x**8 + 2816*x**6 - 1232*x**4 + 220*x**2 - 11'],
    ['sin(pi/21)', '4096*x**12 - 11264*x**10 + 11264*x**8 - 4992*x**6 + 960*x**4 - 64*x**2 + 1'],
    ['sin(pi/14)', '8*x**3 - 4*x**2 - 4*x + 1'],
    ['sin(3*pi/14)', '8*x**3 + 4*x**2 - 4*x - 1'],
    ['tan(pi/7)', 'x**6 - 21*x**4 + 35*x**2 - 7'],
    ['tan(2*pi/7)', 'x**6 - 21*x**4 + 35*x**2 - 7'],
    ['tan(pi/9)', 'x**6 - 33*x**4 + 27*x**2 - 3'],
    ['sqrt(y**2)', 'x - y'],
    ['sqrt(y**(-2))', 'x*y - 1'],
    ['exp(2*I*pi/9)', 'x**6 + x**3 + 1'],
    ['exp(I*pi/7)', 'x**6 - x**5 + x**4 - x**3 + x**2 - x + 1'],
    ['exp(3*I*pi/4)', 'x**4 + 1'],
    ['GoldenRatio**2', 'x**2 - 3*x + 1'],
    ['tan(pi/14)', '7*x**6 - 35*x**4 + 21*x**2 - 1'],
    ['I*y*sqrt(2)', 'x**2 + 2*y**2'],
    ['0', 'x'],
    ['(sqrt(2) + I)*(sqrt(3) + 1)', 'x**8 - 16*x**6 + 520*x**4 - 576*x**2 + 1296'],
  ];
  for (const [src, expected] of CASES) it(src, () => expect(mp(src)).toBe(expected));

  it('roots of polynomials', () => {
    expect(String(sj.minimalPolynomial(new sj.CRootOf(parse('x**5 - x - 1'), 0), x))).toBe('x**5 - x - 1');
    expect(String(sj.minimalPolynomial(sj.pow(new sj.CRootOf(parse('y**3 - 2'), 0), 2), x))).toBe('x**3 - 4');
  });
  it('over an algebraic field (SymPy domain=QQ.algebraic_field(...))', () => {
    expect(mp('sqrt(2)', { domain: 'QQ<sqrt(2)>' })).toBe('x - sqrt(2)');
    expect(mp('sqrt(2) + sqrt(3)', { domain: 'QQ<sqrt(2), sqrt(3)>' })).toBe('x - sqrt(3) - sqrt(2)');
    expect(mp('I', { domain: 'QQ<I>' })).toBe('x - I');
    expect(mp('GoldenRatio', { domain: 'QQ<sqrt(5)>' })).toBe('2*x - sqrt(5) - 1');
    expect(mp('sqrt(2)', { domain: 'QQ' })).toBe('x**2 - 2');
    expect(mp('sqrt(3)', { domain: 'QQ<sqrt(2)>' })).toBe('x**2 - 3');
    expect(mp('sqrt(3)*I', { domain: 'QQ<sqrt(2)>' })).toBe('x**2 + 3');
    // SymPy: x - TribonacciConstant; symjs cannot factor over QQ<TribonacciConstant> and keeps the polynomial over QQ
    expect(mp('TribonacciConstant', { domain: 'QQ<TribonacciConstant>' })).toBe('x - TribonacciConstant');
    expect(() => mp('sqrt(2)', { domain: 'ZZ_I' })).toThrow(sj.NotImplementedError);
  });
  it('as a Poly, and compose=False', () => {
    expect(String(sj.minimalPolynomial(parse('sqrt(2)'), undefined, { polys: true }))).toBe("PurePoly(_x**2 - 2, _x, domain='ZZ')");
    expect(String(sj.minimalPolynomial(parse('sqrt(2)'), x, { polys: true }))).toBe("Poly(x**2 - 2, x, domain='QQ')");
    expect(String(sj.minimalPolynomial(parse('sqrt(2)'), undefined))).toMatch(/^_x\*\*2 - 2$/);
    expect(mp('sqrt(2) + 3*1/3', { compose: false })).toBe('x**2 - 2*x - 1');
    expect(() => mp('sqrt(y)', { compose: false })).toThrow(sj.NotImplementedError);
    const alpha = new sj.AlgebraicNumber(parse('sqrt(2)'));
    expect(String(sj.minimalPolynomial(alpha, x))).toBe('x**2 - 2');
  });
  it('a sum of four square roots (the Swinnerton-Dyer polynomial of order 4)', () => {
    expect(mp('sqrt(2) + sqrt(3) + sqrt(5) + sqrt(7)')).toBe(
      'x**16 - 136*x**14 + 6476*x**12 - 141912*x**10 + 1513334*x**8 - 7453176*x**6 + 13950764*x**4 - 5596840*x**2 + 46225',
    );
  });
  it('elements that are not algebraic, and x in the ground domain', () => {
    // SymPy raises NotAlgebraic (a NotImplementedError) and GeneratorsError (a PolynomialError)
    for (const src of ['2**pi', 'cos(1)', 'sin(1)', 'tan(1)', 'exp(1)', 'exp(I)', 'log(2)', 'y**pi', 'cos(sqrt(2)*pi)', 'cos(2*y)', 'cos(pi*y)']) {
      expect(() => mp(src), src).toThrow(sj.NotImplementedError);
    }
    expect(() => sj.minimalPolynomial(x, x)).toThrow(sj.PolynomialError);
    // SymPy: ZeroDivisionError
    expect(() => mp('((1 + sqrt(y))**2 - 1 - y - 2*sqrt(y))**-1')).toThrow(RangeError);
  });
  it('the factor that vanishes is decided numerically (SymPy _choose_factor)', () => {
    expect(String(sj.minimalPolynomial(sj.mul(new sj.CRootOf(parse('x**3 - x + 1'), 0), sqrt(2)), x))).toBe('x**6 - 4*x**4 + 4*x**2 - 8');
    expect(mp('cos(pi/7)', { domain: 'QQ<sqrt(2)>' })).toBe('8*x**3 - 4*x**2 - 4*x + 1');
    // two factors vanishing at the element: SymPy's NotImplementedError
    expect(() => chooseFactor([parse('x - 1'), parse('2*x - 2')], x, sj.S.One, { symbols: [], extension: [] })).toThrow(sj.NotImplementedError);
  });
});

describe('LaTeX of algebraic numbers (SymPy 1.14 test_latex_basic)', () => {
  it('prints the value, or the polynomial in the alias', () => {
    expect(sj.latex(new AlgebraicNumber(sqrt(2)))).toBe('\\sqrt{2}');
    expect(sj.latex(new AlgebraicNumber(sqrt(2), [3, -7]))).toBe('-7 + 3 \\sqrt{2}');
    expect(sj.latex(new AlgebraicNumber(sqrt(2), [3, -7], { alias: 'alpha' }))).toBe('3 \\alpha - 7');
  });
});

import * as enclosureModule from '../../src/polys/numberfields/interval';
it('refines indecisive factor enclosures, propagates errors, and retains the numeric fallback for unsupported syntax',()=>{
  const x=new sj.Sym('x'),r=sj.CRootOf(parse('x**2-2'),1),factors=[parse('x**2-2'),parse('x**2-3')],dom={symbols:[],extension:[]};
  const spy=vi.spyOn(enclosureModule,'algebraicEnclosure');
  try {
    spy.mockImplementationOnce(()=>{throw new RangeError('precision insufficient');});
    expect(chooseFactor(factors,x,r,dom)).toEqual(factors[0]);
    spy.mockImplementationOnce(()=>{throw new sj.NotImplementedError('unsupported interval syntax');});
    expect(chooseFactor(factors,x,r,dom)).toEqual(factors[0]);
    spy.mockImplementationOnce(()=>{throw new TypeError('invalid interval input');});
    expect(()=>chooseFactor(factors,x,r,dom)).toThrow(TypeError);
  } finally {spy.mockRestore();}
});
it('separates algebraic factor values closer than the initial enclosure and rejects ambiguous values',()=>{
  const x=new sj.Sym('x'),r=sj.CRootOf(parse('x**2-2'),1),f=[parse('x**2-2'),parse('x**2-2-1/10**60')];
  expect(chooseFactor(f,x,r,{symbols:[],extension:[]})).toEqual(f[0]);
  expect(()=>chooseFactor([parse('x-1'),parse('x+1')],x,sj.S.Zero,{symbols:[],extension:[]})).toThrow(sj.NotImplementedError);
});
it('computes minimal polynomials over supplied algebraic domains with indexed generators',()=>{
  const x=new sj.Sym('x'),r=sj.CRootOf(parse('x**3-x-1'),0),K=new sj.AlgebraicField(sj.QQ,r);
  expect(String(sj.minimalPolynomial(r,x,{domain:K}))).toBe(String(add(x,sj.mul(-1,r))));
  const polynomial=sj.minimalPolynomial(r,x,{domain:K,polys:true});
  expect(polynomial.domain).toBe(String(K));expect(String(polynomial.eval(r))).toBe('0');
  expect(String(sj.minimalPolynomial(sqrt(2),x,{domain:K}))).toBe('x**2 - 2');
  expect(String(sj.minimalPolynomial(sqrt(2),x,{domain:sj.QQ}))).toBe('x**2 - 2');
  expect(String(sj.minimalPolynomial(sj.I,x,{domain:sj.QQ_I}))).toBe('x - I');
  expect(String(sj.minimalPolynomial(sj.I,x,{domain:'QQ_I'}))).toBe('x - I');
  const theta=new sj.Sym('theta'),A=new sj.AlgebraicField(sj.QQ,new AlgebraicNumber(theta,[1,0],{minpoly:sj.Poly.from(parse('x**2-2'),[x])}));
  expect(String(sj.minimalPolynomial(add(theta,1),x,{domain:A}))).toBe(String(parse('x-theta-1')));
});
it('propagates failures of a supplied coefficient domain',()=>{
  const K=new sj.AlgebraicField(sj.QQ,sqrt(2)),spy=vi.spyOn(K,'convert').mockImplementation(()=>{throw new TypeError('coefficient conversion failed');});
  try {expect(()=>sj.minimalPolynomial(sqrt(2),new sj.Sym('x'),{domain:K})).toThrow(TypeError);}
  finally {spy.mockRestore();}
});
it('rejects free symbols over an explicitly rational coefficient field',()=>{
  expect(()=>sj.minimalPolynomial(new sj.Sym('y'),new sj.Sym('x'),{domain:sj.QQ})).toThrow(sj.NotImplementedError);
  expect(()=>sj.minimalPolynomial(new sj.Sym('y'),new sj.Sym('x'),{domain:'QQ'})).toThrow(sj.NotImplementedError);
});


it('preserves algebraic field representations in polynomial conversion and equality', () => {
  const a = new AlgebraicNumber(sqrt(2), [2, 3]);
  const b = new AlgebraicNumber(sqrt(2), [2, 3], { alias: 'alpha' });
  expect(String(a.asExpr(new sj.Sym('t')))).toBe('2*t + 3');
  expect(String(a.asPoly(new sj.Sym('t')))).toBe("Poly(2*t + 3, t, domain='QQ')");
  expect(String(a.asPoly())).toBe("PurePoly(2*_x + 3, _x, domain='QQ')");
  expect(String(b.asPoly())).toBe("Poly(2*alpha + 3, alpha, domain='QQ')");
  expect(a.isNumber).toBe(true);
  expect(a.equals(b)).toBe(false);
  expect(a.equals(new AlgebraicNumber(sqrt(2), [2, 3]))).toBe(true);
  expect(b.equals(new AlgebraicNumber(sqrt(2), [2, 3], { alias: 'alpha' }))).toBe(true);
  expect(b.equals(new AlgebraicNumber(sqrt(2), [2, 3], { alias: 'beta' }))).toBe(false);
  expect(a.equals(2)).toBe(false);
  expect(a.equals(new AlgebraicNumber(sqrt(3), [2, 3]))).toBe(false);
  expect(a.equals(new AlgebraicNumber(sqrt(2), [1]))).toBe(false);
  expect(a.equals(new AlgebraicNumber(sqrt(2), [2, 4]))).toBe(false);
});


it('retains rational and symbolic ground fields in minimal polynomial results', () => {
  const x = new sj.Sym('x'), y = new sj.Sym('y');
  expect(String(sj.minimalPolynomial(sqrt(2), x, { polys: true, domain: 'QQ' }))).toBe("Poly(x**2 - 2, x, domain='QQ')");
  expect(String(sj.minimalPolynomial(sqrt(2), x, { polys: true, domain: sj.QQ }))).toBe("Poly(x**2 - 2, x, domain='QQ')");
  expect(String(sj.minimalPolynomial(sqrt(y), x, { polys: true }))).toBe("Poly(x**2 - y, x, domain='ZZ(y)')");
  expect(String(sj.minimalPolynomial(sj.S.I, x, { domain: 'QQ(y)' }))).toBe('x**2 + 1');
});

it('finds minimal polynomials of symmetric expressions in cubic conjugates', () => {
  const x = new sj.Sym('x'), p = parse('x**3 - 3*x + 1');
  const a = sj.CRootOf(p, 0), b = sj.CRootOf(p, 1);
  expect(String(sj.minimalPolynomial(sj.add(a, b), x))).toBe('x**3 - 3*x - 1');
  expect(String(sj.minimalPolynomial(sj.mul(a, b), x))).toBe('x**3 + 3*x**2 - 1');
  expect(String(sj.minimalPolynomial(sj.add(sj.pow(a, 3), sj.pow(b, 3), sj.mul(-3, sj.add(a, b))), x))).toBe('x + 2');
});

it('reduces the degree of a product of positive rational radicals', () => {
  const x = new sj.Sym('x');
  expect(String(positiveRadicalMinpoly(Rational.of(324), 6n, x))).toBe('x**3 - 18');
  expect(String(positiveRadicalMinpoly(Rational.of(16, 81), 12n, x))).toBe('3*x**3 - 2');
  expect(String(sj.minimalPolynomial(parse('6**(1/6)*54**(1/6)'), x))).toBe('x**3 - 18');
  expect(String(sj.minimalPolynomial(parse('(2/3)**(1/6)*(1/6)**(1/6)'), x))).toBe('3*x**3 - 1');
  expect(String(sj.minimalPolynomial(parse('6**(1/10)*24**(3/10)'), x))).toBe('x**5 - 288');
});

it('falls back to composition outside symmetric cubic polynomials', () => {
  const x = new sj.Sym('x'), p = parse('x**3 - 3*x + 1'), q = parse('x**2 - 2');
  const a = sj.CRootOf(p, 0), b = sj.CRootOf(p, 1);
  const c = sj.CRootOf(q, 0), d = sj.CRootOf(q, 1);
  const reducible = parse('x**3 - x');
  const e = new sj.CRootOf(reducible, 0), f = new sj.CRootOf(reducible, 1);
  const mp = (expression: sj.Expr) => String(sj.minimalPolynomial(expression, x));
  expect(mp(add(a, c))).toBe('x**6 - 12*x**4 + 2*x**3 + 21*x**2 + 6*x - 1');
  expect(mp(add(a, d))).toBe('x**6 - 12*x**4 + 2*x**3 + 21*x**2 + 6*x - 1');
  expect(mp(add(c, d))).toBe('x');
  expect(mp(add(e, f))).toBe('x + 1');
  expect(mp(add(a, b.pow(2)))).toBe('x**3 - 6*x**2 + 24');
  expect(mp(add(a.pow(-1), b.pow(-1)))).toBe('x**3 - 6*x**2 + 9*x - 1');
  expect(mp(add(a, b, sqrt(2)))).toBe('x**6 - 12*x**4 - 2*x**3 + 21*x**2 - 6*x - 1');
});

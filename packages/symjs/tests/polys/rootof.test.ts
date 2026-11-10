// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/polys/rootof.ts: CRootOf; expected values from SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { evalf, parse, Poly, rootOf, solve, symbols } from '../../src';

import rootRefs from './rootof.references.json';

const [x] = symbols('x');
const P = (s: string) => Poly.from(parse(s), [x]);

describe('CRootOf', () => {
  const f = parse('x**3 - x - 1');
  it('caches the root values of a polynomial and drops the oldest beyond the limit', () => {
    const g = parse('x**5 - x - 7');
    const v = new sj.CRootOf(g, 0).numericValue(15);
    // the same nroots result serves every index of the polynomial
    expect(new sj.CRootOf(g, 0).numericValue(15)).toBe(v);
    expect(String(new sj.CRootOf(g, 4).numericValue(15))).toBe('0.407853675209471 + 1.44155543108039*I');
    for (let k = 0; k <= sj.CRootOf.rootValuesLimit; k++) new sj.CRootOf(parse(`x - ${k}`), 0).numericValue(15);
    // recomputed after eviction: equal, not the same object
    const w = new sj.CRootOf(g, 0).numericValue(15);
    expect(w).not.toBe(v);
    expect(String(w)).toBe(String(v));
  });
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
    // SymPy CRootOf.is_real, and exp(c*log(y)) = y**c for a real root c (exp.eval: c is comparable)
    expect([new sj.CRootOf(f, 0).isRealSelf(), c.isRealSelf(), sj.isReal(new sj.CRootOf(f, 0))]).toEqual([true, false, true]);
    const y = sj.symbols('y')[0] as sj.Sym;
    expect(String(sj.exp(sj.mul(new sj.CRootOf(f, 0), sj.log(y))))).toBe('y**CRootOf(x**3 - x - 1, 0)');
    expect(String(sj.exp(sj.mul(c, sj.log(y))))).toBe('exp(log(y)*CRootOf(x**3 - x - 1, 1))');
    expect(String(sj.exp(sj.mul(sj.re(c), sj.log(y))))).toBe('y**re(CRootOf(x**3 - x - 1, 1))');
    expect(String(c.gen)).toBe('x');
    expect(String(c.poly)).toBe('x**3 - x - 1');
    expect(String(c.withArgs([f, sj.Rational.of(2n)]))).toBe('CRootOf(x**3 - x - 1, 2)');
    expect(() => c.withArgs([f, x])).toThrow('CRootOf index is not a Rational');
  });
});

describe('CRootOf', () => {
  it('all_roots and real_roots order', () => {
    expect(P('x**5 + x + 1').allRoots().map(String)).toEqual([
      'CRootOf(x**3 - x**2 + 1, 0)',
      '-1/2 - sqrt(3)*I/2',
      '-1/2 + sqrt(3)*I/2',
      'CRootOf(x**3 - x**2 + 1, 1)',
      'CRootOf(x**3 - x**2 + 1, 2)',
    ]);
    expect(P('(x**2 - 2)*(x**3 + x + 1)').realRoots().map(String)).toEqual(['-sqrt(2)', 'CRootOf(x**3 + x + 1, 0)', 'sqrt(2)']);
  });
  it('numeric values', () => {
    expect(String(evalf(rootOf(parse('x**3 + x + 1'), 0), 30))).toBe('-0.682327803828019327369483739711');
    expect(String(evalf(rootOf(parse('x**3 + x + 1'), 1)))).toBe('0.34116390191401 - 1.16154139999725*I');
  });
  it('solve falls back to CRootOf', () => {
    expect(solve(parse('x**5 - x - 1'), x).map(String)).toEqual([0, 1, 2, 3, 4].map((i) => `CRootOf(x**5 - x - 1, ${i})`));
    expect(solve(parse('x**3 - x + 1'), x, { cubics: false }).map(String)).toEqual([0, 1, 2].map((i) => `CRootOf(x**3 - x + 1, ${i})`));
  });
  it('keeps the defining polynomial intact when substituting a bound generator', () => {
    const r = rootOf(parse('x**5 - x - 1'), 0);
    expect(r.subs(x, 2)).toBe(r);
    expect(r.subs(new sj.Sym('y'), 2)).toBe(r);
    expect(String(r.subs(r, 2))).toBe('2');
  });
});


describe('evaluated indexed-root constructors', () => {
  for (const row of rootRefs) it(`${row.poly}, radicals=${row.radicals}`, () => {
    expect(row.roots.map((_,i) => String(sj.CRootOf(parse(row.poly),i,{radicals:row.radicals})))).toEqual(row.roots);
  });
  it('keeps raw nodes available and validates evaluated constructors', () => {
    expect(String(sj.ComplexRootOf(parse('x**2-3'),0))).toBe('CRootOf(x**2 - 3, 0)');
    expect(String(sj.RootOf(parse('x**2-3'),0))).toBe('-sqrt(3)');
    expect(String(sj.rootof(parse('x**3-2'),sj.Rational.of(0)))).toBe('2**(1/3)');
    expect(String(sj.rootof(parse('x**2-2.0'),0))).toBe('-sqrt(2)');
    expect(() => sj.CRootOf(parse('x*y+1'),0)).toThrow(sj.PolynomialError);
    expect(() => sj.CRootOf(parse('sin(x)+1'),0)).toThrow(sj.PolynomialError);
    expect(() => sj.CRootOf(Poly.from(1,[x]),0)).toThrow(sj.PolynomialError);
    expect(() => sj.CRootOf(parse('x**2-3'),sj.Rational.of(1,2))).toThrow(RangeError);
    const r = new sj.CRootOf(parse('x**3-x-1'),0);
    expect([...sj.freeSymbols(r)]).toEqual([]);
    expect([...sj.freeSymbols(sj.add(r,x))].map(String)).toEqual(['x']);
    // SymPy gives 1 + r + r**2; compare the exact expression, independent of term order.
    expect(sj.QQ.algebraicField(r).toSympy(sj.QQ.algebraicField(r).new([1,1,1])).equals(sj.add(1,r,sj.pow(r,2)))).toBe(true);
    expect(String(r.evalApprox(2))).toBe('1.3');
    expect(String(r.evalApprox(sj.Rational.of(2)))).toBe('1.3');
    const cached = r.numericValue(15);
    sj.CRootOf.clearCache();
    expect(r.numericValue(15)).not.toBe(cached);
  });
  it('refines certified real intervals to rational approximations', () => {
    sj.CRootOf.clearCache();
    const r=new sj.CRootOf(parse('x**3-x-1'),0);
    expect(String(r.evalRational(undefined,undefined,{n:2}))).toBe('23869/18018');
    const a = r.evalRational(sj.Rational.of(1,10000));
    expect(Math.abs(a.toNumber()-r.evalApprox(15).toNumber())).toBeLessThan(1e-4);
    expect(() => r.evalRational(-1)).toThrow(RangeError);
    expect(() => r.evalRational(x)).toThrow(RangeError);
    expect(() => r.evalRational(undefined,undefined,{n:-1})).toThrow(RangeError);
    // SymPy also refines complex roots; the present implementation explicitly
    // requires a real isolating interval rather than claiming an error bound.
    expect(() => new sj.CRootOf(parse('x**2+1'),0).evalRational()).toThrow(sj.NotImplementedError);
  });
});


it('handles signed roots, decimal tolerances, default precision and exact intervals', () => {
  // Values independently generated by SymPy 1.14 CRootOf.eval_rational after clear_cache.
  sj.CRootOf.clearCache();
  expect(String(new sj.CRootOf(parse('x**2-2'), 0).evalRational(undefined, undefined, { n: sj.Rational.of(2) }))).toBe('-33461/23660');
  expect(String(new sj.CRootOf(parse('x**3-x-1'), 0).evalRational(new sj.Float(0.01)))).toBe('271/204');
  sj.CRootOf.clearCache();
  expect(String(new sj.CRootOf(parse('x**3-x-1'), 0).evalRational())).toBe('795896198939712001/600804265230223300');
  // Evaluating CRootOf(x, 0) gives 0 in SymPy; the raw AST node can refine its exact interval too.
  expect(new sj.CRootOf(x, 0).evalRational().equals(0)).toBe(true);
});

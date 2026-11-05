// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/polys/rootof.ts: CRootOf; expected values from SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { evalf, parse, Poly, rootOf, solve, symbols } from '../../src';

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

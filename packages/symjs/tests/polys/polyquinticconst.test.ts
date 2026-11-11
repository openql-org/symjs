// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { Poly, PolyQuintic, add, mul, pow, symbol, parseExpr, toComplex, expand, subs } from '../../src';
import cases from './polyquinticconst-cases.json';
import { at } from '../../src/core/guard';

const x = symbol('x');
it('matches every coefficient and invariant against SymPy 1.14', () => {
  for (const row of cases) {
    const p = Poly.from(add(pow(x, 5), ...row.coefficients.map((v, i) => mul(parseExpr(v), pow(x, 3 - i)))), [x]);
    const q = new PolyQuintic(p);
    expect([q.p, q.q, q.r, q.s].map(String)).toEqual(row.coefficients);
    expect(q.f20.allCoeffs().map(String)).toEqual(row.f20);
    expect(q.b.map(r => r.map(String))).toEqual(row.b);
    expect(q.a.map(String)).toEqual(row.a);
    expect(q.c.map(String)).toEqual(row.c);
    expect(q.o.map(String)).toEqual(row.o);
    expect(String(q.F)).toBe(row.F);
    expect(String(q.l0(2))).toBe(row.l0);
    expect(q.T(2, 3).map(String)).toEqual(row.T);
    expect(toComplex(q.order(2, 3)).re).toBeCloseTo(row.order, 10);
    q.uv(2, 3).forEach((v, i) => expect(toComplex(v).re).toBeCloseTo(at(row.uv, i), 10));
    q.zeta.forEach((z, i) => {
      const v = toComplex(z);
      expect(v.re).toBeCloseTo(Math.cos(2 * Math.PI * (i + 1) / 5), 14);
      expect(v.im).toBeCloseTo(Math.sin(2 * Math.PI * (i + 1) / 5), 14);
    });
  }
  expect(() => new PolyQuintic(Poly.from(x, [x]))).toThrow(RangeError);
});

it('retains symbolic coefficients in the resolvent', () => {
  const q = new PolyQuintic(Poly.from(parseExpr('x**5+p*x**3+q*x**2+r*x+s'), [x]));
  const z = subs(q.f20.asExpr(), [['p', 2], ['q', 3], ['r', 5], ['s', 7]].map(([name, value]) => [symbol(String(name)), Number(value)]));
  const expected = new PolyQuintic(Poly.from(parseExpr('x**5+2*x**3+3*x**2+5*x+7'), [x])).f20.asExpr();
  expect(expand(z).equals(expected)).toBe(true);
});

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { Poly, rootFactors, rootsQuintic, roots, symbol, parseExpr, expand, mul, evalf, toComplex } from '../../src';
const x = symbol('x');
it('returns root factors and preserves unresolved residual factors', () => {
  const f = parseExpr('x**2-y');
  const factors = rootFactors(f,x);
  expect(new Set(factors.map(String))).toEqual(new Set(['x - sqrt(y)','x + sqrt(y)']));
  expect(expand(mul(...factors)).equals(f)).toBe(true);
  expect(rootFactors(Poly.from(parseExpr('x**2-1'),[x])).every(p => p instanceof Poly)).toBe(true);
  expect(rootFactors(parseExpr('x**2-1'))).toHaveLength(2);
  expect(rootFactors(parseExpr('x**5-x+1'),x).map(String)).toEqual(['x**5 - x + 1']);
  const g = parseExpr('x*(x-1)*(x**5-x+1)');
  expect(expand(mul(...rootFactors(g,x))).equals(expand(g))).toBe(true);
  expect(() => rootFactors(parseExpr('x+y'))).toThrow(RangeError);
});

it('solves the upstream rational quintics in radicals', () => {
  // Higher-precision branch selection also resolves the radical formula for
  // x**5-6*x**3-6*x**2+x-6, where SymPy's double-precision search returns [].
  for (const expression of ['x**5-2', '(x/2+1)**5-5*(x/2+1)+12', 'x**5-110*x**3-55*x**2+2310*x+979', 'x**5+15*x+12', 'x**5-6*x**3-6*x**2+x-6', 'x**5+x**4-4*x**3-3*x**2+3*x+1']) {
    const p = Poly.from(parseExpr(expression), [x]);
    const rs = rootsQuintic(p);
    expect(rs, expression).toHaveLength(5);
    for (const r of rs) {
      const residual = p.eval(evalf(r, 30));
      if (residual instanceof Poly) throw new TypeError('expected scalar residual');
      const value = toComplex(evalf(residual, 25));
      expect(Math.hypot(value.re, value.im), expression).toBeLessThan(1e-15);
    }
  }
}, 300000);

it('rejects reducible, nonsolvable, symbolic and nonquintic inputs', () => {
  for (const e of ['x**5-x', 'x**5-x+1', 'x**5+x**2+x+1', 'x**5-y', 'x**5-50000000000000000*x+1200000000000000000000']) {
    expect(rootsQuintic(Poly.from(parseExpr(e), [x])), e).toEqual([]);
  }
  expect(() => rootsQuintic(Poly.from(x, [x]))).toThrow(RangeError);
  expect(() => rootsQuintic(Poly.from(parseExpr('x**5+y'), [x, symbol('y')]))).toThrow(RangeError);
});

it('checks Vieta coefficients when vanishing resolvents leave branch identities underdetermined', () => {
  // SymPy 1.14 returns five distinct nonroots for this De Moivre quintic:
  // its cubic branch identities vanish. Vieta's identities select the roots.
  for (const expression of ['x**5+5*x**3+5*x-1', '1000000000000000*x**5+5000000000*x**3+5000*x-1']) {
    const p = Poly.from(parseExpr(expression), [x]);
    const rs = rootsQuintic(p);
    expect(rs).toHaveLength(5);
    const values = rs.map(r => toComplex(evalf(r, 30)));
    expect(values.filter(v => Math.abs(v.im) < 1e-15)).toHaveLength(1);
    for (const r of rs) {
      const residual = p.eval(evalf(r, 30));
      if (residual instanceof Poly) throw new TypeError('expected scalar residual');
      const value = toComplex(residual);
      expect(Math.hypot(value.re, value.im)).toBeLessThan(1e-20);
    }
  }
});

it('routes requested quintic radicals through the public roots API with multiplicity', () => {
  const rs = roots(parseExpr('(x**5-5*x+12)**2'), x, { quintics: true });
  expect(rs.size).toBe(5);
  expect([...rs.values()]).toEqual([2, 2, 2, 2, 2]);
  expect(roots(parseExpr('x**5-x+1'), x, { quintics: true }).size).toBe(0);
});

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { QQ, S, Sym, dmpFromDict, dmpSqfNorm, dmpToDict, parseExpr as p, Poly, ring } from '../../src';
const x = new Sym('x'), y = new Sym('y');
it('finds a minimal shift and verifies its norm and square-freeness', () => {
  const K = QQ.algebraicField(S.I);
  const [R, X, Y] = ring('x,y', K) as [typeof import('../../src/polys/rings').PolyRing.prototype, import('../../src/polys/rings').PolyElement, import('../../src/polys/rings').PolyElement];
  const f = X.mul(Y).add(Y.pow(2));
  const [shift, g, norm] = R.dmpSqfNorm(f);
  expect(shift).toEqual([0, 1]);
  expect(g.asExpr().expand().equals(p('x*y-I*x+y**2-2*I*y-1'))).toBe(true);
  expect(norm.asExpr().equals(p('x**2*y**2+x**2+2*x*y**3+2*x*y+y**4+2*y**2+1'))).toBe(true);
  expect(norm.isSquarefree).toBe(true);
  const [zeroShift] = dmpSqfNorm([K.one, K.new([1, 0])], 0, K);
  expect(zeroShift).toEqual([0]);
});
it('handles univariate and constant polynomials and rejects repeated factors', () => {
  const K = QQ.algebraicField(S.I);
  const [s, , r] = dmpSqfNorm([K.one, K.zero, K.new(-1)], 0, K);
  expect(s).toEqual([1]);
  expect([...dmpToDict(r, 0)].length).toBeGreaterThan(0);
  expect(dmpSqfNorm([K.new(2)], 0, K)[0]).toEqual([0]);
  expect(() => dmpSqfNorm([], 0, K)).toThrow(RangeError);
  expect(() => dmpSqfNorm([K.one, K.zero, K.zero], 0, K)).toThrow(RangeError);
  expect(() => dmpSqfNorm([1], 0, QQ)).toThrow('ground domain');
  const f = Poly.from(p('x*y'), [x, y]);
  const dense = dmpFromDict(new Map(f.terms().map(([m,c]) => [m,K.convert(c)])), 1, K);
  expect(dmpSqfNorm(dense, 1, K)[0]).toEqual([1,1]);
});

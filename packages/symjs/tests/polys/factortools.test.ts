// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { NoMatch } from '../../src/core/truth';
import { expect, it } from 'vitest';
import { PolyRing } from '../../src/polys/rings';
import { parse } from '../../src/parsing/parser';
import { QQ, ZZ } from '../../src/polys/domains';
import { AlgebraicField } from '../../src/polys/domains/algebraicfield';
import { dupTrialDivision, dmpZzMignotteBound, dupZzHenselStep, dupZzHenselLift, dmpZzWang, dmpZzWangNonDivisors, sortExtensionFactors } from '../../src/polys/factortools';
const R = new PolyRing('x', ZZ);
const x = R.gens[0];
if (x === undefined) throw new TypeError('missing generator');
it('determines multiplicities by exact division and rejects invalid factors', () => {
  const a = x.add(1), b = x.add(2), f = a.pow(2).mul(b.pow(3));
  expect(dupTrialDivision(f, [b, a]).map(([p, k]) => [String(p), k])).toEqual([['x + 1', 2], ['x + 2', 3]]);
  expect(dupTrialDivision(f, [])).toEqual([]);
  expect(() => dupTrialDivision(f, [x])).toThrow('trial division failed');
  expect(() => dupTrialDivision(f, [R.one])).toThrow('nonconstant');
  expect(() => dupTrialDivision(R.zero, [a])).toThrow('nonzero');
  const S = new PolyRing('x,y', ZZ), a0 = S.fromExpr(parse('x+y'));
  expect(dupTrialDivision(a0.pow(2), [a0]).map(([,k])=>k)).toEqual([2]);
  expect(dupTrialDivision(x.add(1).mul(x.sub(1)), [x.add(1), x.sub(1)]).map(([p]) => String(p))).toEqual(['x - 1', 'x + 1']);
});
it('computes the multivariate Mignotte bound', () => {
  const R = new PolyRing('x,y', ZZ), f = R.fromExpr(parse('2*x**2 + 3*x*y - y**2'));
  expect(String(dmpZzMignotteBound(f))).toBe('192');
  expect(String(dmpZzMignotteBound(f.neg()))).toBe('192');
  expect(String(dmpZzMignotteBound(R.zero))).toBe('0');
});
it('lifts both factorization and Bezout identities modulo m squared', () => {
  const f = x.pow(4).sub(1), g = x.pow(3).add(x.pow(2).mul(2)).sub(x).sub(2), h = x.sub(2);
  const s = R.fromExpr(parse('-2')), t = R.fromExpr(parse('2*x**2-2*x-1'));
  const [G,H,S,T] = dupZzHenselStep(5n, f, g, h, s, t);
  expect([G,H,S,T].map(String)).toEqual(['x**3 + 7*x**2 - x - 7', 'x - 7', '8', '-8*x**2 - 12*x - 1']);
  expect(f.sub(G.mul(H)).truncGround(25).isZero).toBe(true);
  expect(S.mul(G).add(T.mul(H)).sub(1).truncGround(25).isZero).toBe(true);
  expect(G.sub(g).truncGround(5).isZero).toBe(true);
  expect(H.sub(h).truncGround(5).isZero).toBe(true);
});

it('lifts several relatively prime factors to the requested precision', () => {
  const f = x.pow(4).sub(1), factors = [x.sub(1), x.sub(2), x.add(2), x.add(1)];
  const lifted = dupZzHenselLift(5n, f, factors, 4);
  expect(lifted.map(String)).toEqual(['x - 1', 'x - 182', 'x + 182', 'x + 1']);
  expect(lifted.reduce((a, b) => a.mul(b), R.one).sub(f).truncGround(625).isZero).toBe(true);
  expect(dupZzHenselLift(5n, f, factors, 1).map(String)).toEqual(factors.map(String));
  expect(() => dupZzHenselLift(5n, f, [], 1)).toThrow(RangeError);
  expect(() => dupZzHenselLift(5n, f, factors, 0)).toThrow(RangeError);
  expect(() => dupZzHenselLift(5n, f, factors, 1.5)).toThrow(RangeError);
});
it('extracts the nondivisors needed by Wang factorization', () => {
  expect(dmpZzWangNonDivisors([14n, 15n, -11n, 17n], 2n, 5n)).toEqual([7n, 3n, 11n, 17n]);
  expect(dmpZzWangNonDivisors([2n], 2n, 1n)).toBe(NoMatch);
  expect(dmpZzWangNonDivisors([0n], 0n, 1n)).toBe(NoMatch);
  expect(dmpZzWangNonDivisors([], 1n, 1n)).toEqual([]);
});
it('restarts Wang factorization after extraneous factors from seeded points', () => {
  const ring = new PolyRing('x,y,z', ZZ);
  const f = ring.fromExpr(parse('2*x**2 + y*z - y - z**2 + z'));
  const seed = [-1, -1, 0, 0, 0, 0, -1, -1, 0, -1, 3, -1, 3, 3, 3, 3, -1, 3];
  expect(dmpZzWang(f, undefined, seed).map(String)).toEqual([String(f)]);
  expect(dmpZzWang(f).map(String)).toEqual([String(f)]);
  expect(() => dmpZzWang(f, 1, [2, 2])).toThrow('sequence exhausted');
  const a = ring.fromExpr(parse('x*y + 1')), b = ring.fromExpr(parse('x*z + 1'));
  expect(dmpZzWang(a.mul(b)).map(String).sort()).toEqual([String(a), String(b)].sort());
});
it('orders factors with identical dense coefficient lists consistently', () => {
  const domain = new AlgebraicField(QQ, parse('sqrt(2)'));
  const ring = new PolyRing('x', domain);
  const f = ring.fromExpr(parse('x + sqrt(2)'));
  const copy = ring.fromExpr(f.asExpr());
  expect(sortExtensionFactors([[f, 2], [copy, 2]], domain, 0)).toEqual([[f, 2], [copy, 2]]);
});
it('keeps the largest absolute coefficient when later terms are smaller', () => {
  const R = new PolyRing('x,y', ZZ);
  expect(String(dmpZzMignotteBound(R.fromExpr(parse('x**2 + 9*x*y + y**2'))))).toBe('288');
});

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { ANP } from '../../src/polys/polyclasses';
import { QQ, ZZ, type Domain } from '../../src/polys/domains';
import { UnificationFailed } from '../../src/polys/polyerrors';

it('compares defining polynomials as well as representatives', () => {
  const a = new ANP([1, 1], [1, 0, 1]);
  expect(a.equals(new ANP([1, 1], [1, 0, 2]))).toBe(false);
  expect(a.equals(new ANP([1, 1], [1, 0, 1]))).toBe(true);
  expect(a.equals(new ANP([1, 2], [1, 0, 1]))).toBe(false);
  expect(new ANP(1, [1, 0, 1]).isOne).toBe(true);
  expect(a.isOne).toBe(false);
  expect(new ANP(2, [1, 0, 1]).isOne).toBe(false);
  const modulus = a.modToList();
  modulus.pop();
  expect(a.modToList().map(String)).toEqual(['1', '0', '1']);
});

it('computes quotient and remainder in the algebraic field', () => {
  const a = new ANP([2, -1, 1], [1, 0, 0, -2]);
  const b = new ANP([1, 2], [1, 0, 0, -2]);
  const [q, r] = a.divmod(b);
  expect(q.mul(b).equals(a)).toBe(true);
  expect(a.quo(a).isOne).toBe(true);
  expect(r.isZero).toBe(true);
  expect(a.rem(b).isZero).toBe(true);
  expect(() => a.rem(0)).toThrow('zero divisor');
  expect(() => a.divmod(0)).toThrow('zero divisor');
});

it('unifies ground domains without changing the defining polynomial', () => {
  const a = new ANP([1], [1, 0, -2], ZZ);
  const b = new ANP([1, 2], [1, 0, -2], QQ);
  const [domain, per, f, g, mod] = a.unify(b);
  expect(domain).toBe(QQ);
  expect(per(f).dom).toBe(QQ);
  expect(per(g).equals(b)).toBe(true);
  expect(mod.map(String)).toEqual(['1', '0', '-2']);
  expect(a.unify(a)[0]).toBe(ZZ);
  expect(() => a.unify(new ANP(1, [1, 0, 2]))).toThrow(UnificationFailed);
  expect(() => a.unify(new ANP(1, [1, 0, 0, 2]))).toThrow(UnificationFailed);
});

import '../../src/polys/densetools';
import { DMPJs } from '../../src/polys/polyclasses';
import { GF } from '../../src/polys/domains/finitefield';
import { PythonMPQ } from '../../src/polys/domains/pythonrational';
import * as euclidtools from '../../src/polys/euclidtools';
import { vi } from 'vitest';

const dense = (rep: readonly unknown[], K: Domain = ZZ): DMPJs => new DMPJs(rep, K);
it('keeps recursive dense representations and independent levels', () => {
  const f = dense([[0], [], [0, 1, 2], [3]]);
  expect(f.toList().map(String)).toEqual(['1,2', '3']);
  expect(f.lev).toBe(1);
  expect(f.dom).toBe(ZZ);
  expect(() => new DMPJs([[1]], ZZ, 0)).toThrow('inconsistent');
  expect(f.equals(dense([[1, 2], [3]], QQ))).toBe(true);
  expect(f.equals(dense([[[1]]]))).toBe(false);
  expect(f.equals(1)).toBe(false);
  expect(f.equals(dense([[1, 3], [3]]))).toBe(false);
  expect(f.equals(dense([[1], [3]]))).toBe(false);
  expect(f.toDict().size).toBe(3);
  expect([...f.toSympyDict().values()].map(String).sort()).toEqual(['1', '2', '3']);
  expect(f.toString()).toBe('DMP_Python([[1, 2], [3]], ZZ)');
  expect(dense([new PythonMPQ(1n, 3n)], QQ).toString()).toBe('DMP_Python([MPQ(1,3)], QQ)');
  const copy = f.toList();
  (copy[0] as unknown[]).pop();
  expect(f.toList()).toHaveLength(2);
  expect(f.toDict().size).toBe(3);
  expect(() => f.add(dense([1]))).toThrow(UnificationFailed);
  expect(() => dense([[1], 2])).toThrow();
  expect(dense([[]]).isZero).toBe(true);
  expect(dense([[1]]).isOne).toBe(true);
  expect(dense([[2]]).isOne).toBe(false);
  expect(dense([[]]).isGround).toBe(true);
  expect(dense([[2]]).isGround).toBe(true);
  expect(f.isGround).toBe(false);
  expect(f.isMonic).toBe(true);
  expect(f.mulGround(2).isMonic).toBe(false);
  expect(f.isPrimitive).toBe(true);
  expect(f.mulGround(2).isPrimitive).toBe(false);
  expect(f.degree()).toBe(1);
  expect(f.degreeList()).toEqual([1, 1]);
  expect(f.totalDegree()).toBe(2);
  expect(dense([[]]).totalDegree()).toBe(0);
  expect(String(f.LC())).toBe('1');
  expect(String(f.TC())).toBe('3');
  expect(f.nth(1, 0)?.toString()).toBe('2');
  expect(f.maxNorm()?.toString()).toBe('3');
  expect(f.l1Norm()?.toString()).toBe('6');
  expect(f.exclude()[0]).toEqual([]);
  expect(dense([[[1], []]]).exclude()[0]).toEqual([0, 2]);
});

it('performs dense arithmetic and exact and pseudo division', () => {
  const f = dense([[1], [], [1, 0, 0]]), g = dense([[2], [-2, 0]]);
  const [q, r] = f.pdiv(g);
  expect(g.mul(q).add(r).equals(f.mulGround(4))).toBe(true);
  expect(f.pquo(g).equals(q)).toBe(true);
  expect(f.prem(g).equals(r)).toBe(true);
  expect(() => f.pexquo(g)).toThrow();
  const h = dense([[1], [-1, 0]]);
  const [d, s] = f.div(h);
  expect(h.mul(d).add(s).equals(f)).toBe(true);
  expect(f.quo(h).equals(d)).toBe(true);
  expect(f.rem(h).equals(s)).toBe(true);
  expect(() => f.exquo(h)).toThrow();
  expect(f.sqr().equals(f.pow(2))).toBe(true);
  expect(f.sqr().exquo(f).equals(f)).toBe(true);
  expect(f.sqr().pexquo(f).equals(f)).toBe(true);
  expect(f.neg().abs().equals(f)).toBe(true);
  expect(f.add(5).sub(5).equals(f)).toBe(true);
  expect(f.mulGround(2).quoGround(2).equals(f)).toBe(true);
  expect(f.mulGround(2).exquoGround(2).equals(f)).toBe(true);
  expect(() => f.exquoGround(3)).toThrow();
  expect(f.primitive()[1].equals(f)).toBe(true);
  expect(f.mulGround(3).content()?.toString()).toBe('3');
  expect(f.mulGround(3).trunc(3).isZero).toBe(true);
  expect(f.diff(2).toString()).toBe('DMP_Python([[2]], ZZ)');
  expect((f.eval(1) as DMPJs).toString()).toBe('DMP_Python([1, 0, 1], ZZ)');
  expect(dense([1, 2, 1]).eval(1)?.toString()).toBe('4');
  expect(dense([1, 0, 1]).compose(dense([1, 1])).equals(dense([1, 2, 2]))).toBe(true);
  expect(dense([1, 0, 2, 0, 1]).decompose().map(String)).toEqual(['DMP_Python([1, 2, 1], ZZ)', 'DMP_Python([1, 0, 0], ZZ)']);
  expect(() => f.decompose()).toThrow('univariate');
});

it('computes multivariate gcds, square-free factors and zero cofactors', () => {
  const g = dense([[1], [1, 0]]), f = g.sqr();
  expect(f.gcd(g).equals(g)).toBe(true);
  expect(f.lcm(g).equals(f)).toBe(true);
  expect(f.cofactors(g).map(String)).toEqual([g, g, dense([[1]])].map(String));
  expect(f.isSqf).toBe(false);
  expect(g.isSqf).toBe(true);
  expect(dense([[]]).isSqf).toBe(false);
  expect(f.sqfPart().equals(g)).toBe(true);
  const [c, factors] = f.mulGround(-3).sqfList();
  expect(String(c)).toBe('-3');
  expect(factors.map(([p, k]) => [String(p), k])).toEqual([[String(g), 2]]);
  expect(dense([[]]).sqfList()).toHaveLength(2);
  expect(dense([[]]).sqfPart().isZero).toBe(true);
  expect(dense([[]]).cofactors(dense([[]])).every((p) => p.isZero)).toBe(true);
  expect(g.lcm(0).isZero).toBe(true);
  expect(dense([[]]).lcm(g).isZero).toBe(true);
  expect(g.gcd(0).equals(g)).toBe(true);
  expect(dense([[]]).gcd(g).equals(g)).toBe(true);
  expect(dense([[-1], [-1, 0]]).gcd(0).equals(g)).toBe(true);
  const qq = dense([[new PythonMPQ(1n, 2n)], [1, 0]], QQ);
  expect(qq.sqr().sqfPart().equals(qq.monic())).toBe(true);
  expect(qq.sqr().sqfList()[1][0]?.[1]).toBe(2);
  expect(qq.lcm(qq).equals(qq.monic())).toBe(true);
  expect(dense([[1], [1]], GF(5)).gcd(dense([[1]], GF(5))).isOne).toBe(true);
  const fallback = vi.spyOn(euclidtools, 'heuGcd').mockReturnValue(undefined);
  try {
    expect(f.gcd(g).equals(g)).toBe(true);
    expect(dense([2, 2]).gcd(dense([4, 4])).equals(dense([2, 2]))).toBe(true);
  } finally { fallback.mockRestore(); }
  expect(dense([2, 2], QQ).gcd(dense([4, 4], QQ)).equals(dense([1, 1], QQ))).toBe(true);
  expect(dense([2, 2], QQ).lcm(dense([4, 4], QQ)).equals(dense([1, 1], QQ))).toBe(true);
});

it('computes subresultants, resultants, discriminants and Bezout identities', () => {
  const f = dense([[-1], [], [], [5]]), g = dense([[3, 1], [], []]);
  expect(f.subresultants(g).map(String)).toEqual([f, g, dense([[45, 30, 5]])].map(String));
  expect(String(f.resultant(g))).toBe(String(dense([675, 675, 225, 25])));
  expect(String(dense([1, 3, 9, -13]).discriminant())).toBe('-11664');
  expect(String(dense([1, 0, -1]).resultant(dense([1, -1])))).toBe('0');
  expect(String(dense([1, 1]).resultant(dense([1, 0, 0, 0])))).toBe('-1');
  expect(dense([[]]).resultant(g) instanceof DMPJs).toBe(true);
  expect(dense([[]]).subresultants(dense([[]]))).toEqual([]);
  expect(f.subresultants(dense([[]]))).toHaveLength(1);
  expect(String(dense([1]).discriminant())).toBe('0');
  expect((dense([[1]]).discriminant() as DMPJs).isZero).toBe(true);
  expect(String(dense([[1], [], [-1]]).discriminant())).toBe(String(dense([4])));
  const a = dense([2, 0], QQ), b = dense([1, 0, -16], QQ);
  const [s, t, h] = a.gcdex(b);
  expect(s.mul(a).add(t.mul(b)).equals(h)).toBe(true);
  expect(a.halfGcdex(b).map(String)).toEqual([s, h].map(String));
  expect(a.invert(b).equals(s)).toBe(true);
  expect(() => a.invert(a)).toThrow('zero divisor');
  expect(() => f.gcdex(f)).toThrow('univariate');
  expect(dense([1, 0, -1]).sturm().map(String)).toEqual(['DMP_Python([MPQ(1,1), MPQ(0,1), MPQ(-1,1)], QQ)', 'DMP_Python([MPQ(2,1), MPQ(0,1)], QQ)', 'DMP_Python([MPQ(1,1)], QQ)']);
});

it('cancels fractions over rings and fields with signed coefficient normalization', () => {
  const f = dense([new PythonMPQ(1n, 3n), 1], QQ), g = dense([new PythonMPQ(1n, 7n), 1], QQ);
  expect(f.cancel(g).map(String)).toEqual(['DMP_Python([MPQ(7,1), MPQ(21,1)], QQ)', 'DMP_Python([MPQ(3,1), MPQ(21,1)], QQ)']);
  expect(f.cancel(g, false).map(String)).toEqual(['7', '3', 'DMP_Python([MPQ(1,1), MPQ(3,1)], QQ)', 'DMP_Python([MPQ(1,1), MPQ(7,1)], QQ)']);
  expect(f.cancelFraction(g).map(String)[0]).toBe('7/3');
  expect(dense([-1, -1]).cancel(dense([1, -1])).map(String)).toEqual(['DMP_Python([-1, -1], ZZ)', 'DMP_Python([1, -1], ZZ)']);
  expect(dense([1, 1]).cancel(dense([-1, 1])).map(String)).toEqual(['DMP_Python([-1, -1], ZZ)', 'DMP_Python([1, -1], ZZ)']);
  expect(dense([]).cancel(dense([])).every((p) => p.isZero)).toBe(true);
  expect(dense([]).cancel(dense([]), false).slice(0, 2).map(String)).toEqual(['1', '1']);
});

it('handles primitive positive factors and rejects corrupted coefficient levels', () => {
  expect(dense([[1], [1, 0]]).sqfList()[1]).toHaveLength(1);
  const p = dense([[1], [1]], QQ);
  p.rep[0] = 1;
  expect(() => p.gcd(dense([[1]], QQ))).toThrow('must be a list');
});

it('requires field coefficients when automatic conversion is disabled', () => {
  expect(() => dense([1, 1]).gcdex(dense([2, 1]), false)).toThrow('over a ring');
  expect(dense([2, 0], QQ).invert(dense([1, 0, -16], QQ), false).equals(dense([new PythonMPQ(1n, 32n), 0], QQ))).toBe(true);
});

it('checks integer exponents and derivative orders at the public boundary', () => {
  const f = dense([[1], [1, 0]]);
  expect(() => f.pow(Number.NaN)).toThrow(TypeError);
  expect(() => f.diff(Number.NaN, 0)).toThrow(TypeError);
  expect(() => f.diff(1, Number.NaN)).toThrow(TypeError);
});

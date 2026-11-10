// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// sympy.polys.groebnertools: the F5B algorithm and its labeled polynomials, reduced bases and the
// lcm/gcd by Groebner bases; references from SymPy 1.14.0 (scripts/gen_groebnertools.py).
import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import * as sj from '../../src';
import type { CriticalPair, LabeledPolynomial } from '../../src/polys/groebnertools';
import { QQ, ZZ } from '../../src/polys/domains';
import { grevlex, grlex, lex } from '../../src/polys/orderings';
import { PolyElement, PolyRing } from '../../src/polys/rings';

const ref = JSON.parse(readFileSync(new URL('./groebnertools.references.json', import.meta.url), 'utf8'));
const ORDERS = { lex, grlex, grevlex } as const;
const tup = (items: readonly string[]): string => (items.length === 1 ? `(${items[0]},)` : `(${items.join(', ')})`);
const monom = (m: readonly number[]): string => tup(m.map(String));
const mpq = (c: sj.Expr): string => {
  const r = c as sj.Rational;
  return `MPQ(${r.p},${r.q})`;
};
const showLbp = (f: LabeledPolynomial): string => `((${monom(f[0][0])}, ${f[0][1]}), ${String(f[1])}, ${f[2]})`;
const showCp = (c: CriticalPair): string =>
  `((${monom(c[0][0])}, ${c[0][1]}), (${monom(c[1][0])}, ${mpq(c[1][1])}), ${showLbp(c[2])}, (${monom(c[3][0])}, ${c[3][1]}), (${monom(c[4][0])}, ${mpq(c[4][1])}), ${showLbp(c[5])})`;
const showKey = (k: sj.MonomialKey): string => (typeof k === 'number' ? String(k) : tup(k.map(showKey)));

describe('F5B', () => {
  for (const [n, s] of (ref.systems as any[]).entries()) {
    it(`system ${n} (${s.order})`, () => {
      const R = new PolyRing(sj.symbols('x y z'), QQ, ORDERS[s.order as keyof typeof ORDERS]);
      const F = s.F.map((f: string) => R.fromExpr(sj.parse(f)));
      const G = sj.f5b(F, R);
      expect(G.map(String)).toEqual(s.f5b);
      expect(G.map(String)).toEqual(s.buchberger);
      expect([sj.isGroebner(G), sj.isGroebner(F)]).toEqual(s.is_groebner);
      expect([sj.isMinimal(G, R), sj.isMinimal(F, R)]).toEqual(s.is_minimal);
      expect([sj.isReduced(G, R), sj.isReduced(F, R)]).toEqual(s.is_reduced);
      if (G.length) expect(sj.redGroebner([...G, ...G.slice(0, 1).map((g) => g.mulGround(2))]).map(String)).toEqual(s.red);
      expect(String(sj.spoly(F[0], F[1]))).toBe(s.spoly);
    });
  }
});

describe('labeled polynomials', () => {
  for (const l of ref.labeled as any[]) {
    it(`signatures and critical pairs (${l.order})`, () => {
      const R = new PolyRing(sj.symbols('x y z'), QQ, ORDERS[l.order as keyof typeof ORDERS]);
      const [x, y, z] = R.gens as [PolyElement, PolyElement, PolyElement];
      const f = sj.lbp(sj.sig([1, 1, 1], 4), x, 3);
      const g = sj.lbp(sj.sig([0, 0, 0], 2), x, 2);
      const h = sj.lbp(sj.sig([0, 1, 0], 3), x.mul(y).add(z), 5);
      const k = sj.lbp(sj.sig([0, 0, 1], 3), y.pow(2).sub(x), 6);
      expect(showLbp(sj.f5Reduce(f, [g]))).toBe(l.f5_reduce);
      expect(showLbp(sj.f5Reduce(sj.lbp(sj.sig([2, 0, 0], 1), x.pow(2).mul(y).add(z), 7), [h, k]))).toBe(l.f5_reduce2);
      const cp = sj.criticalPair(h, k, R);
      expect(showCp(cp)).toBe(l.cp);
      expect(showLbp(sj.sPoly(cp))).toBe(l.s_poly);
      expect(showKey(sj.cpKey(cp, R))).toBe(l.cp_key);
      expect(showKey(sj.lbpKey(h))).toBe(l.lbp_key);
      expect(sj.lbpSign(h)).toEqual([[0, 1, 0], 3]);
      expect(sj.lbpPolyn(h)).toBe(h[1]);
      expect(sj.lbpNum(h)).toBe(5);
      expect(sj.sigCmp(sj.sig([0, 0, 0], 2), sj.sig([0, 0, 0], 1), R)).toBe(-1);
      expect(sj.sigKey(sj.sig([1, 0, 0], 2), R)).toEqual([-2, R.order.key([1, 0, 0])]);
      expect(sj.lbpCmp(h, sj.lbp(sj.sig([0, 1, 0], 3), x, 4))).toBe(-1);
      expect(sj.lbpCmp(sj.lbp(sj.sig([0, 1, 0], 3), x, 4), h)).toBe(1);
      expect(sj.cpCmp(cp, sj.criticalPair(k, h, R))).toBe(1);
      expect(sj.cpCmp(sj.criticalPair(f, h, R), cp)).toBe(-1);
      expect(sj.isRewritableOrComparable(sj.sig([1, 1, 0], 2), 1, [h])).toBe(true);
      expect(sj.isRewritableOrComparable(sj.sig([1, 1, 0], 3), 1, [h])).toBe(true);
      expect(sj.isRewritableOrComparable(sj.sig([1, 0, 0], 3), 1, [h])).toBe(false);
      expect(sj.f5Reduce(sj.lbp(sj.sig([0, 0, 0], 1), R.zero, 1), [h])[1].isZero).toBe(true);
      // the difference carries the larger signature
      expect(sj.lbpSub(h, k)[0]).toEqual(h[0]);
      expect(sj.lbpSub(sj.lbp(sj.sig([0, 0, 0], 3), x, 1), h)[0]).toEqual(h[0]);
    });
  }
});

describe('lcm and gcd by Groebner bases', () => {
  for (const c of ref.lcm as any[]) {
    it(`${c.f}, ${c.g} over ${c.domain}`, () => {
      const R = new PolyRing(sj.symbols('x y'), c.domain === 'ZZ' ? ZZ : QQ, lex);
      const f = R.fromExpr(sj.parse(c.f));
      const g = R.fromExpr(sj.parse(c.g));
      expect(String(sj.groebnerLcm(f, g))).toBe(c.lcm);
      if (c.gcd !== null) expect(String(sj.groebnerGcd(f, g))).toBe(c.gcd);
    });
  }
  it('different rings', () => {
    const R = new PolyRing(sj.symbols('x'), ZZ, lex);
    const S = new PolyRing(sj.symbols('y'), ZZ, lex);
    expect(() => sj.groebnerLcm(R.gens[0]!, S.gens[0]!)).toThrow(RangeError);
    expect(() => sj.groebnerGcd(R.gens[0]!, S.gens[0]!)).toThrow(RangeError);
  });
});

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// References from SymPy 1.14.0 (tools/sympy-reference/generators/gen_numberfields.py): maximal orders, discriminants and
// nilradicals by the Round Two algorithm.
import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import { Sym, parseExpr as P } from '../../../src';
import { AlgebraicField } from '../../../src/polys/domains/algebraicfield';
import { QQ } from '../../../src/polys/domains';
import { nilradicalModP, roundTwo } from '../../../src/polys/numberfields/basis';
import type { Submodule } from '../../../src/polys/numberfields/modules';
import { PowerBasis } from '../../../src/polys/numberfields/modules';
import { Poly } from '../../../src/polys/sympoly';

const ref = JSON.parse(readFileSync(new URL('./numberfields.references.json', import.meta.url), 'utf8'));
const x = new Sym('x');
const poly = (s: string): Poly => Poly.from(P(s), [x]);
const tab = (M: Map<number, Map<number, bigint[]>>, n: number): number[][][] =>
  Array.from({ length: n }, (_, u) => Array.from({ length: n - u }, (_, v) => (M.get(u)?.get(u + v) ?? []).map(Number)));

describe('roundTwo', () => {
  for (const r of ref.fields) {
    it(`maximal order of ${r.T}`, () => {
      const radicals = new Map<bigint, Submodule>();
      const [ZK, dK] = roundTwo(poly(r.T), { radicals });
      expect([String(ZK), String(dK)]).toEqual([r.ZK, r.dK]);
      expect(tab(ZK.multTab(), ZK.n)).toEqual(r.multab);
      expect([ZK.startsWithUnity(), ZK.isSqMaxrankHNF()]).toEqual([true, true]);
      if (r.radicals !== null) expect(Object.fromEntries([...radicals].map(([p, I]) => [String(p), String(I)]))).toEqual(r.radicals);
    });
  }
  it('records a nilradical only under its own prime', () => {
    // x**3 - 30*x - 16: the primes 3 (second enlargement) then 2 are processed; SymPy stores the
    // nilradical modulo 3 under the prime 2, so that the primes above 2 come out wrong
    const radicals = new Map<bigint, Submodule>();
    roundTwo(poly('x**3 - 30*x - 16'), { radicals });
    expect(radicals.has(2n)).toBe(false);
  });
  for (const r of ref.nonmonic) {
    it(`scales the roots of ${r.T}`, () => {
      const [ZK, dK] = roundTwo(poly(r.T));
      expect([String(ZK), String(dK), String(ZK.parent)]).toEqual([r.ZK, r.dK, r.parent]);
    });
  }
  it('works on an algebraic field', () => {
    const K = new AlgebraicField(QQ, P('sqrt(2)/3'));
    const [ZK, dK] = roundTwo(K);
    // QQ<sqrt(2)/3> = QQ(sqrt(2)): the ring of integers ZZ[sqrt(2)] = ZZ[theta'/3] for theta' = 9*theta = 3*sqrt(2), discriminant 8
    // (SymPy builds a power basis of 9*x**2 - 2 and gets the discriminant 0)
    expect([String(ZK), String(dK)]).toEqual(['Submodule[[3, 0], [0, 1]]/3', '8']);
    expect((ZK.parent as PowerBasis).K).toBe(K);
  });
  it('rejects polynomials that are not irreducible over ZZ or QQ', () => {
    const y = new Sym('y');
    for (const T of [poly('x**2 - 4'), poly('3'), Poly.from(P('x*y + 1'), [x, y]), Poly.from(P('x**2 + 1'), [x], { modulus: 5 })]) {
      expect(() => roundTwo(T)).toThrow(RangeError);
    }
  });
});

describe('nilradicalModP', () => {
  it('computes the nilradical of an order modulo p', () => {
    const [ZK] = roundTwo(poly('x**3 + 3*x**2 + 5'));
    expect(String(nilradicalModP(ZK, 3))).toBe('Submodule[[-1, 1, 0], [-1, 0, 1]]');
    expect(String(nilradicalModP(ZK, 3, 9))).toBe('Submodule[[-1, 1, 0], [-1, 0, 1]]');
    expect(String(nilradicalModP(ZK, 2))).toBe('Submodule[]');
  });
});

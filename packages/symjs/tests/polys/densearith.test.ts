// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it, vi } from 'vitest';
import { passingModuleCases, runTestCase } from '../../../../tools/sympy-corpus/tests-harness';
import * as D from '../../src/polys/densearith';
import { EX, QQ, RR, ZZ } from '../../src/polys/domains';
import { GF } from '../../src/polys/domains/finitefield';
import { CC } from '../../src/polys/domains/complexfield';
import { ExactQuotientFailed } from '../../src/core/errors';
import { PolynomialDivisionFailed } from '../../src/polys/polyerrors';
import { Float, Sym } from '../../src/core/nodes';
import { add, mul } from '../../src/core/ops';

it('replays every measured SymPy densearith assertion', () => {
  const failures = passingModuleCases('polys', 'sympy.polys.tests.test_densearith').flatMap((c) => {
    const o = runTestCase(c);
    return o.status === 'pass' || o.status === 'equivalent' ? [] : [{ src: c.src, fn: c.fn, ...o }];
  });
  expect(failures).toEqual([]);
});

it('validates powers, recursion and division, including zero dividends', () => {
  for (const n of [-1, 0.5, NaN, 1e20]) expect(() => D.dupPow([1], n, ZZ)).toThrow(RangeError);
  expect(() => D.dmpAdd([1], [[1]], 1, ZZ)).toThrow(TypeError);
  expect(() => D.dupDiv([], [], ZZ)).toThrow(RangeError);
  expect(() => D.dmpPdiv([[]], [[]], 1, ZZ)).toThrow(RangeError);
  expect(() => D.dupQuoGround([], 0, ZZ)).toThrow(RangeError);
  expect(() => D.dupExquoGround([1], 2, ZZ)).toThrow(ExactQuotientFailed);
  expect(() => D.dupFfDiv([1], [2], ZZ)).toThrow(ExactQuotientFailed);
  expect(() => D.dupExquo([1, 0], [1, 1], ZZ)).toThrow(ExactQuotientFailed);
  expect(() => D.dmpPexquo([[1], []], [[1], [1]], 1, ZZ)).toThrow(ExactQuotientFailed);
  expect(D.dupDiv([1], [1, 1], QQ)[0]).toEqual([]);
  expect(D.dmpMulGround([[1], [2]], 0, 1, ZZ)).toEqual([[], []]);
  // A zero shift divides by one; SymPy 1.14's empty slice loses the polynomial.
  expect(D.dupRshift([1, 2], 0, ZZ)).toEqual([1, 2]);
  const faultyDivision = vi.spyOn(ZZ, 'div').mockReturnValue([0n, 0n]);
  try { expect(() => D.dupRrDiv([1, 2], [1], ZZ)).toThrow(PolynomialDivisionFailed); }
  finally { faultyDivision.mockRestore(); }
});

it('computes in polynomial coefficient rings, expression fields and finite fields', () => {
  const t = new Sym('t');
  const K = ZZ.polyRing(t);
  const t1 = add(t, 1);
  const f = [mul(t1, t1), mul(2, t1)];
  expect(D.dupExquoGround(f, t1, K).map(String)).toEqual(['t + 1', '2']);
  expect(D.dupQuoGround([add(t, 2)], t1, K).map(String)).toEqual(['1']);
  expect(() => D.dupExquoGround([1], t, K)).toThrow(ExactQuotientFailed);
  expect(D.dupDiv([t, 1], [t1], K)[0]).toEqual([]);
  expect(D.dupDiv([t1, t1], [t1], K)[0].map(String)).toEqual(['1', '1']);
  expect(D.dupDiv([t, t], [t], EX)[0].map(String)).toEqual(['EX(1)', 'EX(1)']);
  const F = GF(5);
  expect(D.dupDiv([1, 0, 1], [1, 1], F).map((p) => p.map((c) => String(F.toSympy(c))))).toEqual([['1', '-1'], ['2']]);
  expect(D.dupMul([2], [3], GF(6))).toEqual([]);
});

it('decreases the degree during floating point division', () => {
  for (const a of [1, 0.1, 0.3, 1.3, 5.7, -0.066]) for (const b of [49, 0.3, 0.7, 7.87]) {
    const [q, r] = D.dupFfDiv([new Float(a), new Float(1)], [new Float(b)], RR);
    expect(q).toHaveLength(2);
    expect(r).toEqual([]);
  }
  expect(D.dmpFfDiv([[1], [1]], [[1]], 1, RR)[1]).toEqual([[]]);
  expect(D.dupFfDiv([1, 1], [49], CC)[1]).toEqual([]);
});

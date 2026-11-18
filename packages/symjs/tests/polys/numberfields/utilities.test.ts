// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Reference values independently generated with SymPy 1.14.0.
import { expect, it, vi } from 'vitest';
import { extractFundamentalDiscriminant, isolate, parse, Rational, I, NotImplementedError } from '../../../src';
import { readFileSync } from 'node:fs';
import { AlgIntPowers, coeffSearch, supplementASubspace, isRat, isInt, getNumDenom, PythonMPQ, Sym, Poly, QQ, GF, DM, DMRankError } from '../../../src';
import refs from './utilities.references.json';
// the helpers of the number-field modules (references from tools/sympy-reference/generators/gen_numberfields.py)
const nf = JSON.parse(readFileSync(new URL('./numberfields.references.json', import.meta.url), 'utf8')).utilities;
it('computes powers of an algebraic integer', () => {
  const x = new Sym('x');
  const P5 = new AlgIntPowers(Poly.from(parse('x**4 + x**3 + x**2 + x + 1'), [x]));
  expect(Array.from({ length: 12 }, (_, i) => P5.get(i).map(Number))).toEqual(nf.powers);
  const P7 = new AlgIntPowers(Poly.from(parse('x**3 - 2*x + 7'), [x]), 5);
  expect([8, 3, 4, 5, 6, 7, 0, 1, 2].map((i) => P7.get(i).map(Number))).toEqual([8, 3, 4, 5, 6, 7, 0, 1, 2].map((i) => nf.powers_mod[i]));
  expect([P7.n, P7.modulus, P7.red(-3n), P5.red(-3n)]).toEqual([3, 5n, 2n, -3n]);
  P7.computeUpThrough(2);
  expect(() => P5.get(-1)).toThrow(RangeError);
});
it('searches coefficient vectors', () => {
  const take = (g: Generator<number[]>, n: number): number[][] => Array.from({ length: n }, () => g.next().value as number[]);
  expect(take(coeffSearch(2, 1), 30)).toEqual(nf.search);
  expect(take(coeffSearch(3, 2), 40)).toEqual(nf.search3);
});
it('supplements a subspace', () => {
  const M = DM([[1, 7, 0], [2, 3, 4]], QQ).transpose();
  expect(String(supplementASubspace(M).toMatrix())).toBe(nf.supplement);
  expect(String(supplementASubspace(M.convertTo(GF(7))).toMatrix())).toBe(nf.supplement_ff);
  expect(() => supplementASubspace(DM([[1, 2, 0], [2, 4, 0]], QQ).transpose())).toThrow(DMRankError);
  expect(() => supplementASubspace(DM([[1, 0, 0], [0, 1, 0]], QQ))).toThrow(DMRankError);
});
it('recognizes rational numbers', () => {
  expect([1, 2n, Rational.of(1n, 2n), new PythonMPQ(1, 2), 0.5, '1'].map(isRat)).toEqual([true, true, true, true, false, false]);
  expect([1, 2n, Rational.of(3n), Rational.of(1n, 2n), 0.5].map(isInt)).toEqual([true, true, true, false, false]);
  expect([getNumDenom(Rational.of(-3n, 4n)), getNumDenom(new PythonMPQ(3, -4)), getNumDenom(5), getNumDenom(6n)]).toEqual([[-3n, 4n], [-3n, 4n], [5n, 1n], [6n, 1n]]);
  expect(() => getNumDenom(0.5)).toThrow(TypeError);
});
for (const row of refs.discriminants) it(`extracts the fundamental discriminant of ${row.a}`, () => {
  const [d,f] = extractFundamentalDiscriminant(row.a);
  expect(Object.fromEntries(d)).toEqual(row.D);
  expect(Object.fromEntries(f)).toEqual(row.F);
  const product = (m: ReadonlyMap<bigint,number>): bigint => [...m].reduce((a,[p,k]) => a * p ** BigInt(k),1n);
  expect(product(d)*product(f)**2n).toBe(BigInt(row.a));
});
for (const row of refs.intervals) it(`isolates ${row.expr} with eps=${row.eps}`, () => {
  const eps = row.eps === null ? undefined : parse(row.eps);
  if (eps !== undefined && !(eps instanceof Rational)) throw new TypeError('reference tolerance');
  expect(isolate(parse(row.expr),eps).map(String)).toEqual(row.interval);
});
it('rejects invalid discriminants and nonreal algebraic numbers', () => {
  for(const d of [2,3,-1]) expect(() => extractFundamentalDiscriminant(d)).toThrow(RangeError);
  expect(() => isolate(I)).toThrow(NotImplementedError);
  expect(() => isolate(parse('sqrt(2)'),Rational.of(-1))).toThrow(RangeError);
});
it('increases numeric precision when the first approximation overlaps an endpoint', () => {
  // SymPy 1.14 isolate can overflow its precision counter for such large values.
  // The reference is instead the positive interval from Poly(x**2-2*10**40).intervals().
  // Its positivity selects the unique positive root, 10**20*sqrt(2), exactly.
  expect(isolate(parse('100000000000000000000*sqrt(2)')).map(String)).toEqual(refs.largeInterval);
});

import continuationRefs from '../continuation.references.json';
for(const row of continuationRefs.intervals) it(`selects the exact interval for ${row.expr}`,()=>{
  expect(isolate(parse(row.expr),Rational.of(1,1000)).map(String)).toEqual(row.interval);
});

import * as enclosureModule from '../../../src/polys/numberfields/interval';
it('retries undecided interval arithmetic and propagates unsupported algebraic input',()=>{
  const spy=vi.spyOn(enclosureModule,'algebraicEnclosure');
  try {
    spy.mockImplementationOnce(()=>{throw new RangeError('precision insufficient');});
    expect(isolate(parse('sqrt(2)+sqrt(3)'),Rational.of(1,1000)).map(String)).toEqual(continuationRefs.intervals[0]?.interval);
    spy.mockImplementationOnce(()=>{throw new NotImplementedError('unsupported interval input');});
    expect(()=>isolate(parse('sqrt(2)+sqrt(3)'))).toThrow(NotImplementedError);
  } finally {spy.mockRestore();}
});

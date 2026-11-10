// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Reference values independently generated with SymPy 1.14.0.
import { expect, it } from 'vitest';
import { extractFundamentalDiscriminant, isolate, parse, Rational, I, NotImplementedError } from '../../../src';
import refs from './utilities.references.json';
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

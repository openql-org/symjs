// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import { galoisGroup, hasSquareDisc, MaxTriesException, Poly, Sym, PermutationGroup, parseExpr as p } from '../../../src';
import { tschirnhausenTransformation } from '../../../src/polys/numberfields/galoisgroups';
const x = new Sym('x');
const references: {polynomial: string; name: string; even: boolean}[] = JSON.parse(readFileSync(new URL('./galoisgroups.references.json', import.meta.url), 'utf8'));
for (const reference of references) it(`classifies ${reference.name}`, () => {
  const [name, even] = galoisGroup(p(reference.polynomial), x, {byName:true});
  expect(String(name)).toBe(reference.name); expect(even).toBe(reference.even);
});
it('returns permutation groups and accepts nonmonic rational polynomials', () => {
  expect(galoisGroup(p('x**3-2'))[0]).toBeInstanceOf(PermutationGroup);
  expect(String(galoisGroup(Poly.from(p('(x**4+1)/2'), [x]), {byName:true})[0])).toBe('S4TransitiveSubgroups.V');
  expect(hasSquareDisc(Poly.from(p('x**2-2'), [x]))).toBe(false);
  expect(() => galoisGroup(p('x**7-2'))).toThrow(RangeError);
  expect(() => galoisGroup(p('x**2-1'))).toThrow(RangeError);
  expect(() => galoisGroup(Poly.from(1, [x]))).toThrow(RangeError);
  expect(() => galoisGroup(p('x**4+1'), {maxTries:0})).toThrow(MaxTriesException);
});
it('finds separating Tschirnhausen transforms and reports exhausted searches', () => {
  const f = Poly.from(p('x**4+1'), [x]);
  const [a, g] = tschirnhausenTransformation(f);
  expect(a.degree()).toBeLessThan(f.degree());
  expect(g.degree()).toBe(f.degree()); expect(g.isIrreducible).toBe(true);
  expect(() => tschirnhausenTransformation(f, 0)).toThrow(MaxTriesException);
});
it('handles cyclic sextics after translation and bounds unsuccessful searches', () => {
  const cyclotomic = p('x**6+x**5+x**4+x**3+x**2+x+1');
  expect(String(galoisGroup(cyclotomic.subs(x,x.add(1)).expand(), {byName:true})[0])).toBe('S6TransitiveSubgroups.C6');
  const f = Poly.from(p('x**4+1'), [x]);
  const [, g] = tschirnhausenTransformation(f);
  expect(() => tschirnhausenTransformation(f, 1, new Set([g.asExpr().key]))).toThrow(MaxTriesException);
  expect(() => galoisGroup(p('x**5-5*x+12'), {maxTries:1})).toThrow('quintic norm');
});

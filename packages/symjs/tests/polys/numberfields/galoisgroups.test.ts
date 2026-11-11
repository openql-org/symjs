// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import { galoisGroup, hasSquareDisc, MaxTriesException, GaloisGroupException, Poly, Sym, PermutationGroup, QQ, AlgebraicField, xreplace, parseExpr as p } from '../../../src';
import {
  galoisGroupDegree4RootApprox, galoisGroupDegree4Lookup, galoisGroupDegree5Hybrid, galoisGroupDegree5LookupExtFactor, galoisGroupDegree6Lookup,
  repKey, tschirnhausenTransformation,
} from '../../../src/polys/numberfields/galoisgroups';
const x = new Sym('x');
const poly = (s: string): Poly => Poly.from(p(s), [x]);
const references: {polynomial: string; name: string; even: boolean}[] = JSON.parse(readFileSync(new URL('./galoisgroups.references.json', import.meta.url), 'utf8'));
const ofDegree = (n: number) => references.filter((r) => poly(r.polynomial).degree() === n);

for (const reference of references) it(`classifies ${reference.name}`, () => {
  const [name, even] = galoisGroup(p(reference.polynomial), x, {byName:true});
  expect(String(name)).toBe(reference.name); expect(even).toBe(reference.even);
});

it('classifies quartics by root approximation and quintics by the hybrid method', () => {
  for (const r of ofDegree(4)) expect(galoisGroupDegree4RootApprox(poly(r.polynomial)).map(String)).toEqual([r.name, String(r.even)]);
  for (const r of ofDegree(5)) expect(galoisGroupDegree5Hybrid(poly(r.polynomial)).map(String)).toEqual([r.name, String(r.even)]);
}, 120_000);

it('returns permutation groups and accepts nonmonic rational polynomials', () => {
  expect(galoisGroup(p('x**3-2'))[0]).toBeInstanceOf(PermutationGroup);
  expect(String(galoisGroup(Poly.from(p('(x**4+1)/2'), [x]), {byName:true})[0])).toBe('S4TransitiveSubgroups.V');
  expect(hasSquareDisc(poly('x**2-2'))).toBe(false);
  expect(hasSquareDisc([1n, 0n, -4n])).toBe(true);
  expect(() => galoisGroup(p('x**7-2'))).toThrow('up to degree 6');
  expect(() => galoisGroup(p('x**2-1'))).toThrow(RangeError);
  expect(() => galoisGroup(Poly.from(1, [x]))).toThrow(RangeError);
  expect(() => galoisGroup(Poly.from(0, [x]))).toThrow(RangeError);
  const k = QQ.algebraicField(p('2**(1/4)'));
  expect(k).toBeInstanceOf(AlgebraicField);
  expect(String((k as AlgebraicField).galoisGroup({byName:true})[0])).toBe('S4TransitiveSubgroups.D4');
});

it('finds Tschirnhausen transformations in a fixed or random order', () => {
  for (const s of ['x**2 - 2', 'x**2 + x + 1', 'x**4 + 1', 'x**4 - x**3 + x**2 - x + 1']) {
    const T = poly(s);
    const [A, U] = tschirnhausenTransformation(T);
    expect([U.degree(), U.isMonic, U.isIrreducible]).toEqual([T.degree(), true, true]);
    expect(A.degree()).toBeGreaterThan(1);
    // A maps the roots of T to roots of U: U(A(x)) vanishes modulo T.
    expect(Poly.from(xreplace(U.asExpr(), [[U.gen, A.asExpr()]]), [x]).rem(T).isZero).toBe(true);
  }
  const T = poly('x**4 + 1');
  const history = new Set<string>();
  const seen = Array.from({ length: 4 }, () => repKey(tschirnhausenTransformation(T, { history })[1]));
  history.forEach((h) => expect(typeof h).toBe('string'));
  expect(new Set(seen).size).toBe(1);
  // Excluding each U found in turn walks through degrees and coefficient bounds of A.
  const degrees = new Set<number>();
  for (let k = 0; k < 40; k++) {
    const [A, U] = tschirnhausenTransformation(T, { history, maxTries: 200 });
    history.add(repKey(U));
    degrees.add(A.degree());
  }
  expect([...degrees].sort((a, b) => a - b)).toEqual([2, 3, 4]);
  expect(history.size).toBe(41);
  let seed = 1;
  const random = (): number => (seed = (seed * 16807) % 2147483647) / 2147483647;
  const [A, U] = tschirnhausenTransformation(T, { fixedOrder: false, random, maxCoeff: 2 });
  expect([U.degree(), U.isIrreducible]).toEqual([4, true]);
  expect(A.degree()).toBeGreaterThanOrEqual(2);
  expect(tschirnhausenTransformation(T, { fixedOrder: false })[1].degree()).toBe(4);
  expect(() => tschirnhausenTransformation(T, { maxTries: 0 })).toThrow(MaxTriesException);
  expect(new MaxTriesException('m')).toBeInstanceOf(GaloisGroupException);
}, 120_000);

it('reports exhausted searches', () => {
  const T = poly('x**4 + 1');
  for (const f of [galoisGroupDegree4RootApprox, galoisGroupDegree4Lookup, galoisGroupDegree5Hybrid, galoisGroupDegree5LookupExtFactor, galoisGroupDegree6Lookup]) {
    expect(() => f(T, 0)).toThrow(MaxTriesException);
  }
  expect(() => galoisGroup(p('x**4+1'), {maxTries:0})).toThrow(MaxTriesException);
  // Repeated roots give resolvents with repeated roots, which are retried.
  expect(() => galoisGroupDegree4RootApprox(poly('x**4'), 1)).toThrow(MaxTriesException);
  expect(() => galoisGroupDegree5Hybrid(poly('x**5'), 1)).toThrow(MaxTriesException);
  expect(String(galoisGroup(p('x**5-5*x+12'), {byName:true, randomize:true})[0])).toBe('S5TransitiveSubgroups.D5');
});

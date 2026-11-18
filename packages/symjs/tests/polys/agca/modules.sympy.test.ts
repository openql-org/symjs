// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { readFileSync } from 'node:fs';
import { expect, it } from 'vitest';
import { QQ, GF, PolynomialRingBase, homomorphism } from '../../../src/polys';
import { Sym, parse as p } from '../../../src/core';
import { at } from '../../../src/core/guard';

interface Reference { left: string[][]; right: string[][]; syzygies: string[][]; intersection: string[][]; quotient: string[] }
const cases: Reference[] = JSON.parse(readFileSync(new URL('./modules.references.json', import.meta.url), 'utf8'));
const x = new Sym('x'), y = new Sym('y'), R = new PolynomialRingBase(QQ, [x, y]), F = R.freeModule(2);
const vectors = (rows: string[][]) => rows.map((row) => row.map((e) => p(e)));
for (const [i, reference] of cases.entries()) it(`matches SymPy generating sets ${i}`, () => {
  const A = F.submodule(...vectors(reference.left)), B = F.submodule(...vectors(reference.right));
  const syzygies = A.syzygyModule();
  expect(syzygies.equals(R.freeModule(A.gens.length).submodule(...vectors(reference.syzygies)))).toBe(true);
  for (const relation of syzygies.gens) expect(A.gens.reduce((sum, g, j) => sum.add(g.mul(at(relation.data, j))), F.convert(0)).isZero()).toBe(true);
  const I = A.intersect(B);
  expect(I.equals(F.submodule(...vectors(reference.intersection)))).toBe(true);
  expect(A.isSubmodule(I) && B.isSubmodule(I)).toBe(true);
  const quotient = A.moduleQuotient(B);
  expect(quotient.equals(R.ideal(...reference.quotient.map((e) => p(e))))).toBe(true);
  for (const c of quotient.gens) for (const g of B.gens) expect(A.contains(g.mul(c))).toBe(true);
});

it('supports finite coefficient fields and quotient-ring zero divisors', () => {
  const K = new PolynomialRingBase(GF(5), [x, y]);
  const M = K.freeModule(1).submodule([p('2*x')], [p('3*x')]);
  expect(M.contains([x])).toBe(true);
  expect(M.syzygyModule().contains([3, -2])).toBe(true);
  const C = R.quotientRing([p('x*y')]), CF = C.freeModule(1);
  const N = CF.submodule([x], [y]), syzygies = N.syzygyModule();
  expect(syzygies.contains([y, 0])).toBe(true);
  expect(syzygies.contains([0, x])).toBe(true);
  for (const g of syzygies.gens) expect(N.gens.reduce((sum, v, j) => sum.add(v.mul(at(g.data, j))), CF.convert(0)).isZero()).toBe(true);
  const h = homomorphism(F, F, [[0, 0], [0, 1]]), D = F.submodule([x, 0]);
  expect(h.restrictDomain(D).kernel().equals(D)).toBe(true);
});

interface LocalReference { order: string; generators: string[][]; vector: string[]; coordinates: string[] }
const local: { version: string; modules: LocalReference[] } = JSON.parse(readFileSync(new URL('./local.references.json', import.meta.url), 'utf8'));
for (const [i, reference] of local.modules.entries()) it(`matches SymPy ${local.version} localized coordinates ${i}`, () => {
  const L = new PolynomialRingBase(QQ, [x, y], reference.order), ambient = L.freeModule(2);
  const M = ambient.submodule(...vectors(reference.generators));
  const target = ambient.convert(reference.vector.map((e) => p(e)));
  const coefficients = M.inTermsOfGenerators(target);
  expect(coefficients.map((e) => L.canon(e).key)).toEqual(reference.coordinates.map((e) => L.fromSympy(p(e)).key));
  expect(coefficients).toHaveLength(reference.coordinates.length);
  expect(M.gens.reduce((sum, g, j) => sum.add(g.mul(at(coefficients, j))), ambient.convert(0)).equals(target)).toBe(true);
  for (const relation of M.syzygyModule().gens) expect(M.gens.reduce((sum, g, j) => sum.add(g.mul(at(relation.data, j))), ambient.convert(0)).isZero()).toBe(true);
});

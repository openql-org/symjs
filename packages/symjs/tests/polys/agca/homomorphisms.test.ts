// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { readFileSync } from 'node:fs';
import { expect, it } from 'vitest';
import { QQ, PolynomialRingBase, homomorphism } from '../../../src/polys';
import { Sym } from '../../../src/core';
const refs: Record<string, string> = JSON.parse(readFileSync(new URL('./references.json', import.meta.url), 'utf8'));
const x = new Sym('x'), y = new Sym('y'), R = new PolynomialRingBase(QQ, [x, y]), F = R.freeModule(2);
it('computes images and kernels and verifies the first isomorphism theorem', () => {
  const h = homomorphism(F, F, [[1, 0], [x, 0]]);
  expect(String(h.kernel())).toBe(refs['kernel']);
  expect(String(h.image())).toBe(refs['image']);
  expect(String(h.apply([1, 1]))).toBe(refs['apply']);
  for (const k of h.kernel().gens) expect(h.apply(k).isZero()).toBe(true);
  expect(h.isInjective()).toBe(false);
  expect(h.isSurjective()).toBe(false);
  expect(h.isIsomorphism()).toBe(false);
  expect(h.isZero()).toBe(false);
  expect(h.quotientDomain(h.kernel()).isInjective()).toBe(true);
  expect(h.restrictCodomain(h.image()).isSurjective()).toBe(true);
  const iso = h.restrictCodomain(h.image()).quotientDomain(h.kernel());
  expect(iso.isIsomorphism()).toBe(true);
  expect(h.restrictDomain(F.submodule()).isZero()).toBe(true);
  expect(h.quotientCodomain(h.image()).isZero()).toBe(true);
  expect(h.restrictDomain(F.submodule([1, 0])).kernel().isZero()).toBe(true);
  expect(h.compose(h).apply([1, 1]).equals(h.apply(h.apply([1, 1])))).toBe(true);
  expect(h.restrictDomain(F.submodule([1, 0])).compose(h.restrictCodomain(h.image())).apply([1, 1]).equals(h.apply([1, 1]))).toBe(true);
});
it('rejects invalid dimensions, restrictions and maps that do not descend', () => {
  const h = homomorphism(F, F, [[1, 0], [x, 0]]), M = F.submodule([0, 1]);
  expect(() => homomorphism(F, F, [[1, 0]])).toThrow(RangeError);
  expect(() => homomorphism(F, QQ.oldPolyRing(x).freeModule(2), [[1, 0], [0, 1]])).toThrow(RangeError);
  expect(() => homomorphism(F, M, [[1, 0], [0, 1]])).toThrow(RangeError);
  expect(() => h.quotientDomain(M)).toThrow(RangeError);
  expect(() => h.restrictCodomain(M)).toThrow(RangeError);
  expect(() => h.restrictDomain(R.freeModule(1))).toThrow(RangeError);
  expect(() => h.restrictDomain(M).compose(h)).toThrow(RangeError);
  expect(() => homomorphism(F.quotientModule([[x, 0]]), F, [[1, 0], [0, 1]])).toThrow(RangeError);
  const id = homomorphism(F, F, [[1, 0], [0, 1]]);
  const Q = F.quotientModule([[x, 0]]);
  expect(homomorphism(Q, Q, id.matrix).isIsomorphism()).toBe(true);
});

it('constructs canonical identity, inclusion and quotient maps', async () => {
  const a = await import('../../../src');
  const x = new a.Sym('x'), R = a.QQ.oldPolyRing(x), F = R.freeModule(2);
  const sub = F.submodule([x,x]);
  const id = a.identityHom(sub), inc = a.inclusionHom(sub);
  expect(id.apply([x,x]).equals(sub.convert([x,x]))).toBe(true);
  expect(inc.codomain).toBe(F);
  const quotient = F.quotientModule([[1,1]]);
  expect(quotient).toBeInstanceOf(a.QuotientModule);
  const projection = a.quotientHom(quotient);
  expect(projection.apply([1,1]).isZero()).toBe(true);
  expect(a.identityHom(quotient).apply([1,0]).equals(quotient.convert([1,0]))).toBe(true);
  const image = quotient.submodule([x,0]);
  const restricted = a.quotientHom(image);
  expect(restricted.codomain.equals(image)).toBe(true);
  expect(restricted.apply([1,1]).isZero()).toBe(true);
  expect(() => a.quotientHom(sub)).toThrow(TypeError);
  expect(String(a.identityHom(F))).toContain('[1, 0], : QQ[x]**2 -> QQ[x]**2');
  expect(String(a.identityHom(R.freeModule(1)))).toBe('Matrix([[1]]) : QQ[x]**1 -> QQ[x]**1');
  expect(String(a.identityHom(R.freeModule(0)))).toBe('Matrix(0, 0, []) : QQ[x]**0 -> QQ[x]**0');
});

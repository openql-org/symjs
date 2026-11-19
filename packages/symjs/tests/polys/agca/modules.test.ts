// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { readFileSync } from 'node:fs';
import { describe, expect, it, vi } from 'vitest';
import { QQ, ZZ, PolynomialRingBase, FreeModule, QuotientModule, ModuleElement, CoercionFailed } from '../../../src/polys';
import { NotImplementedError } from '../../../src/core/errors';
import { at, first } from '../../../src/core/guard';
import { Sym, S, parse as p, str, add, mul } from '../../../src/core';

const refs: Record<string, string> = JSON.parse(readFileSync(new URL('./references.json', import.meta.url), 'utf8'));
const x = new Sym('x'), y = new Sym('y'), R = new PolynomialRingBase(QQ, [x, y]), F = R.freeModule(2);
const fmt = (v: readonly { toString(): string }[]): string => `[${v.map(String).join(', ')}]`;

describe('free modules and elements', () => {
  it('matches the pinned SymPy representations', () => {
    expect(String(F)).toBe(refs['free']);
    expect(`(${F.basis().map(String).join(', ')})`).toBe(refs['basis']);
    expect(String(F.convert(0))).toBe(refs['zero']);
    expect(String(F.submodule([x, add(x, y)]))).toBe(refs['module']);
    expect(F.contains([p('1/x'), 0])).toBe(false);
    expect(F.contains([1])).toBe(false);
    expect(F.contains(1)).toBe(false);
    expect(F.contains(S.Zero)).toBe(true);
    expect(F.subset([[1, x], [x, 2]])).toBe(true);
    expect(F.subset([[1, x], [p('1/x'), 2]])).toBe(false);
    expect(F.convert(F.convert([1, x])).equals(F.convert([1, x]))).toBe(true);
  });
  it('checks rank and the coefficient domain', () => {
    expect(() => new FreeModule(R, -1)).toThrow(RangeError);
    expect(() => QQ.freeModule(2)).toThrow(NotImplementedError);
    expect(() => new PolynomialRingBase(ZZ, [x]).freeModule(2)).toThrow(NotImplementedError);
    expect(R.freeModule(0).isZero()).toBe(true);
    expect(F.isZero()).toBe(false);
    expect(F.isSubmodule(R.freeModule(1))).toBe(false);
    expect(F.isSubmodule(new PolynomialRingBase(QQ, [y]).freeModule(2))).toBe(false);
  });
  it('does exact vector arithmetic and compares across submodules', () => {
    const a = F.convert([x, 1]), b = F.convert([1, y]);
    expect(a.add(b).equals(F.convert([add(x, 1), add(y, 1)]))).toBe(true);
    expect(a.sub(a).isZero()).toBe(true);
    expect(a.mul(y).equals(F.convert([mul(x, y), y]))).toBe(true);
    expect(a.equals(b)).toBe(false);
    expect(a.equals(R.freeModule(1).convert([x]))).toBe(false);
    expect(F.submodule([x, 1]).convert(a).equals(b)).toBe(false);
    expect(a.neg().add(a).isZero()).toBe(true);
    expect(() => F.convert([1])).toThrow(CoercionFailed);
  });
});

describe('submodule standard bases', () => {
  it('tests containment, equality and full modules', () => {
    const M = F.submodule([x, add(x, y)]);
    expect(M.contains([p('2*x'), p('2*x+2*y')])).toBe(true);
    expect(M.contains([x, y])).toBe(false);
    expect(M.isSubmodule(M.submodule([p('x*x'), p('x*x+x*y')]))).toBe(true);
    expect(M.isSubmodule(F)).toBe(false);
    expect(F.isSubmodule(M)).toBe(true);
    expect(M.isFullModule()).toBe(false);
    expect(F.submodule([1, 1], [1, 2]).isFullModule()).toBe(true);
    expect(F.submodule([0, 0]).isZero()).toBe(true);
    expect(M.equals(F.submodule([p('2*x'), p('2*x+2*y')]))).toBe(true);
    expect(() => M.submodule([x, y])).toThrow(CoercionFailed);
  });
  it('returns syzygies and reconstructs generator representations', () => {
    const M = F.submodule([1, 0], [x, 0]), syz = M.syzygyModule();
    expect(String(syz)).toBe(refs['syzygy']);
    for (const relation of syz.gens) expect(M.gens.reduce((sum, g, i) => sum.add(g.mul(at(relation.data, i))), F.convert(0)).isZero()).toBe(true);
    const N = F.submodule([1, 0], [1, 1]);
    expect(String(N.syzygyModule())).toBe(refs['injective_syzygy']);
    const coefficients = N.inTermsOfGenerators([x, p('x*x')]);
    expect(N.inTermsOfGenerators([x, p('x*x')])).toEqual(coefficients);
    expect(`[${coefficients.map(str).join(', ')}]`).toBe(refs['coefficients']);
    expect(N.gens.reduce((sum, g, i) => sum.add(g.mul(at(coefficients, i))), F.convert(0)).equals(F.convert([x, p('x*x')]))).toBe(true);
    expect(() => M.inTermsOfGenerators([0, 1])).toThrow(RangeError);
    expect(F.submodule().syzygyModule().isZero()).toBe(true);
    expect(M.reduceElement([x, 1]).equals(F.convert([0, 1]))).toBe(true);
    expect(N.reduceElement([x, y], true).isZero()).toBe(true);
    expect(F.submodule([1, 0]).union(F.submodule([0, 1])).isFullModule()).toBe(true);
    expect(() => M.union(R.freeModule(1).submodule([1]))).toThrow(RangeError);
  });
  it('computes intersections and verifies both sets of relations', () => {
    const M = F.submodule([x, x]), N = F.submodule([y, y]);
    expect(String(M.intersect(N))).toBe(refs['intersection']);
    const [I, left, right] = M.intersect(N, true);
    for (const [i, g] of I.gens.entries()) {
      expect(M.gens.reduce((sum, h, j) => sum.add(h.mul(at(at(left, i), j))), F.convert(0)).equals(g)).toBe(true);
      expect(N.gens.reduce((sum, h, j) => sum.add(h.mul(at(at(right, i), j))), F.convert(0)).equals(g)).toBe(true);
    }
    expect(M.intersect(F.submodule()).isZero()).toBe(true);
  });
  it('computes module quotients and reconstructs their relations', () => {
    const M = F.submodule([p('x*y'), p('x*y')]), N = F.submodule([x, x]);
    expect(String(M.moduleQuotient(N))).toBe(refs['quotient_ideal']);
    const [I, relations] = M.moduleQuotient(N, true);
    for (const [i, c] of I.gens.entries()) expect(first(N.gens).mul(c).equals(M.gens.reduce((sum, g, j) => sum.add(g.mul(at(at(relations, i), j))), F.convert(0)))).toBe(true);
    expect(M.moduleQuotient(F.submodule()).isWholeRing()).toBe(true);
    expect(M.moduleQuotient(F.submodule([x, x], [y, y])).contains(p('x*y'))).toBe(true);
    expect(() => M.moduleQuotient(F.submodule(), true)).toThrow(NotImplementedError);
    expect(String(F.multiplyIdeal(R.ideal(x)))).toBe('<[x, 0], [0, x]>'); // SymPy 1.14.0
    expect(() => F.multiplyIdeal(new PolynomialRingBase(QQ, [x]).ideal(x))).toThrow(RangeError);
  });
});

describe('quotient modules and quotient coefficients', () => {
  it('compares representatives modulo the denominator', () => {
    const Q = new QuotientModule(F, F.submodule([x, x]));
    expect(String(Q)).toBe(refs['quotient']);
    expect(String(Q.convert([1, 0]))).toBe(refs['coset']);
    expect(Q.convert([1, 0]).equals(Q.convert([add(x, 1), x]))).toBe(true);
    expect(Q.convert([1, 0]).equals(F.convert([1, 0]))).toBe(true);
    expect(F.convert([1, 0]).equals(Q.convert([1, 0]))).toBe(false);
    expect(Q.isSubmodule(Q.submodule([1, 0]))).toBe(true);
    expect(Q.submodule([1, 0]).isSubmodule(Q)).toBe(false);
    expect(Q.equals(new QuotientModule(F, F.submodule([p('2*x'), p('2*x')])))).toBe(true);
    expect(Q.equals(new QuotientModule(F, F.submodule([1, 0])))).toBe(false);
    expect(Q.isZero()).toBe(false);
    expect(F.quotientModule([[1, 0], [0, 1]]).isZero()).toBe(true);
    expect(Q.quotientModule([[1, 0], [0, 1]]).isZero()).toBe(true);
    expect(String(F.submodule([x, 1]).quotientModule(F.submodule([p('x*x'), x])))).toBe(refs['subquotient']);
    expect(() => F.submodule([x, 1]).quotientModule(F.submodule([1, 0]))).toThrow(RangeError);
    expect(() => new QuotientModule(F, R.freeModule(1).submodule([1]))).toThrow(RangeError);
  });
  it('lifts relations when computing kernels and intersections in a quotient', () => {
    const Q = new QuotientModule(F, F.submodule([x, 0]));
    const M = Q.submodule([1, 0]), N = Q.submodule([0, 1]);
    expect(M.syzygyModule().contains([x])).toBe(true);
    expect(M.intersect(N).isZero()).toBe(true);
    expect(M.moduleQuotient(Q.submodule([1, 1])).isZero()).toBe(true);
    const K = R.quotientRing([p('x*x-y*y')]), KF = K.freeModule(2);
    expect(String(KF)).toBe(refs['quotient_ring_free']);
    const S = KF.submodule([x, add(x, y)]);
    expect(S.contains([p('y*y'), p('x*x+x*y')])).toBe(true);
    expect(S.contains([x, y])).toBe(false);
    const A = K.freeModule(1).submodule([add(x, y)]);
    expect(A.syzygyModule().contains([p('x-y')])).toBe(true);
    expect(KF.convert([p('x*x-y*y'), 0]).isZero()).toBe(true);
    expect(fmt([new ModuleElement(F, [x, y])])).toBe('[[x, y]]');
  });
});
it('prints quotient coefficients and lifts them to polynomial-module cosets', () => {
  const F = QQ.oldPolyRing(x).quotientRing([x.pow(2).add(1)]).freeModule(2);
  const e = F.convert([1,0]);
  expect(String(e)).toBe('[1 + <x**2 + 1>, 0 + <x**2 + 1>]');
  const lifted = F.lift(e);
  expect(String(lifted)).toBe('[1, 0] + <[x**2 + 1, 0], [0, x**2 + 1]>');
  expect(F.quot.contains(lifted)).toBe(true);
  expect(F.convert([x.pow(2),0]).equals(e.neg())).toBe(true);
});

it('reconstructs fractional intersection and quotient relations over a local ring', () => {
  const L = new PolynomialRingBase(QQ, [x, y], 'ilex'), ambient = L.freeModule(1);
  const A = ambient.submodule([p('x/(1+x)')]), B = ambient.submodule([p('1/(1+y)')]);
  const [I, relations] = A.moduleQuotient(B, true);
  for (const [i, c] of I.gens.entries()) expect(A.gens.reduce((s, g, j) => s.add(g.mul(at(at(relations, i), j))), ambient.convert(0)).equals(first(B.gens).mul(c))).toBe(true);
  expect(A.moduleQuotient(B, true)[0].equals(I)).toBe(true);
  const [intersection, left, right] = A.intersect(B, true);
  for (const [i, g] of intersection.gens.entries()) {
    expect(A.gens.reduce((s, a, j) => s.add(a.mul(at(at(left, i), j))), ambient.convert(0)).equals(g)).toBe(true);
    expect(B.gens.reduce((s, b, j) => s.add(b.mul(at(at(right, i), j))), ambient.convert(0)).equals(g)).toBe(true);
  }
  expect(() => A.inTermsOfGenerators([1])).toThrow(CoercionFailed);
  const D = ambient.submodule([p('x+x*x+y*y')]);
  const input = ambient.convert([x]), remainder = D.reduceElement(input);
  expect(D.contains(input.sub(remainder))).toBe(true);
  expect(ambient.submodule().reduceElement([p('x/(1+x)')]).equals(ambient.convert([p('x/(1+x)')]))).toBe(true);
});

it('propagates computation failures from membership checks', () => {
  const ambient = R.freeModule(1), failure = new RangeError('computation failed');
  const conversion = vi.spyOn(ambient, 'convert').mockImplementation(() => { throw failure; });
  expect(() => ambient.contains([0])).toThrow(failure);
  conversion.mockRestore();
});

it('divides module elements by scalars with exact cancellation', () => {
  const value = F.convert([p('x**2+x'), p('x+1')]);
  expect(String(value.div(p('x+1')))).toBe('[x, 1]');
  expect(() => value.div(x)).toThrow(CoercionFailed);
  expect(F.isSubmodule(0)).toBe(false);
  expect(F.submodule([x, 0]).isSubmodule(0)).toBe(false);
  expect(String(F.convert([2, 4]).div(2))).toBe('[1, 2]');
});


it('converts quotient cosets only along containment of their relations', () => {
  const A = F.quotientModule([[x, 0]]), B = F.quotientModule([[1, 0]]);
  const a = A.convert([x, 1]);
  expect(B.convert(a).equals([0, 1])).toBe(true);
  expect(A.convert(a).equals(a)).toBe(true);
  expect(() => A.convert(B.convert([0, 1]))).toThrow(CoercionFailed);
  expect(() => F.convert(a)).toThrow(CoercionFailed);
  expect([...F.convert([x, y])]).toEqual([x, y]);
  expect(F.convert([x, y]).equals([1])).toBe(false);
  expect(F.convert([0, 0]).equals(0)).toBe(true);
  expect(a.equals([p('1/x'), 0])).toBe(false);
});

it('forms cosets by addition and multiplies modules by scalars and ideals', () => {
  const N = F.submodule([x, 0]);
  expect(N.add([x, 1]).equals([0, 1])).toBe(true);
  expect(F.convert([x, 1]).add(N).equals([0, 1])).toBe(true);
  expect(F.mul(x).equals(F.multiplyIdeal(R.ideal(x)))).toBe(true);
  expect(F.mul(R.ideal(y)).equals(F.multiplyIdeal(R.ideal(y)))).toBe(true);
  expect(F.mul(2).isFullModule()).toBe(true);
  const e = F.convert([1, 0]);
  const spy = vi.spyOn(F, 'convert').mockImplementation(() => { throw new RangeError('conversion failed'); });
  expect(() => e.equals([1, 0])).toThrow('conversion failed');
  spy.mockRestore();
});

it('orders module positions before or after polynomial monomials', async () => {
  const { ModuleOrder, lex, grlex, ilex } = await import('../../../src/polys');
  const positionFirst = new ModuleOrder(lex, grlex, false);
  expect(positionFirst.key([1, 2, 3])).toEqual([1, [5, [2, 3]]]);
  expect(new ModuleOrder(ilex, lex, false).key([1, 2, 3])).toEqual([-1, [2, 3]]);
  expect(new ModuleOrder(lex, grlex, true).key([1, 2, 3])).toEqual([[5, [2, 3]], 1]);
  expect(String(positionFirst)).toBe('ModuleOrder(lex, grlex)');
  expect(positionFirst.equals(new ModuleOrder(lex, grlex, false))).toBe(true);
  expect(positionFirst.equals(new ModuleOrder(ilex, grlex, false))).toBe(false);
  expect(positionFirst.equals(0)).toBe(false);
  expect(new ModuleOrder(lex, lex, false).equals(new ModuleOrder(lex, lex, true))).toBe(false);
});

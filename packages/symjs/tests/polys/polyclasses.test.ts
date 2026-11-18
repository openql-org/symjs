// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { ANP } from '../../src/polys/polyclasses';
import { QQ, ZZ } from '../../src/polys/domains';
import { UnificationFailed } from '../../src/polys/polyerrors';

it('compares defining polynomials as well as representatives', () => {
  const a = new ANP([1, 1], [1, 0, 1]);
  expect(a.equals(new ANP([1, 1], [1, 0, 2]))).toBe(false);
  expect(a.equals(new ANP([1, 1], [1, 0, 1]))).toBe(true);
  expect(a.equals(new ANP([1, 2], [1, 0, 1]))).toBe(false);
  expect(new ANP(1, [1, 0, 1]).isOne).toBe(true);
  expect(a.isOne).toBe(false);
  expect(new ANP(2, [1, 0, 1]).isOne).toBe(false);
  const modulus = a.modToList();
  modulus.pop();
  expect(a.modToList().map(String)).toEqual(['1', '0', '1']);
});

it('computes quotient and remainder in the algebraic field', () => {
  const a = new ANP([2, -1, 1], [1, 0, 0, -2]);
  const b = new ANP([1, 2], [1, 0, 0, -2]);
  const [q, r] = a.divmod(b);
  expect(q.mul(b).equals(a)).toBe(true);
  expect(a.quo(a).isOne).toBe(true);
  expect(r.isZero).toBe(true);
  expect(a.rem(b).isZero).toBe(true);
  expect(() => a.rem(0)).toThrow('zero divisor');
  expect(() => a.divmod(0)).toThrow('zero divisor');
});

it('unifies ground domains without changing the defining polynomial', () => {
  const a = new ANP([1], [1, 0, -2], ZZ);
  const b = new ANP([1, 2], [1, 0, -2], QQ);
  const [domain, per, f, g, mod] = a.unify(b);
  expect(domain).toBe(QQ);
  expect(per(f).dom).toBe(QQ);
  expect(per(g).equals(b)).toBe(true);
  expect(mod.map(String)).toEqual(['1', '0', '-2']);
  expect(a.unify(a)[0]).toBe(ZZ);
  expect(() => a.unify(new ANP(1, [1, 0, 2]))).toThrow(UnificationFailed);
  expect(() => a.unify(new ANP(1, [1, 0, 0, 2]))).toThrow(UnificationFailed);
});

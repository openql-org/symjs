// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
import { expect, it } from 'vitest';
import { Poly, Sym, add, mul, pow, orderAt, orderAtOo } from '../../src';

const t = new Sym('t');
const poly = (e: Parameters<typeof Poly.from>[0]) => Poly.from(e, [t]);

it('counts polynomial factor multiplicities, including zero and coprime inputs', () => {
  const p = add(pow(t, 2), 1);
  const a = mul(pow(t, 37), pow(p, 100));
  expect(orderAt(poly(a), poly(t), t)).toBe(37);
  expect(orderAt(poly(a), poly(p), t)).toBe(100);
  expect(orderAt(poly(pow(t, 4)), poly(p), t)).toBe(0);
  expect(orderAt(poly(0), poly(t), t)).toBe(Infinity);
  expect(() => orderAt(poly(1), poly(1), t)).toThrow(RangeError);
  expect(() => orderAt(poly(1), poly(0), t)).toThrow(RangeError);
});

it('computes orders of rational functions at infinity', () => {
  expect(orderAtOo(poly(add(pow(t, 2), -1)), poly(add(t, 1)), t)).toBe(-1);
  expect(orderAtOo(poly(1), poly(pow(t, 3)), t)).toBe(3);
  expect(orderAtOo(poly(0), poly(t), t)).toBe(Infinity);
  expect(() => orderAtOo(poly(t), poly(0), t)).toThrow(RangeError);
});

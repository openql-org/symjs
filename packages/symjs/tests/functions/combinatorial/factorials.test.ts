// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { expect, it } from 'vitest';
import { ff, rf, Fn, Poly, S, Sym, expand, mul, pow, rational } from '../../../src';

const x = new Sym('x');
const y = new Sym('y');

it('evaluates ordinary factorial products through the expression API', () => {
  expect(ff(5, 3)).toEqual(rational(60));
  expect(rf(5, 3)).toEqual(rational(210));
});

it('shifts polynomial generators and preserves polynomial results', () => {
  const p = Poly.from(mul(x, x), [x]);
  for (const [f, direction] of [[ff, -1], [rf, 1]] as const) {
    const result = f(p, 3);
    expect(result).toBeInstanceOf(Poly);
    if (!(result instanceof Poly)) throw new TypeError('expected Poly');
    expect(result.asExpr().equals(expand(mul(p.asExpr(), p.shift(direction).asExpr(), p.shift(2 * direction).asExpr())))).toBe(true);
    expect(f(p, -2).equals(pow(expand(mul(p.shift(-direction).asExpr(), p.shift(-2 * direction).asExpr())), -1))).toBe(true);
    expect(f(p, 0)).toBe(S.One);
    expect(() => f(p, rational(1, 2))).toThrow(TypeError);
    expect(() => f(Poly.from(x, [x, y]), 2)).toThrow(RangeError);
    expect(() => f(Poly.from(x, [x, y]), -2)).toThrow(RangeError);
  }
});

it('uses the public constructors as expression heads', () => {
  expect(new Fn('ff', [x, y]).func).toBe(ff);
  expect(new Fn('rf', [x, y]).func).toBe(rf);
});

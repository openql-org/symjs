// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/ops.ts.

// core/ops without the elementary functions loaded (this file must import only the modules below,
// so it must stay a separate file).

import { describe, expect, it } from 'vitest';
import { Sym } from '../../src/core/nodes';
import '../../src/core/ops';

describe('realRoot without the elementary functions', () => {
  it('reports that sign is not loaded', async () => {
    const { realRoot } = await import('../../src/core/ops');
    expect(() => realRoot(new Sym('r', { real: true }), 3)).toThrow("sign is not available: import '@symjs/symjs/core'");
  });
});

describe('couldExtractMinusSign without the sort keys', () => {
  it('decides a tie by the structural key', async () => {
    const { add, mul, couldExtractMinusSign } = await import('../../src/core/ops');
    const a = new Sym('a');
    const b = new Sym('b');
    // exactly one of a - b and b - a has the minus sign extracted
    expect(couldExtractMinusSign(add(a, mul(-1, b)))).toBe(!couldExtractMinusSign(add(b, mul(-1, a))));
  });
});

it('combines Order terms before the series arithmetic module is loaded', async () => {
  await import('../../src/core/traverse');
  await import('../../src/printing/str');
  const { Add, Fn, Mul, Order, Pow, S } = await import('../../src/core/nodes');
  const { add, mul, pow } = await import('../../src/core/ops');
  const x = new Sym('x');
  const y = new Sym('y');
  const order = (e: import('../../src/core/nodes').Expr) => new Order([e]);
  expect(String(add(pow(x, 3), order(pow(x, 2))))).toBe('O(x**2)');
  expect(String(add(order(pow(x, 3)), order(x), order(pow(x, 2))))).toBe('O(x)');
  expect(add(order(x), order(y))).toBeInstanceOf(Add);
  expect(String(add(x, order(new Pow(x, y))))).toBe('O(x**y)');
  expect(String(add(mul(x, add(1, x)), order(pow(x, 3))))).toBe('x*(x + 1) + O(x**3)');
  expect(String(add(mul(x, add(1, new Fn('sin', [x]))), order(pow(x, 3))))).toBe('x*(sin(x) + 1) + O(x**3)');
  expect(String(add(new Fn('sin', [x]), order(pow(x, 2))))).toBe('sin(x) + O(x**2)');
  expect(String(add(new Add([S.One, x]), order(pow(x, 2))))).toBe('1 + x + O(x**2)');
  const shifted = add(x, -1);
  const o = order(pow(shifted, 2));
  expect(add(pow(shifted, 3), o)).toBe(o);
  expect(add(new Mul([shifted, pow(shifted, 2), S.One]), o)).toBe(o);
  expect(add(new Mul([shifted, y]), o)).toBeInstanceOf(Add);
  expect(add(new Pow(shifted, y), o)).toBeInstanceOf(Add);
  expect(String(add(1, o))).toBe('1 + O((x - 1)**2)');
  expect(add(S.Infinity, x, mul(-1, x))).toBe(S.Infinity);
  expect(pow(new Fn('exp_polar', [x]), y).key).toBe(new Fn('exp_polar', [mul(x, y)]).key);
  expect(mul(S.ComplexInfinity, new Sym('p', { positive: true }))).toBe(S.ComplexInfinity);
  expect(pow(0, S.Half.neg())).toBe(S.ComplexInfinity);
  expect(pow(S.E, new Add([new Fn('log', [x]), new Fn('log', [y])])).key).toBe(mul(x, y).key);
  const { seterr } = await import('../../src/core/errors');
  seterr({ divide: true });
  try {
    expect(() => mul(new Mul([S.Zero, S.ComplexInfinity]))).toThrow(RangeError);
  } finally {
    seterr({ divide: false });
  }
  expect(mul(new Mul([S.Zero, S.ComplexInfinity]))).toBe(S.NaN);
});

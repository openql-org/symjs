// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { expect, it } from 'vitest';
import { ExtensionExpr, S, add, doit, factor, latex, mul, neg, sub, symbol, xreplace } from '@symjs/symjs';
import { Commutator } from '../src/secondquant';

it('canonicalizes and evaluates second-quantization commutators', () => {
  const x = symbol('x');
  const a = symbol('a', { commutative: false });
  const b = symbol('b', { commutative: false });
  const c = symbol('c', { commutative: false });
  const commutator = Commutator(a, b);
  expect(commutator.isCommutative).toBe(false);
  expect(Commutator(a, a)).toBe(S.Zero);
  expect(Commutator(x, b)).toBe(S.Zero);
  expect(Commutator(b, x)).toBe(S.Zero);
  expect(Commutator(b, a).equals(neg(commutator))).toBe(true);
  expect(Commutator(mul(x, a), mul(2, b)).equals(mul(2, x, commutator))).toBe(true);
  expect(Commutator(a, mul(x, b)).equals(mul(x, commutator))).toBe(true);
  expect(Commutator(add(a, c), b).equals(add(commutator, Commutator(c, b)))).toBe(true);
  expect(Commutator(a, add(b, c)).equals(add(commutator, Commutator(a, c)))).toBe(true);
  expect(doit(commutator).equals(sub(mul(a, b), mul(b, a)))).toBe(true);
  expect(latex(commutator)).toBe('\\left[a,b\\right]');
  if (commutator instanceof ExtensionExpr) {
    for (const args of [[], [a], [a, b, c]]) expect(() => commutator.withArgs(args)).toThrow(RangeError);
  }
  const right = Commutator(a, c);
  expect(factor(add(mul(x, commutator), mul(x, right, commutator))).equals(mul(x, add(1, right), commutator))).toBe(true);
  expect(xreplace(commutator, new Map([[b, c]])).equals(Commutator(a, c))).toBe(true);
});

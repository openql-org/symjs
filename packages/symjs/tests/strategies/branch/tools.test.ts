// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/strategies/branch/tools.ts (SymPy sympy/strategies/branch/tools.py).
// Cases from sympy/strategies/branch/tests/test_tools.py; expected values are SymPy 1.14's.

import { describe, expect, it } from 'vitest';
import { Basic, Rational, str } from '../../../src';
import type { Expr } from '../../../src';
import { branch } from '../../../src/strategies';

const isInt = (x: Expr): x is Rational => x instanceof Rational && x.q === 1n;
const val = (x: Rational): number => Number(x.p);

function* posdec(x: Expr): Generator<Expr> {
  yield isInt(x) && val(x) > 0 ? Rational.of(val(x) - 1) : x;
}

function* branch5(x: Expr): Generator<Expr> {
  if (isInt(x)) {
    const v = val(x);
    if (0 < v && v < 5) yield Rational.of(v - 1);
    else if (5 < v && v < 10) yield Rational.of(v + 1);
    else if (v === 5) {
      yield Rational.of(v + 1);
      yield Rational.of(v - 1);
    } else yield x;
  }
}

describe('branching canon', () => {
  it('zero ints', () => {
    const expr = Basic(2, Basic(5, 3), 8);
    expect(new Set([...branch.canon(posdec)(expr)].map(str))).toEqual(new Set(['Basic(0, Basic(0, 0), 0)']));
  });

  it('split 5', () => {
    const expr = Basic(2, Basic(5, 3), 8);
    expect(new Set([...branch.canon(branch5)(expr)].map(str))).toEqual(new Set(['Basic(0, Basic(0, 0), 10)', 'Basic(0, Basic(10, 0), 10)']));
  });
});

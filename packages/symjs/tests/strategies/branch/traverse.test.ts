// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/strategies/branch/traverse.ts (SymPy sympy/strategies/branch/traverse.py).
// Cases from sympy/strategies/branch/tests/test_traverse.py; expected values are SymPy 1.14's.

import { describe, expect, it } from 'vitest';
import { Basic, Rational, str } from '../../../src';
import type { Expr } from '../../../src';
import { branch } from '../../../src/strategies';

const { doOne, identity } = branch;
const { sall, topDown } = branch.traverse;

function* inc(x: Expr): Generator<Expr> {
  if (x instanceof Rational && x.q === 1n) yield x.add(1);
}

const strs = (xs: Iterable<Expr>): Set<string> => new Set([...xs].map(str));

describe('branching traversals', () => {
  it('top_down: easy', () => {
    expect(strs(topDown(inc)(Basic(1, 2)))).toEqual(new Set(['Basic(2, 3)']));
  });

  it('top_down: big tree', () => {
    const expr = Basic(1, Basic(2), Basic(3, Basic(4), 5));
    expect(strs(topDown(inc)(expr))).toEqual(new Set(['Basic(2, Basic(3), Basic(4, Basic(5), 6))']));
  });

  it('top_down: harder function', () => {
    function* split5(x: Expr): Generator<Expr> {
      if (x.equals(5)) {
        yield x.sub(1);
        yield x.add(1);
      }
    }
    const expr = Basic(Basic(5, 6), 1);
    expect(strs(topDown(split5)(expr))).toEqual(new Set(['Basic(Basic(4, 6), 1)', 'Basic(Basic(6, 6), 1)']));
  });

  it('sall', () => {
    expect([...sall(inc)(Basic(1, 2))].map(str)).toEqual(['Basic(2, 3)']);
    const expr = Basic(1, 2, Basic(3, 4));
    expect([...sall(doOne(inc, identity))(expr)].map(str)).toEqual(['Basic(2, 3, Basic(3, 4))']);
  });
});

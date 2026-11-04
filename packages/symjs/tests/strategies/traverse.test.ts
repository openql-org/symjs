// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/strategies/traverse.ts (SymPy sympy/strategies/traverse.py).
// Cases from sympy/strategies/tests/test_traverse.py; expected values are SymPy 1.14's.

import { describe, expect, it } from 'vitest';
import { Add, Basic, BasicNode, Float, Rational, S, Sym, add, pow, str, symbols } from '../../src';
import type { Expr } from '../../src';
import { Str } from '../../src/matrices';
import { rebuild, traverse, util } from '../../src/strategies';

const { bottomUp, bottomUpOnce, sall, topDown, topDownOnce } = traverse;
const [x, y, z] = symbols('x y z');
const n = (v: number): Expr => Rational.of(v);
const eq = (a: Expr, b: Expr): void => expect(a.key).toBe(b.key);

const zeroSymbols = (e: Expr): Expr => (e instanceof Sym ? S.Zero : e);

describe('traversals', () => {
  it('sall', () => {
    const zeroOnelevel = sall(zeroSymbols);
    eq(zeroOnelevel(Basic(x, y, Basic(x, z))), Basic(0, 0, Basic(x, z)));
  });

  for (const [name, trav] of [
    ['bottom_up', bottomUp],
    ['top_down', topDown],
  ] as const) {
    it(`${name}: global traversal`, () => {
      const zeroAllSymbols = trav(zeroSymbols);
      eq(zeroAllSymbols(Basic(x, y, Basic(x, z))), Basic(0, 0, Basic(0, 0)));
    });
    it(`${name}: stops on non-Basics`, () => {
      // SymPy adds one where it can (a Str raises TypeError and is kept)
      const addOneIfCan = (e: Expr): Expr => (e instanceof Str || e instanceof BasicNode ? e : add(e, 1));
      const expr = Basic(1, new Str('a'), Basic(2, new Str('b')));
      const expected = Basic(2, new Str('a'), Basic(3, new Str('b')));
      eq(trav(addOneIfCan)(expr), expected);
    });
  }

  const Basic2 = (...args: Expr[]): Expr => new BasicNode(args, 'Basic2');
  const rl = (e: Expr): Expr => (e.args.length && !(e.args[0] instanceof Rational && e.args[0].q === 1n) ? Basic2(...e.args) : e);

  it('top_down_once', () => {
    const topRl = topDownOnce(rl);
    eq(topRl(Basic(new Float(1.0), new Float(2.0), Basic(3, 4))), Basic2(new Float(1.0), new Float(2.0), Basic(3, 4)));
    // the rule does not apply at the top, so it is applied below
    eq(topRl(Basic(1, Basic(new Float(3.0)))), Basic(1, Basic2(new Float(3.0))));
  });

  it('bottom_up_once', () => {
    const bottomRl = bottomUpOnce(rl);
    eq(bottomRl(Basic(1, 2, Basic(new Float(3.0), new Float(4.0)))), Basic(1, 2, Basic2(new Float(3.0), new Float(4.0))));
    // nothing changes below, so the rule is applied at the top
    eq(bottomRl(Basic(new Float(1.0), 2)), Basic2(new Float(1.0), n(2)));
  });

  it('expr_fns', () => {
    const expr = add(x, pow(y, 3));
    const e = bottomUp((v) => add(v, 1), util.exprFns)(expr);
    const b = bottomUp((v) => new Add([v, n(1)]), util.basicFns)(expr);
    eq(rebuild(b), e);
    expect(str(e)).toBe('x + (y + 1)**4 + 3');
  });
});

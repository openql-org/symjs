// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/strategies/tools.ts (SymPy sympy/strategies/tools.py).
// Cases from sympy/strategies/tests/test_tools.py and the doctests; expected values are SymPy 1.14's.

import { describe, expect, it } from 'vitest';
import { Add, Basic, BasicNode, Mul, Rational, S, str, symbols } from '../../src';
import type { Expr } from '../../src';
import { canon, rmId, tools, typed, util } from '../../src/strategies';

const [a, b, c, d, e, f, x, y] = symbols('a b c d e f x y');
const n = (v: number): Expr => Rational.of(v);
const eq = (p: Expr, q: Expr): void => expect(p.key).toBe(q.key);

describe('tools', () => {
  it('subs', () => {
    const mapping = new Map<Expr, Expr>([
      [a, d],
      [d, a],
      [Basic(e), Basic(f)],
    ]);
    const expr = Basic(a, Basic(b, c), Basic(d, Basic(e)));
    eq(tools.subs(mapping)(expr), Basic(d, Basic(b, c), Basic(a, Basic(f))));
    // doctest
    const m2 = new Map<Expr, Expr>([
      [n(1), n(4)],
      [n(4), n(1)],
      [Basic(5), Basic(6, 7)],
    ]);
    expect(str(tools.subs(m2)(Basic(1, Basic(2, 3), Basic(4, Basic(5)))))).toBe('Basic(4, Basic(2, 3), Basic(1, Basic(6, 7)))');
    // pairs, and evaluation through the tree functions
    expect(str(tools.subs([[x, n(1)]], util.exprFns)(new Add([x, n(1)])))).toBe('2');
  });

  it('subs of an empty mapping', () => {
    eq(tools.subs(new Map())(Basic(1, 2)), Basic(1, 2));
  });

  it('typed', () => {
    const A = (...args: Expr[]) => new BasicNode(args, 'A');
    const B = (...args: Expr[]) => new BasicNode(args, 'B');
    const rmzeros = rmId((v) => v.equals(S.Zero));
    const rmones = rmId((v) => v.equals(S.One));
    const removeSomething = typed({ A: rmzeros, B: rmones });
    eq(removeSomething(A(n(0), n(1))), A(n(1)));
    eq(removeSomething(B(n(0), n(1))), B(n(0)));
    // doctest: typed({Add: rm_zeros, Mul: rm_ones}), with a Map
    const removeIdents = typed(
      new Map([
        ['Add', rmzeros],
        ['Mul', rmones],
      ]),
    );
    expect(removeIdents(new Add([x, n(0)])).args).toEqual([x]);
    expect(removeIdents(new Mul([x, n(1)])).args).toEqual([x]);
    eq(removeIdents(Basic(0)), Basic(0));
  });

  it('canon', () => {
    const zeroX = (v: Expr): Expr => (v.equals(x) ? S.Zero : v);
    const oneY = (v: Expr): Expr => (v.equals(y) ? S.One : v);
    expect(str(canon(zeroX)(Basic(x, Basic(x, y))))).toBe('Basic(0, Basic(0, y))');
    expect(str(canon(zeroX, oneY)(Basic(x, Basic(x, y))))).toBe('Basic(0, Basic(0, 1))');
    // canon(..., fns=expr_fns) evaluates the rebuilt nodes
    expect(str(canon(zeroX, { fns: util.exprFns })(new Add([x, y, x])))).toBe('y');
  });
});

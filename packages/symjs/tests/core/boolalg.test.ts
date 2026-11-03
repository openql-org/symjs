// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/boolalg.ts.
// And, Or, Not, Xor and the boolean functions (SymPy sympy.logic.boolalg). Expected values are
// SymPy 1.14's, plus cross-checks against SymPy on generated expressions.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { BoolOp, and, not, or, xor } from '../../src/core/boolalg';
import { Gt, Lt } from '../../src/core/logic';
import { Expr, Rational, S } from '../../src/core/nodes';
import { mul } from '../../src/core/ops';

const [x, y, z, a, A, B] = sj.symbols('x y z a A B');

const { oo } = sj;

const s = (e: Expr): string => e.toString();
const R = (p: number, q = 1) => Rational.of(p, q);
const negOo = mul(-1, oo);

const s2 = (e: unknown): string => sj.str(e as Expr);

const { And, Or, Not, Xor } = sj;
const T = sj.S.true;
const F = sj.S.false;

describe('And, Or, Not, Xor (SymPy logic.boolalg)', () => {
  it('rebuilds with new arguments', () => {
    // SymPy: Not(x).subs(x, y) = ~y; ITE(x > 0, y > 0, z > 0).subs(x, a) = ITE(a > 0, y > 0, z > 0)
    expect(s(not(x).subs(x, y))).toBe('~y');
    const ite = new BoolOp('ITE', [Gt(x, 0), Gt(y, 0), Gt(z, 0)]);
    expect(s(ite.subs(x, a))).toBe('ITE(a > 0, y > 0, z > 0)');
    expect(s(xor(x, y).subs(x, z))).toBe('y ^ z');
  });
  it('prints ITE and Xor in LaTeX', () => {
    // SymPy: latex(ITE(x > 0, y > 0, z > 0)) = \operatorname{ITE}\left(x > 0, y > 0, z > 0\right)
    const ite = new BoolOp('ITE', [Gt(x, 0), Gt(y, 0), Gt(z, 0)]);
    expect(sj.latex(ite)).toBe('\\operatorname{ITE}\\left(x > 0, y > 0, z > 0\\right)');
    expect(sj.latex(xor(x, y))).toBe('x \\veebar y');
  });
  it('prints relations with -oo first in And', () => {
    // SymPy: str(And(Gt(x, -oo), Gt(y, 0))) = (x > -oo) & (y > 0); And(Lt(-oo, x), Gt(y, 0), z) = (-oo < x) & z & (y > 0)
    expect(s(and(Gt(x, negOo), Gt(y, 0)))).toBe('(x > -oo) & (y > 0)');
    expect(s(and(Lt(negOo, x), Gt(y, 0), z))).toBe('(-oo < x) & z & (y > 0)');
  });
  it('reads the integers 1 and 0 as true and false and rejects other numbers', () => {
    // SymPy: And(1, x) = x, Or(0, x) = x, Not(1) = False, Not(2) = False, Xor(1, x) = ~x
    expect(and(1, x)).toBe(x);
    expect(or(0, x)).toBe(x);
    expect(not(1)).toBe(S.false);
    expect(not(0)).toBe(S.true);
    expect(not(2)).toBe(S.false);
    expect(s(xor(1, x))).toBe('~x');
    // SymPy: And(2, x), And(S.Half, x) and Or(Float(1.0), x) raise TypeError
    expect(() => and(2, x)).toThrow('expecting bool or Boolean, not `2`.');
    expect(() => and(R(1, 2), x)).toThrow(TypeError);
    expect(() => or(1.5, x)).toThrow(TypeError);
  });
});

describe('boolean functions', () => {
  it('And, Or, Not, Xor (core) print like SymPy', () => {
    expect(s2(And(x, y))).toBe('x & y');
    expect(s2(Or(x, y))).toBe('x | y');
    expect(Not(true)).toBe(F);
    expect(Not(false)).toBe(T);
    expect(Not(And(true, false))).toBe(T);
    expect(Not(Or(true, false))).toBe(F);
    expect(s2(Not(And(And(true, x), Or(x, false))))).toBe('~x');
    expect(s2(Not(And(Or(A, B), Or(Not(A), Not(B)))))).toBe('~((A | B) & (~A | ~B))');
    expect(Not(T)).toBe(F);
    expect(Xor(true, false)).toBe(T);
    expect(Xor(true, true)).toBe(F);
    expect(Xor(true, false, true, true, false)).toBe(T);
    expect(Xor(true, false, true, false)).toBe(F);
    expect(s2(Xor(x, y))).toBe('x ^ y');
  });
});

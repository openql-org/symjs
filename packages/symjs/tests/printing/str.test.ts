// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/printing/str.ts.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { add, adjoint, exp, I, latex, mul, pow, Sym, transpose } from '../../src';
import { Add, ExtensionExpr, Float, Limit, Mul, Pow, Rational, S } from '../../src/core/nodes';
import type { Expr } from '../../src/core/nodes';
import { precedence, str } from '../../src/printing/str';
import * as Sets from '../../src/sets/sets';

const x = new Sym('x');
const y = new Sym('y');
const z = new Sym('z');
const A = new Sym('A', { commutative: false });
const B = new Sym('B', { commutative: false });

// expected values generated with SymPy 1.14 (str, latex)
const CASES: [unknown, string, string][] = [
    [pow(A, -1), 'A**(-1)', 'A^{-1}'],
    [pow(mul(A, B), 2), '(A*B)**2', '\\left(A B\\right)^{2}'],
    [mul(-1, A, B), '-A*B', '- A B'],
    [mul(A, Rational.of(1, 2)), 'A/2', '\\frac{A}{2}'],
    [mul(I, A, B), 'I*A*B', 'i A B'],
    [mul(x, A, pow(B, 2)), 'x*A*B**2', 'x A B^{2}'],
    [mul(adjoint(A), A), 'adjoint(A)*A', 'A^{\\dagger} A'],
    [pow(adjoint(mul(A, B)), 2), '(adjoint(B)*adjoint(A))**2', '\\left(B^{\\dagger} A^{\\dagger}\\right)^{2}'],
    [add(mul(A, B), mul(-1, B, A)), 'A*B - B*A', 'A B - B A'],
    [mul(add(A, B), add(A, mul(-1, B))), '(A + B)*(A - B)', '\\left(A + B\\right) \\left(A - B\\right)'],
    [mul(exp(A), exp(B)), 'exp(A)*exp(B)', 'e^{A} e^{B}'],
    [adjoint(mul(I, x, A)), '-I*conjugate(x)*adjoint(A)', '- i \\overline{x} A^{\\dagger}'],
    [pow(transpose(A), -1), 'transpose(A)**(-1)', '\\operatorname{transpose}^{-1}{\\left(A \\right)}'],
    [pow(A, Rational.of(1, 2)), 'sqrt(A)', '\\sqrt{A}'],
    [add(mul(2, adjoint(A)), B), 'B + 2*adjoint(A)', 'B + 2 A^{\\dagger}'],
];

const R = (p: number, q = 1): Rational => Rational.of(BigInt(p), BigInt(q));

/** An extension node printed Name(args) with a declared str precedence. */
class Ext extends ExtensionExpr {
  constructor(
    name: string,
    args: readonly Expr[],
    readonly prec: unknown,
  ) {
    super(name, args);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new Ext(this.name, args, this.prec);
  }
  strPrecedence(): unknown {
    return this.prec;
  }
}

describe('non-commutative printing matches SymPy', () => {
  it.each(CASES.map((c, i) => [i, ...c] as const))('case %i', (_i, e, s, l) => {
    expect(String(e)).toBe(s);
    expect(latex(e as never)).toBe(l);
  });
});

/**
 * Coverage of the str printer and the printing sort keys: expected
 * values are SymPy 1.14 `str(expr)`, `latex(expr)` and
 * `expr.as_ordered_terms()` / `sorted(..., key=default_sort_key)`.
 */

describe('str', () => {
  const cases: [string, () => sj.Expr, string][] = [
    ['Pow(-oo, x, evaluate=False)', () => new Pow(S.NegativeInfinity, x), '(-oo)**x'],
    ['Mul(2, 3, evaluate=False)', () => new Mul([R(2), R(3)]), '2*3'],
    ['Limit(x, x, 0)', () => new Limit([x, x, R(0)]), "Limit(x, x, 0, dir='+')"],
    ['ImageSet(Lambda(x, x**2), S.Naturals)', () => new Sets.ImageSet(x, sj.pow(x, 2), Sets.Naturals), 'ImageSet(Lambda(x, x**2), Naturals)'],
    ['ConditionSet(x, x > 0, S.Reals)', () => new Sets.ConditionSet(x, sj.Gt(x, 0), Sets.Reals), 'ConditionSet(x, x > 0, Reals)'],
    ['Mul(Float(-2.0), 1, evaluate=False)', () => new Mul([new Float(-2), R(1)]), '-2.0*1'],
    ['Mul(-2, Float(1.0), evaluate=False)', () => new Mul([R(-2), new Float(1)]), '-2*1.0'],
    ['Mul(-2, 1, evaluate=False)', () => new Mul([R(-2), R(1)]), '-2*1'],
    ['Mul(1, -2, evaluate=False)', () => new Mul([R(1), R(-2)]), '1*(-2)'],
    ['Mul(Float(2.0), -1, evaluate=False)', () => new Mul([new Float(2), R(-1)]), '2.0*(-1)'],
    ['Mul(Rational(-1, 2), 3, evaluate=False)', () => new Mul([R(-1, 2), R(3)]), '-1/2*3'],
    ['Mul(-1, 1, evaluate=False)', () => new Mul([R(-1), R(1)]), '-1*1'],
    // SymPy Mul(-2, evaluate=False) is -2 itself
    ['Mul(-2, evaluate=False)', () => new Mul([R(-2)]), '-2'],
    ['-oo*x', () => sj.mul(S.NegativeInfinity, x), '-oo*x'],
    ['-oo*x/y', () => sj.mul(S.NegativeInfinity, x, sj.pow(y, -1)), '-oo*x/y'],
    ['x - oo*y', () => sj.add(x, sj.mul(S.NegativeInfinity, y)), 'x - oo*y'],
    ['Pow(-oo*x, 2, evaluate=False)', () => new Pow(sj.mul(S.NegativeInfinity, x), R(2)), '(-oo*x)**2'],
    ['And(x < y, z)', () => sj.And(sj.Lt(x, y), z), 'z & (x < y)'],
    ['Or(Eq(x, y), z)', () => sj.Or(sj.Eq(x, y), z), 'z | Eq(x, y)'],
    ['Pow(Float(-1.5), x, evaluate=False)', () => new Pow(new Float(-1.5), x), '(-1.5)**x'],
  ];
  for (const [label, build, want] of cases) it(label, () => expect(str(build())).toBe(want));

  it('an expression class the printer does not know prints as its key', () => {
    // an Expr subclass outside the library's node classes
    class MyExpr extends sj.Expr {
      readonly kind = 'Extension' as const;
      readonly args: readonly sj.Expr[] = [];
      protected computeKey(): string {
        return 'MyExpr()';
      }
    }
    expect(str(new MyExpr())).toBe('MyExpr()');
  });
});

/**
 * Coverage of printing/sets.ts, sortkey.ts, str.ts and the pretty printer
 * (pretty.ts, stringpict.ts, symbology.ts). Expected strings from SymPy 1.14
 * (str, pretty with and without unicode, latex, default_sort_key).
 */

describe('str precedence', () => {
  it('follows PRECEDENCE_VALUES for relations', () => {
    // SymPy precedence(Eq(x, y)) = precedence(Ne(x, y)) = 50, precedence(x < y) = 35
    expect(precedence(sj.Eq(x, y))).toBe(50);
    expect(precedence(sj.Ne(x, y))).toBe(50);
    expect(precedence(sj.Lt(x, y))).toBe(35);
  });
  it('reads the precedence an extension node declares', () => {
    // a declared precedence that is not a number is ignored (atom)
    expect(precedence(new Ext('Foo', [x], 'high'))).toBe(1000);
    expect(precedence(new Ext('Foo', [x], 10))).toBe(10);
    // a term binding looser than Add is parenthesized
    expect(str(new Add([x, new Ext('Foo', [y], 10)]))).toBe('x + (Foo(y))');
  });
});

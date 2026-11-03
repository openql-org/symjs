// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * @file Coverage of the 2D pretty printer: every expected string was
 * produced by `sympy.pretty(expr, use_unicode=False|True)` with SymPy 1.14.
 */

import { describe, expect, it } from 'vitest';
import * as sj from '../src';
import { Add, Fn, Integral, Mul, Pow, Rational, S } from '../src/core/nodes';
import { Interval, SetExpr, SetOp, UniversalSet } from '../src/sets/sets';
import { pretty } from '../src/printing/pretty';
import type { Printable } from '../src/printing/pretty';

const [x, y] = sj.symbols('x y');
const R = (p: number, q = 1): Rational => Rational.of(BigInt(p), BigInt(q));

/** [SymPy source, symjs builder, ASCII output, unicode output]. */
const CASES: [string, () => Printable, string, string][] = [
  ["Union(Interval(sqrt(2), 3), FiniteSet(x), evaluate=False)", () => new SetOp('Union', [sj.Interval.of(sj.sqrt(2), 3), sj.FiniteSet.of(x)]), "   ___          \n[\\/ 2 , 3] U {x}", "[√2, 3] ∪ {x}"],
  ["Union(S.Integers, Interval(0, 1), evaluate=False)", () => new SetOp('Union', [sj.Integers, sj.Interval.of(0, 1)]), "Integers U [0, 1]", "ℤ ∪ [0, 1]"],
  ["Union(S.Naturals, FiniteSet(-1), evaluate=False)", () => new SetOp('Union', [sj.Naturals, sj.FiniteSet.of(-1)]), "{-1} U Naturals", "{-1} ∪ ℕ"],
  ["Union(S.Naturals0, FiniteSet(-1), evaluate=False)", () => new SetOp('Union', [sj.Naturals0, sj.FiniteSet.of(-1)]), "{-1} U Naturals0", "{-1} ∪ ℕ₀"],
  ["Union(S.Naturals0, S.Naturals, evaluate=False)", () => new SetOp('Union', [sj.Naturals, sj.Naturals0]), "Naturals0 U Naturals", "ℕ₀ ∪ ℕ"],
  ["Union(FiniteSet(1, x), Interval(0, 1), evaluate=False)", () => new SetOp('Union', [sj.FiniteSet.of(1, x), sj.Interval.of(0, 1)]), "[0, 1] U {1, x}", "[0, 1] ∪ {1, x}"],
  ["Union(FiniteSet(1, 2), Interval(-1, 0), evaluate=False)", () => new SetOp('Union', [sj.FiniteSet.of(1, 2), sj.Interval.of(-1, 0)]), "[-1, 0] U {1, 2}", "[-1, 0] ∪ {1, 2}"],
  ["Intersection(Union(Interval(0, 1), Interval(2, 3), evaluate=False), Interval(-5, -4), evaluate=False)", () => new SetOp('Intersection', [new SetOp('Union', [sj.Interval.of(0, 1), sj.Interval.of(2, 3)]), sj.Interval.of(-5, -4)]), "[-5, -4] n ([0, 1] U [2, 3])", "[-5, -4] ∩ ([0, 1] ∪ [2, 3])"],
  ["Union(S.Reals, FiniteSet(-1), evaluate=False)", () => new SetOp('Union', [sj.Reals, sj.FiniteSet.of(-1)]), "(-oo, oo) U {-1}", "ℝ ∪ {-1}"],
  ["Union(S.Complexes, FiniteSet(-1), evaluate=False)", () => new SetOp('Union', [sj.Complexes, sj.FiniteSet.of(-1)]), "{-1} U Complexes", "{-1} ∪ ℂ"],
  ["S.TribonacciConstant", () => S.TribonacciConstant, "TribonacciConstant", "TribonacciConstant"],
  ["factorial(x + 1)", () => new Fn('factorial', [sj.add(x, 1)]), "(x + 1)!", "(x + 1)!"],
  ["factorial2(x + 1)", () => new Fn('factorial2', [sj.add(x, 1)]), "(x + 1)!!", "(x + 1)!!"],
  ["subfactorial(x + 1)", () => new Fn('subfactorial', [sj.add(x, 1)]), "!(x + 1)", "!(x + 1)"],
  ["factorial(Rational(1, 2), evaluate=False)", () => new Fn('factorial', [R(1, 2)]), "(1/2)!", "(1/2)!"],
  ["exp_polar(x)", () => new Fn('exp_polar', [x]), " x\ne ", " x\nℯ "],
  ["gamma(x)", () => new Fn('gamma', [x]), "Gamma(x)", "Γ(x)"],
  ["uppergamma(x, y)", () => new Fn('uppergamma', [x, y]), "Gamma(x, y)", "Γ(x, y)"],
  ["lowergamma(x, y)", () => new Fn('lowergamma', [x, y]), "lowergamma(x, y)", "γ(x, y)"],
  ["beta(x, y)", () => new Fn('beta', [x, y]), "B(x, y)", "Β(x, y)"],
  ["fresnels(x)", () => new Fn('fresnels', [x]), "S(x)", "S(x)"],
  ["fresnelc(x)", () => new Fn('fresnelc', [x]), "C(x)", "C(x)"],
  ["airyai(x)", () => new Fn('airyai', [x]), "Ai(x)", "Ai(x)"],
  ["airybiprime(x)", () => new Fn('airybiprime', [x]), "Bi'(x)", "Bi'(x)"],
  ["LambertW(x)", () => new Fn('LambertW', [x]), "W(x)", "W(x)"],
  ["DiracDelta(x)", () => sj.DiracDelta(x), "DiracDelta(x)", "δ(x)"],
  ["DiracDelta(x, 1)", () => sj.DiracDelta(x, 1), "DiracDelta(x, 1)", " (1)    \nδ    (x)"],
  ["Add(x, -oo, evaluate=False)", () => new Add([x, S.NegativeInfinity]), "x - oo", "x - ∞"],
  ["Add(-oo, x, evaluate=False)", () => new Add([S.NegativeInfinity, x]), "x - oo", "x - ∞"],
  ["Add(y, Mul(x, -1, evaluate=False), evaluate=False)", () => new Add([y, new Mul([x, R(-1)])]), "x*-1 + y", "x⋅-1 + y"],
  ["Pow(S.Half, x, evaluate=False)", () => new Pow(R(1, 2), x), " -x\n2  ", " -x\n2  "],
  ["Integral(x, (x, 1))", () => new Integral([x, x, R(1)]), "  1     \n  /     \n |      \n |  x dx\n |      \n/       \n        ", "1     \n⌠     \n⎮ x dx\n⌡     \n      "],
  // a degenerate Interval node prints as the point set, which is what SymPy's Interval(x, x) evaluates to
  ["FiniteSet(x)", () => new Interval(x, x, false, false), "{x}", "{x}"],
  ["ConditionSet(x, x > 0, S.UniversalSet)", () => new sj.ConditionSet(x, sj.Gt(x, 0), UniversalSet), "{x | x > 0}", "{x │ (x > 0)}"],
  ["AccumBounds(1, 2)", () => sj.AccumBounds(1, 2), "<1, 2>", "<1, 2>"],
  ["x**(1/y)", () => sj.pow(x, sj.pow(y, -1)), "y ___\n\\/ x ", "y ___\n╲╱ x "],
  ["(x**2)**(1/y)", () => new Pow(sj.pow(x, 2), sj.pow(y, -1)), "   ____\ny /  2 \n\\/  x  ", "   ____\ny ╱  2 \n╲╱  x  "],
  ["Mod(x, y)", () => sj.Mod(x, y), "x mod y", "x mod y"],
  ["Mod(x + 1, y)", () => sj.Mod(sj.add(x, 1), y), "(x + 1) mod y", "(x + 1) mod y"],
  ["floor(x)", () => new Fn('floor', [x]), "floor(x)", "⌊x⌋"],
  ["atan2(y, x)", () => new Fn('atan2', [y, x]), "atan2(y, x)", "atan2(y, x)"],
  ["KroneckerDelta(x, y)", () => new Fn('KroneckerDelta', [x, y]), "d   \n x,y", "δ   \n x,y"],
  ["primenu(x)", () => new Fn('primenu', [x]), "nu(x)", "ν(x)"],
  ["primeomega(x)", () => new Fn('primeomega', [x]), "Omega(x)", "Ω(x)"],
  ["expint(2, x)", () => new Fn('expint', [R(2), x]), "expint(2, x)", "E₂(x)"],
  ["expint(y, x)", () => new Fn('expint', [y, x]), "expint(y, x)", "expint(y, x)"],
  ["Chi(x)", () => new Fn('Chi', [x]), "Chi(x)", "Chi(x)"],
  ["binomial(x, y)", () => new Fn('binomial', [x, y]), "/x\\\n| |\n\\y/", "⎛x⎞\n⎜ ⎟\n⎝y⎠"],
  ["Union(Interval(0, 1), FiniteSet(0, 5), evaluate=False)", () => new SetOp('Union', [sj.Interval.of(0, 1), sj.FiniteSet.of(0, 5)]), "{0, 5} U [0, 1]", "{0, 5} ∪ [0, 1]"],
  ["Union(FiniteSet(f(1)), Interval(0, 1), evaluate=False)", () => new SetOp('Union', [sj.FiniteSet.of(sj.SymFunction('f')(1)), sj.Interval.of(0, 1)]), "[0, 1] U {f(1)}", "[0, 1] ∪ {f(1)}"],
  ["Union(FiniteSet(5), Interval(0, 1), evaluate=False)", () => new SetOp('Union', [sj.FiniteSet.of(5), sj.Interval.of(0, 1)]), "[0, 1] U {5}", "[0, 1] ∪ {5}"],
  ["Union(FiniteSet(pi), FiniteSet(3), evaluate=False)", () => new SetOp('Union', [sj.FiniteSet.of(S.Pi), sj.FiniteSet.of(3)]), "{3} U {pi}", "{3} ∪ {π}"],
  ["Derivative(f(x, n), x) with n integer", () => sj.Derivative(sj.SymFunction('f')(x, sj.symbol('n', { integer: true })), x), "d          \n--(f(x, n))\ndx         ", "d          \n──(f(x, n))\ndx         "],
  ["Derivative(f(x, y), x)", () => sj.Derivative(sj.SymFunction('f')(x, y), x), "d          \n--(f(x, y))\ndx         ", "∂          \n──(f(x, y))\n∂x         "],
];

describe('pretty: SymPy 1.14 output', () => {
  for (const [src, build, ascii, unicode] of CASES) {
    it(src, () => {
      const e = build();
      expect(pretty(e, { useUnicode: false })).toBe(ascii);
      expect(pretty(e, { useUnicode: true })).toBe(unicode);
    });
  }
});

describe('pretty: values it cannot print', () => {
  it('a value that is not printable throws a TypeError', () => {
    expect(() => pretty({} as unknown as Printable)).toThrow(TypeError);
  });
  it('an expression or set class the printer does not know prints as its str form', () => {
    // an Expr subclass outside the library's node classes
    class MyExpr extends sj.Expr {
      readonly kind = 'Extension' as const;
      readonly args: readonly sj.Expr[] = [];
      protected computeKey(): string {
        return 'MyExpr()';
      }
    }
    class MySet extends SetExpr {
      readonly args: readonly sj.Expr[] = [];
      get className(): string {
        return 'MySet';
      }
      protected computeKey(): string {
        return 'MySet()';
      }
    }
    expect(pretty(new MyExpr(), { useUnicode: false })).toBe('MyExpr()');
    expect(pretty(new MySet(), { useUnicode: false })).toBe('MySet()');
  });
});

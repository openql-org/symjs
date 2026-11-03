// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/logic/boolalg.ts.
// Boolean functions, simplification and the logic module helpers. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import type { Expr } from '../../src';
import * as L from '../../src/logic';
import * as boolalg from '../../src/logic/boolalg';
import { BoolOp } from '../../src/core/boolalg';
import { Rel, type RelOp } from '../../src/core/nodes';

const s = (e: unknown): string => sj.str(e as Expr);
const syms = (names: string): Expr[] => sj.symbols(names) as Expr[];
const [x, y, z, w] = syms('x y z w') as [Expr, Expr, Expr, Expr];
const [A, B, C] = syms('A B C D') as [Expr, Expr, Expr, Expr];
const { And, Or, Not, Xor } = sj;
const T = sj.S.true;
const F = sj.S.false;

describe('boolean functions', () => {
  it('as_Boolean', () => {
    expect(L.asBoolean(0)).toBe(F);
    expect(L.asBoolean(1)).toBe(T);
    expect(s(L.asBoolean(x))).toBe('x');
    expect(() => L.asBoolean(2)).toThrow(TypeError);
    expect(() => L.asBoolean(sj.nan)).toThrow(TypeError);
  });

  it('Boolean.equals', () => {
    expect(L.booleanEquals(L.Implies(A, B), L.Implies(Not(B), Not(A)))).toBe(true);
    expect(L.booleanEquals(Not(And(A, B, C)), And(Not(A), Not(B), Not(C)))).toBe(false);
    expect(L.booleanEquals(Not(And(A, Not(A))), Or(B, Not(B)))).toBe(false);
    expect(() => L.booleanEquals(sj.Lt(x, 1), A)).toThrow(sj.NotImplementedError);
  });

  // And(x, y).subs(x, 1) -> y, Or(x, y).subs(x, 0) -> y, Xor(x, y).subs(y, 0) -> x:
  // the core substitution does not rebuild And/Or/Xor nodes yet (core/traverse.ts rebuild)
  it('substitutes into And, Or, Xor and Implies, and prints them in LaTeX', () => {
    const [x, y, z] = sj.symbols('x y z') as [Expr, Expr, Expr];
    expect(String(sj.subs(sj.and(x, y), [[x, sj.S.true]]))).toBe('y');
    expect(String(sj.subs(sj.or(x, y), [[x, sj.S.false]]))).toBe('y');
    expect(String(sj.subs(sj.Xor(x, y), [[x, sj.S.true]]))).toBe('~y');
    expect(String(sj.subs(L.Implies(x, y), [[x, sj.S.true]]))).toBe('y');
    expect(sj.latex(sj.and(L.Implies(x, y), z))).toBe('z \\wedge \\left(x \\Rightarrow y\\right)');
    expect(sj.latex(sj.or(x, sj.not(y)))).toBe('x \\vee \\neg y');
    expect(sj.latex(sj.not(sj.and(x, y)))).toBe('\\neg \\left(x \\wedge y\\right)');
  });

  it('Nand, Nor, Xnor', () => {
    expect(L.Nand(false, true)).toBe(T);
    expect(L.Nand(true, true)).toBe(F);
    expect(s(L.Nand(x, y))).toBe('~(x & y)');
    expect(L.Nor(true, false)).toBe(F);
    expect(L.Nor(true, true)).toBe(F);
    expect(L.Nor(false, true)).toBe(F);
    expect(L.Nor(false, false)).toBe(T);
    expect(s(L.Nor(x, y))).toBe('~(x | y)');
    expect(L.Xnor(true, false)).toBe(F);
    expect(L.Xnor(true, true)).toBe(T);
    expect(L.Xnor(true, false, true, true, false)).toBe(F);
    expect(L.Xnor(true, false, true, false)).toBe(T);
    // unevaluated gates print with function precedence
    const nand = L.Nand(A, B, { evaluate: false });
    expect(s(nand)).toBe('Nand(A, B)');
    expect(s(L.Nor(A, B, { evaluate: false }))).toBe('Nor(A, B)');
    expect(s(L.Xnor(A, B, { evaluate: false }))).toBe('Xnor(A, B)');
    expect(s(Not(nand))).toBe('~Nand(A, B)');
    expect(s(And(nand, sj.Lt(x, 1)))).toBe('Nand(A, B) & (x < 1)');
    expect(sj.latex(nand)).toBe('\\operatorname{Nand}\\left(A, B\\right)');
    expect(s((nand as L.LogicGate).withArgs([T, B]))).toBe('~B');
  });

  it('Implies', () => {
    expect(L.Implies(true, false)).toBe(F);
    expect(L.Implies(false, false)).toBe(T);
    expect(L.Implies(true, true)).toBe(T);
    expect(L.Implies(false, true)).toBe(T);
    expect(s(L.Implies(x, y))).toBe('Implies(x, y)');
    expect(L.Implies(T, F)).toBe(F);
    expect(s(Not(L.Implies(x, y)))).toBe('~(Implies(x, y))');
    expect(s(And(L.Implies(x, y), z))).toBe('z & (Implies(x, y))');
    expect(s(Or(L.Equivalent(x, y), z))).toBe('z | (Equivalent(x, y))');
    expect(s(Xor(L.Implies(x, y), z))).toBe('z ^ (Implies(x, y))');
    expect(s(L.ITE(x, L.Implies(x, y), z))).toBe('ITE(x, Implies(x, y), z)');
    expect(s(L.Implies(And(x, y), Or(x, z)))).toBe('Implies(x & y, x | z)');
    expect(s(L.Implies(Not(x), y))).toBe('Implies(~x, y)');
    expect(s(L.Implies(sj.Lt(x, 1), sj.Ge(x, 1)))).toBe('x >= 1');
    expect(L.Implies(sj.Lt(x, 1), sj.Lt(x, 1))).toBe(T);
    expect(L.Implies(sj.Gt(x, 1), sj.Lt(1, x))).toBe(T);
    expect(s(L.Implies(1, A))).toBe('A');
    expect(s(L.Implies(A, 0))).toBe('~A');
    expect(() => L.Implies(A)).toThrow(RangeError);
  });

  it('Equivalent', () => {
    expect(L.Equivalent(false, false, false)).toBe(T);
    expect(L.Equivalent(true, false, false)).toBe(F);
    expect(L.Equivalent(x, And(x, true))).toBe(T);
    expect(s(L.Equivalent(x, And(y, z)))).toBe('Equivalent(x, y & z)');
    expect(L.Equivalent(sj.Lt(x, 1), sj.Ge(x, 1), A)).toBe(F);
    // SymPy 1.14: Equivalent(A, x < 1) (x < 1 and 1 > x are one relation)
    expect(s(L.Equivalent(sj.Lt(x, 1), sj.Gt(1, x), A))).toBe('Equivalent(A, x < 1)');
    expect(s(L.Equivalent(A, 1, B))).toBe('A & B');
    expect(s(L.Equivalent(B, A))).toBe('Equivalent(A, B)');
  });

  it('ITE', () => {
    expect(L.ITE(true, false, true)).toBe(F);
    expect(L.ITE(Or(true, false), And(true, true), Xor(true, true))).toBe(T);
    expect(s(L.ITE(x, y, z))).toBe('ITE(x, y, z)');
    expect(s(L.ITE(true, x, y))).toBe('x');
    expect(s(L.ITE(false, x, y))).toBe('y');
    expect(s(L.ITE(x, y, y))).toBe('y');
    expect(s(L.ITE(x, true, false))).toBe('x');
    expect(s(L.ITE(x, false, true))).toBe('~x');
    expect(() => L.ITE(true, sj.Rational.of(2n), 3)).toThrow(TypeError);
    expect(s(L.ITE(sj.Eq(x, 1), A, B))).toBe('ITE(Eq(x, 1), A, B)');
    expect(s(L.ITE(x, y, z, { evaluate: false }))).toBe('ITE(x, y, z)');
    expect(sj.latex(L.ITE(x, y, z))).toBe('\\operatorname{ITE}\\left(x, y, z\\right)');
    expect(s(And(L.ITE(x, y, z), w))).toBe('w & ITE(x, y, z)');
    expect(s(Not(L.ITE(x, y, z)))).toBe('~ITE(x, y, z)');
  });

  it('Exclusive', () => {
    expect(L.Exclusive(false, false, false)).toBe(T);
    expect(L.Exclusive(false, true, false)).toBe(T);
    expect(L.Exclusive(false, true, true)).toBe(F);
    expect(s(L.Exclusive(A, B, C))).toBe('~(A & B) & ~(A & C) & ~(B & C)');
  });

  it('conjuncts and disjuncts', () => {
    expect(L.conjuncts(And(A, B)).map(s)).toEqual(['A', 'B']);
    expect(L.conjuncts(Or(A, B)).map(s)).toEqual(['A | B']);
    expect(L.disjuncts(Or(A, B)).map(s)).toEqual(['A', 'B']);
    expect(L.disjuncts(And(A, B)).map(s)).toEqual(['A & B']);
  });

  it('LaTeX of Implies and Equivalent (printLatex)', () => {
    const p = (e: Expr): string => sj.latex(e);
    expect((L.Implies(x, y) as L.LogicOp).printLatex(p)).toBe('x \\Rightarrow y');
    expect((L.Equivalent(x, y, z) as L.LogicOp).printLatex(p)).toBe('x \\Leftrightarrow y \\Leftrightarrow z');
  });

  it('binary_symbols', () => {
    expect([...L.binarySymbols(And(x, sj.Lt(y, 1), sj.Eq(z, sj.S.true))).values()].map(s)).toEqual(['x', 'z']);
  });
});

// Coverage of logic/boolalg.ts. Each case gives the SymPy 1.14 expression and its str().
// And, Or and Xor of the core do not merge relations; the logic module's andFn, orFn and xorFn
// (used by the normal forms and simplify_logic) do, as SymPy's And, Or and Xor.

const p = sj.symbol('p', { positive: true });
const show = (v: unknown): string =>
  v === undefined
    ? 'None'
    : typeof v === 'boolean'
      ? v
        ? 'True'
        : 'False'
      : v instanceof Map
        ? `{${[...v.values()].map(String).sort().join(', ')}}`
        : Array.isArray(v)
          ? `[${v.map(String).sort().join(', ')}]`
          : v instanceof sj.Expr
            ? v.toString()
            : typeof v === 'string'
              ? v
              : JSON.stringify(v);

const CASES: readonly (readonly [sympy: string, run: () => unknown, expected: string])[] = [
  ["Implies(x > 1, x <= 1)", () => L.Implies(sj.Gt(x, 1), sj.Le(x, 1)), "x <= 1"],
  ["Implies(x > 1, 1 < x)", () => L.Implies(sj.Gt(x, 1), sj.Lt(1, x)), "True"],
  ["Implies(-x > 1, x < -1)", () => L.Implies(sj.Gt(sj.mul(-1, x), 1), sj.Lt(x, -1)), "True"],
  ["Implies(x > y, y < x)", () => L.Implies(sj.Gt(x, y), sj.Lt(y, x)), "True"],
  ["Implies(y > x, x < y)", () => L.Implies(sj.Gt(y, x), sj.Lt(x, y)), "True"],
  ["Implies(x - y > 0, y - x < 0)", () => L.Implies(sj.Gt(sj.sub(x, y), 0), sj.Lt(sj.sub(y, x), 0)), "True"],
  ["Implies(1 > x, x < 1)", () => L.Implies(sj.Gt(1, x), sj.Lt(x, 1)), "True"],
  ["Implies(x, x)", () => L.Implies(x, x), "True"],
  ["Implies(True, x)", () => L.Implies(true, x), "x"],
  ["Implies(x, 0)", () => L.Implies(x, 0), "~x"],
  ["Equivalent(x > 1, x <= 1)", () => L.Equivalent(sj.Gt(x, 1), sj.Le(x, 1)), "False"],
  ["Equivalent(x > 1, 1 < x)", () => L.Equivalent(sj.Gt(x, 1), sj.Lt(1, x)), "True"],
  ["Equivalent(x > 1, 1 < x, y)", () => L.Equivalent(sj.Gt(x, 1), sj.Lt(1, x), y), "Equivalent(y, x > 1)"],
  ["Equivalent(x, y, False)", () => L.Equivalent(x, y, sj.S.false), "~x & ~y"],
  ["Equivalent(x, y, True)", () => L.Equivalent(x, y, sj.S.true), "x & y"],
  ["Equivalent(x, 1)", () => L.Equivalent(x, 1), "x"],
  ["Equivalent(x)", () => L.Equivalent(x), "True"],
  ["Equivalent(y, x)", () => L.Equivalent(y, x), "Equivalent(x, y)"],
  ["Xor(x > 1, x <= 1, y)", () => boolalg.xorFn([sj.Gt(x, 1), sj.Le(x, 1), y]), "~y"],
  ["Xor(x > 1, 1 < x, y)", () => boolalg.xorFn([sj.Gt(x, 1), sj.Lt(1, x), y]), "y"],
  ["And(x > 1, 1 < x)", () => boolalg.andFn(sj.Gt(x, 1), sj.Lt(1, x)), "x > 1"],
  ["And(x > 1, x <= 1, y)", () => boolalg.andFn(sj.Gt(x, 1), sj.Le(x, 1), y), "False"],
  ["Or(x > 1, x <= 1, y)", () => boolalg.orFn(sj.Gt(x, 1), sj.Le(x, 1), y), "True"],
  ["Nand(x, y)", () => L.Nand(x, y), "~(x & y)"],
  ["Nor(x, y)", () => L.Nor(x, y), "~(x | y)"],
  ["Xnor(x, y)", () => L.Xnor(x, y), "~(x ^ y)"],
  ["Nand(x, y, evaluate=False)", () => L.Nand(x, y, { evaluate: false }), "Nand(x, y)"],
  ["Nand(x, y, evaluate=False).subs(x, True)", () => L.Nand(x, y, { evaluate: false }).subs(x, sj.S.true), "~y"],
  ["Exclusive(x, y, z)", () => L.Exclusive(x, y, z), "~(x & y) & ~(x & z) & ~(y & z)"],
  ["ITE(True, x, y)", () => L.ITE(true, x, y), "x"],
  ["ITE(False, x, y)", () => L.ITE(false, x, y), "y"],
  ["ITE(z, x, x)", () => L.ITE(z, x, x), "x"],
  ["ITE(z, True, False)", () => L.ITE(z, true, sj.S.false), "z"],
  ["ITE(z, False, True)", () => L.ITE(z, false, sj.S.true), "~z"],
  ["ITE(z, x, y)", () => L.ITE(z, x, y), "ITE(z, x, y)"],
  ["ITE(Eq(z, True), x, y)", () => L.ITE(sj.Eq(z, sj.S.true), x, y), "ITE(z, x, y)"],
  ["ITE(Eq(True, z), x, y)", () => L.ITE(sj.Eq(sj.S.true, z), x, y), "ITE(z, x, y)"],
  ["ITE(Eq(z, False), x, y)", () => L.ITE(sj.Eq(z, sj.S.false), x, y), "ITE(~z, x, y)"],
  ["ITE(Eq(False, z), x, y)", () => L.ITE(sj.Eq(sj.S.false, z), x, y), "ITE(~z, x, y)"],
  ["ITE(Ne(z, True), x, y)", () => L.ITE(sj.Ne(z, sj.S.true), x, y), "ITE(~z, x, y)"],
  ["ITE(Eq(z, w), x, y)", () => L.ITE(sj.Eq(z, w), x, y), "ITE(Eq(z, w), x, y)"],
  ["ITE(Eq(x, True), x, y)", () => L.ITE(sj.Eq(x, sj.S.true), x, y), "ITE(x, x, y)"],
  ["ITE(Eq(z, True), x, y, evaluate=False)", () => L.ITE(sj.Eq(z, sj.S.true), x, y, { evaluate: false }), "ITE(Eq(z, True), x, y)"],
  ["ITE(x > 1, y, z)", () => L.ITE(sj.Gt(x, 1), y, z), "ITE(x > 1, y, z)"],
  ["as_Boolean(1)", () => L.asBoolean(1), "True"],
  ["as_Boolean(0)", () => L.asBoolean(0), "False"],
  ["as_Boolean(p)", () => L.asBoolean(p), "True"],
  ["as_Boolean(z)", () => L.asBoolean(z), "z"],
  ["is_literal(~z)", () => L.isLiteral(sj.Not(z)), "True"],
  ["is_literal(x + y)", () => L.isLiteral(sj.add(x, y)), "True"],
  ["is_literal(z & y)", () => L.isLiteral(sj.And(z, y)), "False"],
  ["is_literal(True)", () => L.isLiteral(sj.S.true), "True"],
  ["is_literal(sin(x + 1))", () => L.isLiteral(sj.sin(sj.add(x, 1))), "False"],
  ["conjuncts(z & y)", () => L.conjuncts(sj.And(z, y)), "[y, z]"],
  ["conjuncts(z | y)", () => L.conjuncts(sj.Or(z, y)), "[y | z]"],
  ["disjuncts(z | y)", () => L.disjuncts(sj.Or(z, y)), "[y, z]"],
  ["disjuncts(z & y)", () => L.disjuncts(sj.And(z, y)), "[y & z]"],
  ["ITE(z, x, y).binary_symbols", () => L.binarySymbols(L.ITE(z, x, y)), "{x, y, z}"],
  ["(Eq(z, True) & Eq(x, 1) & Ne(y, False) & (w > 1)).binary_symbols", () => L.binarySymbols(sj.And(sj.Eq(z, sj.S.true), sj.Eq(x, 1), sj.Ne(y, sj.S.false), sj.Gt(w, 1))), "{y, z}"],
  ["Eq(True, z).binary_symbols", () => L.binarySymbols(sj.Eq(sj.S.true, z)), "{z}"],
  ["simplify_logic(Implies(x > 1, (x > 1) | y))", () => L.simplifyLogic(L.Implies(sj.Gt(x, 1), boolalg.orFn(sj.Gt(x, 1), y))), "True"],
  ["pl_true(Implies(z, y), {z: True, y: False})", () => L.plTrue(L.Implies(z, y), new Map([[z, true], [y, false]])), "False"],
  ["pl_true(Equivalent(z, y, w), {z: True, y: True, w: True})", () => L.plTrue(L.Equivalent(z, y, w), new Map([[z, true], [y, true], [w, true]])), "True"],
  ["pl_true(Xor(z, y), {z: True, y: True})", () => L.plTrue(sj.Xor(z, y), new Map([[z, true], [y, true]])), "False"],
  ["pl_true(ITE(z, y, w), {z: False, y: True, w: False})", () => L.plTrue(L.ITE(z, y, w), new Map([[z, false], [y, true], [w, false]])), "False"],
  ["pl_true(Nand(z, y, evaluate=False), {z: True, y: True})", () => L.plTrue(L.Nand(z, y, { evaluate: false }), new Map([[z, true], [y, true]])), "False"],
  ["pl_true(Nor(z, y, evaluate=False), {z: False, y: False})", () => L.plTrue(L.Nor(z, y, { evaluate: false }), new Map([[z, false], [y, false]])), "True"],
  ["pl_true(Xnor(z, y, evaluate=False), {z: True, y: False})", () => L.plTrue(L.Xnor(z, y, { evaluate: false }), new Map([[z, true], [y, false]])), "False"],
  ["pl_true(ITE(z, y, w, evaluate=False), {z: True, y: True, w: False})", () => L.plTrue(L.ITE(z, y, w, { evaluate: false }), new Map([[z, true], [y, true], [w, false]])), "True"],
  ["satisfiable(ITE(z, y, w, evaluate=False) & ~y & ~w)", () => L.satisfiable(sj.And(L.ITE(z, y, w, { evaluate: false }), sj.Not(y), sj.Not(w))), "False"],
  ["latex(Implies(z, y & w))", () => sj.latex(L.Implies(z, sj.And(y, w))), "z \\Rightarrow \\left(w \\wedge y\\right)"],
  ["latex(Equivalent(z, ~y, w))", () => sj.latex(L.Equivalent(z, sj.Not(y), w)), "w \\Leftrightarrow z \\Leftrightarrow \\neg y"],
  ["Implies(z, y).subs(z, True)", () => L.Implies(z, y).subs(z, sj.S.true), "y"],
  ["Equivalent(z, y).subs(z, False)", () => L.Equivalent(z, y).subs(z, sj.S.false), "~y"],
];

describe('logic boolean functions (SymPy sympy.logic.boolalg)', () => {
  it.each(CASES)('%s', (_sympy, run, expected) => {
    expect(show(run())).toBe(expected);
  });
});

describe('relations and evaluation helpers', () => {
  const R = (op: RelOp, a: sj.ExprLike, b: sj.ExprLike): string => String(boolalg.relCanonical(new Rel(op, sj.sympify(a), sj.sympify(b))));
  it('puts relations in canonical form (SymPy Relational.canonical)', () => {
    expect(R('Lt', 2, sj.sqrt(5))).toBe('2 < sqrt(5)');
    expect(R('Lt', 3, sj.sqrt(5))).toBe('3 < sqrt(5)');
    expect(R('Lt', 4, sj.pi)).toBe('4 < pi');
    expect(R('Gt', sj.Rational.of(3n, 4n), sj.Rational.of(1n, 2n))).toBe('1/2 < 3/4');
    // SymPy prints the float as 0.750000000000000
    expect(R('Gt', sj.sympify(0.75), sj.Rational.of(1n, 2n))).toBe('1/2 < 0.75');
    expect(R('Lt', y, sj.mul(-1, x))).toBe('x < -y');
    expect(R('Lt', sj.mul(-1, x), y)).toBe('x > -y');
    expect(R('Eq', sj.mul(-1, x), y)).toBe('Eq(x, -y)');
    expect(R('Lt', 1, x)).toBe('x > 1');
    expect(R('Lt', sj.add(x, -1), sj.mul(-1, y))).toBe('y < 1 - x');
    expect(R('Eq', x, sj.S.true)).toBe('Eq(x, True)');
    expect(R('Lt', sj.mul(-1, y), sj.mul(-1, x))).toBe('x < y');
  });

  it('evaluates boolean functions under an assignment', () => {
    const env = new Map([
      [z.key, true],
      [y.key, false],
      [w.key, true],
    ]);
    const ev = (e: sj.Expr): boolean => boolalg.evalBool(e, env);
    expect(ev(sj.S.true)).toBe(true);
    expect(ev(sj.sympify(0))).toBe(false);
    expect(ev(L.Implies(z, y))).toBe(false);
    expect(ev(L.Equivalent(z, w))).toBe(true);
    expect(ev(sj.And(z, w))).toBe(true);
    expect(ev(sj.Or(y, sj.Not(z)))).toBe(false);
    expect(ev(sj.Xor(z, y))).toBe(true);
    expect(ev(new BoolOp('ITE', [y, z, y]))).toBe(false);
    expect(ev(new BoolOp('ITE', [z, w, y]))).toBe(true);
    expect(ev(L.ITE(y, z, y, { evaluate: false }))).toBe(false);
    expect(ev(L.ITE(z, w, y, { evaluate: false }))).toBe(true);
    expect(ev(L.Nand(z, w, { evaluate: false }))).toBe(false);
    expect(ev(L.Nor(y, y, { evaluate: false }))).toBe(true);
    expect(ev(L.Xnor(z, y, { evaluate: false }))).toBe(false);
    expect(() => ev(sj.Gt(x, 1))).toThrow(sj.NotImplementedError);
  });

  it('rebuilds boolean functions with evaluation', () => {
    expect(String(boolalg.rebuildBool(sj.Xor(z, y), [z, sj.S.true]))).toBe('~z');
    expect(String(boolalg.rebuildBool(new BoolOp('ITE', [z, w, y]), [sj.S.true, w, y]))).toBe('w');
    expect(String(boolalg.rebuildBool(sj.Not(z), [sj.S.false]))).toBe('True');
    expect(String(boolalg.rebuildBool(L.Equivalent(z, y), [z, sj.S.true]))).toBe('z');
    expect(boolalg.isLogicOp(L.Implies(z, y), 'Implies')).toBe(true);
    expect(boolalg.isLogicOp(sj.And(z, y), 'Implies')).toBe(false);
    expect(() => L.Nand({ evaluate: false }, z)).toThrow(TypeError);
  });
});

// Coverage of logic/*.ts. Expected values are the str() of SymPy 1.14.

const strOf = (e: unknown): string => String(e);
const eqT = (a: sj.Expr, b: sj.Expr): Rel => new Rel('Eq', a, b);
const neT = (a: sj.Expr, b: sj.Expr): Rel => new Rel('Ne', a, b);

describe('boolalg', () => {
  it('ITE with Eq/Ne of a binary symbol', () => {
    const T = sj.S.true;
    const F = sj.S.false;
    expect(strOf(L.ITE(eqT(x, T), x, z))).toBe('ITE(x, x, z)');
    expect(strOf(L.ITE(eqT(T, x), x, z))).toBe('ITE(x, x, z)');
    expect(strOf(L.ITE(eqT(x, F), x, z))).toBe('ITE(~x, x, z)');
    expect(strOf(L.ITE(eqT(F, x), x, z))).toBe('ITE(~x, x, z)');
    expect(strOf(L.ITE(neT(x, T), x, z))).toBe('ITE(~x, x, z)');
    expect(strOf(L.ITE(sj.Eq(x, y), x, z))).toBe('z');
    expect(strOf(L.ITE(sj.Ne(x, y), x, z))).toBe('x');
    expect(strOf(L.ITE(sj.Eq(x, y), x, y))).toBe('ITE(Eq(x, y), x, y)');
  });

  it('as_Boolean, Not of floats, canonical relations', () => {
    // SymPy as_Boolean(Symbol('p', positive=True)) is True; symjs has no zero=True symbols (SymPy gives False for them)
    expect(strOf(L.asBoolean(sj.symbol('p', { positive: true })))).toBe('True');
    expect(strOf(boolalg.notFn(new sj.Float(2.5)))).toBe('False');
    expect(strOf(boolalg.notFn(new sj.Float(0)))).toBe('True');
    expect(strOf(boolalg.relCanonical(sj.Lt(x, sj.mul(-1, y)) as Rel))).toBe('x < -y');
    expect(strOf(boolalg.relCanonical(sj.Lt(y, sj.mul(-1, x)) as Rel))).toBe('x < -y');
  });

  it('relations in And, Or, Xor, Equivalent, Implies', () => {
    // Or keeps the first of equal relations in the given order, And the first in sorted order
    expect(strOf(boolalg.orFn(sj.Lt(x, 1), sj.Gt(1, x), y))).toBe('y | (x < 1)');
    expect(strOf(boolalg.orFn(sj.Gt(1, x), sj.Lt(x, 1), y))).toBe('y | (1 > x)');
    expect(strOf(boolalg.andFn(sj.Lt(x, 1), sj.Gt(1, x), y))).toBe('y & (1 > x)');
    expect(strOf(boolalg.andFn(sj.Gt(1, x), sj.Lt(x, 1), y))).toBe('y & (1 > x)');
    // Or compares only its own arguments, not those of a nested Or
    expect(strOf(boolalg.orFn(sj.Lt(x, 1), boolalg.orFn(sj.Gt(1, x), y)))).toBe('y | (1 > x) | (x < 1)');
    expect(strOf(boolalg.orFn(sj.Lt(x, 1), boolalg.orFn(sj.Ge(x, 1), y)))).toBe('y | (x >= 1) | (x < 1)');
    expect(strOf(boolalg.orFn(sj.Lt(x, 1), sj.Ge(x, 1)))).toBe('True');
    expect(strOf(boolalg.xorFn([sj.Lt(x, 1), sj.Lt(y, 2)]))).toBe('(x < 1) ^ (y < 2)');
    expect(strOf(L.Equivalent(sj.Lt(x, 1), sj.Lt(y, 2)))).toBe('Equivalent(x < 1, y < 2)');
    expect(strOf(L.Implies(sj.Lt(x, 1), sj.Lt(y, 2)))).toBe('Implies(x < 1, y < 2)');
  });

  it('binary_symbols', () => {
    expect([...boolalg.binarySymbols(eqT(sj.S.true, x)).values()].map(strOf)).toEqual(['x']);
    expect(boolalg.binarySymbols(eqT(boolalg.andFn(x, y), sj.S.true)).size).toBe(0);
    expect(boolalg.binarySymbols(sj.S.true).size).toBe(0);
  });
});

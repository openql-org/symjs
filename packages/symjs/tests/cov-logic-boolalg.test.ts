// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Coverage of logic/boolalg.ts. Each case gives the SymPy 1.14 expression and its str().
// And, Or and Xor of the core do not merge relations; the logic module's andFn, orFn and xorFn
// (used by the normal forms and simplify_logic) do, as SymPy's And, Or and Xor.
import { describe, expect, it } from 'vitest';
import * as sj from '../src';
import * as L from '../src/logic';
import * as B from '../src/logic/boolalg';
import { BoolOp } from '../src/core/boolalg';
import { Rel } from '../src/core/nodes';
import type { RelOp } from '../src/core/nodes';

const [x, y, w, z] = sj.symbols('x y w z');
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
  ["Xor(x > 1, x <= 1, y)", () => B.xorFn([sj.Gt(x, 1), sj.Le(x, 1), y]), "~y"],
  ["Xor(x > 1, 1 < x, y)", () => B.xorFn([sj.Gt(x, 1), sj.Lt(1, x), y]), "y"],
  ["And(x > 1, 1 < x)", () => B.andFn(sj.Gt(x, 1), sj.Lt(1, x)), "x > 1"],
  ["And(x > 1, x <= 1, y)", () => B.andFn(sj.Gt(x, 1), sj.Le(x, 1), y), "False"],
  ["Or(x > 1, x <= 1, y)", () => B.orFn(sj.Gt(x, 1), sj.Le(x, 1), y), "True"],
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
  ["simplify_logic(Implies(x > 1, (x > 1) | y))", () => L.simplifyLogic(L.Implies(sj.Gt(x, 1), B.orFn(sj.Gt(x, 1), y))), "True"],
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
  const R = (op: RelOp, a: sj.ExprLike, b: sj.ExprLike): string => String(B.relCanonical(new Rel(op, sj.sympify(a), sj.sympify(b))));
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
    const ev = (e: sj.Expr): boolean => B.evalBool(e, env);
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
    expect(String(B.rebuildBool(sj.Xor(z, y), [z, sj.S.true]))).toBe('~z');
    expect(String(B.rebuildBool(new BoolOp('ITE', [z, w, y]), [sj.S.true, w, y]))).toBe('w');
    expect(String(B.rebuildBool(sj.Not(z), [sj.S.false]))).toBe('True');
    expect(String(B.rebuildBool(L.Equivalent(z, y), [z, sj.S.true]))).toBe('z');
    expect(B.isLogicOp(L.Implies(z, y), 'Implies')).toBe(true);
    expect(B.isLogicOp(sj.And(z, y), 'Implies')).toBe(false);
    expect(() => L.Nand({ evaluate: false }, z)).toThrow(TypeError);
  });
});

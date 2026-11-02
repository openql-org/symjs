// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * sympy.logic (boolalg and inference): every doctest example of SymPy 1.14
 * with the expected values printed by SymPy, plus cross-checks against SymPy
 * on generated expressions.
 */

import { describe, expect, it } from 'vitest';
import * as sj from '../src';
import type { Expr } from '../src';
import * as L from '../src/logic';

const s = (e: unknown): string => sj.str(e as Expr);
const syms = (names: string): Expr[] => sj.symbols(names) as Expr[];
const [x, y, z, w] = syms('x y z w') as [Expr, Expr, Expr, Expr];
const [A, B, C, D] = syms('A B C D') as [Expr, Expr, Expr, Expr];
const [a, b, c, d] = syms('a b c d') as [Expr, Expr, Expr, Expr];
const { And, Or, Not, Xor } = sj;
const T = sj.S.true;
const F = sj.S.false;
/** SymPy dict printing: {k: v, ...} with keys in sort order. */
const dict = (m: ReadonlyMap<Expr, unknown> | false): string =>
  m === false
    ? 'False'
    : `{${sj
        .ordered([...m.keys()])
        .map((k) => `${s(k)}: ${(() => {
          const v = m.get(k);
          return typeof v === 'boolean' ? (v ? 'True' : 'False') : s(v);
        })()}`)
        .join(', ')}}`;

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

  it('And, Or, Not, Xor (core) print like SymPy', () => {
    expect(s(And(x, y))).toBe('x & y');
    expect(s(Or(x, y))).toBe('x | y');
    expect(Not(true)).toBe(F);
    expect(Not(false)).toBe(T);
    expect(Not(And(true, false))).toBe(T);
    expect(Not(Or(true, false))).toBe(F);
    expect(s(Not(And(And(true, x), Or(x, false))))).toBe('~x');
    expect(s(Not(And(Or(A, B), Or(Not(A), Not(B)))))).toBe('~((A | B) & (~A | ~B))');
    expect(Not(T)).toBe(F);
    expect(Xor(true, false)).toBe(T);
    expect(Xor(true, true)).toBe(F);
    expect(Xor(true, false, true, true, false)).toBe(T);
    expect(Xor(true, false, true, false)).toBe(F);
    expect(s(Xor(x, y))).toBe('x ^ y');
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
    expect(s(L.Equivalent(sj.Lt(x, 1), sj.Gt(1, x), A))).toBe('A');
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

describe('normal forms', () => {
  it('distribute', () => {
    expect(s(L.distributeAndOverOr(Or(A, And(Not(B), Not(C)))))).toBe('(A | ~B) & (A | ~C)');
    expect(s(L.distributeOrOverAnd(And(Or(Not(A), B), C)))).toBe('(B & C) | (C & ~A)');
    expect(s(L.distributeXorOverAnd(And(Xor(Not(A), B), C)))).toBe('(B & C) ^ (C & ~A)');
  });

  it('to_anf and is_anf', () => {
    expect(s(L.toAnf(Not(A)))).toBe('A ^ True');
    expect(s(L.toAnf(And(Or(A, B), Not(C))))).toBe('A ^ B ^ (A & B) ^ (A & C) ^ (B & C) ^ (A & B & C)');
    expect(s(L.toAnf(L.Implies(Not(A), L.Equivalent(B, C)), false))).toBe('True ^ ~A ^ (~A & (Equivalent(B, C)))');
    expect(L.isAnf(T)).toBe(true);
    expect(L.isAnf(A)).toBe(true);
    expect(L.isAnf(And(A, B, C))).toBe(true);
    expect(L.isAnf(Xor(A, Not(B)))).toBe(false);
  });

  it('to_nnf and is_nnf', () => {
    expect(s(L.toNnf(Not(Or(And(Not(A), Not(B)), And(C, D)))))).toBe('(A | B) & (~C | ~D)');
    expect(s(L.toNnf(L.Equivalent(L.Implies(A, B), L.Implies(B, A))))).toBe('(A | ~B | (A & ~B)) & (B | ~A | (B & ~A))');
    expect(L.isNnf(Or(And(A, B), Not(C)))).toBe(true);
    expect(L.isNnf(And(Or(A, Not(A)), Or(B, C)))).toBe(false);
    expect(L.isNnf(And(Or(A, Not(A)), Or(B, C)), false)).toBe(true);
    expect(L.isNnf(Or(Not(And(A, B)), C))).toBe(false);
    expect(L.isNnf(And(L.Implies(A, B), L.Implies(B, A)))).toBe(false);
  });

  it('to_cnf, to_dnf, is_cnf, is_dnf', () => {
    expect(s(L.toCnf(Or(Not(Or(A, B)), D)))).toBe('(D | ~A) & (D | ~B)');
    expect(s(L.toCnf(And(Or(A, B), Or(A, Not(A))), true))).toBe('A | B');
    expect(s(L.toDnf(And(B, Or(A, C))))).toBe('(A & B) | (B & C)');
    expect(s(L.toDnf(Or(And(A, B), And(A, Not(B)), And(B, C), And(Not(B), C)), true))).toBe('A | C');
    expect(s(L.toCnf(And(Or(A, B), Or(A, Not(A))), { simplify: true }))).toBe('A | B');
    expect(s(L.toCnf(x))).toBe('x');
    const many = Or(...syms('v0:9'));
    expect(() => L.toCnf(many, true)).toThrow(RangeError);
    expect(s(L.toCnf(many, true, true))).toBe('v0 | v1 | v2 | v3 | v4 | v5 | v6 | v7 | v8');
    expect(L.isCnf(Or(A, B, C))).toBe(true);
    expect(L.isCnf(And(A, B, C))).toBe(true);
    expect(L.isCnf(Or(And(A, B), C))).toBe(false);
    expect(L.isDnf(Or(A, B, C))).toBe(true);
    expect(L.isDnf(And(A, B, C))).toBe(true);
    expect(L.isDnf(Or(And(A, B), C))).toBe(true);
    expect(L.isDnf(And(A, Or(B, C)))).toBe(false);
  });

  it('eliminate_implications', () => {
    expect(s(L.eliminateImplications(L.Implies(A, B)))).toBe('B | ~A');
    expect(s(L.eliminateImplications(L.Equivalent(A, B)))).toBe('(A | ~B) & (B | ~A)');
    expect(s(L.eliminateImplications(L.Equivalent(A, B, C)))).toBe('(A | ~C) & (B | ~A) & (C | ~B)');
  });

  it('is_literal', () => {
    expect(L.isLiteral(A)).toBe(true);
    expect(L.isLiteral(Not(A))).toBe(true);
    expect(L.isLiteral(sj.add(A, B))).toBe(true);
    expect(L.isLiteral(Or(A, B))).toBe(false);
  });

  it('to_int_repr, term_to_integer, integer_to_term', () => {
    expect(L.toIntRepr([Or(x, y), y], [x, y])).toEqual([new Set([1, 2]), new Set([2])]);
    expect(L.termToInteger([1, 0, 0])).toBe(4);
    expect(L.termToInteger('100')).toBe(4);
    expect(L.integerToTerm(4)).toEqual([1, 0, 0]);
    expect(L.integerToTerm(2, 4)).toEqual([0, 0, 1, 0]);
  });

  it('truth_table', () => {
    expect(L.truthTable(L.Implies(x, y), [x, y]).map(([t, v]) => `[${t.join(', ')}] -> ${s(v)}`)).toEqual([
      '[0, 0] -> True',
      '[0, 1] -> True',
      '[1, 0] -> False',
      '[1, 1] -> True',
    ]);
    expect(L.truthTable(Or(x, y), [x, y]).map(([t, v]) => [t, s(v)])).toEqual([
      [[0, 0], 'False'],
      [[0, 1], 'True'],
      [[1, 0], 'True'],
      [[1, 1], 'True'],
    ]);
    expect(L.truthTable(L.Implies(x, y), [y, x], false).map(s)).toEqual(['True', 'False', 'True', 'True']);
    expect(L.truthTable(sj.add(x, y), [x]).map(([t, v]) => [t, s(v)])).toEqual([[[0], 'y'], [[1], 'y + 1']]);
    expect(L.truthTable(sj.sin(sj.add(x, 1)), [x])).toEqual([]);
  });

  it('gateinputcount', () => {
    expect(L.gateinputcount(And(x, y))).toBe(2);
    expect(L.gateinputcount(Or(And(x, y), z))).toBe(4);
    expect(L.gateinputcount(L.Nand(x, y, z))).toBe(4);
    expect(L.gateinputcount(Not(And(x, y, z)))).toBe(4);
    expect(L.gateinputcount(L.Nand(x, y, z, { evaluate: false }))).toBe(3);
    expect(L.gateinputcount(And(sj.Gt(x, z), sj.Ge(y, 2)))).toBe(2);
    expect(L.gateinputcount(x)).toBe(0);
    expect(() => L.gateinputcount(sj.add(x, 1))).toThrow(TypeError);
  });
});

describe('minimization', () => {
  it('SOPform', () => {
    const vars = [w, x, y, z];
    const minterms = [[0, 0, 0, 1], [0, 0, 1, 1], [0, 1, 1, 1], [1, 0, 1, 1], [1, 1, 1, 1]];
    const dontcares = [[0, 0, 0, 0], [0, 0, 1, 0], [0, 1, 0, 1]];
    expect(s(L.SOPform(vars, minterms, dontcares))).toBe('(y & z) | (~w & ~x)');
    expect(s(L.SOPform(vars, [1, 3, 7, 11, 15], [0, 2, 5]))).toBe('(y & z) | (~w & ~x)');
    const dicts = [new Map([[w, 0], [x, 1]]), new Map([[y, 1], [z, 1], [x, 0]])];
    expect(s(L.SOPform(vars, dicts))).toBe('(x & ~w) | (y & z & ~x)');
    expect(s(L.SOPform(vars, [4, 7, 11, [1, 1, 1, 1]], [new Map([[w, 0], [x, 0], [y, 0]]), 5]))).toBe('(w & y & z) | (~w & ~y) | (x & z & ~w)');
    expect(L.SOPform(vars, [])).toBe(F);
    expect(() => L.SOPform(vars, [1], [1])).toThrow(RangeError);
    expect(() => L.SOPform(vars, [[1, 0]])).toThrow(RangeError);
  });

  it('POSform', () => {
    const vars = [w, x, y, z];
    const minterms = [[0, 0, 0, 1], [0, 0, 1, 1], [0, 1, 1, 1], [1, 0, 1, 1], [1, 1, 1, 1]];
    const dontcares = [[0, 0, 0, 0], [0, 0, 1, 0], [0, 1, 0, 1]];
    expect(s(L.POSform(vars, minterms, dontcares))).toBe('z & (y | ~w)');
    expect(s(L.POSform(vars, [1, 3, 7, 11, 15], [0, 2, 5]))).toBe('z & (y | ~w)');
    const dicts = [new Map([[w, 0], [x, 1]]), new Map([[y, 1], [z, 1], [x, 0]])];
    expect(s(L.POSform(vars, dicts))).toBe('(x | y) & (x | z) & (~w | ~x)');
    expect(s(L.POSform(vars, [4, 7, 11, [1, 1, 1, 1]], [new Map([[w, 0], [x, 0], [y, 0]]), 5]))).toBe('(w | x) & (y | ~w) & (z | ~y)');
    expect(L.POSform(vars, [])).toBe(F);
  });

  it('ANFform, anf_coeffs, bool_minterm, bool_maxterm, bool_monomial', () => {
    expect(s(L.ANFform([x], [1, 0]))).toBe('x ^ True');
    expect(s(L.ANFform([x, y], [0, 1, 1, 1]))).toBe('x ^ y ^ (x & y)');
    expect(() => L.ANFform([x, y], [0, 1])).toThrow(RangeError);
    const coeffs = L.anfCoeffs([0, 1, 1, 0, 0, 1, 0, 1]);
    expect(coeffs).toEqual([0, 1, 1, 0, 0, 0, 1, 0]);
    const poly = Xor(...coeffs.flatMap((k, i) => (k === 1 ? [L.boolMonomial(i, [a, b, c])] : [])));
    expect(s(poly)).toBe('b ^ c ^ (a & b)');
    expect(() => L.anfCoeffs([0, 1, 1])).toThrow(RangeError);
    expect(s(L.boolMinterm([1, 0, 1], [x, y, z]))).toBe('x & z & ~y');
    expect(s(L.boolMinterm(6, [x, y, z]))).toBe('x & y & ~z');
    expect(s(L.boolMaxterm([1, 0, 1], [x, y, z]))).toBe('y | ~x | ~z');
    expect(s(L.boolMaxterm(6, [x, y, z]))).toBe('z | ~x | ~y');
    expect(s(L.boolMonomial([1, 0, 1], [x, y, z]))).toBe('x & z');
    expect(s(L.boolMonomial(6, [x, y, z]))).toBe('x & y');
  });

  it('simplify_logic', () => {
    const e = Or(And(Not(x), Not(y), Not(z)), And(Not(x), Not(y), z));
    expect(s(L.simplifyLogic(e))).toBe('~x & ~y');
    expect(s(L.simplifyLogic(Or(x, y), { dontcare: y }))).toBe('x');
    expect(s(L.simplifyLogic(Or(x, y), null, true, false, y))).toBe('x');
    expect(() => L.simplifyLogic(x, 'xnf' as 'cnf')).toThrow(RangeError);
    expect(s(L.simplifyLogic(sj.add(x, 1)))).toBe('x + 1');
    // relations are variables; a relation and its negation are one variable
    expect(s(L.simplifyLogic(Or(And(sj.Lt(x, 1), A), And(sj.Ge(x, 1), A))))).toBe('A');
    expect(s(L.simplifyLogic(Or(And(sj.Lt(x, 1), A), And(sj.Ge(x, 1), B)), 'dnf'))).toBe('(A & (x < 1)) | (B & (x >= 1))');
    // more than 8 variables: no minimization without force
    const v = syms('v0:9');
    const big = Or(And(v[0]!, v[1]!), And(v[0]!, Not(v[1]!)), ...v.slice(2));
    expect(s(L.simplifyLogic(big))).toBe(s(big));
    expect(s(L.simplifyLogic(big, { force: true }))).toBe('v0 | v2 | v3 | v4 | v5 | v6 | v7 | v8');
  });

  it('bool_map', () => {
    const f1 = L.SOPform([x, z, y], [[1, 0, 1], [0, 0, 1]]);
    const f2 = L.SOPform([a, b, c], [[1, 0, 1], [1, 0, 0]]);
    const r1 = L.boolMap(f1, f2);
    expect(sj.isNoMatch(r1)).toBe(false);
    if (!sj.isNoMatch(r1)) expect(`(${s(r1[0])}, ${dict(r1[1])})`).toBe('(y & ~z, {y: a, z: b})');
    const eq = Or(And(Not(y), w), And(Not(y), z), And(x, y));
    const eq2 = Or(And(Not(c), a), And(Not(c), d), And(b, c));
    const r2 = L.boolMap(eq, eq2);
    if (sj.isNoMatch(r2)) throw new TypeError('no match');
    expect(`(${s(r2[0])}, ${dict(r2[1])})`).toBe('((x & y) | (w & ~y) | (z & ~y), {w: a, x: b, y: c, z: d})');
    // eq.subs(c, x) built directly (the core substitution does not rebuild And/Xor nodes)
    const eq3 = And(Xor(a, b), c, And(c, d));
    const eq4 = And(Xor(a, b), x, And(x, d));
    const r3 = L.boolMap(eq3, eq4);
    if (sj.isNoMatch(r3)) throw new TypeError('no match');
    expect(`(${s(r3[0])}, ${dict(r3[1])})`).toBe('(c & d & (a | b) & (~a | ~b), {a: a, b: b, c: d, d: x})');
    expect(L.boolMap(And(x, y), Or(a, b))).toBe(sj.NoMatch);
    expect(L.boolMap(T, T)).toBe(sj.NoMatch);
    expect(dict((L.boolMap(x, a) as [Expr, sj.ExprMap<Expr>])[1])).toBe('{x: a}');
  });
});

describe('inference', () => {
  it('literal_symbol', () => {
    expect(s(L.literalSymbol(A))).toBe('A');
    expect(s(L.literalSymbol(Not(A)))).toBe('A');
    expect(L.literalSymbol(true)).toBe(T);
    expect(() => L.literalSymbol(And(A, B))).toThrow(RangeError);
  });

  it('satisfiable', () => {
    expect(dict(L.satisfiable(And(A, Not(B))))).toBe('{A: True, B: False}');
    expect(L.satisfiable(And(A, Not(A)))).toBe(false);
    expect(dict(L.satisfiable(true))).toBe('{True: True}');
    expect(L.satisfiable(false)).toBe(false);
    expect(L.satisfiable(And(A, Not(A)), { allModels: true }).next().value).toBe(false);
    const models = L.satisfiable(And(L.Implies(A, B), B), { allModels: true });
    expect(dict(models.next().value as sj.ExprMap<boolean>)).toBe('{A: False, B: True}');
    expect(dict(models.next().value as sj.ExprMap<boolean>)).toBe('{A: True, B: True}');
    expect(models.next().done).toBe(true);
    const use = (ms: Iterable<sj.ExprMap<boolean> | false>): string[] => [...ms].map((m) => (m === false ? 'UNSAT' : dict(m)));
    expect(use(L.satisfiable(L.Implies(A, Not(A)), { allModels: true }))).toEqual(['{A: False}']);
    expect(use(L.satisfiable(Xor(A, A), { allModels: true }))).toEqual(['UNSAT']);
    expect(dict(L.satisfiable(sj.Lt(x, 1)))).toBe('{x < 1: True}');
  });

  it('satisfiable with minimal models', () => {
    const ms = [...L.satisfiable(Or(A, B, C), { allModels: true, minimal: true })].map((m) => dict(m));
    expect(ms.sort()).toEqual(['{A: False, B: False, C: True}', '{A: False, B: True, C: False}', '{A: True, B: False, C: False}']);
    expect(dict(L.satisfiable(Or(A, B), { minimal: true }))).toMatch(/^\{A: (True, B: False|False, B: True)\}$/);
    expect(dict(L.satisfiable(And(L.Implies(A, B), Or(A, C)), { minimal: true }))).toBe('{A: False, B: False, C: True}');
    expect(L.satisfiable(And(A, Not(A)), { minimal: true })).toBe(false);
  });

  it('valid and entails', () => {
    expect(L.valid(Or(A, Not(A)))).toBe(true);
    expect(L.valid(Or(A, B))).toBe(false);
    expect(L.entails(A, [L.Implies(A, B), L.Implies(B, C)])).toBe(false);
    expect(L.entails(C, [L.Implies(A, B), L.Implies(B, C), A])).toBe(true);
    expect(L.entails(L.Implies(A, B))).toBe(false);
    expect(L.entails(L.Implies(A, L.Implies(B, A)))).toBe(true);
  });

  it('pl_true', () => {
    expect(L.plTrue(And(A, B), new Map([[A, true], [B, true]]))).toBe(true);
    expect(L.plTrue(And(A, B), new Map([[A, false]]))).toBe(false);
    expect(L.plTrue(And(A, B), new Map([[A, true]]))).toBe('unknown');
    expect(L.plTrue(And(A, B), new Map([[A, true]]), true)).toBe('unknown');
    expect(L.plTrue(L.Implies(A, L.Implies(B, A)))).toBe('unknown');
    expect(L.plTrue(L.Implies(A, L.Implies(B, A)), new Map(), true)).toBe(true);
    expect(L.plTrue(And(A, Not(A)))).toBe('unknown');
    expect(L.plTrue(And(A, Not(A)), new Map(), true)).toBe(false);
    expect(L.plTrue(And(A, B, Or(Not(A), Not(B))), new Map([[A, true]]))).toBe('unknown');
    expect(L.plTrue(And(A, B, Or(Not(A), Not(B))), new Map([[A, true]]), true)).toBe(false);
    expect(L.plTrue(true)).toBe(true);
    expect(() => L.plTrue(sj.Lt(x, 1))).toThrow(RangeError);
  });

  it('PropKB', () => {
    const l = new L.PropKB();
    expect(l.clauses).toEqual([]);
    l.tell(Or(x, y));
    expect(l.clauses.map(s)).toEqual(['x | y']);
    l.tell(y);
    expect(l.clauses.map(s)).toEqual(['y', 'x | y']);
    const k = new L.PropKB();
    k.tell(And(x, Not(y)));
    expect(k.ask(x)).toBe(true);
    expect(k.ask(y)).toBe(false);
    const r = new L.PropKB(Or(x, y));
    expect(r.clauses.map(s)).toEqual(['x | y']);
    r.retract(Or(x, y));
    expect(r.clauses).toEqual([]);
  });
});

// Generated by SymPy 1.14 on random expressions (seed 12345). The models of
// satisfiable are those of SymPy's dpll2 with the variables numbered in
// ordered() order (SymPy numbers them in hash order, which varies per run).
type Tree = string | [string, ...Tree[]];
interface Case { j: Tree; s: string; sl: string; cnf: string; dnf: string; tc: string; td: string; nnf: string; nnf0: string; anf: string; g: number; ic: boolean; idn: boolean; inn: boolean; m: string[] }
interface QmCase { v: string[]; mins: number[]; dcs: number[]; sop: string; pos: string }
const CASES: Case[] = [{"j":"c","s":"c","sl":"c","cnf":"c","dnf":"c","tc":"c","td":"c","nnf":"c","nnf0":"c","anf":"c","g":0,"ic":true,"idn":true,"inn":true,"m":["{c: True}"]},{"j":["ITE",["ITE","b","b","c"],["Or","d","b","b"],"a"],"s":"ITE(ITE(b, b, c), b | d, a)","sl":"b | (c & d) | (a & ~c)","cnf":"(a | b | c) & (b | d | ~c)","dnf":"b | (c & d) | (a & ~c)","tc":"(a | b | c) & (a | b | ~b) & (b | d | ~b) & (b | d | ~c)","td":"b | (a & b) | (a & d) | (b & c) | (b & d) | (b & ~b) | (b & c & d) | (a & b & ~b) | (b & c & ~b) | (b & d & ~b) | (c & d & ~b) | (a & ~b & ~c) | (b & ~b & ~c) | (c & ~b & ~c) | (b & c & ~b & ~c)","nnf":"(a | b | c) & (b | d | (~b & (b | ~c)))","nnf0":"(a | ((b | c) & (b | ~b))) & (b | d | (~b & (b | ~c)))","anf":"ITE(ITE(b, b, c), b ^ d ^ (b & d), a)","g":8,"ic":false,"idn":false,"inn":false,"m":["{a: True, b: True, c: False, d: True}","{a: False, b: True, c: False, d: True}","{a: True, b: True, c: True, d: True}","{a: False, b: True, c: True, d: True}","{a: True, b: True, c: False, d: False}","{a: False, b: True, c: False, d: False}","{a: True, b: True, c: True, d: False}","{a: False, b: True, c: True, d: False}","{a: True, b: False, c: False, d: True}","{a: True, b: False, c: True, d: True}","{a: False, b: False, c: True, d: True}","{a: True, b: False, c: False, d: False}"]},{"j":["And","c",["ITE","a","c","a"]],"s":"c & ITE(a, c, a)","sl":"a & c","cnf":"a & c","dnf":"a & c","tc":"a & c & (c | ~a)","td":"(a & c) | (a & c & ~a)","nnf":"a & c & (c | ~a)","nnf0":"a & c & (c | ~a)","anf":"c & ITE(a, c, a)","g":5,"ic":false,"idn":false,"inn":false,"m":["{a: True, c: True}"]},{"j":["ITE",["Not","b"],["Xor","e","c","a"],"d"],"s":"ITE(~b, a ^ c ^ e, d)","sl":"(b & d) | (a & c & e & ~b) | (a & ~b & ~c & ~e) | (c & ~a & ~b & ~e) | (e & ~a & ~b & ~c)","cnf":"(d | ~b) & (a | b | c | e) & (a | b | ~c | ~e) & (b | c | ~a | ~e) & (b | e | ~a | ~c)","dnf":"(b & d) | (a & c & e & ~b) | (a & ~b & ~c & ~e) | (c & ~a & ~b & ~e) | (e & ~a & ~b & ~c)","tc":"(d | ~b) & (a | b | c | e) & (a | b | ~c | ~e) & (b | c | ~a | ~e) & (b | e | ~a | ~c)","td":"(b & d) | (b & ~b) | (a & d & ~a) | (c & d & ~c) | (d & e & ~e) | (a & c & d & e) | (a & ~a & ~b) | (c & ~b & ~c) | (e & ~b & ~e) | (a & c & d & ~a) | (a & c & d & ~c) | (a & c & e & ~b) | (a & d & e & ~a) | (a & d & e & ~e) | (c & d & e & ~c) | (c & d & e & ~e) | (a & c & ~a & ~b) | (a & c & ~b & ~c) | (a & d & ~a & ~c) | (a & d & ~a & ~e) | (a & d & ~c & ~e) | (a & e & ~a & ~b) | (a & e & ~b & ~e) | (c & d & ~a & ~c) | (c & d & ~a & ~e) | (c & d & ~c & ~e) | (c & e & ~b & ~c) | (c & e & ~b & ~e) | (d & e & ~a & ~c) | (d & e & ~a & ~e) | (d & e & ~c & ~e) | (a & c & d & e & ~a) | (a & c & d & e & ~c) | (a & c & d & e & ~e) | (a & ~a & ~b & ~c) | (a & ~a & ~b & ~e) | (a & ~b & ~c & ~e) | (c & ~a & ~b & ~c) | (c & ~a & ~b & ~e) | (c & ~b & ~c & ~e) | (e & ~a & ~b & ~c) | (e & ~a & ~b & ~e) | (e & ~b & ~c & ~e) | (a & c & d & ~a & ~c) | (a & c & d & ~a & ~e) | (a & c & d & ~c & ~e) | (a & c & e & ~a & ~b) | (a & c & e & ~b & ~c) | (a & c & e & ~b & ~e) | (a & d & e & ~a & ~c) | (a & d & e & ~a & ~e) | (a & d & e & ~c & ~e) | (c & d & e & ~a & ~c) | (c & d & e & ~a & ~e) | (c & d & e & ~c & ~e) | (a & c & ~a & ~b & ~c) | (a & c & ~a & ~b & ~e) | (a & c & ~b & ~c & ~e) | (a & d & ~a & ~c & ~e) | (a & e & ~a & ~b & ~c) | (a & e & ~a & ~b & ~e) | (a & e & ~b & ~c & ~e) | (c & d & ~a & ~c & ~e) | (c & e & ~a & ~b & ~c) | (c & e & ~a & ~b & ~e) | (c & e & ~b & ~c & ~e) | (d & e & ~a & ~c & ~e) | (a & ~a & ~b & ~c & ~e) | (c & ~a & ~b & ~c & ~e) | (e & ~a & ~b & ~c & ~e)","nnf":"(d | ~b) & (b | ((a | c | e) & (a | ~c | ~e) & (c | ~a | ~e) & (e | ~a | ~c)))","nnf0":"(d | ~b) & (b | ((a | c | e) & (a | ~c | ~e) & (c | ~a | ~e) & (e | ~a | ~c)))","anf":"ITE(b ^ True, a ^ c ^ e, d)","g":7,"ic":false,"idn":false,"inn":false,"m":["{a: False, b: True, c: False, d: True, e: False}","{a: True, b: True, c: False, d: True, e: False}","{a: False, b: True, c: True, d: True, e: False}","{a: True, b: True, c: True, d: True, e: False}","{a: False, b: True, c: False, d: True, e: True}","{a: True, b: True, c: False, d: True, e: True}","{a: False, b: True, c: True, d: True, e: True}","{a: True, b: True, c: True, d: True, e: True}","{a: True, b: False, c: False, d: True, e: False}","{a: True, b: False, c: False, d: False, e: False}","{a: False, b: False, c: True, d: True, e: False}","{a: False, b: False, c: True, d: False, e: False}","{a: False, b: False, c: False, d: True, e: True}","{a: False, b: False, c: False, d: False, e: True}","{a: True, b: False, c: True, d: True, e: True}","{a: True, b: False, c: True, d: False, e: True}"]},{"j":["Or","c",["Not","a"],["And",["Equivalent","b","a","b"],["And","c","b"]]],"s":"c | ~a | (b & c & (Equivalent(a, b)))","sl":"c | ~a","cnf":"c | ~a","dnf":"c | ~a","tc":"(c | ~a) & (b | c | ~a) & (a | c | ~a | ~b)","td":"c | ~a | (a & b & c) | (b & c & ~b) | (a & b & c & ~a) | (b & c & ~a & ~b)","nnf":"c | ~a | (b & c & (a | ~b) & (b | ~a))","nnf0":"c | ~a | (b & c & (a | ~b) & (b | ~a))","anf":"a ^ True ^ (a & c)","g":7,"ic":false,"idn":false,"inn":false,"m":["{a: False, b: False, c: True}","{a: False, b: True, c: True}","{a: False, b: False, c: False}","{a: False, b: True, c: False}","{a: True, b: False, c: True}","{a: True, b: True, c: True}"]},{"j":["And",["Not","b"],["Or","b","c"],["Or","a","b"]],"s":"~b & (a | b) & (b | c)","sl":"a & c & ~b","cnf":"a & c & ~b","dnf":"a & c & ~b","tc":"~b & (a | b) & (b | c)","td":"(b & ~b) | (a & b & ~b) | (a & c & ~b) | (b & c & ~b)","nnf":"~b & (a | b) & (b | c)","nnf0":"~b & (a | b) & (b | c)","anf":"(a & c) ^ (a & b & c)","g":8,"ic":true,"idn":false,"inn":true,"m":["{a: True, b: False, c: True}"]},{"j":"a","s":"a","sl":"a","cnf":"a","dnf":"a","tc":"a","td":"a","nnf":"a","nnf0":"a","anf":"a","g":0,"ic":true,"idn":true,"inn":true,"m":["{a: True}"]},{"j":["Not",["Or","e","d"]],"s":"~(d | e)","sl":"~d & ~e","cnf":"~d & ~e","dnf":"~d & ~e","tc":"~d & ~e","td":"~d & ~e","nnf":"~d & ~e","nnf0":"~d & ~e","anf":"d ^ e ^ True ^ (d & e)","g":3,"ic":false,"idn":false,"inn":false,"m":["{d: False, e: False}"]},{"j":["Xor","b","a"],"s":"a ^ b","sl":"(a & ~b) | (b & ~a)","cnf":"(a | b) & (~a | ~b)","dnf":"(a & ~b) | (b & ~a)","tc":"(a | b) & (~a | ~b)","td":"(a & ~a) | (a & ~b) | (b & ~a) | (b & ~b)","nnf":"(a | b) & (~a | ~b)","nnf0":"(a | b) & (~a | ~b)","anf":"a ^ b","g":2,"ic":false,"idn":false,"inn":false,"m":["{a: True, b: False}","{a: False, b: True}"]},{"j":["Or",["Or",["Or","c","b"],["Not","c"],"a"],["Xor",["Not","c"],["And","b","a"]]],"s":"a | b | c | ~c | (~c ^ (a & b))","sl":"True","cnf":"True","dnf":"True","tc":"(a | b | c | ~c) & (a | b | c | ~a | ~b | ~c)","td":"a | b | c | ~c | (c & ~c) | (a & b & c) | (~a & ~c) | (~b & ~c) | (a & b & ~a) | (a & b & ~b)","nnf":"True","nnf0":"a | b | c | ~c | ((~c | (a & b)) & (c | ~a | ~b))","anf":"True","g":11,"ic":false,"idn":false,"inn":false,"m":["{a: True, b: True, c: False}","{a: True, b: False, c: False}","{a: False, b: True, c: False}","{a: False, b: False, c: False}","{a: True, b: True, c: True}","{a: True, b: False, c: True}","{a: False, b: True, c: True}","{a: False, b: False, c: True}"]},{"j":["Or",["Not",["And","d","c"]],["And",["And","a","c"],["Xor","b","a"],["Or","a","b"]],["And",["Xor","c","d"],"c"]],"s":"~(c & d) | (c & (c ^ d)) | (a & c & (a | b) & (a ^ b))","sl":"~c | ~d | (a & ~b)","cnf":"(a | ~c | ~d) & (~b | ~c | ~d)","dnf":"~c | ~d | (a & ~b)","tc":"(a | ~c | ~d) & (c | ~c | ~d) & (a | b | ~c | ~d) & (a | c | ~c | ~d) & (c | d | ~c | ~d) & (a | b | c | ~c | ~d) & (a | c | d | ~c | ~d) & (~a | ~b | ~c | ~d) & (a | b | c | d | ~c | ~d) & (c | ~a | ~b | ~c | ~d) & (c | d | ~a | ~b | ~c | ~d)","td":"~c | ~d | (c & ~c) | (c & ~d) | (a & c & ~a) | (a & c & ~b) | (c & d & ~c) | (c & d & ~d) | (a & b & c & ~a) | (a & b & c & ~b)","nnf":"~c | ~d | (c & (c | d) & (~c | ~d)) | (a & c & (a | b) & (~a | ~b))","nnf0":"~c | ~d | (c & (c | d) & (~c | ~d)) | (a & c & (a | b) & (~a | ~b))","anf":"True ^ (c & d) ^ (a & c & d) ^ (a & b & c & d)","g":18,"ic":false,"idn":false,"inn":false,"m":["{a: True, b: False, c: False, d: False}","{a: True, b: True, c: False, d: False}","{a: False, b: False, c: False, d: False}","{a: False, b: True, c: False, d: False}","{a: True, b: False, c: True, d: False}","{a: True, b: True, c: True, d: False}","{a: False, b: False, c: True, d: False}","{a: False, b: True, c: True, d: False}","{a: True, b: False, c: False, d: True}","{a: True, b: True, c: False, d: True}","{a: False, b: False, c: False, d: True}","{a: False, b: True, c: False, d: True}","{a: True, b: False, c: True, d: True}"]},{"j":["Not","c"],"s":"~c","sl":"~c","cnf":"~c","dnf":"~c","tc":"~c","td":"~c","nnf":"~c","nnf0":"~c","anf":"c ^ True","g":1,"ic":true,"idn":true,"inn":true,"m":["{c: False}"]},{"j":["And","c","b"],"s":"b & c","sl":"b & c","cnf":"b & c","dnf":"b & c","tc":"b & c","td":"b & c","nnf":"b & c","nnf0":"b & c","anf":"b & c","g":2,"ic":true,"idn":true,"inn":true,"m":["{b: True, c: True}"]},{"j":["Xor",["Not","b"],["Or","b","c"]],"s":"~b ^ (b | c)","sl":"b | ~c","cnf":"b | ~c","dnf":"b | ~c","tc":"(b | ~b) & (b | ~c) & (b | c | ~b)","td":"b | (b & c) | (b & ~b) | (~b & ~c) | (b & ~b & ~c) | (c & ~b & ~c)","nnf":"b | (~b & ~c)","nnf0":"(b | c | ~b) & (b | (~b & ~c))","anf":"c ^ True ^ (b & c)","g":5,"ic":false,"idn":false,"inn":false,"m":["{b: True, c: False}","{b: True, c: True}","{b: False, c: False}"]},{"j":["ITE","e","e",["Not",["And","c","a"]]],"s":"ITE(e, e, ~(a & c))","sl":"e | ~a | ~c","cnf":"e | ~a | ~c","dnf":"e | ~a | ~c","tc":"(e | ~e) & (e | ~a | ~c)","td":"e | (e & ~a) | (e & ~c) | (e & ~e) | (~a & ~e) | (~c & ~e)","nnf":"e | ~a | ~c","nnf0":"(e | ~e) & (e | ~a | ~c)","anf":"ITE(e, e, True ^ (a & c))","g":6,"ic":false,"idn":false,"inn":false,"m":["{a: False, c: False, e: True}","{a: True, c: False, e: True}","{a: False, c: True, e: True}","{a: True, c: True, e: True}","{a: False, c: False, e: False}","{a: True, c: False, e: False}","{a: False, c: True, e: False}"]},{"j":["Or",["Equivalent","d","a"],["ITE","b","d","a"],["And","a","b"]],"s":"(a & b) | (Equivalent(a, d)) | ITE(b, d, a)","sl":"a | b | ~d","cnf":"a | b | ~d","dnf":"a | b | ~d","tc":"(a | b | ~d) & (a | b | d | ~a) & (a | d | ~a | ~b) & (a | d | ~b | ~d) & (b | d | ~a | ~b) & (a | b | d | ~b | ~d)","td":"(a & b) | (a & d) | (b & d) | (a & ~a) | (a & ~b) | (b & ~b) | (d & ~d) | (~a & ~d)","nnf":"(a & b) | ((a | b) & (d | ~b)) | ((a | ~d) & (d | ~a))","nnf0":"(a & b) | ((a | b) & (d | ~b)) | ((a | ~d) & (d | ~a))","anf":"a ^ d ^ True ^ (a & b) ^ (a & b & d) ^ (a & ITE(b, d, a)) ^ (d & ITE(b, d, a)) ^ (a & b & ITE(b, d, a)) ^ (a & b & d & ITE(b, d, a))","g":8,"ic":false,"idn":false,"inn":false,"m":["{a: True, b: False, d: True}","{a: True, b: True, d: True}","{a: True, b: False, d: False}","{a: True, b: True, d: False}","{a: False, b: True, d: True}","{a: False, b: False, d: False}","{a: False, b: True, d: False}"]},{"j":["Xor","b",["ITE","a","b","c"],["ITE","c","a","c"]],"s":"b ^ ITE(a, b, c) ^ ITE(c, a, c)","sl":"(a & c) | (c & ~b) | (b & ~a & ~c)","cnf":"(b | c) & (c | ~a) & (a | ~b | ~c)","dnf":"(a & c) | (c & ~b) | (b & ~a & ~c)","tc":"(a | b | c) & (b | c | ~a) & (a | ~b | ~c) & (c | ~a | ~b) & (a | b | c | ~c) & (a | b | ~a | ~c) & (a | c | ~b | ~c) & (a | ~a | ~b | ~c) & (b | ~a | ~b | ~c) & (a | c | ~a | ~b | ~c) & (b | c | ~a | ~b | ~c)","td":"(a & ~a) | (b & ~b) | (c & ~c) | (a & b & c) | (a & b & ~a) | (a & b & ~b) | (a & c & ~a) | (a & c & ~b) | (a & c & ~c) | (b & c & ~b) | (b & c & ~c) | (a & ~a & ~b) | (a & ~a & ~c) | (b & ~a & ~c) | (b & ~b & ~c) | (c & ~a & ~b) | (c & ~a & ~c) | (c & ~b & ~c) | (a & b & c & ~a) | (a & b & c & ~b) | (a & b & c & ~c) | (a & b & ~a & ~b) | (a & b & ~a & ~c) | (a & b & ~b & ~c) | (a & c & ~a & ~b) | (a & c & ~a & ~c) | (a & c & ~b & ~c) | (b & c & ~a & ~b) | (b & c & ~a & ~c) | (b & c & ~b & ~c) | (a & ~a & ~b & ~c) | (b & ~a & ~b & ~c) | (c & ~a & ~b & ~c) | (a & b & c & ~a & ~b) | (a & b & c & ~a & ~c) | (a & b & c & ~b & ~c) | (a & b & ~a & ~b & ~c) | (a & c & ~a & ~b & ~c) | (b & c & ~a & ~b & ~c) | (a & b & c & ~a & ~b & ~c)","nnf":"(~a | ~b | ~c | ((a | c) & (b | ~a))) & (b | (c & (a | ~c)) | ((a | c) & (b | ~a))) & (b | ~a | ~c | ((a | ~c) & (~a | ~b))) & (~b | (c & (a | ~c)) | ((a | ~c) & (~a | ~b)))","nnf0":"(b | (c & (a | ~c)) | ((a | c) & (b | ~a))) & (~b | (c & (a | ~c)) | ((a | ~c) & (~a | ~b))) & (~b | ((a | c) & (b | ~a)) | ((c | ~c) & (~a | ~c))) & (b | ((a | ~c) & (~a | ~b)) | ((c | ~c) & (~a | ~c)))","anf":"b ^ ITE(a, b, c) ^ ITE(c, a, c)","g":9,"ic":false,"idn":false,"inn":false,"m":["{a: False, b: True, c: False}","{a: False, b: False, c: True}","{a: True, b: False, c: True}","{a: True, b: True, c: True}"]},{"j":["Or",["Xor","d","a"],["Or","a","a"],["Xor","c","b"]],"s":"a | (a ^ d) | (b ^ c)","sl":"a | d | (b & ~c) | (c & ~b)","cnf":"(a | b | c | d) & (a | d | ~b | ~c)","dnf":"a | d | (b & ~c) | (c & ~b)","tc":"(a | b | c | d) & (a | d | ~b | ~c) & (a | b | c | ~a | ~d) & (a | ~a | ~b | ~c | ~d)","td":"a | (a & ~a) | (a & ~d) | (b & ~b) | (b & ~c) | (c & ~b) | (c & ~c) | (d & ~a) | (d & ~d)","nnf":"a | ((a | d) & (~a | ~d)) | ((b | c) & (~b | ~c))","nnf0":"a | ((a | d) & (~a | ~d)) | ((b | c) & (~b | ~c))","anf":"a ^ b ^ c ^ d ^ (a & b) ^ (a & c) ^ (a & d) ^ (b & d) ^ (c & d) ^ (a & b & d) ^ (a & c & d)","g":7,"ic":false,"idn":false,"inn":false,"m":["{a: True, b: False, c: False, d: False}","{a: True, b: True, c: False, d: False}","{a: True, b: False, c: True, d: False}","{a: True, b: True, c: True, d: False}","{a: True, b: False, c: False, d: True}","{a: True, b: True, c: False, d: True}","{a: True, b: False, c: True, d: True}","{a: True, b: True, c: True, d: True}","{a: False, b: True, c: False, d: False}","{a: False, b: False, c: True, d: False}","{a: False, b: False, c: False, d: True}","{a: False, b: True, c: False, d: True}","{a: False, b: False, c: True, d: True}","{a: False, b: True, c: True, d: True}"]},{"j":["And",["Xor","d","a","a"],["Or","c","b","d"],["Or","d","a"]],"s":"d & (a | d) & (b | c | d)","sl":"d","cnf":"d","dnf":"d","tc":"d & (a | d) & (b | c | d)","td":"d | (a & d) | (b & d) | (c & d) | (a & b & d) | (a & c & d)","nnf":"d & (a | d) & (b | c | d)","nnf0":"d & (a | d) & (b | c | d)","anf":"d","g":8,"ic":true,"idn":false,"inn":true,"m":["{a: True, b: True, c: True, d: True}","{a: True, b: True, c: False, d: True}","{a: True, b: False, c: True, d: True}","{a: True, b: False, c: False, d: True}","{a: False, b: True, c: True, d: True}","{a: False, b: True, c: False, d: True}","{a: False, b: False, c: True, d: True}","{a: False, b: False, c: False, d: True}"]},{"j":["ITE","b",["ITE","b","a","c"],"d"],"s":"ITE(b, ITE(b, a, c), d)","sl":"(a & b) | (d & ~b)","cnf":"(b | d) & (a | ~b)","dnf":"(a & b) | (d & ~b)","tc":"(b | d) & (a | ~b) & (b | c | ~b)","td":"(a & b) | (b & ~b) | (d & ~b) | (a & b & c) | (a & b & d) | (a & c & d) | (b & c & ~b) | (b & d & ~b) | (c & d & ~b)","nnf":"(b | d) & (~b | ((b | c) & (a | ~b)))","nnf0":"(b | d) & (~b | ((b | c) & (a | ~b)))","anf":"ITE(b, ITE(b, a, c), d)","g":6,"ic":false,"idn":false,"inn":false,"m":["{a: True, b: False, c: True, d: True}","{a: True, b: False, c: False, d: True}","{a: False, b: False, c: True, d: True}","{a: False, b: False, c: False, d: True}","{a: True, b: True, c: True, d: True}","{a: True, b: True, c: True, d: False}","{a: True, b: True, c: False, d: True}","{a: True, b: True, c: False, d: False}"]},{"j":["Implies",["Equivalent",["Implies","a","b"],["Or","a","b"]],["Not",["Not","c"]]],"s":"Implies(Equivalent(Implies(a, b), a | b), c)","sl":"c | ~b","cnf":"c | ~b","dnf":"c | ~b","tc":"(c | ~b) & (a | c | ~a) & (a | c | ~b) & (c | ~a | ~b) & (a | b | c | ~a)","td":"c | (a & ~b) | (~a & ~b) | (a & b & ~b) | (a & ~a & ~b) | (b & ~a & ~b)","nnf":"c | (a & ~b) | (~a & ~b)","nnf0":"c | ((a | b | ~a) & ((a & ~b) | (~a & ~b)))","anf":"b ^ True ^ (b & c)","g":0,"ic":false,"idn":false,"inn":false,"m":["{a: False, b: False, c: True}","{a: True, b: False, c: True}","{a: False, b: True, c: True}","{a: True, b: True, c: True}","{a: False, b: False, c: False}","{a: True, b: False, c: False}"]},{"j":"d","s":"d","sl":"d","cnf":"d","dnf":"d","tc":"d","td":"d","nnf":"d","nnf0":"d","anf":"d","g":0,"ic":true,"idn":true,"inn":true,"m":["{d: True}"]},{"j":["And",["Implies",["Or","d","d","b"],["And","a","a","c"]],["ITE",["Or","a","d"],"a",["Not","a"]],["Implies",["Implies","c","d"],"b"]],"s":"(Implies(Implies(c, d), b)) & ITE(a | d, a, ~a) & (Implies(b | d, a & c))","sl":"c & (a | ~b) & (b | ~d)","cnf":"c & (a | ~b) & (b | ~d)","dnf":"(a & b & c) | (c & ~b & ~d)","tc":"(b | c) & (a | ~a) & (a | ~b) & (a | ~d) & (b | ~d) & (c | ~b) & (c | ~d) & (a | d | ~a)","td":"(a & b & c) | (a & c & ~d) | (a & b & c & d) | (a & b & c & ~a) | (a & c & d & ~d) | (a & b & ~b & ~d) | (a & c & ~a & ~d) | (a & c & ~b & ~d) | (b & ~a & ~b & ~d) | (c & ~a & ~b & ~d) | (a & b & c & ~a & ~d) | (a & b & d & ~b & ~d) | (a & c & d & ~a & ~d) | (a & c & d & ~b & ~d) | (a & b & ~a & ~b & ~d) | (a & c & ~a & ~b & ~d) | (b & d & ~a & ~b & ~d) | (c & d & ~a & ~b & ~d) | (a & b & c & d & ~a & ~d)","nnf":"(b | (c & ~d)) & (a | (~a & ~d)) & ((a & c) | (~b & ~d))","nnf0":"(a | d | ~a) & (b | (c & ~d)) & (a | (~a & ~d)) & ((a & c) | (~b & ~d))","anf":"(c & ITE(a ^ d ^ (a & d), a, a ^ True)) ^ (b & c & ITE(a ^ d ^ (a & d), a, a ^ True)) ^ (c & d & ITE(a ^ d ^ (a & d), a, a ^ True)) ^ (a & b & c & ITE(a ^ d ^ (a & d), a, a ^ True)) ^ (b & c & d & ITE(a ^ d ^ (a & d), a, a ^ True))","g":9,"ic":false,"idn":false,"inn":false,"m":["{a: True, b: False, c: True, d: False}","{a: True, b: True, c: True, d: False}","{a: True, b: True, c: True, d: True}","{a: False, b: False, c: True, d: False}"]},{"j":["And",["And",["Equivalent","e","c","e"],"d"],["And","d","e"]],"s":"d & e & (Equivalent(c, e))","sl":"c & d & e","cnf":"c & d & e","dnf":"c & d & e","tc":"d & e & (c | ~e) & (e | ~c)","td":"(c & d & e) | (d & e & ~e) | (c & d & e & ~c) | (d & e & ~c & ~e)","nnf":"d & e & (c | ~e) & (e | ~c)","nnf0":"d & e & (c | ~e) & (e | ~c)","anf":"c & d & e","g":3,"ic":false,"idn":false,"inn":false,"m":["{c: True, d: True, e: True}"]},{"j":["Not","d"],"s":"~d","sl":"~d","cnf":"~d","dnf":"~d","tc":"~d","td":"~d","nnf":"~d","nnf0":"~d","anf":"d ^ True","g":1,"ic":true,"idn":true,"inn":true,"m":["{d: False}"]},{"j":["Or","a","b"],"s":"a | b","sl":"a | b","cnf":"a | b","dnf":"a | b","tc":"a | b","td":"a | b","nnf":"a | b","nnf0":"a | b","anf":"a ^ b ^ (a & b)","g":2,"ic":true,"idn":true,"inn":true,"m":["{a: True, b: True}","{a: True, b: False}","{a: False, b: True}"]},{"j":["Not",["Equivalent","a","e"]],"s":"~(Equivalent(a, e))","sl":"(a & ~e) | (e & ~a)","cnf":"(a | e) & (~a | ~e)","dnf":"(a & ~e) | (e & ~a)","tc":"(a | e) & (~a | ~e)","td":"(a & ~a) | (a & ~e) | (e & ~a) | (e & ~e)","nnf":"(a | e) & (~a | ~e)","nnf0":"(a | e) & (~a | ~e)","anf":"a ^ e","g":1,"ic":false,"idn":false,"inn":false,"m":["{a: True, e: False}","{a: False, e: True}"]},{"j":["Equivalent",["Not",["And","a","a","c"]],"b"],"s":"Equivalent(b, ~(a & c))","sl":"(b & ~a) | (b & ~c) | (a & c & ~b)","cnf":"(a | b) & (b | c) & (~a | ~b | ~c)","dnf":"(b & ~a) | (b & ~c) | (a & c & ~b)","tc":"(a | b) & (b | c) & (~a | ~b | ~c)","td":"(b & ~a) | (b & ~b) | (b & ~c) | (a & c & ~a) | (a & c & ~b) | (a & c & ~c)","nnf":"(b | (a & c)) & (~a | ~b | ~c)","nnf0":"(b | (a & c)) & (~a | ~b | ~c)","anf":"b ^ (a & c)","g":0,"ic":false,"idn":false,"inn":false,"m":["{a: False, b: True, c: False}","{a: True, b: True, c: False}","{a: False, b: True, c: True}","{a: True, b: False, c: True}"]},{"j":["And",["Not","c"],"a"],"s":"a & ~c","sl":"a & ~c","cnf":"a & ~c","dnf":"a & ~c","tc":"a & ~c","td":"a & ~c","nnf":"a & ~c","nnf0":"a & ~c","anf":"a ^ (a & c)","g":3,"ic":true,"idn":true,"inn":true,"m":["{a: True, c: False}"]},{"j":"b","s":"b","sl":"b","cnf":"b","dnf":"b","tc":"b","td":"b","nnf":"b","nnf0":"b","anf":"b","g":0,"ic":true,"idn":true,"inn":true,"m":["{b: True}"]},{"j":["Implies",["Not","b"],["And","c","b"]],"s":"Implies(~b, b & c)","sl":"b","cnf":"b","dnf":"b","tc":"b & (b | c)","td":"b | (b & c)","nnf":"b | (b & c)","nnf0":"b | (b & c)","anf":"b","g":0,"ic":false,"idn":false,"inn":false,"m":["{b: True, c: True}","{b: True, c: False}"]},{"j":["Not",["Implies","a","e"]],"s":"~(Implies(a, e))","sl":"a & ~e","cnf":"a & ~e","dnf":"a & ~e","tc":"a & ~e","td":"a & ~e","nnf":"a & ~e","nnf0":"a & ~e","anf":"a ^ (a & e)","g":1,"ic":false,"idn":false,"inn":false,"m":["{a: True, e: False}"]},{"j":["Or",["Or","e","b","d"],["Not","a"]],"s":"b | d | e | ~a","sl":"b | d | e | ~a","cnf":"b | d | e | ~a","dnf":"b | d | e | ~a","tc":"b | d | e | ~a","td":"b | d | e | ~a","nnf":"b | d | e | ~a","nnf0":"b | d | e | ~a","anf":"a ^ True ^ (a & b) ^ (a & d) ^ (a & e) ^ (a & b & d) ^ (a & b & e) ^ (a & d & e) ^ (a & b & d & e)","g":5,"ic":true,"idn":true,"inn":true,"m":["{a: False, b: True, d: True, e: True}","{a: False, b: True, d: True, e: False}","{a: False, b: True, d: False, e: True}","{a: False, b: True, d: False, e: False}","{a: False, b: False, d: True, e: True}","{a: False, b: False, d: True, e: False}","{a: False, b: False, d: False, e: True}","{a: False, b: False, d: False, e: False}","{a: True, b: True, d: True, e: True}","{a: True, b: True, d: True, e: False}","{a: True, b: True, d: False, e: True}","{a: True, b: True, d: False, e: False}","{a: True, b: False, d: True, e: True}","{a: True, b: False, d: True, e: False}","{a: True, b: False, d: False, e: True}"]},{"j":["And",["ITE","c","b","b"],["Not","a"]],"s":"b & ~a","sl":"b & ~a","cnf":"b & ~a","dnf":"b & ~a","tc":"b & ~a","td":"b & ~a","nnf":"b & ~a","nnf0":"b & ~a","anf":"b ^ (a & b)","g":3,"ic":true,"idn":true,"inn":true,"m":["{a: False, b: True}"]},{"j":["Or",["ITE","c","b","c"],["And","d","d"],["Or","d","b"]],"s":"b | d | ITE(c, b, c)","sl":"b | d","cnf":"b | d","dnf":"b | d","tc":"(b | c | d) & (b | d | ~c)","td":"b | d | (b & c) | (c & ~c)","nnf":"b | d | (c & (b | ~c))","nnf0":"b | d | (c & (b | ~c))","anf":"b ^ d ^ (b & d) ^ ITE(c, b, c) ^ (b & ITE(c, b, c)) ^ (d & ITE(c, b, c)) ^ (b & d & ITE(c, b, c))","g":6,"ic":false,"idn":false,"inn":false,"m":["{b: True, c: False, d: True}","{b: True, c: True, d: True}","{b: True, c: False, d: False}","{b: True, c: True, d: False}","{b: False, c: False, d: True}","{b: False, c: True, d: True}"]},{"j":["Or",["Or","e","b","b"],"a"],"s":"a | b | e","sl":"a | b | e","cnf":"a | b | e","dnf":"a | b | e","tc":"a | b | e","td":"a | b | e","nnf":"a | b | e","nnf0":"a | b | e","anf":"a ^ b ^ e ^ (a & b) ^ (a & e) ^ (b & e) ^ (a & b & e)","g":3,"ic":true,"idn":true,"inn":true,"m":["{a: True, b: True, e: True}","{a: True, b: True, e: False}","{a: True, b: False, e: True}","{a: True, b: False, e: False}","{a: False, b: True, e: True}","{a: False, b: True, e: False}","{a: False, b: False, e: True}"]},{"j":["Implies",["Not","b"],["Or","a","d"]],"s":"Implies(~b, a | d)","sl":"a | b | d","cnf":"a | b | d","dnf":"a | b | d","tc":"a | b | d","td":"a | b | d","nnf":"a | b | d","nnf0":"a | b | d","anf":"a ^ b ^ d ^ (a & b) ^ (a & d) ^ (b & d) ^ (a & b & d)","g":0,"ic":false,"idn":false,"inn":false,"m":["{a: True, b: True, d: True}","{a: True, b: True, d: False}","{a: True, b: False, d: True}","{a: True, b: False, d: False}","{a: False, b: True, d: True}","{a: False, b: True, d: False}","{a: False, b: False, d: True}"]},{"j":["Or",["Not","b"],["And","c","a","c"]],"s":"~b | (a & c)","sl":"~b | (a & c)","cnf":"(a | ~b) & (c | ~b)","dnf":"~b | (a & c)","tc":"(a | ~b) & (c | ~b)","td":"~b | (a & c)","nnf":"~b | (a & c)","nnf0":"~b | (a & c)","anf":"b ^ True ^ (a & b & c)","g":5,"ic":false,"idn":true,"inn":true,"m":["{a: True, b: False, c: True}","{a: True, b: False, c: False}","{a: False, b: False, c: True}","{a: False, b: False, c: False}","{a: True, b: True, c: True}"]},{"j":["ITE",["Equivalent","b","d","a"],["Or","d","c","a"],["Or","b","a","a"]],"s":"ITE(Equivalent(a, b, d), a | c | d, a | b)","sl":"a | b | (c & ~d)","cnf":"(a | b | c) & (a | b | ~d)","dnf":"a | b | (c & ~d)","tc":"(a | b | ~a) & (a | b | ~d) & (a | b | c | d) & (a | b | d | ~b) & (a | c | d | ~a | ~b | ~d)","td":"a | (a & b) | (a & c) | (a & d) | (b & c) | (b & d) | (a & ~a) | (a & ~b) | (a & ~d) | (b & ~a) | (b & ~b) | (b & ~d) | (a & b & d) | (a & b & ~a) | (a & b & ~b) | (a & b & ~d) | (a & d & ~a) | (a & d & ~b) | (a & d & ~d) | (b & d & ~a) | (b & d & ~b) | (b & d & ~d) | (a & b & c & d) | (a & ~a & ~b) | (b & ~b & ~d) | (d & ~a & ~d) | (a & b & c & ~b) | (a & b & d & ~a) | (a & b & d & ~b) | (a & b & d & ~d) | (a & c & d & ~a) | (b & c & d & ~d) | (a & b & ~a & ~b) | (a & b & ~b & ~d) | (a & c & ~a & ~b) | (a & d & ~a & ~b) | (a & d & ~a & ~d) | (b & c & ~b & ~d) | (b & d & ~a & ~d) | (b & d & ~b & ~d) | (c & d & ~a & ~d) | (a & ~a & ~b & ~d) | (b & ~a & ~b & ~d) | (c & ~a & ~b & ~d) | (d & ~a & ~b & ~d) | (a & b & d & ~a & ~b) | (a & b & d & ~a & ~d) | (a & b & d & ~b & ~d) | (a & b & ~a & ~b & ~d) | (a & d & ~a & ~b & ~d) | (b & d & ~a & ~b & ~d)","nnf":"(a | b | ((a | ~d) & (b | ~a) & (d | ~b))) & (a | c | d | ((a | b | d) & (~a | ~b | ~d)))","nnf0":"(a | b | ((a | ~d) & (b | ~a) & (d | ~b))) & (a | c | d | ((a | b | d) & (~a | ~b | ~d)))","anf":"ITE(a ^ b ^ d ^ True ^ (a & b) ^ (a & d) ^ (b & d), a ^ c ^ d ^ (a & c) ^ (a & d) ^ (c & d) ^ (a & c & d), a ^ b ^ (a & b))","g":8,"ic":false,"idn":false,"inn":false,"m":["{a: True, b: True, c: True, d: True}","{a: True, b: False, c: True, d: True}","{a: True, b: True, c: False, d: True}","{a: True, b: False, c: False, d: True}","{a: True, b: True, c: True, d: False}","{a: True, b: False, c: True, d: False}","{a: True, b: True, c: False, d: False}","{a: True, b: False, c: False, d: False}","{a: False, b: True, c: True, d: True}","{a: False, b: True, c: False, d: True}","{a: False, b: True, c: True, d: False}","{a: False, b: False, c: True, d: False}","{a: False, b: True, c: False, d: False}"]},{"j":["Or",["Xor",["And","a","b"],["Or","d","a"],"d"],["Equivalent",["Implies","a","b"],["Or","d","a"],["And","a","d"]]],"s":"(d ^ (a & b) ^ (a | d)) | (Equivalent(a & d, Implies(a, b), a | d))","sl":"a & (b | ~d) & (d | ~b)","cnf":"a & (b | ~d) & (d | ~b)","dnf":"(a & b & d) | (a & ~b & ~d)","tc":"(a | d) & (a | ~d) & (a | b | d) & (a | b | ~d) & (a | d | ~a) & (a | d | ~b) & (a | d | ~d) & (b | d | ~d) & (a | ~a | ~d) & (b | ~a | ~d) & (d | ~a | ~b) & (a | b | d | ~a) & (a | b | d | ~b) & (a | b | d | ~d) & (a | b | ~a | ~d) & (a | d | ~a | ~b) & (a | d | ~a | ~d) & (a | d | ~b | ~d) & (b | d | ~a | ~d) & (d | ~a | ~b | ~d) & (a | b | d | ~a | ~d) & (a | b | d | ~b | ~d) & (a | d | ~a | ~b | ~d) & (b | d | ~a | ~b | ~d) & (a | b | d | ~a | ~b | ~d)","td":"(d & ~d) | (a & b & d) | (a & b & ~a) | (a & b & ~b) | (a & d & ~a) | (a & d & ~d) | (a & ~a & ~d) | (a & ~b & ~d) | (d & ~a & ~d) | (d & ~b & ~d) | (a & b & d & ~a) | (a & b & d & ~b) | (a & b & d & ~d) | (a & b & ~a & ~b) | (a & b & ~a & ~d) | (a & b & ~b & ~d) | (a & d & ~a & ~b) | (a & d & ~a & ~d) | (a & d & ~b & ~d) | (b & d & ~a & ~d) | (a & ~a & ~b & ~d) | (d & ~a & ~b & ~d) | (a & b & d & ~a & ~b) | (a & b & d & ~a & ~d) | (a & b & d & ~b & ~d) | (a & b & ~a & ~b & ~d) | (a & d & ~a & ~b & ~d) | (a & b & d & ~a & ~b & ~d)","nnf":"((b | ~a | ~d) & (a | d | (a & ~b)) & ((a & d) | (~a & ~d))) | ((a | d | (a & b)) & (~d | (a & b) | (~a & ~d)) & (d | ~a | ~b | (~a & ~d)))","nnf0":"((b | ~a | ~d) & (a | d | (a & ~b)) & ((a & d) | (~a & ~d))) | ((a | d | (a & b)) & (a | d | ~a | ~b | ~d) & (~d | (a & b) | (~a & ~d)) & (d | ~a | ~b | (~a & ~d)))","anf":"a ^ (a & b) ^ (a & d)","g":9,"ic":false,"idn":false,"inn":false,"m":["{a: True, b: True, d: True}","{a: True, b: False, d: False}"]},{"j":["Or",["And",["Not","a"],["Or","d","c"]],["Or",["Or","b","c"],"d"]],"s":"b | c | d | (~a & (c | d))","sl":"b | c | d","cnf":"b | c | d","dnf":"b | c | d","tc":"(b | c | d) & (b | c | d | ~a)","td":"b | c | d | (c & ~a) | (d & ~a)","nnf":"b | c | d | (~a & (c | d))","nnf0":"b | c | d | (~a & (c | d))","anf":"b ^ c ^ d ^ (b & c) ^ (b & d) ^ (c & d) ^ (b & c & d)","g":9,"ic":false,"idn":false,"inn":true,"m":["{a: False, b: True, c: True, d: True}","{a: True, b: True, c: True, d: True}","{a: False, b: True, c: True, d: False}","{a: True, b: True, c: True, d: False}","{a: False, b: True, c: False, d: True}","{a: True, b: True, c: False, d: True}","{a: False, b: True, c: False, d: False}","{a: True, b: True, c: False, d: False}","{a: False, b: False, c: True, d: True}","{a: True, b: False, c: True, d: True}","{a: False, b: False, c: True, d: False}","{a: True, b: False, c: True, d: False}","{a: False, b: False, c: False, d: True}","{a: True, b: False, c: False, d: True}"]},{"j":["And",["Implies","b","c"],["Xor","b","b","b"]],"s":"b & (Implies(b, c))","sl":"b & c","cnf":"b & c","dnf":"b & c","tc":"b & (c | ~b)","td":"(b & c) | (b & ~b)","nnf":"b & (c | ~b)","nnf0":"b & (c | ~b)","anf":"b & c","g":2,"ic":false,"idn":false,"inn":false,"m":["{b: True, c: True}"]},{"j":["And","b",["And","b","a","d"]],"s":"a & b & d","sl":"a & b & d","cnf":"a & b & d","dnf":"a & b & d","tc":"a & b & d","td":"a & b & d","nnf":"a & b & d","nnf0":"a & b & d","anf":"a & b & d","g":3,"ic":true,"idn":true,"inn":true,"m":["{a: True, b: True, d: True}"]},{"j":["Equivalent","a","a",["Or","c","b"]],"s":"Equivalent(a, b | c)","sl":"(a & b) | (a & c) | (~a & ~b & ~c)","cnf":"(a | ~b) & (a | ~c) & (b | c | ~a)","dnf":"(a & b) | (a & c) | (~a & ~b & ~c)","tc":"(a | ~b) & (a | ~c) & (b | c | ~a)","td":"(a & b) | (a & c) | (a & ~a) | (b & ~b & ~c) | (c & ~b & ~c) | (~a & ~b & ~c)","nnf":"(b | c | ~a) & (a | (~b & ~c))","nnf0":"(b | c | ~a) & (a | (~b & ~c))","anf":"a ^ b ^ c ^ True ^ (b & c)","g":0,"ic":false,"idn":false,"inn":false,"m":["{a: True, b: True, c: False}","{a: True, b: False, c: True}","{a: True, b: True, c: True}","{a: False, b: False, c: False}"]},{"j":["Or","a",["And","a","b"]],"s":"a | (a & b)","sl":"a","cnf":"a","dnf":"a","tc":"a & (a | b)","td":"a | (a & b)","nnf":"a | (a & b)","nnf0":"a | (a & b)","anf":"a","g":4,"ic":false,"idn":true,"inn":true,"m":["{a: True, b: True}","{a: True, b: False}"]},{"j":["Or",["Implies","c","b"],["Not","d"]],"s":"~d | (Implies(c, b))","sl":"b | ~c | ~d","cnf":"b | ~c | ~d","dnf":"b | ~c | ~d","tc":"b | ~c | ~d","td":"b | ~c | ~d","nnf":"b | ~c | ~d","nnf0":"b | ~c | ~d","anf":"True ^ (c & d) ^ (b & c & d)","g":3,"ic":false,"idn":false,"inn":false,"m":["{b: True, c: False, d: False}","{b: False, c: False, d: False}","{b: True, c: True, d: False}","{b: False, c: True, d: False}","{b: True, c: False, d: True}","{b: False, c: False, d: True}","{b: True, c: True, d: True}"]},{"j":["Equivalent",["Or","c","a","c"],["Xor","a","c"]],"s":"Equivalent(a | c, a ^ c)","sl":"~a | ~c","cnf":"~a | ~c","dnf":"~a | ~c","tc":"(~a | ~c) & (a | c | ~a) & (a | c | ~c)","td":"(a & ~a) | (a & ~c) | (c & ~a) | (c & ~c) | (~a & ~c) | (a & c & ~a) | (a & c & ~c) | (a & ~a & ~c) | (c & ~a & ~c) | (a & c & ~a & ~c)","nnf":"(a | c | ((a | ~c) & (c | ~a))) & ((~a & ~c) | ((a | c) & (~a | ~c)))","nnf0":"(a | c | ((a | ~c) & (c | ~a))) & ((~a & ~c) | ((a | c) & (~a | ~c)))","anf":"True ^ (a & c)","g":0,"ic":false,"idn":false,"inn":false,"m":["{a: False, c: False}","{a: True, c: False}","{a: False, c: True}"]},{"j":["Equivalent",["And","a","e"],"e","c"],"s":"Equivalent(c, e, a & e)","sl":"(a | ~e) & (c | ~e) & (e | ~c)","cnf":"(a | ~e) & (c | ~e) & (e | ~c)","dnf":"(a & c & e) | (~c & ~e)","tc":"(a | ~e) & (e | ~c) & (e | ~e) & (c | ~a | ~e)","td":"(e & ~e) | (a & c & e) | (~c & ~e) | (a & e & ~a) | (a & e & ~e) | (c & e & ~e) | (c & ~c & ~e) | (e & ~a & ~e) | (a & c & e & ~c) | (~a & ~c & ~e) | (a & e & ~a & ~c) | (a & e & ~c & ~e)","nnf":"(e | ~c) & (~e | (a & e)) & (c | ~a | ~e)","nnf0":"(e | ~c) & (~e | (a & e)) & (c | ~a | ~e)","anf":"c ^ e ^ True ^ (c & e) ^ (a & c & e)","g":0,"ic":false,"idn":false,"inn":false,"m":["{a: False, c: False, e: False}","{a: True, c: False, e: False}","{a: True, c: True, e: True}"]},{"j":["Equivalent",["Not","a"],["Implies","c",["Xor","b","a"]],["Equivalent",["Xor","c","b"],["And","c","b","a"]]],"s":"Equivalent(~a, Implies(c, a ^ b), Equivalent(b ^ c, a & b & c))","sl":"(b | ~a) & (b | ~c) & (c | ~b)","cnf":"(b | ~a) & (b | ~c) & (c | ~b)","dnf":"(b & c) | (~a & ~b & ~c)","tc":"(c | ~b) & (a | b | ~c) & (a | c | ~b) & (b | c | ~a) & (b | c | ~b) & (b | c | ~c) & (b | ~a | ~c) & (a | b | c | ~a) & (a | b | c | ~b) & (a | b | c | ~c) & (a | b | ~a | ~c) & (a | b | ~b | ~c) & (b | c | ~a | ~b) & (b | c | ~a | ~c) & (a | ~a | ~b | ~c) & (b | ~a | ~b | ~c) & (c | ~a | ~b | ~c) & (a | b | c | ~a | ~b) & (a | b | c | ~b | ~c) & (b | c | ~a | ~b | ~c) & (a | b | c | ~a | ~b | ~c)","td":"(b & ~b) | (c & ~c) | (a & b & c) | (a & b & ~b) | (a & c & ~a) | (a & c & ~c) | (b & c & ~a) | (b & c & ~b) | (b & c & ~c) | (b & ~a & ~b) | (b & ~b & ~c) | (c & ~a & ~c) | (c & ~b & ~c) | (a & b & c & ~a) | (a & b & c & ~b) | (a & b & c & ~c) | (~a & ~b & ~c) | (a & b & ~a & ~b) | (a & b & ~b & ~c) | (a & c & ~a & ~b) | (a & c & ~a & ~c) | (a & c & ~b & ~c) | (b & c & ~a & ~b) | (b & c & ~a & ~c) | (b & c & ~b & ~c) | (a & ~a & ~b & ~c) | (b & ~a & ~b & ~c) | (c & ~a & ~b & ~c) | (a & b & c & ~a & ~b) | (a & b & c & ~a & ~c) | (a & b & c & ~b & ~c) | (a & b & ~a & ~b & ~c) | (a & c & ~a & ~b & ~c) | (b & c & ~a & ~b & ~c) | (a & b & c & ~a & ~b & ~c)","nnf":"(a | ~c | ((a | b) & (~a | ~b))) & (~a | (((a & b & c) | ((b | c) & (~b | ~c))) & (~a | ~b | ~c | ((b | ~c) & (c | ~b))))) & ((c & (a | ~b) & (b | ~a)) | (((a & b & c) | ((b | ~c) & (c | ~b))) & (~a | ~b | ~c | ((b | c) & (~b | ~c)))))","nnf0":"(a | ~c | ((a | b) & (~a | ~b))) & (~a | (((a & b & c) | ((b | c) & (~b | ~c))) & (~a | ~b | ~c | ((b | ~c) & (c | ~b))))) & ((c & (a | ~b) & (b | ~a)) | (((a & b & c) | ((b | ~c) & (c | ~b))) & (~a | ~b | ~c | ((b | c) & (~b | ~c)))))","anf":"a ^ b ^ c ^ True ^ (a & b) ^ (a & c) ^ (a & b & c)","g":0,"ic":false,"idn":false,"inn":false,"m":["{a: True, b: True, c: True}","{a: False, b: True, c: True}","{a: False, b: False, c: False}"]},{"j":["ITE",["Or","c","c"],["Equivalent","c","d"],"c"],"s":"ITE(c, Equivalent(c, d), c)","sl":"c & d","cnf":"c & d","dnf":"c & d","tc":"c & (d | ~c) & (c | ~c | ~d)","td":"(c & d) | (c & ~c) | (c & d & ~d) | (c & ~c & ~d)","nnf":"c & (~c | ((c | ~d) & (d | ~c)))","nnf0":"c & (~c | ((c | ~d) & (d | ~c)))","anf":"ITE(c, c ^ d ^ True, c)","g":3,"ic":false,"idn":false,"inn":false,"m":["{c: True, d: True}"]},{"j":["And",["Equivalent","b","b"],["ITE","a","d","a"]],"s":"ITE(a, d, a)","sl":"a & d","cnf":"a & d","dnf":"a & d","tc":"a & (d | ~a)","td":"(a & d) | (a & ~a)","nnf":"a & (d | ~a)","nnf0":"a & (d | ~a)","anf":"ITE(a, d, a)","g":3,"ic":false,"idn":false,"inn":false,"m":["{a: True, d: True}"]},{"j":["Or",["ITE","a","b","a"],["Not","c"],"b"],"s":"b | ~c | ITE(a, b, a)","sl":"b | ~c","cnf":"b | ~c","dnf":"b | ~c","tc":"(a | b | ~c) & (b | ~a | ~c)","td":"b | ~c | (a & b) | (a & ~a)","nnf":"b | ~c | (a & (b | ~a))","nnf0":"b | ~c | (a & (b | ~a))","anf":"c ^ True ^ (b & c) ^ (c & ITE(a, b, a)) ^ (b & c & ITE(a, b, a))","g":7,"ic":false,"idn":false,"inn":false,"m":["{a: False, b: True, c: False}","{a: True, b: True, c: False}","{a: False, b: False, c: False}","{a: True, b: False, c: False}","{a: False, b: True, c: True}","{a: True, b: True, c: True}"]},{"j":["ITE",["Or","c","c"],["Implies","b","c"],["And","c","a"]],"s":"ITE(c, Implies(b, c), a & c)","sl":"c","cnf":"c","dnf":"c","tc":"c & (a | c) & (c | ~b | ~c)","td":"c | (a & c) | (c & ~b) | (c & ~c) | (a & c & ~b) | (a & c & ~c)","nnf":"c | (a & c)","nnf0":"(c | (a & c)) & (c | ~b | ~c)","anf":"ITE(c, b ^ True ^ (b & c), a & c)","g":5,"ic":false,"idn":false,"inn":false,"m":["{a: True, b: False, c: True}","{a: False, b: False, c: True}","{a: True, b: True, c: True}","{a: False, b: True, c: True}"]},{"j":["Or","a",["Or","a","d","c"]],"s":"a | c | d","sl":"a | c | d","cnf":"a | c | d","dnf":"a | c | d","tc":"a | c | d","td":"a | c | d","nnf":"a | c | d","nnf0":"a | c | d","anf":"a ^ c ^ d ^ (a & c) ^ (a & d) ^ (c & d) ^ (a & c & d)","g":3,"ic":true,"idn":true,"inn":true,"m":["{a: True, c: True, d: True}","{a: True, c: True, d: False}","{a: True, c: False, d: True}","{a: True, c: False, d: False}","{a: False, c: True, d: True}","{a: False, c: True, d: False}","{a: False, c: False, d: True}"]},{"j":["ITE",["Equivalent","b",["And","c","b","a"]],["Xor",["Or","c","b"],["Equivalent","b","a","b"]],["And",["Not","c"],["Or","c","a"]]],"s":"ITE(Equivalent(b, a & b & c), (Equivalent(a, b)) ^ (b | c), ~c & (a | c))","sl":"(a | ~b) & (a | ~c) & (~b | ~c) & (b | c | ~a)","cnf":"(a | ~b) & (a | ~c) & (~b | ~c) & (b | c | ~a)","dnf":"(a & b & ~c) | (a & c & ~b) | (~a & ~b & ~c)","tc":"(a | b | ~b) & (a | b | ~c) & (a | c | ~b) & (b | c | ~a) & (a | ~b | ~c) & (b | ~a | ~b) & (b | ~b | ~c) & (c | ~b | ~c) & (a | b | c | ~a) & (a | b | c | ~b) & (a | b | c | ~c) & (~a | ~b | ~c) & (a | b | ~a | ~b) & (b | c | ~a | ~b) & (b | ~a | ~b | ~c) & (a | b | ~a | ~b | ~c) & (b | c | ~a | ~b | ~c) & (a | b | c | ~a | ~b | ~c)","td":"(b & ~b) | (a & b & ~b) | (a & b & ~c) | (a & c & ~b) | (b & c & ~b) | (b & c & ~c) | (a & ~a & ~b) | (a & ~a & ~c) | (b & ~a & ~b) | (b & ~b & ~c) | (c & ~b & ~c) | (a & b & c & ~a) | (a & b & c & ~b) | (a & b & c & ~c) | (~a & ~b & ~c) | (a & b & ~a & ~b) | (a & b & ~a & ~c) | (a & b & ~b & ~c) | (a & c & ~a & ~b) | (a & c & ~a & ~c) | (a & c & ~b & ~c) | (b & c & ~a & ~b) | (b & c & ~a & ~c) | (b & c & ~b & ~c) | (a & ~a & ~b & ~c) | (b & ~a & ~b & ~c) | (c & ~a & ~b & ~c) | (a & b & c & ~a & ~b) | (a & b & c & ~a & ~c) | (a & b & c & ~b & ~c) | (a & b & ~a & ~b & ~c) | (a & c & ~a & ~b & ~c) | (b & c & ~a & ~b & ~c) | (a & b & c & ~a & ~b & ~c)","nnf":"(~b | (a & b & c) | (~c & (a | c))) & (((b | (a & b & c)) & (~a | ~b | ~c)) | ((b | c | ((a | ~b) & (b | ~a))) & ((~b & ~c) | ((a | b) & (~a | ~b)))))","nnf0":"((~c & (a | c)) | ((~b | (a & b & c)) & (b | ~a | ~b | ~c))) & (((b | (a & b & c)) & (~a | ~b | ~c)) | ((b | c | ((a | ~b) & (b | ~a))) & ((~b & ~c) | ((a | b) & (~a | ~b)))))","anf":"ITE(b ^ True ^ (a & b & c), a ^ c ^ True ^ (b & c), a ^ (a & c))","g":12,"ic":false,"idn":false,"inn":false,"m":["{a: False, b: False, c: False}","{a: True, b: False, c: True}","{a: True, b: True, c: False}"]},{"j":["ITE",["Or","c","a"],"a",["Or","b","a"]],"s":"ITE(a | c, a, a | b)","sl":"a | (b & ~c)","cnf":"(a | b) & (a | ~c)","dnf":"a | (b & ~c)","tc":"(a | ~a) & (a | ~c) & (a | b | c)","td":"a | (a & b) | (a & c) | (a & ~a & ~c) | (b & ~a & ~c) | (c & ~a & ~c)","nnf":"(a | b | c) & (a | (~a & ~c))","nnf0":"(a | b | c) & (a | (~a & ~c))","anf":"ITE(a ^ c ^ (a & c), a, a ^ b ^ (a & b))","g":7,"ic":false,"idn":false,"inn":false,"m":["{a: True, b: True, c: False}","{a: True, b: False, c: False}","{a: True, b: True, c: True}","{a: True, b: False, c: True}","{a: False, b: True, c: False}"]},{"j":["Xor",["Equivalent",["Implies","d","b"],["Xor","d","c"]],["ITE",["Implies","d","d"],["Or","c","a"],["Implies","c","b"]]],"s":"(a | c) ^ (Equivalent(Implies(d, b), c ^ d))","sl":"(a | b) & (a | d) & (b | ~c) & (d | ~c) & (c | ~a | ~b | ~d)","cnf":"(a | b) & (a | d) & (b | ~c) & (d | ~c) & (c | ~a | ~b | ~d)","dnf":"(b & c & d) | (b & d & ~a) | (a & ~b & ~c) | (a & ~c & ~d)","tc":"(d | ~c) & (a | c | d) & (b | ~c | ~d) & (d | ~a | ~c) & (d | ~b | ~c) & (a | b | c | ~d) & (a | c | d | ~b) & (c | d | ~a | ~d) & (c | d | ~c | ~d) & (b | ~a | ~c | ~d) & (c | ~a | ~b | ~d) & (c | ~b | ~c | ~d) & (d | ~a | ~b | ~c) & (a | c | d | ~c | ~d) & (b | c | d | ~a | ~d) & (b | c | d | ~c | ~d) & (a | c | ~b | ~c | ~d) & (a | b | c | d | ~c | ~d)","td":"(c & ~c) | (d & ~d) | (b & c & d) | (a & c & ~c) | (a & d & ~d) | (b & c & ~c) | (b & d & ~b) | (b & d & ~d) | (c & d & ~c) | (c & d & ~d) | (a & b & c & d) | (a & ~a & ~c) | (a & ~c & ~d) | (c & ~a & ~c) | (c & ~c & ~d) | (d & ~b & ~d) | (d & ~c & ~d) | (a & b & c & ~c) | (a & b & d & ~b) | (a & b & d & ~d) | (a & c & d & ~c) | (a & c & d & ~d) | (b & c & d & ~b) | (b & c & d & ~c) | (b & c & d & ~d) | (a & b & ~c & ~d) | (a & c & ~c & ~d) | (a & d & ~b & ~c) | (a & d & ~b & ~d) | (a & d & ~c & ~d) | (b & c & ~a & ~c) | (b & c & ~c & ~d) | (b & d & ~a & ~c) | (b & d & ~b & ~c) | (b & d & ~b & ~d) | (b & d & ~c & ~d) | (c & d & ~a & ~c) | (c & d & ~b & ~c) | (c & d & ~b & ~d) | (c & d & ~c & ~d) | (c & ~a & ~c & ~d) | (d & ~a & ~c & ~d) | (d & ~b & ~c & ~d) | (a & c & d & ~b & ~c) | (a & c & d & ~b & ~d) | (a & c & d & ~c & ~d) | (b & c & d & ~b & ~c) | (b & c & d & ~b & ~d) | (b & c & d & ~c & ~d) | (b & c & ~a & ~c & ~d) | (b & d & ~a & ~b & ~c) | (b & d & ~a & ~c & ~d) | (b & d & ~b & ~c & ~d) | (c & d & ~a & ~b & ~c) | (c & d & ~a & ~c & ~d) | (c & d & ~b & ~c & ~d) | (d & ~a & ~b & ~c & ~d) | (b & c & d & ~b & ~c & ~d)","nnf":"(a | c | ((b | ~d | ((c | ~d) & (d | ~c))) & ((d & ~b) | ((c | d) & (~c | ~d))))) & ((~a & ~c) | ((b | ~d | ((c | d) & (~c | ~d))) & ((d & ~b) | ((c | ~d) & (d | ~c)))))","nnf0":"(a | c | ((b | ~d | ((c | ~d) & (d | ~c))) & ((d & ~b) | ((c | d) & (~c | ~d))))) & ((~a & ~c) | ((b | ~d | ((c | d) & (~c | ~d))) & ((d & ~b) | ((c | ~d) & (d | ~c)))))","anf":"a ^ (a & c) ^ (b & d)","g":4,"ic":false,"idn":false,"inn":false,"m":["{a: True, b: False, c: False, d: False}","{a: True, b: True, c: False, d: False}","{a: False, b: True, c: False, d: True}","{a: True, b: False, c: False, d: True}","{a: False, b: True, c: True, d: True}","{a: True, b: True, c: True, d: True}"]},{"j":["And",["Or",["ITE","e","e","e"],["Implies","c","e"]],["Xor",["Equivalent","c","b"],"e"],"c"],"s":"c & (e | (Implies(c, e))) & (e ^ (Equivalent(b, c)))","sl":"c & e & ~b","cnf":"c & e & ~b","dnf":"c & e & ~b","tc":"c & (e | ~c) & (b | c | ~e) & (b | e | ~c) & (c | e | ~b) & (~b | ~c | ~e)","td":"(c & ~c) | (b & c & ~c) | (c & e & ~b) | (c & e & ~c) | (c & e & ~e) | (c & ~b & ~c) | (c & ~c & ~e) | (b & c & e & ~b) | (b & c & e & ~c) | (b & c & e & ~e) | (b & c & ~b & ~c) | (b & c & ~c & ~e) | (c & e & ~b & ~c) | (c & e & ~c & ~e) | (c & ~b & ~c & ~e) | (b & c & e & ~b & ~c) | (b & c & e & ~b & ~e) | (b & c & ~b & ~c & ~e) | (c & e & ~b & ~c & ~e)","nnf":"c & (e | ~c) & (e | ((b | ~c) & (c | ~b))) & (~e | ((b | c) & (~b | ~c)))","nnf0":"c & (e | ~c) & (e | ((b | ~c) & (c | ~b))) & (~e | ((b | c) & (~b | ~c)))","anf":"(c & e) ^ (b & c & e)","g":7,"ic":false,"idn":false,"inn":false,"m":["{b: False, c: True, e: True}"]},{"j":["Not",["Or","c","a","b"]],"s":"~(a | b | c)","sl":"~a & ~b & ~c","cnf":"~a & ~b & ~c","dnf":"~a & ~b & ~c","tc":"~a & ~b & ~c","td":"~a & ~b & ~c","nnf":"~a & ~b & ~c","nnf0":"~a & ~b & ~c","anf":"a ^ b ^ c ^ True ^ (a & b) ^ (a & c) ^ (b & c) ^ (a & b & c)","g":4,"ic":false,"idn":false,"inn":false,"m":["{a: False, b: False, c: False}"]},{"j":["And","c",["Or","b",["Not","a"]]],"s":"c & (b | ~a)","sl":"c & (b | ~a)","cnf":"c & (b | ~a)","dnf":"(b & c) | (c & ~a)","tc":"c & (b | ~a)","td":"(b & c) | (c & ~a)","nnf":"c & (b | ~a)","nnf0":"c & (b | ~a)","anf":"c ^ (a & c) ^ (a & b & c)","g":5,"ic":true,"idn":false,"inn":true,"m":["{a: False, b: True, c: True}","{a: False, b: False, c: True}","{a: True, b: True, c: True}"]},{"j":["And",["Not","a"],["Or","c","c"]],"s":"c & ~a","sl":"c & ~a","cnf":"c & ~a","dnf":"c & ~a","tc":"c & ~a","td":"c & ~a","nnf":"c & ~a","nnf0":"c & ~a","anf":"c ^ (a & c)","g":3,"ic":true,"idn":true,"inn":true,"m":["{a: False, c: True}"]},{"j":["And",["And","b","a"],["Or","c","d"]],"s":"a & b & (c | d)","sl":"a & b & (c | d)","cnf":"a & b & (c | d)","dnf":"(a & b & c) | (a & b & d)","tc":"a & b & (c | d)","td":"(a & b & c) | (a & b & d)","nnf":"a & b & (c | d)","nnf0":"a & b & (c | d)","anf":"(a & b & c) ^ (a & b & d) ^ (a & b & c & d)","g":5,"ic":true,"idn":false,"inn":true,"m":["{a: True, b: True, c: True, d: True}","{a: True, b: True, c: True, d: False}","{a: True, b: True, c: False, d: True}"]},{"j":["And",["Implies","a","b"],["ITE","b","a","a"],["Equivalent","d","d","d"]],"s":"a & (Implies(a, b))","sl":"a & b","cnf":"a & b","dnf":"a & b","tc":"a & (b | ~a)","td":"(a & b) | (a & ~a)","nnf":"a & (b | ~a)","nnf0":"a & (b | ~a)","anf":"a & b","g":2,"ic":false,"idn":false,"inn":false,"m":["{a: True, b: True}"]},{"j":["Implies",["Implies","c","b"],["Or","c","a"]],"s":"Implies(Implies(c, b), a | c)","sl":"a | c","cnf":"a | c","dnf":"a | c","tc":"(a | c) & (a | c | ~b)","td":"a | c | (c & ~b)","nnf":"a | c | (c & ~b)","nnf0":"a | c | (c & ~b)","anf":"a ^ c ^ (a & c)","g":0,"ic":false,"idn":false,"inn":false,"m":["{a: True, b: False, c: True}","{a: True, b: True, c: True}","{a: True, b: False, c: False}","{a: True, b: True, c: False}","{a: False, b: False, c: True}","{a: False, b: True, c: True}"]},{"j":["ITE","b",["Not","a"],["Implies","b","d"]],"s":"ITE(b, ~a, Implies(b, d))","sl":"~a | ~b","cnf":"~a | ~b","dnf":"~a | ~b","tc":"(~a | ~b) & (b | d | ~b)","td":"~b | (b & ~a) | (b & ~b) | (d & ~a) | (d & ~b) | (~a & ~b)","nnf":"~a | ~b","nnf0":"(~a | ~b) & (b | d | ~b)","anf":"ITE(b, a ^ True, b ^ True ^ (b & d))","g":4,"ic":false,"idn":false,"inn":false,"m":["{a: False, b: False, d: True}","{a: False, b: False, d: False}","{a: True, b: False, d: True}","{a: True, b: False, d: False}","{a: False, b: True, d: True}","{a: False, b: True, d: False}"]},{"j":["Not",["And",["Not","b"],["Or","b","c"]]],"s":"~(~b & (b | c))","sl":"b | ~c","cnf":"b | ~c","dnf":"b | ~c","tc":"(b | ~b) & (b | ~c)","td":"b | (~b & ~c)","nnf":"b | (~b & ~c)","nnf0":"b | (~b & ~c)","anf":"c ^ True ^ (b & c)","g":6,"ic":false,"idn":false,"inn":false,"m":["{b: True, c: False}","{b: True, c: True}","{b: False, c: False}"]},{"j":["Equivalent",["Or",["And","e","a"],"c"],["Implies",["Or","d","b"],"c"]],"s":"Equivalent(Implies(b | d, c), c | (a & e))","sl":"c | (b & ~a) | (b & ~e) | (d & ~a) | (d & ~e) | (a & e & ~b & ~d)","cnf":"(a | b | c | d) & (b | c | d | e) & (c | ~a | ~b | ~e) & (c | ~a | ~d | ~e)","dnf":"c | (b & ~a) | (b & ~e) | (d & ~a) | (d & ~e) | (a & e & ~b & ~d)","tc":"(a | c | ~c) & (c | e | ~c) & (a | b | c | d) & (b | c | d | e) & (c | ~b | ~c) & (c | ~c | ~d) & (c | ~a | ~b | ~e) & (c | ~a | ~d | ~e)","td":"c | (a & c & e) | (b & c & ~c) | (c & d & ~c) | (b & ~a & ~c) | (b & ~c & ~e) | (c & ~a & ~c) | (c & ~b & ~d) | (c & ~c & ~e) | (d & ~a & ~c) | (d & ~c & ~e) | (a & e & ~a & ~c) | (a & e & ~b & ~d) | (a & e & ~c & ~e) | (b & ~b & ~c & ~d) | (d & ~b & ~c & ~d)","nnf":"(c | (a & e) | (~c & (b | d))) & (c | (~b & ~d) | (~c & (~a | ~e)))","nnf0":"(c | (a & e) | (~c & (b | d))) & (c | (~b & ~d) | (~c & (~a | ~e)))","anf":"b ^ c ^ d ^ (a & e) ^ (b & c) ^ (b & d) ^ (c & d) ^ (a & c & e) ^ (b & c & d)","g":0,"ic":false,"idn":false,"inn":false,"m":["{a: False, b: False, c: True, d: False, e: False}","{a: True, b: False, c: True, d: False, e: False}","{a: False, b: True, c: True, d: False, e: False}","{a: True, b: True, c: True, d: False, e: False}","{a: False, b: False, c: True, d: True, e: False}","{a: True, b: False, c: True, d: True, e: False}","{a: False, b: True, c: True, d: True, e: False}","{a: True, b: True, c: True, d: True, e: False}","{a: False, b: False, c: True, d: False, e: True}","{a: True, b: False, c: True, d: False, e: True}","{a: False, b: True, c: True, d: False, e: True}","{a: True, b: True, c: True, d: False, e: True}","{a: False, b: False, c: True, d: True, e: True}","{a: True, b: False, c: True, d: True, e: True}","{a: False, b: True, c: True, d: True, e: True}","{a: True, b: True, c: True, d: True, e: True}","{a: False, b: True, c: False, d: False, e: False}","{a: True, b: True, c: False, d: False, e: False}","{a: False, b: False, c: False, d: True, e: False}","{a: True, b: False, c: False, d: True, e: False}","{a: False, b: True, c: False, d: True, e: False}","{a: True, b: True, c: False, d: True, e: False}","{a: True, b: False, c: False, d: False, e: True}","{a: False, b: True, c: False, d: False, e: True}","{a: False, b: False, c: False, d: True, e: True}","{a: False, b: True, c: False, d: True, e: True}"]},{"j":["Not",["ITE","a","c",["Or","b","b","c"]]],"s":"~ITE(a, c, b | c)","sl":"~c & (a | ~b)","cnf":"~c & (a | ~b)","dnf":"(a & ~c) | (~b & ~c)","tc":"(a | ~b) & (a | ~c) & (~a | ~c)","td":"(a & ~a) | (a & ~c) | (~b & ~c) | (~a & ~b & ~c)","nnf":"(~a | ~c) & (a | (~b & ~c))","nnf0":"(~a | ~c) & (a | (~b & ~c))","anf":"True ^ ITE(a, c, b ^ c ^ (b & c))","g":6,"ic":false,"idn":false,"inn":false,"m":["{a: True, b: False, c: False}","{a: True, b: True, c: False}","{a: False, b: False, c: False}"]},{"j":["Or",["And","a","c"],["Equivalent","b","c"]],"s":"(a & c) | (Equivalent(b, c))","sl":"(b & c) | (a & ~b) | (~b & ~c)","cnf":"(c | ~b) & (a | b | ~c)","dnf":"(b & c) | (a & ~b) | (~b & ~c)","tc":"(c | ~b) & (a | b | ~c) & (a | c | ~b) & (b | c | ~c)","td":"(a & c) | (b & c) | (b & ~b) | (c & ~c) | (~b & ~c)","nnf":"(a & c) | ((b | ~c) & (c | ~b))","nnf0":"(a & c) | ((b | ~c) & (c | ~b))","anf":"b ^ c ^ True ^ (a & c) ^ (a & b & c)","g":4,"ic":false,"idn":false,"inn":false,"m":["{a: True, b: False, c: True}","{a: True, b: True, c: True}","{a: False, b: True, c: True}","{a: True, b: False, c: False}","{a: False, b: False, c: False}"]},{"j":["Or",["ITE","b","c","a"],["Not","a"],["Or","c","a"]],"s":"a | c | ~a | ITE(b, c, a)","sl":"True","cnf":"True","dnf":"True","tc":"(a | b | c | ~a) & (a | c | ~a | ~b)","td":"a | c | ~a | (a & c) | (b & c) | (a & ~b) | (b & ~b)","nnf":"True","nnf0":"a | c | ~a | ((a | b) & (c | ~b))","anf":"True","g":8,"ic":false,"idn":false,"inn":false,"m":["{a: False, b: False, c: True}","{a: False, b: True, c: True}","{a: False, b: False, c: False}","{a: False, b: True, c: False}","{a: True, b: False, c: True}","{a: True, b: True, c: True}","{a: True, b: False, c: False}","{a: True, b: True, c: False}"]},{"j":["Or",["Or","c","b","c"],"d",["Or","d","c","c"]],"s":"b | c | d","sl":"b | c | d","cnf":"b | c | d","dnf":"b | c | d","tc":"b | c | d","td":"b | c | d","nnf":"b | c | d","nnf0":"b | c | d","anf":"b ^ c ^ d ^ (b & c) ^ (b & d) ^ (c & d) ^ (b & c & d)","g":3,"ic":true,"idn":true,"inn":true,"m":["{b: True, c: True, d: True}","{b: True, c: True, d: False}","{b: True, c: False, d: True}","{b: True, c: False, d: False}","{b: False, c: True, d: True}","{b: False, c: True, d: False}","{b: False, c: False, d: True}"]},{"j":["Implies","b","c"],"s":"Implies(b, c)","sl":"c | ~b","cnf":"c | ~b","dnf":"c | ~b","tc":"c | ~b","td":"c | ~b","nnf":"c | ~b","nnf0":"c | ~b","anf":"b ^ True ^ (b & c)","g":0,"ic":false,"idn":false,"inn":false,"m":["{b: False, c: True}","{b: False, c: False}","{b: True, c: True}"]},{"j":["Not",["Or",["And","a","d"],["And","c","a"],["Not","a"]]],"s":"~(~a | (a & c) | (a & d))","sl":"a & ~c & ~d","cnf":"a & ~c & ~d","dnf":"a & ~c & ~d","tc":"a & (~a | ~c) & (~a | ~d)","td":"(a & ~a) | (a & ~a & ~c) | (a & ~a & ~d) | (a & ~c & ~d)","nnf":"a & (~a | ~c) & (~a | ~d)","nnf0":"a & (~a | ~c) & (~a | ~d)","anf":"a ^ (a & c) ^ (a & d) ^ (a & c & d)","g":9,"ic":false,"idn":false,"inn":false,"m":["{a: True, c: False, d: False}"]},{"j":["ITE",["Or",["Xor","c","b"],["And","d","b","e"]],"e",["And",["ITE","b","b","b"],["Xor","e","a","d"]]],"s":"ITE((b ^ c) | (b & d & e), e, b & (a ^ d ^ e))","sl":"(b | c) & (b | e) & (c | e) & (a | d | e) & (e | ~a | ~d) & (d | ~a | ~b | ~c | ~e)","cnf":"(b | c) & (b | e) & (c | e) & (a | d | e) & (e | ~a | ~d) & (d | ~a | ~b | ~c | ~e)","dnf":"(c & d & e) | (b & e & ~c) | (c & e & ~a) | (c & e & ~b) | (b & c & d & ~a) | (a & b & c & ~d & ~e)","tc":"(b | c) & (b | c | d) & (b | c | e) & (b | e | ~c) & (c | e | ~b) & (b | ~b | ~c) & (a | b | c | d | e) & (b | d | ~b | ~c) & (b | e | ~b | ~c) & (e | ~b | ~d | ~e) & (a | b | c | ~d | ~e) & (a | d | e | ~b | ~c) & (b | c | d | ~a | ~e) & (b | c | e | ~a | ~d) & (a | b | c | d | ~d | ~e) & (a | b | c | e | ~d | ~e) & (a | b | d | e | ~b | ~c) & (b | c | d | e | ~a | ~d) & (b | c | d | e | ~a | ~e) & (d | ~a | ~b | ~c | ~e) & (e | ~a | ~b | ~c | ~d) & (a | b | ~b | ~c | ~d | ~e) & (a | d | ~b | ~c | ~d | ~e) & (a | e | ~b | ~c | ~d | ~e) & (b | d | ~a | ~b | ~c | ~e) & (b | e | ~a | ~b | ~c | ~d) & (d | e | ~a | ~b | ~c | ~d) & (d | e | ~a | ~b | ~c | ~e)","td":"(b & ~b) | (b & d & e) | (b & c & ~b) | (b & e & ~b) | (b & e & ~c) | (b & e & ~e) | (c & e & ~b) | (c & e & ~c) | (a & b & d & e) | (b & ~b & ~c) | (b & ~b & ~d) | (b & ~b & ~e) | (c & ~b & ~c) | (c & ~c & ~d) | (c & ~c & ~e) | (a & b & e & ~a) | (a & b & e & ~e) | (b & c & d & ~d) | (b & c & e & ~e) | (b & d & e & ~b) | (b & d & e & ~d) | (b & d & e & ~e) | (a & b & ~a & ~b) | (b & c & ~b & ~c) | (b & c & ~b & ~d) | (b & c & ~b & ~e) | (b & c & ~c & ~d) | (b & c & ~c & ~e) | (b & d & ~b & ~d) | (b & e & ~a & ~d) | (b & e & ~a & ~e) | (b & e & ~b & ~e) | (b & e & ~d & ~e) | (a & b & c & d & ~d) | (a & b & c & e & ~e) | (a & b & d & e & ~a) | (a & b & d & e & ~b) | (a & b & d & e & ~d) | (a & b & d & e & ~e) | (b & c & d & e & ~b) | (b & c & d & e & ~d) | (b & c & d & e & ~e) | (b & ~b & ~c & ~d) | (b & ~b & ~c & ~e) | (c & ~b & ~c & ~d) | (c & ~b & ~c & ~e) | (a & b & c & ~a & ~b) | (a & b & c & ~a & ~d) | (a & b & c & ~a & ~e) | (a & b & c & ~d & ~e) | (a & b & d & ~a & ~b) | (a & b & d & ~b & ~d) | (a & b & e & ~a & ~b) | (a & b & e & ~a & ~d) | (a & b & e & ~a & ~e) | (a & b & e & ~b & ~e) | (a & b & e & ~d & ~e) | (b & c & d & ~a & ~d) | (b & c & d & ~a & ~e) | (b & c & d & ~b & ~d) | (b & c & d & ~c & ~d) | (b & c & d & ~d & ~e) | (b & c & e & ~a & ~d) | (b & c & e & ~a & ~e) | (b & c & e & ~b & ~e) | (b & c & e & ~c & ~e) | (b & c & e & ~d & ~e) | (b & d & e & ~a & ~d) | (b & d & e & ~a & ~e) | (b & d & e & ~b & ~c) | (b & d & e & ~b & ~d) | (b & d & e & ~b & ~e) | (b & d & e & ~d & ~e) | (a & b & c & d & e & ~b) | (a & b & c & d & e & ~d) | (a & b & c & d & e & ~e) | (a & b & ~a & ~b & ~c) | (a & b & ~a & ~b & ~d) | (a & b & ~a & ~b & ~e) | (a & b & ~b & ~d & ~e) | (b & c & ~b & ~c & ~d) | (b & c & ~b & ~c & ~e) | (b & d & ~a & ~b & ~d) | (b & d & ~a & ~b & ~e) | (b & d & ~b & ~c & ~d) | (b & d & ~b & ~d & ~e) | (b & e & ~a & ~b & ~d) | (b & e & ~a & ~b & ~e) | (b & e & ~a & ~d & ~e) | (b & e & ~b & ~c & ~e) | (b & e & ~b & ~d & ~e) | (a & b & c & d & ~a & ~b) | (a & b & c & d & ~a & ~d) | (a & b & c & d & ~a & ~e) | (a & b & c & d & ~b & ~d) | (a & b & c & d & ~c & ~d) | (a & b & c & d & ~d & ~e) | (a & b & c & e & ~a & ~b) | (a & b & c & e & ~a & ~d) | (a & b & c & e & ~a & ~e) | (a & b & c & e & ~b & ~e) | (a & b & c & e & ~c & ~e) | (a & b & c & e & ~d & ~e) | (a & b & d & e & ~a & ~b) | (a & b & d & e & ~a & ~d) | (a & b & d & e & ~a & ~e) | (a & b & d & e & ~b & ~c) | (a & b & d & e & ~b & ~d) | (a & b & d & e & ~b & ~e) | (a & b & d & e & ~d & ~e) | (b & c & d & e & ~a & ~d) | (b & c & d & e & ~a & ~e) | (b & c & d & e & ~b & ~c) | (b & c & d & e & ~b & ~d) | (b & c & d & e & ~b & ~e) | (b & c & d & e & ~c & ~d) | (b & c & d & e & ~c & ~e) | (b & c & d & e & ~d & ~e) | (a & b & c & ~a & ~b & ~c) | (a & b & c & ~a & ~b & ~d) | (a & b & c & ~a & ~b & ~e) | (a & b & c & ~a & ~c & ~d) | (a & b & c & ~a & ~c & ~e) | (a & b & c & ~a & ~d & ~e) | (a & b & c & ~b & ~d & ~e) | (a & b & c & ~c & ~d & ~e) | (a & b & d & ~a & ~b & ~c) | (a & b & d & ~a & ~b & ~d) | (a & b & d & ~a & ~b & ~e) | (a & b & d & ~b & ~c & ~d) | (a & b & d & ~b & ~d & ~e) | (a & b & e & ~a & ~b & ~c) | (a & b & e & ~a & ~b & ~d) | (a & b & e & ~a & ~b & ~e) | (a & b & e & ~a & ~d & ~e) | (a & b & e & ~b & ~c & ~e) | (a & b & e & ~b & ~d & ~e) | (b & c & d & ~a & ~b & ~d) | (b & c & d & ~a & ~b & ~e) | (b & c & d & ~a & ~c & ~d) | (b & c & d & ~a & ~c & ~e) | (b & c & d & ~a & ~d & ~e) | (b & c & d & ~b & ~c & ~d) | (b & c & d & ~b & ~d & ~e) | (b & c & d & ~c & ~d & ~e) | (b & c & e & ~a & ~b & ~d) | (b & c & e & ~a & ~b & ~e) | (b & c & e & ~a & ~c & ~d) | (b & c & e & ~a & ~c & ~e) | (b & c & e & ~a & ~d & ~e) | (b & c & e & ~b & ~c & ~e) | (b & c & e & ~b & ~d & ~e) | (b & c & e & ~c & ~d & ~e) | (b & d & e & ~a & ~b & ~d) | (b & d & e & ~a & ~b & ~e) | (b & d & e & ~a & ~d & ~e) | (b & d & e & ~b & ~c & ~d) | (b & d & e & ~b & ~c & ~e) | (b & d & e & ~b & ~d & ~e) | (a & b & c & d & e & ~a & ~b) | (a & b & c & d & e & ~a & ~d) | (a & b & c & d & e & ~a & ~e) | (a & b & c & d & e & ~b & ~c) | (a & b & c & d & e & ~b & ~d) | (a & b & c & d & e & ~b & ~e) | (a & b & c & d & e & ~c & ~d) | (a & b & c & d & e & ~c & ~e) | (a & b & c & d & e & ~d & ~e) | (a & b & ~a & ~b & ~c & ~d) | (a & b & ~a & ~b & ~c & ~e) | (a & b & ~a & ~b & ~d & ~e) | (a & b & ~b & ~c & ~d & ~e) | (b & d & ~a & ~b & ~c & ~d) | (b & d & ~a & ~b & ~c & ~e) | (b & d & ~a & ~b & ~d & ~e) | (b & d & ~b & ~c & ~d & ~e) | (b & e & ~a & ~b & ~c & ~d) | (b & e & ~a & ~b & ~c & ~e) | (b & e & ~a & ~b & ~d & ~e) | (b & e & ~b & ~c & ~d & ~e) | (a & b & c & d & ~a & ~b & ~c) | (a & b & c & d & ~a & ~b & ~d) | (a & b & c & d & ~a & ~b & ~e) | (a & b & c & d & ~a & ~c & ~d) | (a & b & c & d & ~a & ~c & ~e) | (a & b & c & d & ~a & ~d & ~e) | (a & b & c & d & ~b & ~c & ~d) | (a & b & c & d & ~b & ~d & ~e) | (a & b & c & d & ~c & ~d & ~e) | (a & b & c & e & ~a & ~b & ~c) | (a & b & c & e & ~a & ~b & ~d) | (a & b & c & e & ~a & ~b & ~e) | (a & b & c & e & ~a & ~c & ~d) | (a & b & c & e & ~a & ~c & ~e) | (a & b & c & e & ~a & ~d & ~e) | (a & b & c & e & ~b & ~c & ~e) | (a & b & c & e & ~b & ~d & ~e) | (a & b & c & e & ~c & ~d & ~e) | (a & b & d & e & ~a & ~b & ~c) | (a & b & d & e & ~a & ~b & ~d) | (a & b & d & e & ~a & ~b & ~e) | (a & b & d & e & ~b & ~c & ~d) | (a & b & d & e & ~b & ~c & ~e) | (a & b & d & e & ~b & ~d & ~e) | (b & c & d & e & ~a & ~b & ~d) | (b & c & d & e & ~a & ~b & ~e) | (b & c & d & e & ~a & ~c & ~d) | (b & c & d & e & ~a & ~c & ~e) | (b & c & d & e & ~a & ~d & ~e) | (b & c & d & e & ~b & ~c & ~d) | (b & c & d & e & ~b & ~c & ~e) | (b & c & d & e & ~b & ~d & ~e) | (b & c & d & e & ~c & ~d & ~e) | (a & b & c & ~a & ~b & ~c & ~d) | (a & b & c & ~a & ~b & ~c & ~e) | (a & b & c & ~a & ~b & ~d & ~e) | (a & b & c & ~a & ~c & ~d & ~e) | (a & b & c & ~b & ~c & ~d & ~e) | (a & b & d & ~a & ~b & ~c & ~d) | (a & b & d & ~a & ~b & ~c & ~e) | (a & b & d & ~a & ~b & ~d & ~e) | (a & b & d & ~b & ~c & ~d & ~e) | (a & b & e & ~a & ~b & ~c & ~d) | (a & b & e & ~a & ~b & ~c & ~e) | (a & b & e & ~a & ~b & ~d & ~e) | (a & b & e & ~b & ~c & ~d & ~e) | (b & c & d & ~a & ~b & ~c & ~d) | (b & c & d & ~a & ~b & ~c & ~e) | (b & c & d & ~a & ~b & ~d & ~e) | (b & c & d & ~a & ~c & ~d & ~e) | (b & c & d & ~b & ~c & ~d & ~e) | (b & c & e & ~a & ~b & ~c & ~d) | (b & c & e & ~a & ~b & ~c & ~e) | (b & c & e & ~a & ~b & ~d & ~e) | (b & c & e & ~a & ~c & ~d & ~e) | (b & c & e & ~b & ~c & ~d & ~e) | (b & d & e & ~a & ~b & ~c & ~d) | (b & d & e & ~a & ~b & ~c & ~e) | (b & d & e & ~a & ~b & ~d & ~e) | (b & d & e & ~b & ~c & ~d & ~e) | (a & b & c & d & e & ~a & ~b & ~c) | (a & b & c & d & e & ~a & ~c & ~d) | (a & b & c & d & e & ~a & ~c & ~e) | (a & b & c & d & e & ~b & ~c & ~d) | (a & b & c & d & e & ~b & ~c & ~e) | (a & b & c & d & e & ~c & ~d & ~e) | (a & b & ~a & ~b & ~c & ~d & ~e) | (b & d & ~a & ~b & ~c & ~d & ~e) | (b & e & ~a & ~b & ~c & ~d & ~e) | (a & b & c & d & ~a & ~b & ~c & ~d) | (a & b & c & d & ~a & ~b & ~c & ~e) | (a & b & c & d & ~a & ~c & ~d & ~e) | (a & b & c & d & ~b & ~c & ~d & ~e) | (a & b & c & e & ~a & ~b & ~c & ~d) | (a & b & c & e & ~a & ~b & ~c & ~e) | (a & b & c & e & ~a & ~c & ~d & ~e) | (a & b & c & e & ~b & ~c & ~d & ~e) | (a & b & d & e & ~a & ~b & ~c & ~d) | (a & b & d & e & ~a & ~b & ~c & ~e) | (a & b & d & e & ~b & ~c & ~d & ~e) | (b & c & d & e & ~a & ~b & ~c & ~d) | (b & c & d & e & ~a & ~b & ~c & ~e) | (b & c & d & e & ~a & ~c & ~d & ~e) | (b & c & d & e & ~b & ~c & ~d & ~e) | (a & b & c & ~a & ~b & ~c & ~d & ~e) | (a & b & d & ~a & ~b & ~c & ~d & ~e) | (a & b & e & ~a & ~b & ~c & ~d & ~e) | (b & c & d & ~a & ~b & ~c & ~d & ~e) | (b & c & e & ~a & ~b & ~c & ~d & ~e) | (b & d & e & ~a & ~b & ~c & ~d & ~e)","nnf":"(e | ((b | ~c) & (c | ~b) & (~b | ~d | ~e))) & ((b & d & e) | ((b | c) & (~b | ~c)) | (b & (a | d | e) & (a | ~d | ~e) & (d | ~a | ~e) & (e | ~a | ~d)))","nnf0":"(e | ((b | ~c) & (c | ~b) & (~b | ~d | ~e))) & ((b & d & e) | ((b | c) & (~b | ~c)) | (b & (a | d | e) & (a | ~d | ~e) & (d | ~a | ~e) & (e | ~a | ~d)))","anf":"ITE(b ^ c ^ (b & c & d & e), e, (a & b) ^ (b & d) ^ (b & e))","g":15,"ic":false,"idn":false,"inn":false,"m":["{a: False, b: True, c: False, d: True, e: True}","{a: True, b: True, c: False, d: True, e: True}","{a: False, b: True, c: False, d: False, e: True}","{a: True, b: True, c: False, d: False, e: True}","{a: False, b: True, c: True, d: True, e: True}","{a: True, b: True, c: True, d: True, e: True}","{a: False, b: True, c: True, d: False, e: True}","{a: False, b: True, c: True, d: True, e: False}","{a: True, b: True, c: True, d: False, e: False}","{a: False, b: False, c: True, d: True, e: True}","{a: True, b: False, c: True, d: True, e: True}","{a: False, b: False, c: True, d: False, e: True}","{a: True, b: False, c: True, d: False, e: True}"]},{"j":["And",["And","c","e","c"],"b"],"s":"b & c & e","sl":"b & c & e","cnf":"b & c & e","dnf":"b & c & e","tc":"b & c & e","td":"b & c & e","nnf":"b & c & e","nnf0":"b & c & e","anf":"b & c & e","g":3,"ic":true,"idn":true,"inn":true,"m":["{b: True, c: True, e: True}"]},{"j":["And","b",["Not","d"]],"s":"b & ~d","sl":"b & ~d","cnf":"b & ~d","dnf":"b & ~d","tc":"b & ~d","td":"b & ~d","nnf":"b & ~d","nnf0":"b & ~d","anf":"b ^ (b & d)","g":3,"ic":true,"idn":true,"inn":true,"m":["{b: True, d: False}"]},{"j":"e","s":"e","sl":"e","cnf":"e","dnf":"e","tc":"e","td":"e","nnf":"e","nnf0":"e","anf":"e","g":0,"ic":true,"idn":true,"inn":true,"m":["{e: True}"]},{"j":["And","a","c","a"],"s":"a & c","sl":"a & c","cnf":"a & c","dnf":"a & c","tc":"a & c","td":"a & c","nnf":"a & c","nnf0":"a & c","anf":"a & c","g":2,"ic":true,"idn":true,"inn":true,"m":["{a: True, c: True}"]},{"j":["Not",["Or","b","d"]],"s":"~(b | d)","sl":"~b & ~d","cnf":"~b & ~d","dnf":"~b & ~d","tc":"~b & ~d","td":"~b & ~d","nnf":"~b & ~d","nnf0":"~b & ~d","anf":"b ^ d ^ True ^ (b & d)","g":3,"ic":false,"idn":false,"inn":false,"m":["{b: False, d: False}"]},{"j":["ITE",["Or","e","a"],["Implies","d","d"],"c"],"s":"ITE(a | e, True, c)","sl":"a | c | e","cnf":"a | c | e","dnf":"a | c | e","tc":"a | c | e","td":"a | c | e","nnf":"a | c | e","nnf0":"a | c | e","anf":"ITE(a ^ e ^ (a & e), True, c)","g":5,"ic":false,"idn":false,"inn":false,"m":["{a: False, c: True, e: False, True: True}","{a: True, c: True, e: False, True: True}","{a: True, c: False, e: False, True: True}","{a: False, c: True, e: True, True: True}","{a: False, c: False, e: True, True: True}","{a: True, c: True, e: True, True: True}","{a: True, c: False, e: True, True: True}","{a: False, c: True, e: False, True: False}"]}];
const QM: QmCase[] = [{"v":["a","b","c","d","e"],"mins":[0,2,4,5,6,7,10,11,12,13,14,15,16,17,19,20,21,23,25,27,28,29,30],"dcs":[8,22,31],"sop":"c | (a & e) | (~a & ~e) | (b & d & ~a) | (~b & ~d & ~e)","pos":"(a | b | c | ~e) & (a | c | d | ~e) & (c | e | ~a | ~b) & (c | e | ~a | ~d)"},{"v":["a","b","c","d","e"],"mins":[2,4,6,9,11,12,15,16,18,19,20,21,22,23,24,25,26,27,29,31],"dcs":[],"sop":"(a & c & e) | (b & d & e) | (a & d & ~b) | (b & e & ~c) | (a & ~b & ~e) | (a & ~c & ~e) | (d & ~b & ~e) | (c & ~a & ~d & ~e)","pos":"(a | b | ~e) & (a | c | d | e) & (b | c | d | ~e) & (a | d | ~c | ~e) & (a | e | ~b | ~d) & (e | ~a | ~b | ~c)"},{"v":["a","b","c","d"],"mins":[0,2,3,5,6,9,14],"dcs":[10],"sop":"(c & ~d) | (c & ~a & ~b) | (~a & ~b & ~d) | (a & d & ~b & ~c) | (b & d & ~a & ~c)","pos":"(c | d | ~a) & (c | d | ~b) & (b | ~a | ~c) & (c | ~a | ~b) & (a | b | c | ~d) & (~b | ~c | ~d)"},{"v":["a","b","c"],"mins":[2,3,5,6],"dcs":[],"sop":"(b & ~a) | (b & ~c) | (a & c & ~b)","pos":"(a | b) & (b | c) & (~a | ~b | ~c)"},{"v":["a","b","c","d"],"mins":[2,4,5,7,9,10],"dcs":[0,3,13],"sop":"(a & d & ~c) | (b & d & ~a) | (b & ~a & ~c) | (c & ~b & ~d)","pos":"(a | b | c) & (c | d | ~a) & (d | ~b | ~c) & (~a | ~c | ~d)"},{"v":["a","b","c"],"mins":[1,2,4],"dcs":[],"sop":"(a & ~b & ~c) | (b & ~a & ~c) | (c & ~a & ~b)","pos":"(a | b | c) & (~a | ~b) & (~a | ~c) & (~b | ~c)"},{"v":["a","b","c","d"],"mins":[0,1,2,3,5,6,7,8,9,10,11,12,13,14,15],"dcs":[4],"sop":"True","pos":"True"},{"v":["a","b","c","d","e"],"mins":[0,2,5,6,9,10,12,13,14,15,16,19,20,21,23,25,26,27,29,30,31],"dcs":[17,22],"sop":"(a & e) | (b & c & ~a) | (b & d & ~e) | (b & e & ~d) | (c & e & ~d) | (a & ~b & ~d) | (d & ~a & ~e) | (~a & ~b & ~c & ~e)","pos":"(a | b | c | ~e) & (c | d | e | ~b) & (a | b | ~d | ~e) & (a | c | ~d | ~e) & (b | e | ~a | ~d) & (d | e | ~a | ~b) & (a | b | d | e | ~c)"},{"v":["a","b","c","d"],"mins":[0,2,3,4,5,6,7,8,9,10,11,13,14,15],"dcs":[12],"sop":"a | b | c | ~d","pos":"a | b | c | ~d"},{"v":["a","b","c","d"],"mins":[0,1,2,4,5,6,7,8,9,10,11,12,13,14],"dcs":[3,15],"sop":"True","pos":"True"},{"v":["a","b","c","d"],"mins":[1,4,10,13],"dcs":[2,3],"sop":"(c & ~b & ~d) | (d & ~a & ~b) | (a & b & d & ~c) | (b & ~a & ~c & ~d)","pos":"(b | c | d) & (~b | ~c) & (c | d | ~a) & (a | ~b | ~d) & (b | ~a | ~d)"},{"v":["a","b","c","d"],"mins":[0,1,4,5,7,8,9,10,11,14,15],"dcs":[12],"sop":"(a & c) | (~a & ~c) | (~b & ~c) | (b & d & ~a)","pos":"(a | b | ~c) & (a | d | ~c) & (c | ~a | ~b)"},{"v":["a","b","c"],"mins":[7],"dcs":[1,5],"sop":"a & c","pos":"a & c"},{"v":["a","b","c","d","e"],"mins":[0,1,2,3,5,6,7,8,9,10,11,13,14,15,16,17,18,19,20,21,22,27,28,29,30,31],"dcs":[4,23,24],"sop":"~b | (a & c) | (d & e) | (d & ~a) | (e & ~a) | (~a & ~c)","pos":"(a | d | e | ~c) & (c | d | ~a | ~b) & (c | e | ~a | ~b)"},{"v":["a","b","c"],"mins":[1,2,3,7],"dcs":[0,4,5],"sop":"c | ~a","pos":"c | ~a"},{"v":["a","b","c"],"mins":[0,3],"dcs":[],"sop":"(b & c & ~a) | (~a & ~b & ~c)","pos":"~a & (b | ~c) & (c | ~b)"},{"v":["a","b","c"],"mins":[1,4,5,6,7],"dcs":[],"sop":"a | (c & ~b)","pos":"(a | c) & (a | ~b)"},{"v":["a","b","c"],"mins":[0,3,4,5,6,7],"dcs":[1,2],"sop":"True","pos":"True"},{"v":["a","b","c"],"mins":[1,2,3,7],"dcs":[0,5,6],"sop":"c | ~a","pos":"b | c"},{"v":["a","b","c"],"mins":[2,4,7],"dcs":[3,6],"sop":"b | (a & ~c)","pos":"(a | b) & (b | ~c)"},{"v":["a","b","c","d","e"],"mins":[0,1,2,3,4,5,6,10,12,13,15,16,19,20,21,22,23,25,26,28,29,30,31],"dcs":[8,14],"sop":"(a & c) | (b & c) | (~a & ~e) | (b & d & ~e) | (a & b & e & ~d) | (~a & ~b & ~d) | (~b & ~d & ~e) | (d & e & ~b & ~c)","pos":"(a | c | d | ~b) & (c | d | e | ~b) & (c | ~b | ~d | ~e) & (b | c | d | ~a | ~e) & (b | c | e | ~a | ~d) & (a | b | ~c | ~d | ~e)"},{"v":["a","b","c","d"],"mins":[1,3,4,5,6,9,11,12,14,15],"dcs":[],"sop":"(b & ~d) | (d & ~b) | (a & c & d) | (d & ~a & ~c)","pos":"(b | d) & (a | ~b | ~c | ~d) & (c | ~a | ~b | ~d)"},{"v":["a","b","c","d","e"],"mins":[3,10,19,21,27,28],"dcs":[23,24],"sop":"(a & c & e & ~b) | (a & d & e & ~c) | (a & b & ~d & ~e) | (d & e & ~b & ~c) | (b & d & ~a & ~c & ~e)","pos":"(b | e) & (c | d) & (a | ~c) & (a | ~b | ~e) & (e | ~a | ~d) & (~b | ~c | ~e)"},{"v":["a","b","c"],"mins":[2,3],"dcs":[],"sop":"b & ~a","pos":"b & ~a"},{"v":["a","b","c"],"mins":[0,2,3,4,5],"dcs":[],"sop":"(a & ~b) | (b & ~a) | (~a & ~c)","pos":"(~a | ~b) & (a | b | ~c)"},{"v":["a","b","c","d","e"],"mins":[8],"dcs":[10,25],"sop":"b & ~a & ~c & ~e","pos":"b & ~a & ~c & ~e"},{"v":["a","b","c","d"],"mins":[0,1,3,5,6,7,8,14,15],"dcs":[9],"sop":"(b & c) | (d & ~a) | (~b & ~c)","pos":"(b | d | ~c) & (c | d | ~b) & (b | ~a | ~c) & (c | ~a | ~b)"},{"v":["a","b","c","d"],"mins":[2,6,7,9,10,11,12,13,14],"dcs":[3,5],"sop":"(c & ~a) | (c & ~d) | (a & b & ~c) | (a & d & ~b)","pos":"(a | c) & (b | c | d) & (~a | ~b | ~c | ~d)"},{"v":["a","b","c","d"],"mins":[7,12],"dcs":[],"sop":"(b & c & d & ~a) | (a & b & ~c & ~d)","pos":"b & (a | c) & (d | ~c) & (~a | ~d)"},{"v":["a","b","c","d"],"mins":[2,4,5,6,8,9,10,13],"dcs":[11,15],"sop":"(a & ~b) | (b & d & ~c) | (b & ~a & ~c) | (c & ~a & ~d)","pos":"(a | b | c) & (~c | ~d) & (d | ~a | ~b)"}];

const build = (t: Tree): Expr => {
  if (typeof t === 'string') return sj.symbol(t);
  const [op, ...rest] = t;
  const xs = rest.map(build);
  switch (op) {
    case 'And':
      return And(...xs);
    case 'Or':
      return Or(...xs);
    case 'Not':
      return Not(xs[0]!);
    case 'Xor':
      return Xor(...xs);
    case 'Implies':
      return L.Implies(...xs);
    case 'Equivalent':
      return L.Equivalent(...xs);
    default:
      return L.ITE(xs[0]!, xs[1]!, xs[2]!);
  }
};

describe('cross-check with SymPy on generated expressions', () => {
  it.each(CASES.map((c) => [c.s, c] as const))('%s', (_, c) => {
    const e = build(c.j);
    expect(s(e)).toBe(c.s);
    expect(s(L.simplifyLogic(e))).toBe(c.sl);
    expect(s(L.simplifyLogic(e, 'cnf'))).toBe(c.cnf);
    expect(s(L.simplifyLogic(e, 'dnf'))).toBe(c.dnf);
    expect(s(L.toCnf(e))).toBe(c.tc);
    expect(s(L.toDnf(e))).toBe(c.td);
    expect(s(L.toNnf(e))).toBe(c.nnf);
    expect(s(L.toNnf(e, false))).toBe(c.nnf0);
    expect(s(L.toAnf(e))).toBe(c.anf);
    expect(L.gateinputcount(e)).toBe(c.g);
    expect([L.isCnf(e), L.isDnf(e), L.isNnf(e)]).toEqual([c.ic, c.idn, c.inn]);
    expect([...L.satisfiable(e, { allModels: true })].map((m) => dict(m))).toEqual(c.m);
  });

  it.each(QM.map((q) => [`${q.v.join('')} ${q.mins.join(',')} / ${q.dcs.join(',')}`, q] as const))('SOPform/POSform %s', (_, q) => {
    const vars = q.v.map((n) => sj.symbol(n));
    expect(s(L.SOPform(vars, q.mins, q.dcs))).toBe(q.sop);
    expect(s(L.POSform(vars, q.mins, q.dcs))).toBe(q.pos);
  });
});

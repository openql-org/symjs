// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/logic/minimize.ts.
// SOPform, POSform and logic minimization. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import type { Expr } from '../../src';
import * as L from '../../src/logic';
import * as boolalg from '../../src/logic/boolalg';

const s = (e: unknown): string => sj.str(e as Expr);
const syms = (names: string): Expr[] => sj.symbols(names) as Expr[];
const [x, y, z, w] = syms('x y z w') as [Expr, Expr, Expr, Expr];
const [A, B] = syms('A B C D') as [Expr, Expr, Expr, Expr];
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
interface QmCase { v: string[]; mins: number[]; dcs: number[]; sop: string; pos: string }
const QM: QmCase[] = [{"v":["a","b","c","d","e"],"mins":[0,2,4,5,6,7,10,11,12,13,14,15,16,17,19,20,21,23,25,27,28,29,30],"dcs":[8,22,31],"sop":"c | (a & e) | (~a & ~e) | (b & d & ~a) | (~b & ~d & ~e)","pos":"(a | b | c | ~e) & (a | c | d | ~e) & (c | e | ~a | ~b) & (c | e | ~a | ~d)"},{"v":["a","b","c","d","e"],"mins":[2,4,6,9,11,12,15,16,18,19,20,21,22,23,24,25,26,27,29,31],"dcs":[],"sop":"(a & c & e) | (b & d & e) | (a & d & ~b) | (b & e & ~c) | (a & ~b & ~e) | (a & ~c & ~e) | (d & ~b & ~e) | (c & ~a & ~d & ~e)","pos":"(a | b | ~e) & (a | c | d | e) & (b | c | d | ~e) & (a | d | ~c | ~e) & (a | e | ~b | ~d) & (e | ~a | ~b | ~c)"},{"v":["a","b","c","d"],"mins":[0,2,3,5,6,9,14],"dcs":[10],"sop":"(c & ~d) | (c & ~a & ~b) | (~a & ~b & ~d) | (a & d & ~b & ~c) | (b & d & ~a & ~c)","pos":"(c | d | ~a) & (c | d | ~b) & (b | ~a | ~c) & (c | ~a | ~b) & (a | b | c | ~d) & (~b | ~c | ~d)"},{"v":["a","b","c"],"mins":[2,3,5,6],"dcs":[],"sop":"(b & ~a) | (b & ~c) | (a & c & ~b)","pos":"(a | b) & (b | c) & (~a | ~b | ~c)"},{"v":["a","b","c","d"],"mins":[2,4,5,7,9,10],"dcs":[0,3,13],"sop":"(a & d & ~c) | (b & d & ~a) | (b & ~a & ~c) | (c & ~b & ~d)","pos":"(a | b | c) & (c | d | ~a) & (d | ~b | ~c) & (~a | ~c | ~d)"},{"v":["a","b","c"],"mins":[1,2,4],"dcs":[],"sop":"(a & ~b & ~c) | (b & ~a & ~c) | (c & ~a & ~b)","pos":"(a | b | c) & (~a | ~b) & (~a | ~c) & (~b | ~c)"},{"v":["a","b","c","d"],"mins":[0,1,2,3,5,6,7,8,9,10,11,12,13,14,15],"dcs":[4],"sop":"True","pos":"True"},{"v":["a","b","c","d","e"],"mins":[0,2,5,6,9,10,12,13,14,15,16,19,20,21,23,25,26,27,29,30,31],"dcs":[17,22],"sop":"(a & e) | (b & c & ~a) | (b & d & ~e) | (b & e & ~d) | (c & e & ~d) | (a & ~b & ~d) | (d & ~a & ~e) | (~a & ~b & ~c & ~e)","pos":"(a | b | c | ~e) & (c | d | e | ~b) & (a | b | ~d | ~e) & (a | c | ~d | ~e) & (b | e | ~a | ~d) & (d | e | ~a | ~b) & (a | b | d | e | ~c)"},{"v":["a","b","c","d"],"mins":[0,2,3,4,5,6,7,8,9,10,11,13,14,15],"dcs":[12],"sop":"a | b | c | ~d","pos":"a | b | c | ~d"},{"v":["a","b","c","d"],"mins":[0,1,2,4,5,6,7,8,9,10,11,12,13,14],"dcs":[3,15],"sop":"True","pos":"True"},{"v":["a","b","c","d"],"mins":[1,4,10,13],"dcs":[2,3],"sop":"(c & ~b & ~d) | (d & ~a & ~b) | (a & b & d & ~c) | (b & ~a & ~c & ~d)","pos":"(b | c | d) & (~b | ~c) & (c | d | ~a) & (a | ~b | ~d) & (b | ~a | ~d)"},{"v":["a","b","c","d"],"mins":[0,1,4,5,7,8,9,10,11,14,15],"dcs":[12],"sop":"(a & c) | (~a & ~c) | (~b & ~c) | (b & d & ~a)","pos":"(a | b | ~c) & (a | d | ~c) & (c | ~a | ~b)"},{"v":["a","b","c"],"mins":[7],"dcs":[1,5],"sop":"a & c","pos":"a & c"},{"v":["a","b","c","d","e"],"mins":[0,1,2,3,5,6,7,8,9,10,11,13,14,15,16,17,18,19,20,21,22,27,28,29,30,31],"dcs":[4,23,24],"sop":"~b | (a & c) | (d & e) | (d & ~a) | (e & ~a) | (~a & ~c)","pos":"(a | d | e | ~c) & (c | d | ~a | ~b) & (c | e | ~a | ~b)"},{"v":["a","b","c"],"mins":[1,2,3,7],"dcs":[0,4,5],"sop":"c | ~a","pos":"c | ~a"},{"v":["a","b","c"],"mins":[0,3],"dcs":[],"sop":"(b & c & ~a) | (~a & ~b & ~c)","pos":"~a & (b | ~c) & (c | ~b)"},{"v":["a","b","c"],"mins":[1,4,5,6,7],"dcs":[],"sop":"a | (c & ~b)","pos":"(a | c) & (a | ~b)"},{"v":["a","b","c"],"mins":[0,3,4,5,6,7],"dcs":[1,2],"sop":"True","pos":"True"},{"v":["a","b","c"],"mins":[1,2,3,7],"dcs":[0,5,6],"sop":"c | ~a","pos":"b | c"},{"v":["a","b","c"],"mins":[2,4,7],"dcs":[3,6],"sop":"b | (a & ~c)","pos":"(a | b) & (b | ~c)"},{"v":["a","b","c","d","e"],"mins":[0,1,2,3,4,5,6,10,12,13,15,16,19,20,21,22,23,25,26,28,29,30,31],"dcs":[8,14],"sop":"(a & c) | (b & c) | (~a & ~e) | (b & d & ~e) | (a & b & e & ~d) | (~a & ~b & ~d) | (~b & ~d & ~e) | (d & e & ~b & ~c)","pos":"(a | c | d | ~b) & (c | d | e | ~b) & (c | ~b | ~d | ~e) & (b | c | d | ~a | ~e) & (b | c | e | ~a | ~d) & (a | b | ~c | ~d | ~e)"},{"v":["a","b","c","d"],"mins":[1,3,4,5,6,9,11,12,14,15],"dcs":[],"sop":"(b & ~d) | (d & ~b) | (a & c & d) | (d & ~a & ~c)","pos":"(b | d) & (a | ~b | ~c | ~d) & (c | ~a | ~b | ~d)"},{"v":["a","b","c","d","e"],"mins":[3,10,19,21,27,28],"dcs":[23,24],"sop":"(a & c & e & ~b) | (a & d & e & ~c) | (a & b & ~d & ~e) | (d & e & ~b & ~c) | (b & d & ~a & ~c & ~e)","pos":"(b | e) & (c | d) & (a | ~c) & (a | ~b | ~e) & (e | ~a | ~d) & (~b | ~c | ~e)"},{"v":["a","b","c"],"mins":[2,3],"dcs":[],"sop":"b & ~a","pos":"b & ~a"},{"v":["a","b","c"],"mins":[0,2,3,4,5],"dcs":[],"sop":"(a & ~b) | (b & ~a) | (~a & ~c)","pos":"(~a | ~b) & (a | b | ~c)"},{"v":["a","b","c","d","e"],"mins":[8],"dcs":[10,25],"sop":"b & ~a & ~c & ~e","pos":"b & ~a & ~c & ~e"},{"v":["a","b","c","d"],"mins":[0,1,3,5,6,7,8,14,15],"dcs":[9],"sop":"(b & c) | (d & ~a) | (~b & ~c)","pos":"(b | d | ~c) & (c | d | ~b) & (b | ~a | ~c) & (c | ~a | ~b)"},{"v":["a","b","c","d"],"mins":[2,6,7,9,10,11,12,13,14],"dcs":[3,5],"sop":"(c & ~a) | (c & ~d) | (a & b & ~c) | (a & d & ~b)","pos":"(a | c) & (b | c | d) & (~a | ~b | ~c | ~d)"},{"v":["a","b","c","d"],"mins":[7,12],"dcs":[],"sop":"(b & c & d & ~a) | (a & b & ~c & ~d)","pos":"b & (a | c) & (d | ~c) & (~a | ~d)"},{"v":["a","b","c","d"],"mins":[2,4,5,6,8,9,10,13],"dcs":[11,15],"sop":"(a & ~b) | (b & d & ~c) | (b & ~a & ~c) | (c & ~a & ~d)","pos":"(a | b | c) & (~c | ~d) & (d | ~a | ~b)"}];

describe('cross-check with SymPy on generated expressions', () => {
  it.each(QM.map((q) => [`${q.v.join('')} ${q.mins.join(',')} / ${q.dcs.join(',')}`, q] as const))('SOPform/POSform %s', (_, q) => {
    const vars = q.v.map((n) => sj.symbol(n));
    expect(s(L.SOPform(vars, q.mins, q.dcs))).toBe(q.sop);
    expect(s(L.POSform(vars, q.mins, q.dcs))).toBe(q.pos);
  });
});

// Coverage of logic/*.ts. Expected values are the str() of SymPy 1.14.

const strOf = (e: unknown): string => String(e);

describe('minimization', () => {
  it('simplify_logic with constants among the predicates, deep=False', () => {
    expect(strOf(L.simplifyLogic(L.Nand(x, true, { evaluate: false })))).toBe('~x');
    expect(strOf(L.simplifyLogic(L.Nand(x, false, { evaluate: false })))).toBe('True');
    expect(strOf(L.simplifyLogic(L.Nand(x, 1, { evaluate: false })))).toBe('~x');
    expect(strOf(L.simplifyLogic(L.Nand(x, 0, { evaluate: false })))).toBe('True');
    expect(strOf(L.simplifyLogic(L.ITE(x, y, true, { evaluate: false })))).toBe('y | ~x');
    expect(strOf(L.simplifyLogic(L.Xnor(x, y, false, { evaluate: false })))).toBe('(x | ~y) & (y | ~x)');
    const r = boolalg.orFn(y, sj.Eq(sj.sub(sj.mul(x, sj.add(x, 1)), sj.pow(x, 2)), 1));
    expect(strOf(L.simplifyLogic(r, { deep: false }))).toBe('y | Eq(-x**2 + x*(x + 1), 1)');
    expect(strOf(L.simplifyLogic(r))).toBe('y | Eq(x, 1)');
  });

  it('simplify_logic: a dontcare with too many variables is ignored', () => {
    const v = sj.symbols('v0:9');
    const dc = boolalg.andFn(...v);
    // SymPy: simplify_logic((x & y) | (x & ~y), dontcare=And(v0, ..., v8)) is x
    expect(strOf(L.simplifyLogic(boolalg.orFn(boolalg.andFn(x, y), boolalg.andFn(x, boolalg.notFn(y))), { dontcare: dc }))).toBe('x');
    expect(strOf(L.simplifyLogic(boolalg.orFn(x, y), { dontcare: boolalg.andFn(y, ...v.slice(0, 7)) }))).toBe('x | y');
  });

  it('SOPform with a bad term', () => {
    expect(() => L.SOPform([x], ['a' as unknown as number])).toThrow(TypeError);
  });

  it('bool_map without a match', () => {
    // SymPy gives None or False
    expect(L.boolMap(boolalg.orFn(x, y), boolalg.orFn(x, y, z))).toBe(sj.NoMatch);
    expect(L.boolMap(boolalg.orFn(boolalg.andFn(x, y), z), boolalg.orFn(boolalg.andFn(x, boolalg.notFn(y)), z))).toBe(sj.NoMatch);
    expect(L.boolMap(boolalg.orFn(boolalg.andFn(x, y), z), boolalg.orFn(boolalg.andFn(x, y), boolalg.notFn(z)))).toBe(sj.NoMatch);
    expect(L.boolMap(boolalg.orFn(x, y, boolalg.notFn(z)), boolalg.orFn(x, boolalg.notFn(y), boolalg.notFn(z)))).toBe(sj.NoMatch);
    // SymPy: NotImplementedError unexpected level of nesting
    expect(() => L.boolMap(boolalg.orFn(boolalg.andFn(x, sj.Gt(y, 1)), z), boolalg.orFn(boolalg.andFn(w, sj.Gt(y, 1)), z))).toThrow(sj.NotImplementedError);
    // SymPy: KeyError f(x)
    const f = sj.SymFunction('f');
    expect(() => L.boolMap(boolalg.orFn(boolalg.notFn(f(x)), y), boolalg.orFn(boolalg.notFn(f(z)), w))).toThrow(sj.NotImplementedError);
  });

  it('bool_map with symbols in terms of different shapes', () => {
    const [a, b, c, d] = sj.symbols('a b c d');
    const e1 = boolalg.orFn(boolalg.andFn(x, y), boolalg.andFn(x, boolalg.notFn(z), w));
    const e2 = boolalg.orFn(boolalg.andFn(a, b), boolalg.andFn(a, boolalg.notFn(c), d));
    const m = L.boolMap(e1, e2);
    if (sj.isNoMatch(m)) throw new Error('no match');
    expect(strOf(m[0])).toBe('x & (w | y) & (y | ~z)');
    expect([...m[1]].map(([k, v]) => `${strOf(k)}: ${strOf(v)}`).sort()).toEqual(['w: d', 'x: a', 'y: b', 'z: c']);
  });
});

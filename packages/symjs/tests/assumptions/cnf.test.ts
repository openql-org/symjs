// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/assumptions/cnf.ts. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { AND, CNF, EncodedCNF, Literal, OR, distributeANDOverOR, toNNF } from '../../src/assumptions';

const { Q } = sj;
const [x, y, z] = sj.symbols('x y z') as [sj.Expr, sj.Expr, sj.Expr];

describe('Literal, AND, OR', () => {
  it('literals', () => {
    expect(String(new Literal(Q.even(x)))).toBe('Literal(Q.even(x), False)');
    expect(String(new Literal(sj.not(Q.even(x))))).toBe('Literal(Q.even(x), True)');
    expect(String(new Literal(sj.not(Q.even(x)), true))).toBe('Literal(Q.even(x), False)');
    expect(String(new Literal(true))).toBe('Literal(True, False)');
    expect(String(new Literal(false).invert())).toBe('Literal(False, True)');
    const l = new Literal(Q.even);
    expect(l.arg).toBe(Q.even);
    expect(String(l.rcall(x))).toBe('Literal(Q.even(x), False)');
    expect(() => new Literal(Q.even(x)).rcall(y)).toThrow(TypeError);
    expect(new Literal(Q.even(x)).equals(new Literal(Q.even(x)))).toBe(true);
  });
  it('AND and OR', () => {
    const a = new Literal(Q.even(x));
    const b = new Literal(Q.odd(x), true);
    const o = new OR(b, a);
    expect(String(o)).toBe('(Literal(Q.even(x), False) | Literal(Q.odd(x), True))');
    expect(String(o.invert())).toBe('(Literal(Q.even(x), True) & Literal(Q.odd(x), False))');
    expect(String(new AND(a, b).invert())).toBe('(Literal(Q.even(x), True) | Literal(Q.odd(x), False))');
    expect(o.equals(new OR(a, b))).toBe(true);
    expect(new AND(a, b).equals(new AND(b, a))).toBe(true);
    expect(new AND(a, a).args.length).toBe(2);
    expect(String(new OR(new Literal(Q.even), new Literal(Q.odd)).rcall(y))).toBe('(Literal(Q.even(y), False) | Literal(Q.odd(y), False))');
    expect(String(new AND(new Literal(Q.even)).rcall(y))).toBe('(Literal(Q.even(y), False))');
  });
});

describe('to_NNF', () => {
  it('doctests', () => {
    expect(String(toNNF(sj.And(Q.even(x), sj.not(Q.positive(x)))))).toBe('(Literal(Q.even(x), False) & Literal(Q.positive(x), True))');
    expect(String(toNNF(sj.Eq(x, y)))).toBe('Literal(Q.eq(x, y), False)');
    const cmap = new Map([[Q.nonpositive, [Q.negative, Q.zero]]]);
    expect(String(toNNF(Q.nonpositive, cmap))).toBe('(Literal(Q.negative, False) | Literal(Q.zero, False))');
    expect(String(toNNF(Q.nonpositive(x), cmap))).toBe('(Literal(Q.negative(x), False) | Literal(Q.zero(x), False))');
    expect(String(toNNF(Q.even))).toBe('Literal(Q.even, False)');
    expect(String(toNNF(true))).toBe('Literal(True, False)');
  });
  it('the connectives', () => {
    const [a, b, c] = [Q.even(x), Q.odd(y), Q.zero(z)];
    expect(String(toNNF(sj.Or(a, b)))).toBe('(Literal(Q.even(x), False) | Literal(Q.odd(y), False))');
    expect(String(toNNF(sj.Nand(a, b, { evaluate: false })))).toBe('(Literal(Q.even(x), True) | Literal(Q.odd(y), True))');
    expect(String(toNNF(sj.Nor(a, b, { evaluate: false })))).toBe('(Literal(Q.even(x), True) & Literal(Q.odd(y), True))');
    expect(String(toNNF(sj.Xor(a, b)))).toBe('((Literal(Q.even(x), False) | Literal(Q.odd(y), False)) & (Literal(Q.even(x), True) | Literal(Q.odd(y), True)))');
    expect(String(toNNF(sj.Xnor(a, b, { evaluate: false })))).toBe('((Literal(Q.even(x), False) & Literal(Q.odd(y), False)) | (Literal(Q.even(x), True) & Literal(Q.odd(y), True)))');
    expect(String(toNNF(sj.Implies(a, b)))).toBe('(Literal(Q.even(x), True) | Literal(Q.odd(y), False))');
    expect(String(toNNF(sj.Equivalent(a, b)))).toBe('((Literal(Q.even(x), False) | Literal(Q.odd(y), True)) & (Literal(Q.even(x), True) | Literal(Q.odd(y), False)))');
    expect(String(toNNF(sj.ITE(a, b, c, { evaluate: false })))).toBe('((Literal(Q.even(x), False) | Literal(Q.zero(z), False)) & (Literal(Q.even(x), True) | Literal(Q.odd(y), False)))');
  });
});

describe('CNF', () => {
  it('from_prop and the composite predicates', () => {
    const cnf = CNF.fromProp(sj.And(Q.real(x), sj.not(Q.zero(x))));
    expect(cnf.clauses.map((c) => c.map(String).sort().join(' | ')).sort()).toEqual([
      'Literal(Q.negative(x), False) | Literal(Q.positive(x), False) | Literal(Q.zero(x), False)',
      'Literal(Q.zero(x), True)',
    ]);
    expect(String(CNF.fromProp(Q.even(x)))).toBe('(Literal(Q.even(x), False))');
    expect(String(distributeANDOverOR(new Literal(Q.odd(x))))).toBe('(Literal(Q.odd(x), False))');
    expect(() => distributeANDOverOR(new OR())).toThrow();
  });
  it('operations', () => {
    const a = CNF.fromProp(sj.And(Q.even(x), Q.odd(y)));
    expect(a.size).toBe(2);
    expect(a.copy().iand(CNF.fromProp(Q.zero(z))).size).toBe(3);
    expect(new CNF().extend([Q.even(x), Q.even(x)]).size).toBe(1);
    expect(a.or(CNF.fromProp(Q.zero(z))).size).toBe(2);
    expect(a.and(CNF.fromProp(Q.zero(z))).size).toBe(3);
    expect(sj.str(CNF.CNFToCnf(a.not()))).toBe('~Q.even(x) | ~Q.odd(y)');
    expect(new CNF().not().clauses).toEqual([[]]);
    expect(sj.str(CNF.CNFToCnf(a))).toBe('Q.even(x) & Q.odd(y)');
    expect(a.allPredicates().map(String).sort()).toEqual(['Q.even(x)', 'Q.odd(y)']);
    expect(String(CNF.allAnd(CNF.fromProp(Q.even), CNF.fromProp(Q.odd)).rcall(x))).toContain('Literal(Q.odd(x), False)');
    expect(CNF.allOr(a).size).toBe(2);
    expect(sj.str(CNF.CNFToCnf(new CNF()))).toBe('True');
    expect(() => CNF.CNFToCnf(CNF.fromProp(Q.even))).toThrow(TypeError);
  });
});

describe('EncodedCNF', () => {
  it('lra_theory doctest: add_from_cnf and from_cnf', () => {
    const f = sj.And(sj.Or(sj.Gt(x, 0), sj.Lt(x, 0)), sj.Or(sj.Eq(x, 0), sj.Eq(y, 1)), sj.Or(sj.Lt(y, 1), sj.Gt(y, 1), sj.Eq(1, 2)));
    const cnf = CNF.fromProp(f);
    const enc = new EncodedCNF();
    expect(enc.addFromCnf(cnf)).toBeUndefined();
    expect(enc.data.length).toBe(3);
    expect(enc.symbols.length).toBe(6);
    const enc2 = new EncodedCNF();
    expect(enc2.fromCnf(cnf)).toBeUndefined();
    expect(enc2.variables).toEqual([1, 2, 3, 4, 5, 6]);
    expect(enc2.encoding.size).toBe(6);
    expect(enc2.encodingOf(Q.gt(x, 0))).toBeGreaterThan(0);
    const c = enc2.copy();
    c.addProp(sj.not(Q.even(z)));
    expect(c.data.length).toBe(4);
    expect(c.encodeArg(new Literal(sj.not(Q.even(z))))).toBe(-7);
    expect(enc2.data.length).toBe(3);
  });
});

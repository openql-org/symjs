// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Expected values from SymPy 1.14.0 (sympy.polys.distributedmodules doctests and tests/test_distributedmodules.py).

import { describe, expect, it } from 'vitest';
import { Sym, parseExpr as P } from '../../src/index';
import { EX, QQ, ZZ } from '../../src/polys/domains';
import { PythonMPQ } from '../../src/polys/domains/pythonrational';
import { grlex, igrlex, ilex, lex, type MonomialOrdering } from '../../src/polys/orderings';
import * as M from '../../src/polys/distributedmodules';

const [x, y, z] = [new Sym('x'), new Sym('y'), new Sym('z')];
const q = (n: number): PythonMPQ => new PythonMPQ(n);
const r = (v: unknown): string => {
  if (Array.isArray(v)) {
    const inner = v.map(r).join(', ');
    return v.length === 2 && Array.isArray(v[0]) && !Array.isArray(v[1]) ? `(${inner})` : typeof v[0] === 'number' ? `(${inner}${v.length === 1 ? ',' : ''})` : `[${inner}]`;
  }
  return v instanceof PythonMPQ ? v.repr() : String(v);
};
const V = (v: string[], O: MonomialOrdering = lex): M.SdmTerm[] => M.sdmFromVector(v.map((e) => P(e)), O, QQ, { gens: [x, y, z] });

describe('monomials and terms (SymPy doctests)', () => {
  it('monomial tools', () => {
    expect(M.sdmMonomialMul([1, 1, 0], [1, 3])).toEqual([1, 2, 3]);
    expect(M.sdmMonomialDeg([5, 2, 1])).toBe(3);
    expect(M.sdmMonomialLcm([1, 2, 3], [1, 0, 5])).toEqual([1, 2, 5]);
    const pairs: [number[], number[]][] = [[[1, 0, 0], [1, 0, 0]], [[1, 0, 0], [1, 2, 1]], [[5, 1, 1], [5, 2, 1]], [[1, 0, 0], [2, 0, 0]], [[1, 1, 0], [1, 0, 0]], [[5, 1, 2], [5, 0, 1]]];
    expect(pairs.map(([a, b]) => M.sdmMonomialDivides(a, b))).toEqual([true, true, true, false, false, false]);
  });
  it('dicts, sorting, leading terms', () => {
    const dic = new Map([[[1, 1, 0], q(1)], [[1, 0, 0], q(2)], [[0, 1, 0], q(0)]]);
    expect(r(M.sdmFromDict(dic, lex))).toBe('[((1, 1, 0), MPQ(1,1)), ((1, 0, 0), MPQ(2,1))]');
    const f = M.sdmFromDict(new Map([[[1, 2, 3], q(1)], [[4, 0, 0], q(2)], [[4, 0, 1], q(3)]]), lex);
    expect([r(M.sdmLM(f)), r(M.sdmLT(f)), String(M.sdmLC(f, QQ)), String(M.sdmLC([], QQ))]).toEqual(['(4, 0, 1)', '((4, 0, 1), MPQ(3,1))', '3', '0']);
    expect(r([...M.sdmToDict(f)])).toBe('[((4, 0, 1), MPQ(3,1)), ((4, 0, 0), MPQ(2,1)), ((1, 2, 3), MPQ(1,1))]');
    expect(r(M.sdmSort(f, (m) => -(m[0] ?? 0)))).toBe('[((1, 2, 3), MPQ(1,1)), ((4, 0, 1), MPQ(3,1)), ((4, 0, 0), MPQ(2,1))]');
    expect([M.sdmDeg([[[1, 2, 3], 1], [[10, 0, 1], 1], [[2, 3, 4], 4]]), M.sdmEcart([[[1, 2, 3], 1], [[1, 0, 1], 1]]), M.sdmEcart([[[2, 2, 1], 1], [[1, 5, 1], 1]])]).toEqual([7, 0, 3]);
    expect(M.sdmZero()).toEqual([]);
  });
  it('add and multiply', () => {
    expect(r(M.sdmAdd([[[1, 1, 1], q(1)]], [[[2, 0, 0], q(1)]], lex, QQ))).toBe('[((2, 0, 0), MPQ(1,1)), ((1, 1, 1), MPQ(1,1))]');
    expect(M.sdmAdd([[[1, 1, 1], q(1)]], [[[1, 1, 1], q(-1)]], lex, QQ)).toEqual([]);
    expect(r(M.sdmAdd([[[1, 0, 0], 1]], [[[1, 0, 0], 2]], lex, QQ))).toBe('[((1, 0, 0), MPQ(3,1))]');
    expect(M.sdmMulTerm([[[1, 0, 0], q(1)]], [[0, 0], q(0)], lex, QQ)).toEqual([]);
    expect(M.sdmMulTerm([], [[1, 0], q(1)], lex, QQ)).toEqual([]);
    expect(r(M.sdmMulTerm([[[1, 0, 0], q(1)]], [[1, 0], q(1)], lex, QQ))).toBe('[((1, 1, 0), MPQ(1,1))]');
    expect(r(M.sdmMulTerm([[[2, 0, 1], q(4)], [[1, 1, 0], q(3)]], [[1, 1], q(2)], lex, QQ))).toBe('[((2, 1, 2), MPQ(8,1)), ((1, 2, 1), MPQ(6,1))]');
    expect(r(M.sdmMulTerm([[[1, 0], 3n]], [[1], 2n], lex, ZZ))).toBe('[((1, 1), 6)]');
  });
  it('vectors', () => {
    expect(r(M.sdmFromVector([P('x**2 + y**2'), P('2*z')], lex, QQ))).toBe('[((1, 0, 0, 1), MPQ(2,1)), ((0, 2, 0, 0), MPQ(1,1)), ((0, 0, 2, 0), MPQ(1,1))]');
    expect(r(M.sdmFromVector([P('2*x + 3*x + 1.0'), P('0')], lex, QQ))).toBe('[((0, 1), MPQ(5,1)), ((0, 0), MPQ(1,1))]');
    const f = V(['x**2 + y**2', '2*z']);
    expect(M.sdmToVector(f, [x, y, z], QQ).map(String)).toEqual(['x**2 + y**2', '2*z']);
    expect(M.sdmToVector(f, [x, y, z], QQ, 3).map(String)).toEqual(['x**2 + y**2', '2*z', '0']);
  });
});

describe('normal forms and standard bases', () => {
  const [f, g, h] = [V(['x**2 + y**2', '2*z']), V(['x', 'y']), V(['y', '0'])];
  it('S-polynomials', () => {
    const [ff, gg, hh] = [[[[1, 0, 0], q(1)], [[1, 1, 0], q(1)]], [[[2, 0, 0], q(1)]], [[[1, 1, 0], q(1)], [[1, 0, 0], q(1)]]] as M.SdmTerm[][];
    expect(r(M.sdmSpoly(ff ?? [], hh ?? [], lex, QQ))).toBe('[((1, 2, 0), MPQ(1,1)), ((1, 0, 0), MPQ(-1,1))]');
    expect(r(M.sdmSpoly(ff ?? [], gg ?? [], lex, QQ))).toBe('[]');
    expect(M.sdmSpoly([], f, lex, QQ)).toEqual([]);
    expect(M.sdmSpoly(f, [[[0, 0, 0, 0], q(1)]], lex, QQ, [[], []])).toEqual([[], []]);
    expect(r(M.sdmSpoly([[[1, 1, 0], q(1)]], [[[1, 0, 1], q(1)]], lex, QQ))).toBe('[]');
  });
  it('weak and reduced normal forms', () => {
    const nf = '[((1, 0, 0, 1), MPQ(2,1)), ((0, 2, 0, 0), MPQ(1,1)), ((0, 0, 2, 0), MPQ(1,1))]';
    expect(r(M.sdmNfMora(f, [g, h], lex, QQ))).toBe(nf);
    expect(r(M.sdmNfBuchberger(f, [g, h], lex, QQ))).toBe(nf);
    expect(r(M.sdmNfBuchbergerReduced(f, [g, h], lex, QQ))).toBe('[((1, 0, 0, 1), MPQ(2,1)), ((0, 2, 0, 0), MPQ(1,1))]');
    const phantom = [V(['1', '0']), [V(['0', '1']), V(['1', '1'])]] as const;
    expect(r(M.sdmNfMora(f, [g, h], lex, QQ, phantom))).toBe(`[${nf}, [((0, 0, 0, 0), MPQ(1,1))]]`);
    expect(r(M.sdmNfBuchberger(f, [g, h], lex, QQ, phantom))).toBe(`[${nf}, [((0, 0, 0, 0), MPQ(1,1))]]`);
    const [F, G] = [V(['1 - x', '0'], ilex), V(['x**2 - x', '0'], ilex)];
    expect(M.sdmNfMora(G, [F], ilex, QQ)).toEqual([]);
  });
  it('standard bases', () => {
    const basis = '[[((1, 0, 1, 0), MPQ(1,1)), ((0, 1, 0, 0), MPQ(1,1))], [((1, 0, 0, 1), MPQ(2,1)), ((0, 2, 0, 0), MPQ(1,1)), ((0, 0, 2, 0), MPQ(1,1))], [((0, 1, 0, 1), MPQ(-2,1)), ((0, 0, 3, 0), MPQ(1,1))], [((0, 0, 1, 0), MPQ(1,1))]]';
    expect(r(M.sdmGroebner([f, g, h], M.sdmNfMora, lex, QQ))).toBe(basis);
    expect(r(M.sdmGroebner([f, g, h], M.sdmNfBuchberger, lex, QQ, true))).toBe(`[${basis}, [[((1, 0, 0, 0), MPQ(1,1))], [((0, 0, 0, 0), MPQ(1,1))], [((2, 2, 0, 0), MPQ(-1,1)), ((1, 0, 0, 1), MPQ(-2,1)), ((0, 0, 1, 0), MPQ(1,1))], [((2, 0, 0, 0), MPQ(1,1))]]]`);
    expect(M.sdmGroebner([[], []], M.sdmNfMora, lex, QQ)).toEqual([]);
    expect(M.sdmGroebner([[]], M.sdmNfMora, lex, QQ, true)).toEqual([[], []]);
    const [F, G] = [V(['1 - x', '0'], ilex), V(['x**2 - x', '0'], ilex)];
    expect(r(M.sdmGroebner([G, F], M.sdmNfMora, ilex, QQ))).toBe('[[((0, 0, 0, 0), MPQ(1,1)), ((0, 1, 0, 0), MPQ(-1,1))]]');
    expect(r(M.sdmGroebner([V(['x*y', '0']), V(['x**2', '0']), V(['y', '0'])], M.sdmNfBuchberger, lex, QQ))).toBe('[[((0, 2, 0, 0), MPQ(1,1))], [((0, 0, 1, 0), MPQ(1,1))]]');
    expect(r(M.sdmGroebner([[], V(['x', '0'])], M.sdmNfBuchberger, lex, QQ, true))).toBe('[[[((0, 1, 0, 0), MPQ(1,1))]], [[((1, 0, 0, 0), MPQ(1,1))]]]');
  });
});

describe('SymPy tests/test_distributedmodules.py', () => {
  const D = (entries: [number[], number][], O: Parameters<typeof M.sdmFromDict>[1] = grlex): M.SdmTerm[] => M.sdmFromDict(new Map(entries.map(([m, c]) => [m, q(c)])), O);
  it('test_sdm_nf_mora', () => {
    const f = D([[[1, 2, 1, 1], 1], [[1, 1, 2, 1], 1], [[1, 0, 2, 1], 1], [[1, 0, 0, 3], 1], [[1, 1, 1, 0], 1]]);
    const f1 = D([[[1, 1, 1, 0], 1], [[1, 0, 2, 0], 1], [[1, 0, 0, 0], -1]]);
    const f2 = D([[[1, 1, 1, 0], 1]]);
    const [id0, id1, id2] = [0, 1, 2].map((i) => D([[[i, 0, 0, 0], 1]]));
    expect(r(M.sdmNfMora(f, [f1, f2], grlex, QQ, [id0 ?? [], [id1 ?? [], id2 ?? []]]))).toBe('[[((1, 0, 2, 1), MPQ(1,1)), ((1, 0, 0, 3), MPQ(1,1)), ((1, 1, 1, 0), MPQ(1,1)), ((1, 1, 0, 1), MPQ(1,1))], [((1, 1, 0, 1), MPQ(-1,1)), ((0, 0, 0, 0), MPQ(1,1))]]');
    expect(r(M.sdmNfMora(f, [f2, f1], grlex, QQ, [id0 ?? [], [id2 ?? [], id1 ?? []]]))).toBe('[[((1, 0, 2, 1), MPQ(1,1)), ((1, 0, 0, 3), MPQ(1,1)), ((1, 1, 1, 0), MPQ(1,1))], [((2, 1, 0, 1), MPQ(-1,1)), ((2, 0, 1, 1), MPQ(-1,1)), ((0, 0, 0, 0), MPQ(1,1))]]');
    const [g, g1, g2] = [V(['x*z', 'y**2 + y*z - z', 'y']), V(['x', 'y', '1']), V(['x*y', 'z', 'z**2'])];
    const nf = '[((1, 0, 1, 1), MPQ(1,1)), ((1, 0, 0, 1), MPQ(-1,1)), ((0, 1, 1, 0), MPQ(-1,1)), ((0, 1, 0, 1), MPQ(1,1))]';
    expect([r(M.sdmNfMora(g, [g1, g2], lex, QQ)), r(M.sdmNfMora(g, [g2, g1], lex, QQ))]).toEqual([nf, nf]);
  });
  const contains = (O: MonomialOrdering, I: string[], f: string): boolean => {
    const S = I.map((e) => V([e], O));
    const G = M.sdmGroebner(S, M.sdmNfMora, O, QQ);
    return M.sdmNfMora(V([f]), G, lex, QQ).length === 0;
  };
  it('test_nontrivial and test_local', () => {
    const sym = ['x + y + z', 'x*y + x*z + y*z', 'x*y*z'];
    const cubes = ['x**3 + y**3', 'y**3 + z**3', 'z**3 + x**3', 'x**2*y + x**2*z + y**2*z'];
    expect([
      contains(lex, ['x', 'y'], 'x'), contains(lex, ['x', 'y'], 'x + y'), contains(lex, ['x', 'y'], '1'), contains(lex, ['x', 'y'], 'z'),
      contains(lex, ['x**2 + y', 'x**2 + x'], 'x - y'), contains(lex, sym, 'x**2'), contains(lex, sym, 'x**3'), contains(lex, sym, 'x**4'),
      contains(lex, sym, 'x*y**2'), contains(lex, sym, 'x**4 + y**3 + 2*z*y*x'), contains(lex, sym, 'x*y*z'), contains(lex, ['x', '1 + x + y', '5 - 7*y'], '1'),
      contains(lex, cubes, 'x**3'), contains(lex, cubes, 'x**2 + y**2'), contains(lex, ['x*(1 + x + y)', 'y*(1 + z)'], 'x'), contains(lex, ['x*(1 + x + y)', 'y*(1 + z)'], 'x + y'),
    ]).toEqual([true, true, false, false, true, false, true, true, false, true, true, true, true, false, false, false]);
    expect([
      contains(igrlex, ['x', 'y'], 'x'), contains(igrlex, ['x', 'y'], 'x + y'), contains(igrlex, ['x', 'y'], '1'), contains(igrlex, ['x', 'y'], 'z'),
      contains(igrlex, ['x**2 + y', 'x**2 + x'], 'x - y'), contains(igrlex, sym, 'x**2'), contains(igrlex, ['x*(1 + x + y)', 'y*(1 + z)'], 'x'), contains(igrlex, ['x*(1 + x + y)', 'y*(1 + z)'], 'x + y'),
    ]).toEqual([true, true, false, false, true, false, true, true]);
  });
  it('test_uncovered_line and test_chain_criterion', () => {
    const W = (v: string[], O: MonomialOrdering = lex): M.SdmTerm[] => M.sdmFromVector(v.map((e) => P(e)), O, QQ, { gens: [x, y] });
    expect([M.sdmSpoly([], W(['x', '0']), lex, QQ), M.sdmSpoly(W(['0', 'y']), W(['x', '0']), lex, QQ)]).toEqual([[], []]);
    expect(M.sdmFromVector([P('0'), P('0')], lex, QQ, { gens: [x, y] })).toEqual([]);
    expect(r(M.sdmFromVector([P('x*y + x*z'), P('3')], lex, EX, { gens: [x] }))).toBe('[((1, 0), EX(3)), ((0, 1), EX(y + z))]');
    const W1 = (v: string[]): M.SdmTerm[] => M.sdmFromVector(v.map((e) => P(e)), grlex, QQ, { gens: [x] });
    expect(M.sdmGroebner([W1(['1', 'x']), W1(['0', 'x - 2'])], M.sdmNfMora, grlex, QQ).length).toBe(2);
    expect(M.sdmToVector([[[1, 1, 0, 0], 1n]], [x, y, z], QQ, 3).map(String)).toEqual(['0', 'x', '0']);
  });
});

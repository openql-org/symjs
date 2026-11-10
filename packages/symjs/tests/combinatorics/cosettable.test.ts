// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Coset tables and coset enumeration; references from SymPy 1.14.0 (scripts/gen_fpgroups.py, after
// SymPy's test_coset_table.py): the tables after each scan, both strategies on the test groups of
// Havas's and Holt's examples (with the number of cosets defined), the look-ahead of the Felsch
// strategy, continued drafts and the modified methods.
import { afterEach, describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import { Sym } from '../../src';
import { CosetLimitExceeded, CosetTable, FpGroup, FreeGroup, FreeGroupElement, cosetEnumerationC, cosetEnumerationR, freeGroup, modifiedCosetEnumerationR } from '../../src/combinatorics';

type Af = [string, number][];
const ref = JSON.parse(readFileSync(new URL('./fpgroups.references.json', import.meta.url), 'utf8')).cosets;
const [F, x, y] = freeGroup('x, y') as [FreeGroup, FreeGroupElement, FreeGroupElement];
const wordIn = (G: FreeGroup) => (a: Af): FreeGroupElement => G.dtype(a.map(([s, e]) => [new Sym(s), e]));
const word = wordIn(F);

afterEach(() => {
  CosetTable.maxStackSize = 100;
});

describe('scans', () => {
  for (const [k, sc] of (ref.scans as any[]).entries()) {
    it(`scan and fill ${k}`, () => {
      const C = new CosetTable(new FpGroup(F, sc.rels.map(word)), sc.H.map(word));
      for (const st of sc.steps) {
        C.scanAndFill(st.alpha, word(st.w));
        expect(C.table).toEqual(st.table);
        expect(C.p).toEqual(st.p);
      }
    });
  }
});

describe('scans of the Felsch strategy', () => {
  for (const [k, sc] of (ref.scans_c as any[]).entries()) {
    it(`scan and fill c ${k}`, () => {
      const C = new CosetTable(new FpGroup(F, sc.rels.map(word)), sc.H.map(word));
      for (const st of sc.steps) {
        C.scanAndFillC(st.alpha, word(st.w));
        expect(C.table).toEqual(st.table);
        expect(C.p).toEqual(st.p);
      }
      // standardized with the dead cosets still in the table
      C.standardize();
      expect(C.table).toEqual(sc.standardized.table);
    });
  }
  it('compress keeps the undefined entries of an incomplete table', () => {
    const C = new CosetTable(new FpGroup(F, [x.pow(2)]), []);
    C.table = [[1, null, null, null], [null, 0, null, null], [null, null, null, null]];
    C.p = [0, 1, 1];
    C.compress();
    expect(C.table).toEqual([[1, null, null, null], [null, 0, null, null]]);
  });
  it('standardize skips the dead cosets', () => {
    const C = new CosetTable(new FpGroup(F, [x.pow(2), y.pow(2)]), []);
    C.table = [[2, 2, 0, 0], [null, null, null, null], [0, 0, 2, 2]];
    C.p = [0, 0, 2];
    C.standardize();
    expect(C.table).toEqual([[1, 1, 0, 0], [0, 0, 2, 2], [null, null, null, null]]);
  });
  it('cosets defined for a generator outside the relators', () => {
    const C = cosetEnumerationR(new FpGroup(F, [x.pow(2)]), [], { maxCosets: 10, incomplete: true });
    expect(C.table.length).toBe(10);
    expect(C.isComplete()).toBe(false);
  });
  it('the modified enumeration with coincidences', () => {
    const G0 = new FreeGroup('a, b');
    const [a, b] = G0.generators as [FreeGroupElement, FreeGroupElement];
    const M = modifiedCosetEnumerationR(new FpGroup(G0, [a.pow(6), b.pow(6), a.mul(b).pow(2), a.pow(2).mul(b.pow(2)).pow(2), a.pow(3).mul(b.pow(3)).pow(5)]), [a]);
    expect({ p: M.p.length, omega: M.omega.length }).toEqual(ref.mod_cox);
  });
});

describe('coset enumeration', () => {
  for (const [k, e] of (ref.enumerations as any[]).entries()) {
    it(`group ${k}`, () => {
      const G0 = new FreeGroup(e.free.join(', '));
      const w = wordIn(G0);
      const G = new FpGroup(G0, e.rels.map(w));
      const H = e.H.map(w);
      const Cr = cosetEnumerationR(G, H);
      const Cc = cosetEnumerationC(G, H);
      expect([Cr.p.length, Cc.p.length]).toEqual([e.raw.r, e.raw.c]);
      Cr.compress();
      Cr.standardize();
      Cc.compress();
      Cc.standardize();
      expect(Cr.table).toEqual(e.r);
      expect(Cc.table).toEqual(e.c);
    });
  }
  it('look-ahead of the Felsch strategy', () => {
    const G0 = new FreeGroup('a, b, c');
    const w = wordIn(G0);
    CosetTable.maxStackSize = 10;
    const C = cosetEnumerationC(new FpGroup(G0, ref.look_ahead.rels.map(w)), ref.look_ahead.H.map(w));
    C.compress();
    C.standardize();
    expect(C.table).toEqual(ref.look_ahead.table);
  });
  it('drafts and limits', () => {
    const G0 = new FreeGroup('a, b');
    const [a, b] = G0.generators as [FreeGroupElement, FreeGroupElement];
    const G = new FpGroup(G0, [a.pow(6), b.pow(6), a.mul(b).pow(2), a.pow(2).mul(b.pow(2)).pow(2), a.pow(3).mul(b.pow(3)).pow(5)]);
    for (const strategy of ['relator_based', 'coset_table_based'] as const) {
      const d = G.cosetEnumeration([a], { strategy, maxCosets: 40, incomplete: true });
      expect({ complete: d.isComplete(), n: d.table.length }).toEqual(ref.drafts[strategy].first);
      const C = G.cosetEnumeration([a], { strategy, maxCosets: 20000, draft: d });
      C.standardize();
      expect(C.table).toEqual(ref.drafts[strategy].table);
      expect(() => G.cosetEnumeration([a], { strategy, maxCosets: 40 })).toThrow(CosetLimitExceeded);
    }
    expect(() => new CosetTable(G, [], 1).defineCol(0, 0)).toThrow(CosetLimitExceeded);
    expect(() => new CosetTable(G, [], 1).defineC(0, a)).toThrow(CosetLimitExceeded);
  });
});

describe('the modified methods', () => {
  it('replays SymPy test_modified_methods', () => {
    const f = new FpGroup(F, [x.pow(3), y.pow(5), x.mul(y).pow(2)]);
    const C = new CosetTable(f, [x.mul(y), x.inverse().mul(y.inverse()).mul(x).mul(y).mul(x)]);
    for (const st of ref.modified) {
      if (st.op === 'define') C.modifiedDefine(st.alpha, word(st.w));
      else C.modifiedScan(st.alpha, word(st.w), st.y === 'identity' ? C.grp.identity : C.grp.generators[Number(st.y.slice(-1))]!, st.fill);
      expect(C.table).toEqual(st.table);
      expect(C.p).toEqual(st.p);
      expect(C.P.map((r) => r.map((v) => (v === null ? null : String(v))))).toEqual(st.P);
    }
    C.modifiedRep(1);
    C.modifiedScanAndFill(0, x.pow(3), C.grp.identity);
    expect(modifiedCosetEnumerationR(new FpGroup(F, [x.pow(3), y.pow(3), x.inverse().mul(y.inverse()).mul(x).mul(y)]), [x]).table).toEqual(ref.modified_enumeration);
  });
});

describe('the CosetTable API', () => {
  it('accessors', () => {
    const f = new FpGroup(F, [x.pow(2), y.pow(3), x.mul(y).pow(3)]);
    const C = new CosetTable(f, [x]);
    expect(String(C)).toBe('Coset Table on <fp group on the generators (x, y)> with [x] as subgroup generators');
    expect([...C.ADict.values()]).toEqual([0, 1, 2, 3]);
    expect([...C.ADictInv.values()]).toEqual([1, 0, 3, 2]);
    expect(C.n).toBe(1);
    C.define(0, y);
    C.defineC(0, y.inverse());
    expect(C.table).toEqual([[null, null, 1, 2], [null, null, null, 0], [null, null, 0, null]]);
    expect(() => C.define(0, x.mul(y))).toThrow(RangeError);
    expect(C.conjugates([x.pow(2)]).map((r) => r.map(String))).toEqual([['x**2'], ['x**-2'], [], []]);
    C.table = [];
    expect(C.n).toBe(0);
    const D = new CosetTable(f, [x], 0);
    expect(D.cosetTableLimit).toBe(CosetTable.cosetTableMaxLimit);
    D.table = [[0, 0, null, null]];
    expect(() => D.cosetRepresentative(1)).toThrow();
    D.table = [[0, 0, 1, 1], [1, 1, 0, 0]];
    expect(() => new CosetTable(f, [x]).cosetRepresentative(0)).not.toThrow();
    const E = new CosetTable(f, []);
    E.table = [[0, 0, 0, 0], [1, 1, 1, 1]];
    expect(() => E.cosetRepresentative(1)).toThrow(RangeError);
  });
});

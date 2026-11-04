// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/tensor/indexmethods.ts.
// get_indices and get_contraction_structure. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Eq, IndexedBase, NotImplementedError, Piecewise, SymFunction, Sym, Gt, exp, sin, sympify, type Expr } from '../../src';
import { Idx, IndexConformanceException, getContractionStructure, getIndices } from '../../src/tensor';
import type { ContractionStructure } from '../../src/tensor/indexmethods';

// sympy.tensor.index_methods: get_indices and get_contraction_structure;
// expected values from SymPy 1.14.

const X = new IndexedBase('x');
const Y = new IndexedBase('y');
const A = new IndexedBase('A');
const B = new IndexedBase('B');
const C = new IndexedBase('C');
const i = Idx('i');
const j = Idx('j');
const k = Idx('k');
const l = Idx('l');
const f = SymFunction('f');
const g = SymFunction('g');
const z = new Sym('z');

const ind = (e: Expr): string[] => [...getIndices(e)[0]].map(String).sort();

/** A printable form of a contraction structure: keys and terms sorted. */
function show(d: ContractionStructure): string {
  const parts = [...d].map(([key, v]) => {
    const ks = key === null ? 'None' : Array.isArray(key) ? `(${key.map(String).join(', ')})` : String(key);
    const vs = v instanceof Set ? `{${[...v].map(String).sort().join(', ')}}` : `[${v.map(show).join(', ')}]`;
    return `${ks}: ${vs}`;
  });
  return `{${parts.sort().join(', ')}}`;
}
const cs = (e: Expr): string => show(getContractionStructure(e));
type Entry = [readonly Expr[] | Expr | null, Expr[] | ContractionStructure[]];
/** A contraction structure from SymPy's printed form: key -> terms or nested structures. */
const M = (...entries: Entry[]): ContractionStructure =>
  new Map(entries.map(([key, v]): [readonly Expr[] | Expr | null, Set<Expr> | ContractionStructure[]] => [key, v.every((x) => x instanceof Map) && v.length ? (v as ContractionStructure[]) : new Set(v as Expr[])]));

describe('get_indices', () => {
  it('outer indices', () => {
    expect(ind(X.at(i))).toEqual(['i']);
    expect(ind(X.at(i, i))).toEqual([]);
    expect(ind(X.at(i, j))).toEqual(['i', 'j']);
    expect(ind(X.at(i).mul(Y.at(i)))).toEqual([]);
    expect(ind(X.at(i).mul(Y.at(j)))).toEqual(['i', 'j']);
    expect(ind(X.at(i).add(Y.at(i)))).toEqual(['i']);
    expect(ind(X.at(i).mul(Y.at(i)).add(2))).toEqual([]);
    expect(ind(X.at(i).pow(2))).toEqual(['i']);
    expect(ind(X.at(i).pow(Y.at(j)))).toEqual(['i', 'j']);
    expect(ind(exp(X.at(i)))).toEqual(['i']);
    expect(ind(sin(X.at(i)))).toEqual(['i']);
    expect(ind(f(X.at(i).mul(Y.at(i))))).toEqual([]);
    expect(ind(Piecewise([X.at(i), Gt(X.at(i), 0)], [1, true]))).toEqual([]);
    expect(ind(i)).toEqual(['i']);
    expect(ind(z)).toEqual([]);
    expect(ind(sympify(3))).toEqual([]);
    expect(ind(Eq(z, 1))).toEqual([]);
    expect(ind(A.at(i, j).mul(X.at(i)).mul(Y.at(j)))).toEqual([]);
    expect(ind(A.at(i, j).mul(X.at(j)).add(B.at(i)))).toEqual(['i']);
    expect(ind(X.at(i).mul(Y.at(i)).pow(z))).toEqual([]);
    expect(ind(X.at(i).pow(X.at(j).mul(Y.at(j))))).toEqual(['i']);
    expect(getIndices(X.at(i))[1].size).toBe(0);
  });
  it('inconsistent sums and unhandled types raise', () => {
    expect(() => getIndices(X.at(i).add(Y.at(j)))).toThrow(IndexConformanceException);
    // SymPy raises NotImplementedError for an Equality containing Indexed objects.
    expect(() => getIndices(Eq(X.at(i), Y.at(i)))).toThrow(NotImplementedError);
  });
});

describe('get_contraction_structure', () => {
  it('flat terms', () => {
    expect(cs(X.at(i))).toBe('{None: {x[i]}}');
    expect(cs(X.at(i, i))).toBe('{(i): {x[i, i]}}');
    expect(cs(X.at(i, j))).toBe('{None: {x[i, j]}}');
    expect(cs(X.at(i).mul(Y.at(i)))).toBe('{(i): {x[i]*y[i]}}');
    expect(cs(X.at(i).mul(Y.at(j)))).toBe('{None: {x[i]*y[j]}}');
    expect(cs(X.at(i).add(Y.at(i)))).toBe('{None: {x[i], y[i]}}');
    expect(cs(X.at(i).mul(Y.at(i)).add(2))).toBe('{(i): {x[i]*y[i]}, None: {2}}');
    expect(cs(X.at(i).pow(2))).toBe('{None: {x[i]**2}}');
    expect(cs(X.at(i).pow(Y.at(j)))).toBe('{None: {x[i]**y[j]}}');
    expect(cs(exp(X.at(i)))).toBe('{None: {exp(x[i])}}');
    expect(cs(sin(X.at(i)))).toBe('{None: {sin(x[i])}}');
    expect(cs(i)).toBe('{None: {i}}');
    expect(cs(z)).toBe('{None: {z}}');
    expect(cs(Eq(z, 1))).toBe('{None: {Eq(z, 1)}}');
    const axy = A.at(i, j).mul(X.at(i)).mul(Y.at(j));
    expect(cs(axy)).toBe(`{(i, j): {${String(axy)}}}`);
    const ax = A.at(i, j).mul(X.at(j));
    expect(cs(ax.add(B.at(i)))).toBe(show(M([[j], [ax]], [null, [B.at(i)]])));
    expect(cs(X.at(i).mul(Y.at(i)).add(X.at(j).mul(Y.at(j))))).toBe('{(i): {x[i]*y[i]}, (j): {x[j]*y[j]}}');
  });
  it('Piecewise is a single term', () => {
    // SymPy 1.14 gives {None: Piecewise(...)} (the expression itself, not a
    // set of terms); symjs keeps the set form used for every other key.
    expect(cs(Piecewise([X.at(i), Gt(X.at(i), 0)], [1, true]))).toBe('{None: {Piecewise((x[i], x[i] > 0), (1, True))}}');
  });
  it('nested structures', () => {
    expect(cs(f(X.at(i).mul(Y.at(i))))).toBe('{None: {f(x[i]*y[i])}, f(x[i]*y[i]): [{(i): {x[i]*y[i]}}]}');
    expect(cs(X.at(i).mul(Y.at(i)).pow(z))).toBe('{(x[i]*y[i])**z: [{(i): {x[i]*y[i]}}], None: {(x[i]*y[i])**z}}');
    expect(cs(X.at(i).pow(X.at(j).mul(Y.at(j))))).toBe('{None: {x[i]**(x[j]*y[j])}, x[i]**(x[j]*y[j]): [{(j): {x[j]*y[j]}}]}');
    // Terms are printed with symjs (its factor order of Indexed objects
    // differs from SymPy's printer); the structure is SymPy's.
    const yA = Y.at(l).mul(A.at(l, l));
    const fyA = f(yA);
    const xf = X.at(k).mul(fyA);
    expect(cs(X.at(i).mul(Y.at(i)).add(A.at(j, j)).add(xf))).toBe(
      show(
        M(
          [[i], [X.at(i).mul(Y.at(i))]],
          [[j], [A.at(j, j)]],
          [null, [xf]],
          [xf, [M([null, [fyA]], [fyA, [M([null, [yA]], [yA, [M([[l], [A.at(l, l)]])]])]])]],
        ),
      ),
    );
    const By = B.at(j).mul(Y.at(j));
    const fBy = f(By);
    const big = X.at(i).mul(fBy).mul(A.at(k).mul(C.at(k)).pow(2));
    expect(cs(big)).toBe(show(M([[k], [big]], [big, [M([null, [fBy]], [fBy, [M([[j], [By]])]])]])));
    const xy = X.at(j).mul(Y.at(j));
    const t1 = X.at(i).mul(f(xy));
    const t2 = Y.at(i).mul(g(xy));
    expect(cs(t1.add(t2))).toBe(
      show(M([null, [t1, t2]], [t1, [M([null, [f(xy)]], [f(xy), [M([[j], [xy]])]])]], [t2, [M([null, [g(xy)]], [g(xy), [M([[j], [xy]])]])]])),
    );
  });
  it('unhandled types raise (SymPy NotImplementedError)', () => {
    expect(() => getContractionStructure(Eq(X.at(i), Y.at(i)))).toThrow(NotImplementedError);
  });
});

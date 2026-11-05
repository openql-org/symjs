// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/liealgebras (cartantype.ts, standard.ts, typea.ts ... typeg.ts, cartanmatrix.ts, dynkindiagram.ts, rootsystem.ts, weylgroup.ts).
// Cartan types, root systems and Weyl groups. Expected values are those of SymPy 1.14 unless a comment says otherwise.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import * as L from '../../src/liealgebras';

const mat = (m: sj.Matrix): string => m.toString();
const rootStr = (r: L.Root): string => `[${r.map((x) => (typeof x === 'number' ? String(x) : sj.str(x))).join(', ')}]`;
const rootsStr = (m: Map<number, L.Root>): string => [...m].map(([k, r]) => `${k}: ${rootStr(r)}`).join(', ');

describe('Cartan types', () => {
  it('construction', () => {
    expect(L.CartanType('A3')).toBeInstanceOf(L.TypeA);
    expect(L.CartanType(['C', 3])).toBeInstanceOf(L.TypeC);
    const a = L.CartanType('A3');
    expect(L.CartanType(a)).toBe(a);
    expect(String(a)).toBe('A3');
    expect(a.rank()).toBe(3);
    expect(() => L.CartanType('Ax')).toThrow(TypeError);
    expect(() => L.CartanType(['A', -1])).toThrow('Lie algebra rank cannot be negative');
    expect(() => L.CartanType('H3')).toThrow(RangeError);
    for (const bad of ['A0', 'B1', 'C2', 'D2', 'E5', 'E9', 'F3', 'G3']) expect(() => L.CartanType(bad)).toThrow(RangeError);
  });
  it('simple and positive roots, dimensions', () => {
    const cases: [string, number, number, number, string, string][] = [
      ['A3', 4, 12, 15, '[1, -1, 0, 0], [0, 1, -1, 0], [0, 0, 1, -1]', '0---0---0\n1   2   3'],
      ['B3', 3, 18, 21, '[1, -1, 0], [0, 1, -1], [0, 0, 1]', '0---0=>=0\n1   2   3'],
      ['C3', 3, 18, 21, '[1, -1, 0], [0, 1, -1], [0, 0, 2]', '0---0=<=0\n1   2   3'],
      ['D4', 4, 24, 28, '[1, -1, 0, 0], [0, 1, -1, 0], [0, 0, 1, -1], [0, 0, 1, 1]', '    3\n    0\n    |\n    |\n0---0---0\n1   2   4'],
      ['E6', 8, 72, 78, '[0.5, -0.5, -0.5, -0.5, -0.5, -0.5, -0.5, 0.5], [1, 1, 0, 0, 0, 0, 0, 0], [-1, 1, 0, 0, 0, 0, 0, 0], [0, -1, 1, 0, 0, 0, 0, 0], [0, 0, -1, 1, 0, 0, 0, 0], [0, 0, 0, -1, 1, 0, 0, 0]', '        2\n        0\n        |\n        |\n0---0---0---0---0\n1   3   4   5   6'],
      ['E7', 8, 126, 133, '[0.5, -0.5, -0.5, -0.5, -0.5, -0.5, -0.5, 0.5], [1, 1, 0, 0, 0, 0, 0, 0], [-1, 1, 0, 0, 0, 0, 0, 0], [0, -1, 1, 0, 0, 0, 0, 0], [0, 0, -1, 1, 0, 0, 0, 0], [0, 0, 0, -1, 1, 0, 0, 0], [0, 0, 0, 0, -1, 1, 0, 0]', '        2\n        0\n        |\n        |\n0---0---0---0---0---0\n1   3   4   5   6   7'],
      ['E8', 8, 240, 248, '[0.5, -0.5, -0.5, -0.5, -0.5, -0.5, -0.5, 0.5], [1, 1, 0, 0, 0, 0, 0, 0], [-1, 1, 0, 0, 0, 0, 0, 0], [0, -1, 1, 0, 0, 0, 0, 0], [0, 0, -1, 1, 0, 0, 0, 0], [0, 0, 0, -1, 1, 0, 0, 0], [0, 0, 0, 0, -1, 1, 0, 0], [0, 0, 0, 0, 0, -1, 1, 0]', '        2\n        0\n        |\n        |\n0---0---0---0---0---0---0\n1   3   4   5   6   7   8'],
      ['F4', 4, 48, 52, '[1, -1, 0, 0], [0, 1, -1, 0], [0, 0, 0, 1], [-1/2, -1/2, -1/2, -1/2]', '0---0=>=0---0\n1   2   3   4'],
      ['G2', 3, 12, 14, '[0, 1, -1], [1, -2, 1]', '0≡<≡0\n1   2'],
    ];
    for (const [t, dim, roots, basis, simple, diagram] of cases) {
      const c = L.CartanType(t);
      expect(c.dimension()).toBe(dim);
      expect(c.roots()).toBe(roots);
      // (SymPy gives n**2 - 1 for A, (n**2 - n)/2 for B and n*(n - 1)/2 for D, not the dimensions of the algebras)
      expect(c.basis()).toBe(basis);
      expect(Array.from({ length: c.rank() }, (_x, i) => rootStr(c.simpleRoot(i + 1))).join(', ')).toBe(simple);
      // there are half as many positive roots as roots, all distinct (SymPy repeats some half-integer roots of the E series)
      const pos = [...c.positiveRoots().values()].map(rootStr);
      expect(pos.length).toBe(roots / 2);
      expect(new Set(pos).size).toBe(roots / 2);
      expect(L.DynkinDiagram(t)).toBe(diagram);
    }
    expect(rootsStr(L.CartanType('A3').positiveRoots())).toBe('1: [1, -1, 0, 0], 2: [1, 0, -1, 0], 3: [1, 0, 0, -1], 4: [0, 1, -1, 0], 5: [0, 1, 0, -1], 6: [0, 0, 1, -1]');
    expect(rootStr((L.CartanType('A3') as L.TypeA).highestRoot())).toBe('[1, 0, 0, -1]');
    expect(rootsStr(L.CartanType('F4').positiveRoots()).endsWith('22: [1/2, -1/2, 1/2, -1/2], 23: [1/2, -1/2, -1/2, 1/2], 24: [1/2, -1/2, -1/2, -1/2]')).toBe(true);
    expect([...L.CartanType('G2').positiveRoots().values()].map(rootStr).slice(3).join(', ')).toBe('[1, 0, 1], [1, 1, -2], [2, -1, -1]');
    expect(() => L.CartanType('E6').simpleRoot(7)).toThrow('E6 only has six simple roots!');
    expect(() => L.CartanType('E7').simpleRoot(8)).toThrow('E7 only has seven simple roots!');
    expect(rootStr((L.CartanType('B3') as L.TypeB).basicRoot(0, 2))).toBe('[1, 0, -1]');
    expect(rootStr((L.CartanType('F4') as L.TypeF).basicRoot(0, 2))).toBe('[1, 0, -1, 0]');
  });
  it('Lie algebras', () => {
    expect((L.CartanType('A3') as L.TypeA).lieAlgebra()).toBe('su(4)');
    // B_3 is so(7) (SymPy prints so(6))
    expect((L.CartanType('B3') as L.TypeB).lieAlgebra()).toBe('so(7)');
    expect((L.CartanType('C3') as L.TypeC).lieAlgebra()).toBe('sp(6)');
    expect((L.CartanType('D4') as L.TypeD).lieAlgebra()).toBe('so(8)');
  });
  it('Cartan matrices', () => {
    expect(mat(L.CartanMatrix('A2'))).toBe('Matrix([[2, -1], [-1, 2]])');
    expect(mat(L.CartanMatrix(['C', 3]))).toBe('Matrix([[2, -1, 0], [-1, 2, -1], [0, -2, 2]])');
    expect(mat(L.CartanMatrix('B4'))).toBe('Matrix([[2, -1, 0, 0], [-1, 2, -1, 0], [0, -1, 2, -2], [0, 0, -1, 2]])');
    expect(mat(L.CartanMatrix('D4'))).toBe('Matrix([[2, -1, 0, 0], [-1, 2, -1, -1], [0, -1, 2, 0], [0, -1, 0, 2]])');
    expect(mat(L.CartanMatrix('E6'))).toBe('Matrix([[2, 0, -1, 0, 0, 0], [0, 2, 0, -1, 0, 0], [-1, 0, 2, -1, 0, 0], [0, -1, -1, 2, -1, 0], [0, 0, 0, -1, 2, -1], [0, 0, 0, 0, -1, 2]])');
    expect(mat(L.CartanMatrix('F4'))).toBe('Matrix([[2, -1, 0, 0], [-1, 2, -2, 0], [0, -1, 2, -1], [0, 0, -1, 2]])');
    expect(mat(L.CartanMatrix('G2'))).toBe('Matrix([[2, -1], [-3, 2]])');
  });
});

describe('RootSystem', () => {
  it('roots and their sums', () => {
    const r = new L.RootSystem('A3');
    expect(rootsStr(r.simpleRoots())).toBe('1: [1, -1, 0, 0], 2: [0, 1, -1, 0], 3: [0, 0, 1, -1]');
    expect(rootsStr(r.allRoots())).toBe(
      '1: [1, -1, 0, 0], 2: [1, 0, -1, 0], 3: [1, 0, 0, -1], 4: [0, 1, -1, 0], 5: [0, 1, 0, -1], 6: [0, 0, 1, -1], 7: [-1, 1, 0, 0], 8: [-1, 0, 1, 0], 9: [-1, 0, 0, 1], 10: [0, -1, 1, 0], 11: [0, -1, 0, 1], 12: [0, 0, -1, 1]',
    );
    expect(r.rootSpace()).toBe('alpha[1] + alpha[2] + alpha[3]');
    expect(rootStr(r.addSimpleRoots(1, 2))).toBe('[1, 0, -1, 0]');
    expect(rootStr(r.addAsRoots([1, 0, -1, 0], [0, 0, 1, -1]) as L.Root)).toBe('[1, 0, 0, -1]');
    expect(r.addAsRoots([1, -1, 0, 0], [0, 0, -1, 1])).toBe('The sum of these two roots is not a root');
    expect(() => r.addSimpleRoots(1, 5)).toThrow("You've used a root that doesn't exist!");
    expect(mat(r.cartanMatrix())).toBe('Matrix([[2, -1, 0], [-1, 2, -1], [0, -1, 2]])');
    expect(r.dynkinDiagram()).toBe('0---0---0\n1   2   3');
    const f = new L.RootSystem('F4');
    expect(rootStr(f.allRoots().get(25) ?? [])).toBe('[-1, 1, 0, 0]');
    expect(rootStr(f.addSimpleRoots(3, 4))).toBe('[-1/2, -1/2, -1/2, 1/2]');
    expect(rootStr(f.addSimpleRoots(4, 4))).toBe('[-1, -1, -1, -1]');
    expect(rootStr(f.allRoots().get(48) ?? [])).toBe('[-1/2, 1/2, 1/2, 1/2]');
  });
});

describe('WeylGroup', () => {
  it('orders, names and diagrams', () => {
    const cases: [string, bigint, string, string][] = [
      ['A3', 24n, 'S4: the symmetric group acting on 4 elements.', '0---0---0\n1   2   3'],
      ['B3', 48n, 'The hyperoctahedral group acting on 6 elements.', '0---0===0\n1   2   3'],
      ['C3', 48n, 'The hyperoctahedral group acting on 6 elements.', '0---0===0\n1   2   3'],
      ['D4', 192n, 'The symmetry group of the 4-dimensional demihypercube.', '    3\n    0\n    |\n    |\n0---0---0\n1   2   4'],
      ['E6', 51840n, 'The symmetry group of the 6-polytope.', '        2\n        0\n        |\n        |\n0---0---0---0---0\n1   3   4   5   6'],
      ['E7', 2903040n, 'The symmetry group of the 7-polytope.', L.DynkinDiagram('E7')],
      ['E8', 696729600n, 'The symmetry group of the 8-polytope.', L.DynkinDiagram('E8')],
      ['F4', 1152n, 'The symmetry group of the 24-cell, or icositetrachoron.', '0---0===0---0\n1   2   3   4'],
      ['G2', 12n, 'D6, the dihedral group of order 12, and symmetry group of the hexagon.', '0≡≡≡0\n1   2'],
    ];
    for (const [t, order, name, diagram] of cases) {
      const w = new L.WeylGroup(t);
      expect(w.groupOrder()).toBe(order);
      expect(w.groupName()).toBe(name);
      expect(w.coxeterDiagram()).toBe(diagram);
    }
    expect(new L.WeylGroup('F4').generators()).toEqual(['r1', 'r2', 'r3', 'r4']);
    expect(new L.WeylGroup('A2').deleteDoubles([1, 1, 2, 2, 3, 1, 1])).toEqual([2, 2, 3]);
  });
  it('matrix forms and element orders', () => {
    const cases: [string, string, number, string][] = [
      ['A3', 'r1*r2*r3', 4, 'Matrix([[0, 0, 0, 1], [1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0]])'],
      ['B4', 'r1*r4*r2', 4, 'Matrix([[0, -1, 0, 0], [1, 0, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0]])'],
      ['C3', 'r1*r2', 4, 'Matrix([[0, -1, 0], [1, 0, 0], [0, 0, 1]])'],
      ['D4', 'r1*r2*r3*r4', 6, 'Matrix([[0, 0, -1, 0], [1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, -1]])'],
      ['D4', 'r4', 2, 'Matrix([[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, -1], [0, 0, -1, 0]])'],
      ['E6', 'r2*r3', 2, 'Matrix([[-1, 0, 0, 0, 0, 0, 0, 0], [0, -1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]])'],
      ['E6', 'r3*r4', 3, 'Matrix([[0, 0, 1, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]])'],
      ['F4', 'r2*r3', 4, 'Matrix([[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, -1], [0, 0, 1, 0]])'],
      ['F4', 'r1*r4', 2, 'Matrix([[1/2, 1/2, 1/2, 1/2], [1/2, -1/2, 1/2, -1/2], [1/2, 1/2, -1/2, -1/2], [1/2, -1/2, -1/2, 1/2]])'],
      ['G2', 'r1*r2*r1', 2, 'Matrix([[2/3, -1/3, 2/3], [-1/3, 2/3, 2/3], [2/3, 2/3, -1/3]])'],
      ['G2', 'r1*r2', 6, 'Matrix([[2/3, 2/3, -1/3], [-1/3, 2/3, 2/3], [2/3, -1/3, 2/3]])'],
      ['G2', 'r1*r2*r1*r2', 3, 'Matrix([[0, 1, 0], [0, 0, 1], [1, 0, 0]])'],
      ['G2', 'r1*r2*r2*r1', 1, 'Matrix([[1, 0, 0], [0, 1, 0], [0, 0, 1]])'],
    ];
    for (const [t, e, order, m] of cases) {
      const w = new L.WeylGroup(t);
      expect(w.elementOrder(e)).toBe(order);
      expect(mat(w.matrixForm(e))).toBe(m);
    }
    // (SymPy's first reflection of the E series does not generate a finite group: SymPy loops forever)
    expect(() => new L.WeylGroup('E6').elementOrder('r1*r2')).toThrow(sj.NotImplementedError);
  });
});

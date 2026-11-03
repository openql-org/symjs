// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/tensor/idx.ts.
// Idx, Indexed and IndexedBase. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Sym, add, diff, mul, oo, symbols, S, sympify } from '../../src';
import { isIntegerQ } from '../../src/core/assumptions';
import { NoMatch } from '../../src/core/truth';
import { Idx } from '../../src/tensor';

// SymPy sympy.tensor.array (every doctest of its modules that implement
// sympy.tensor.array.__all__) and sympy.tensor.indexed.Idx; expected
// values from SymPy 1.14.

const [x, y] = symbols('x y z t');
const s = (v: unknown): string => String(v);

describe('sympy.tensor.indexed.Idx', () => {
  const [n, i, L, U] = symbols('n i L U', { integer: true });

  it('Idx', () => {
    const q = Idx('qwerty');
    expect(s(q)).toBe('qwerty');
    expect([(q as Idx).lower, (q as Idx).upper]).toEqual([NoMatch, NoMatch]);
    const iLU = Idx(i, [L, U]) as Idx;
    expect(s(iLU)).toBe('i');
    expect([s(iLU.lower), s(iLU.upper)]).toEqual(['L', 'U']);
    const iN = Idx(i, n) as Idx;
    expect([s(iN.lower), s(iN.upper)]).toEqual(['0', 'n - 1']);
    const i4 = Idx(i, 4) as Idx;
    expect([s(i4.lower), s(i4.upper)]).toEqual(['0', '3']);
    const iOo = Idx(i, oo) as Idx;
    expect([s(iOo.lower), s(iOo.upper)]).toEqual(['0', 'oo']);
  });

  it('label, lower, upper', () => {
    const xi = new Sym('x', { integer: true });
    expect(s((Idx(xi) as Idx).label)).toBe('x');
    const jj = new Sym('j', { integer: true });
    expect(s((Idx(jj) as Idx).label)).toBe('j');
    expect(s((Idx(add(jj, 1)) as Idx).label)).toBe('j + 1');
    expect(s((Idx('j', 2) as Idx).lower)).toBe('0');
    expect(s((Idx('j', 5) as Idx).lower)).toBe('0');
    expect((Idx('j') as Idx).lower).toBe(NoMatch);
    expect(s((Idx('j', 2) as Idx).upper)).toBe('1');
    expect(s((Idx('j', 5) as Idx).upper)).toBe('4');
    expect((Idx('j') as Idx).upper).toBe(NoMatch);
  });
});

describe('Idx: more cases', () => {
  const [i, n] = symbols('i n', { integer: true });
  it('construction', () => {
    expect(s(Idx(3))).toBe('3');
    expect(Idx(3).equals(Idx(3n))).toBe(true);
    expect(() => Idx(x)).toThrow('Idx object requires an integer label.');
    expect(() => Idx(i, 2.5)).toThrow('Idx object requires an integer dimension.');
    expect(() => Idx(i, [1, 2, 3])).toThrow('Idx range tuple must have length 2, but got 3');
    expect(() => Idx(i, [1.5, 2])).toThrow('Idx object requires integer bounds.');
    expect(s((Idx(i, [mul(-1, oo), oo]) as Idx).lower)).toBe('-oo');
    expect(s((Idx(i, [n, oo]) as Idx).upper)).toBe('oo');
    expect(s(Idx(i, x))).toBe('i');
    expect(() => new Idx(3 as never)).toThrow(TypeError);
  });

  it('a symbol with a range', () => {
    const i4 = Idx(i, 4) as Idx;
    expect(i4).toBeInstanceOf(Idx);
    expect(i4).toBeInstanceOf(Sym);
    expect(i4.name).toBe('i');
    expect([...i4.freeSymbols()]).toEqual([i4]);
    expect(isIntegerQ(i4)).toBe(true);
    expect(s(diff(i4, i4))).toBe('1');
    expect(s(mul(2, i4))).toBe('2*i');
    expect(i4.equals(i)).toBe(false);
    expect(i4.equals(Idx(i, 4))).toBe(true);
    expect(i4.equals(Idx(i, 5))).toBe(false);
  });

  it('latex', () => {
    expect((Idx(i, 4) as Idx).toLatex()).toBe('{i}_{0\\mathrel{..}\\nobreak 3}');
    expect((Idx(i, [1, y]) as Idx).toLatex()).toBe('{i}_{1\\mathrel{..}\\nobreak y}');
    expect((Idx(i) as Idx).toLatex()).toBe('i');
    expect((Idx(i, oo) as Idx).toLatex()).toBe('{i}_{0\\mathrel{..}\\nobreak \\infty}');
  });
});

// Edge cases of sympy.tensor.array (slicing, construction, assignment,
// sparse arrays, derivatives), ArrayComprehension and Idx; expected values
// from SymPy 1.14.

describe('ArrayComprehension and Idx', () => {
  it('Idx labels', () => {
    expect(() => Idx(S.Half)).toThrow(TypeError);
    expect(() => new Idx(sympify(3))).toThrow(TypeError);
  });
});

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/public.ts: the public forms of the Expr methods that return NoMatch.

import { describe, expect, it } from 'vitest';
import { NoMatch, O, Wild, add, getO, matches, symbols } from '../../src';

const [x, y, z] = symbols('x y z');
const show = (m: unknown): string => (m instanceof Map ? `{${[...m].map(([k, v]) => `${String(k)}: ${String(v)}`).join(', ')}}` : String(m));

describe('matches and getO', () => {
  it('matches is match with the pattern first (SymPy pattern.matches(expr))', () => {
    const [w, v] = [new Wild('w'), new Wild('v')];
    expect(show(matches(add(w, v), add(x, y)))).toBe('{w_: y, v_: x}');
    expect(show(matches(add(x, w), add(x, y)))).toBe('{w_: y}');
    expect(matches(add(x, w), z)).toBe(NoMatch);
    expect(show(matches(w, x))).toBe('{w_: x}');
  });
  it('getO', () => {
    const o = O(x.pow(2));
    expect(String(getO(add(1, x, o)))).toBe('O(x**2)');
    expect(String(getO(o))).toBe('O(x**2)');
    // SymPy (1 + x).getO() is None
    expect(getO(add(1, x))).toBe(NoMatch);
  });
});

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/solvers/decompogen.ts.
// General functional decomposition and composition. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { compogen, decompogen } from '../../src/solvers';

const [x, y] = sj.symbols('x y') as sj.Sym[];
const f = sj.SymFunction('f');
const P = (s: string): sj.Expr => sj.parse(s, { symbols: [x!, y!] });
const d = (s: string | sj.Expr): string[] => decompogen(typeof s === 'string' ? P(s) : s, x!).map(sj.str);

describe('decompogen', () => {
  it('decomposes functions and polynomials', () => {
    expect(d('sin(cos(x))')).toEqual(['sin(x)', 'cos(x)']);
    expect(d('sin(x)**2 + sin(x) + 1')).toEqual(['x**2 + x + 1', 'sin(x)']);
    expect(d('sqrt(6*x**2 - 5)')).toEqual(['sqrt(x)', '6*x**2 - 5']);
    expect(d('sin(sqrt(cos(x**2 + 1)))')).toEqual(['sin(x)', 'sqrt(x)', 'cos(x)', 'x**2 + 1']);
    expect(d('x**4 + 2*x**3 - x - 1')).toEqual(['x**2 - x - 1', 'x**2 + x']);
    expect(d('exp(sin(x))')).toEqual(['exp(x)', 'sin(x)']);
    expect(d('exp(x)')).toEqual(['exp(x)']);
    expect(d('Abs(x**2 - 1)')).toEqual(['Abs(x)', 'x**2 - 1']);
    expect(d(f(P('x**2')))).toEqual(['f(x)', 'x**2']);
    expect(d('5')).toEqual(['5']);
    expect(d('x')).toEqual(['x']);
    expect(d('x**3 + x')).toEqual(['x**3 + x']);
    expect(d('x**2*y + x')).toEqual(['x**2*y + x']);
    expect(d('x*y + 1')).toEqual(['x*y + 1']);
  });
  it('Min and Max', () => {
    expect(d('Max(sin(x)**3 + 1, sin(x)**2)')).toEqual(['Max(x**2, x**3 + 1)', 'sin(x)']);
    expect(d('Max(2, sin(x), sin(x)**2)')).toEqual(['Max(2, x, x**2)', 'sin(x)']);
    expect(d('Min(sin(x)**2, cos(x)**2)')).toEqual(['Min(sin(x)**2, cos(x)**2)']);
    expect(d('Max(3, sqrt(x))')).toEqual(['Max(3, sqrt(x))']);
    expect(d('Max(x**2 + 1, sin(x))')).toEqual(['Max(x**2 + 1, sin(x))']);
    expect(d('Max(y, sin(x)**2)')).toEqual(['Max(x**2, y)', 'sin(x)']);
  });
  it('rejects relations and boolean functions', () => {
    expect(() => decompogen(sj.Eq(x!, 1), x!)).toThrow('expecting Expr but got: `Equality`');
    expect(() => decompogen(sj.And(sj.Gt(x!, 1), sj.Gt(y!, 1)), x!)).toThrow('expecting Expr but got: `And`');
  });
});

describe('compogen', () => {
  it('composes', () => {
    const c = (gs: string[]): string => sj.str(compogen(gs.map(P), x!));
    expect(c(['sin(x)', 'cos(x)'])).toBe('sin(cos(x))');
    expect(c(['x**2 + x + 1', 'sin(x)'])).toBe('sin(x)**2 + sin(x) + 1');
    expect(c(['sqrt(x)', '6*x**2 - 5'])).toBe('sqrt(6*x**2 - 5)');
    expect(c(['sin(x)', 'sqrt(x)', 'cos(x)', 'x**2 + 1'])).toBe('sin(sqrt(cos(x**2 + 1)))');
    expect(c(['x**2 - x - 1', 'x**2 + x'])).toBe('-x**2 - x + (x**2 + x)**2 - 1');
    expect(c(['x'])).toBe('x');
  });
});

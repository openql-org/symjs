// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/** Public names of docs/api-policy.md: SymPy names, deprecated aliases, Map results. */

import { describe, expect, it } from 'vitest';
import * as sj from '../src';

const [x, y] = sj.symbols('x y');

describe('SymPy names', () => {
  it('classes have SymPy names', () => {
    expect(new sj.Sym('z')).toBeInstanceOf(sj.Sym);
    expect(sj.pi).toBeInstanceOf(sj.NumberSymbol);
    expect(sj.sin(x)).toBeInstanceOf(sj.AppliedFunction);
    expect(sj.S.true).toBeInstanceOf(sj.BooleanAtom);
    expect(sj.SymFunction('f')(x)).toBeInstanceOf(sj.AppliedUndef);
  });

  it('Derivative and Piecewise are callable classes', () => {
    const f = sj.SymFunction('f');
    const d = sj.Derivative(f(x), x, [y, 2]);
    expect(d).toBeInstanceOf(sj.Derivative);
    expect(sj.sstr(d)).toBe('Derivative(f(x), x, (y, 2))');
    const p = sj.Piecewise([x, sj.Lt(x, 0)], [y, true]);
    expect(p).toBeInstanceOf(sj.Piecewise);
    expect(sj.sstr(p)).toBe('Piecewise((x, x < 0), (y, True))');
  });

  it('logic and set operations use SymPy class names', () => {
    expect(sj.sstr(sj.And(sj.Lt(x, 1), sj.Gt(x, 0)))).toBe('(x > 0) & (x < 1)');
    expect(sj.sstr(sj.Or(sj.Lt(x, 0), sj.Not(sj.Lt(x, 1))))).toBe('(x >= 1) | (x < 0)');
    expect(sj.sstr(sj.Union(sj.Interval.of(0, 1), sj.Interval.open(2, 3)))).toBe('Union(Interval(0, 1), Interval.open(2, 3))');
    expect(sj.sstr(sj.Intersection(sj.Interval.Lopen(0, 2), sj.Interval.Ropen(1, 3)))).toBe('Interval(1, 2)');
    expect(sj.sstr(sj.Complement(sj.FiniteSet.of(1, 2, 3), sj.FiniteSet.of(2)))).toBe('{1, 3}');
  });

  it('kept aliases and camelCase names', () => {
    expect(sj.sstr(sj.parseExpr('x + 1'))).toBe(sj.str(sj.parse('x + 1')));
    expect(sj.sstr(sj.Abs(sj.mul(-2, x)))).toBe('2*Abs(x)');
    expect(sj.sstr(sj.expandMul(sj.parse('x*(y + 1)')))).toBe('x*y + x');
    expect(sj.sstr(sj.expandLog(sj.parse('log(x*y)'), { force: true } as never))).toBe('log(x) + log(y)');
    expect([...sj.factorint(12n)]).toEqual([[2n, 2n], [3n, 1n]]);
  });

  it('deprecated aliases still work', () => {
    expect(sj.Sym).toBe(sj.Sym);
    expect(sj.rational(1, 2)).toEqual(sj.Rational.of(1, 2));
    expect(sj.str(sj.interval(0, 1))).toBe('Interval(0, 1)');
    expect(sj.str(sj.union(sj.finiteSet(1), sj.finiteSet(2)))).toBe('{1, 2}');
  });
});

describe('dict results are Maps keyed structurally', () => {
  it('roots returns root -> multiplicity', () => {
    const r = sj.roots(sj.parse('(x - 1)**2*(x + 2)'), x);
    expect(r).toBeInstanceOf(Map);
    expect(r.get(sj.Rational.of(1))).toBe(2);
    expect(r.get(-2)).toBe(1);
    expect(sj.roots(sj.parse('x**2 - 1'), x, { multiple: true }).map(String)).toEqual(['-1', '1']);
  });

  it('asCoefficientsDict and ExprMap lookups', () => {
    const d = sj.asCoefficientsDict(sj.parse('3*x + 2*y + 5'));
    expect(d.get(sj.parse('x'))).toEqual(sj.Rational.of(3));
    expect(d.get(1)).toEqual(sj.Rational.of(5));
    const m = new sj.ExprMap<number>([[sj.parse('x + 1'), 1]]);
    m.set(sj.parse('1 + x'), 2);
    expect(m.size).toBe(1);
    expect(m.get(sj.add(x, 1))).toBe(2);
    expect(m.delete(sj.add(1, x))).toBe(true);
    expect(m.has(sj.add(x, 1))).toBe(false);
  });
});

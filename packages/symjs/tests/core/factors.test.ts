// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/factors.ts.
// Factors (SymPy sympy.core.exprtools.Factors). Each case gives the SymPy 1.14 expression and its str().

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';

const [x, y, z, n, m] = sj.symbols('x y z n m');

const A = sj.symbol('A', { commutative: false });
const B = sj.symbol('B', { commutative: false });

const show = (v: unknown): string =>
  typeof v === 'boolean' ? (v ? 'True' : 'False') : v instanceof Set ? `{${[...v].map(String).sort().join(', ')}}` : Array.isArray(v) ? `(${v.map(String).join(', ')})` : String(v);

const attempt = (run: () => unknown): string => {
  try {
    return show(run());
  } catch (err) {
    return `ERR ${err instanceof Error ? err.name : String(err)}`;
  }
};

const CASES: readonly (readonly [sympy: string, run: () => unknown, expected: string])[] = [
  ["Factors({I: 2, S.NegativeOne: 1, x: 1})", () => new sj.Factors(new Map<sj.Expr, sj.ExprLike>([[sj.I, 2], [sj.S.NegOne, 1], [x, 1]])), "Factors({x: 1})"],
  ["Factors({I: 3, x: 1})", () => new sj.Factors(new Map<sj.Expr, sj.ExprLike>([[sj.I, 3], [x, 1]])), "Factors({-1: 1, I: 1, x: 1})"],
  ["Factors({S.NegativeOne: Rational(1, 2), x: 1})", () => new sj.Factors(new Map<sj.Expr, sj.ExprLike>([[sj.S.NegOne, sj.Rational.of(1n, 2n)], [x, 1]])), "Factors({I: 1, x: 1})"],
  ["Factors({S.NegativeOne: n, x: 1})", () => new sj.Factors(new Map<sj.Expr, sj.ExprLike>([[sj.S.NegOne, n], [x, 1]])), "Factors({-1: n, x: 1})"],
  ["Factors({S.One: 2, x: 1})", () => new sj.Factors(new Map<sj.Expr, sj.ExprLike>([[sj.S.One, 2], [x, 1]])), "Factors({x: 1})"],
  ["Factors(0)", () => new sj.Factors(0), "Factors({0: 1})"],
  ["Factors(1)", () => new sj.Factors(1), "Factors({})"],
  ["Factors()", () => new sj.Factors(), "Factors({})"],
  ["Factors(x)", () => new sj.Factors(x), "Factors({x: 1})"],
  ["Factors(Rational(-3, 4))", () => new sj.Factors(sj.Rational.of(-3n, 4n)), "Factors({-1: 1, 3: 1, 4: -1})"],
  ["Factors(Rational(-1, 4))", () => new sj.Factors(sj.Rational.of(-1n, 4n)), "Factors({-1: 1, 4: -1})"],
  ["Factors(-1)", () => new sj.Factors(-1), "Factors({-1: 1})"],
  ["Factors(6)", () => new sj.Factors(6), "Factors({6: 1})"],
  ["Factors(x**2*y/3)", () => new sj.Factors(sj.mul(sj.pow(x, 2), y, sj.Rational.of(1n, 3n))), "Factors({1: 1, 3: -1, x: 2, y: 1})"],
  ["Factors(2*x/3)", () => new sj.Factors(sj.mul(2, x, sj.Rational.of(1n, 3n))), "Factors({2: 1, 3: -1, x: 1})"],
  ["Factors(2*I*x)", () => new sj.Factors(sj.mul(2, sj.I, x)), "Factors({2: 1, I: 1, x: 1})"],
  ["Factors(A*B*x)", () => new sj.Factors(sj.mul(A, B, x)), "Factors({x: 1, A*B: 1})"],
  ["Factors(pi)", () => new sj.Factors(sj.pi), "Factors({pi: 1})"],
  ["Factors({x**2: 3, y: Rational(1,2), z: 1}).as_expr()", () => new sj.Factors(new Map<sj.Expr, sj.ExprLike>([[sj.pow(x, 2), 3], [y, sj.Rational.of(1n, 2n)], [z, 1]])).asExpr(), "x**6*sqrt(y)*z"],
  ["Factors(x).gens", () => new sj.Factors(x).gens, "{x}"],
  ["Factors(0).is_zero", () => new sj.Factors(0).isZero, "True"],
  ["Factors(1).is_one", () => new sj.Factors(1).isOne, "True"],
  ["Factors(x).mul(0)", () => new sj.Factors(x).mul(0), "Factors({0: 1})"],
  ["Factors(x).mul(1/x)", () => new sj.Factors(x).mul(sj.pow(x, -1)), "Factors({})"],
  ["Factors(x*y).mul(x*z)", () => new sj.Factors(sj.mul(x, y)).mul(sj.mul(x, z)), "Factors({x: 2, y: 1, z: 1})"],
  ["Factors(x*y).mul(Factors(x))", () => new sj.Factors(sj.mul(x, y)).mul(new sj.Factors(x)), "Factors({x: 2, y: 1})"],
  ["Factors(x).div(0)", () => new sj.Factors(x).div(0), "ERR RangeError"],  // SymPy 1.14 raises ZeroDivisionError
  ["Factors(0).div(x)", () => new sj.Factors(0).div(x), "(Factors({0: 1}), Factors({}))"],
  ["Factors(x**3*y).div(x**2*z)", () => new sj.Factors(sj.mul(sj.pow(x, 3), y)).div(sj.mul(sj.pow(x, 2), z)), "(Factors({x: 1, y: 1}), Factors({z: 1}))"],
  ["Factors(x**2*y).div(Factors(x**3))", () => new sj.Factors(sj.mul(sj.pow(x, 2), y)).div(new sj.Factors(sj.pow(x, 3))), "(Factors({y: 1}), Factors({x: 1}))"],
  ["Factors(x**2).div(x**2)", () => new sj.Factors(sj.pow(x, 2)).div(sj.pow(x, 2)), "(Factors({}), Factors({}))"],
  ["Factors(x**(n+2)).div(x**(n+1))", () => new sj.Factors(sj.pow(x, sj.add(n, 2))).div(sj.pow(x, sj.add(n, 1))), "(Factors({x: 1}), Factors({}))"],
  ["Factors(x**(n+1)).div(x**(n+1))", () => new sj.Factors(sj.pow(x, sj.add(n, 1))).div(sj.pow(x, sj.add(n, 1))), "(Factors({}), Factors({}))"],
  ["Factors(x**(n+2)).div(x**(m+1))", () => new sj.Factors(sj.pow(x, sj.add(n, 2))).div(sj.pow(x, sj.add(m, 1))), "(Factors({x: n + 1}), Factors({x: m}))"],
  ["Factors(x**(n+1)).div(x**(m+2))", () => new sj.Factors(sj.pow(x, sj.add(n, 1))).div(sj.pow(x, sj.add(m, 2))), "(Factors({x: n}), Factors({x: m + 1}))"],
  ["Factors(x**(n+1)).div(x**(m+1))", () => new sj.Factors(sj.pow(x, sj.add(n, 1))).div(sj.pow(x, sj.add(m, 1))), "(Factors({x: n}), Factors({x: m}))"],
  ["Factors(x**n).div(x**m)", () => new sj.Factors(sj.pow(x, n)).div(sj.pow(x, m)), "(Factors({x: n}), Factors({x: m}))"],
  ["Factors(x**(n+1)).div(x**(n+3))", () => new sj.Factors(sj.pow(x, sj.add(n, 1))).div(sj.pow(x, sj.add(n, 3))), "(Factors({}), Factors({x: 2}))"],
  ["Factors(x*y).quo(x)", () => new sj.Factors(sj.mul(x, y)).quo(x), "Factors({y: 1})"],
  ["Factors(x*y).rem(x*z)", () => new sj.Factors(sj.mul(x, y)).rem(sj.mul(x, z)), "Factors({z: 1})"],
  ["Factors(x**2).div(x**n)", () => new sj.Factors(sj.pow(x, 2)).div(sj.pow(x, n)), "(Factors({x: 2}), Factors({x: n}))"],
  ["Factors(x**(n+m)).div(x**z)", () => new sj.Factors(sj.pow(x, sj.add(n, m))).div(sj.pow(x, z)), "(Factors({x: m + n}), Factors({x: z}))"],
  ["Factors({S.NegativeOne: Rational(1,3), x: 1})", () => new sj.Factors(new Map<sj.Expr, sj.ExprLike>([[sj.S.NegOne, sj.Rational.of(1n, 3n)], [x, 1]])), "Factors({-1: 1/3, x: 1})"],
  ["Factors(x**(2*n)).div(x**n)", () => new sj.Factors(sj.pow(x, sj.mul(2, n))).div(sj.pow(x, n)), "(Factors({x: n}), Factors({}))"],
  ["Factors(x**(n+2)).div(x**3)", () => new sj.Factors(sj.pow(x, sj.add(n, 2))).div(sj.pow(x, 3)), "(Factors({x: n}), Factors({x: 1}))"],
  ["Factors(x**(n+2)).div(x**1)", () => new sj.Factors(sj.pow(x, sj.add(n, 2))).div(x), "(Factors({x: n + 1}), Factors({}))"],
  ["Factors(None)", () => new sj.Factors(null), "Factors({})"],
  ["Factors(Factors(x))", () => new sj.Factors(new sj.Factors(x)), "Factors({x: 1})"],
];

describe('Factors (SymPy Factors)', () => {
  it.each(CASES)('%s', (_sympy, run, expected) => {
    expect(attempt(run)).toBe(expected);
  });
});

describe('Factors product operations', () => {
  const a = new sj.Factors(sj.mul(sj.pow(x, 5), sj.pow(y, 3), sj.pow(z, 7)));
  const b = new sj.Factors(sj.mul(sj.pow(y, 4), sj.pow(z, 3)));
  it('scales exponents and validates powers', () => {
    expect(String(a.pow(3))).toBe('Factors({x: 15, y: 9, z: 21})');
    expect(String(a.pow(new sj.Factors(2)))).toBe('Factors({x: 10, y: 6, z: 14})');
    expect(a.pow(0).isOne).toBe(true);
    for (const e of [-1, x, sj.Rational.of(1n, 2n)]) expect(() => a.pow(e)).toThrow(RangeError);
  });
  it('takes common and union factors with comparable exponents', () => {
    expect(String(a.gcd(b))).toBe('Factors({y: 3, z: 3})');
    expect(String(a.gcd(0))).toBe(String(a));
    expect(String(a.gcd(sj.pow(y, 2)))).toBe('Factors({y: 2})');
    expect(String(new sj.Factors(sj.pow(x, n)).gcd(sj.pow(x, m)))).toBe('Factors({})');
    expect(String(a.lcm(b))).toBe('Factors({x: 5, y: 4, z: 7})');
    expect(String(a.lcm(sj.mul(sj.pow(y, 2), n)))).toBe('Factors({n: 1, x: 5, y: 3, z: 7})');
    expect(a.lcm(0).isZero).toBe(true);
    expect(new sj.Factors(0).lcm(x).isZero).toBe(true);
    expect(() => new sj.Factors(sj.pow(x, n)).lcm(sj.pow(x, m))).toThrow(TypeError);
  });
  it('normalizes products and zero inputs', () => {
    expect(a.normal(b).map(String)).toEqual(['Factors({x: 5, z: 4})', 'Factors({y: 1})']);
    expect(new sj.Factors(x).normal(2).map(String)).toEqual(['Factors({x: 1})', 'Factors({2: 1})']);
    expect(new sj.Factors(x).normal(0).map(String)).toEqual(['Factors({})', 'Factors({0: 1})']);
    expect(new sj.Factors(0).normal(x).map(String)).toEqual(['Factors({0: 1})', 'Factors({})']);
    expect(new sj.Factors(sj.pow(x, sj.add(n, 3))).div(sj.pow(x, -3)).map(String)).toEqual(['Factors({x: n + 6})', 'Factors({})']);
  });
  it('splits signed floats and infinity', () => {
    expect(String(new sj.Factors(sj.S.NegativeInfinity))).toBe('Factors({-1: 1, oo: 1})');
    expect(String(new sj.Factors(new sj.Float(-2)))).toBe('Factors({2.00000000000000: 1, -1: 1})');
    expect(String(new sj.Factors(new sj.Float(2)))).toBe('Factors({2.00000000000000: 1})');
  });
});


it('normalizes float units in factor maps without normalizing other bases', () => {
  const make = (b: number, e: sj.ExprLike) => new sj.Factors(new Map<sj.Expr, sj.ExprLike>([[new sj.Float(b), e], [sj.I, 1]]));
  expect(String(make(-1, 2))).toBe('Factors({1.00000000000000: 1, I: 1})');
  expect(String(make(-1, 3))).toBe('Factors({1.00000000000000: 1, -1: 1, I: 1})');
  expect(String(make(1, 2))).toBe('Factors({1.00000000000000: 1, I: 1})');
  expect(String(make(2, 2))).toBe('Factors({2.00000000000000: 2, I: 1})');
});

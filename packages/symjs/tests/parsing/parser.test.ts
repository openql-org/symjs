// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/parsing/parser.ts.

// The expression parser and the ex template tag: errors, unevaluated sums and products, and the deprecated polys
// entry divExact. Expected values are `str(parse_expr(s))` (and `evaluate=False`) of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Add, Mul, ex, parse, pow, simplify, sstr, symbol, symbols } from '../../src';
import * as sj from '../../src';

const [x] = symbols('x y');
const s = (src: string, opts: Parameters<typeof parse>[1] = {}): string => sj.str(parse(src, opts));

describe('parser', () => {
  it('parses expressions', () => {
    expect(parse('x^2 + 2*x + 1').toString()).toBe('x**2 + 2*x + 1');
    expect(parse('-x^2').toString()).toBe('-x**2');
    expect(parse('2^3^2').toString()).toBe('512');
    expect(parse('sqrt(8)/2').toString()).toBe('sqrt(2)');
    expect(parse('exp(I*pi)').toString()).toBe('-1');
    expect(parse('x ** 2').equals(pow(x, 2))).toBe(true);
    expect(() => parse('2x')).toThrow(/implicit multiplication/);
  });

  it('supports the ex template tag', () => {
    const t = symbol('t', { real: true });
    const e = ex`cos(${t}/2)^2 + sin(${t}/2)^2`;
    expect(simplify(e).toString()).toBe('1');
    expect(ex`${t} + t`.toString()).toBe('2*t');
  });
});

describe('parser and assumptions', () => {
  it('repeating decimals', () => {
    expect(['.[3]', '1.2[3]', '0.[142857]', '-1.[3]'].map((s) => sstr(parse(s)))).toEqual(['1/3', '37/30', '1/7', '-4/3']);
  });
});

describe('parser options', () => {
  it('logical operators, Xor, evaluate=False and implicit multiplication', () => {
    expect(sstr(parse('x^y', { convertXor: false }))).toBe('x ^ y');
    expect(sstr(parse('~x | y & x'))).toBe('~x | (x & y)');
    expect(sstr(parse('2**2 / 3 + 5', { evaluate: false }))).toBe('2**2/3 + 5');
    expect(sstr(parse('4/2+7', { evaluate: false }))).toBe('4/2 + 7');
    expect(sstr(parse('2x y + sin x', { transformations: 'all' }))).toBe('2*x*y + sin(x)');
    expect(sstr(parse('x(y+1)', { transformations: 'all' }))).toBe('x*(y + 1)');
  });
});

describe('relations in the parser, Wild collect and piecewise definite integrals', () => {
  it('match SymPy', async () => {
    const { collect, Wild, integrate, Piecewise, Rational, add, pow } = await import('../../src');
    const [x, t, y] = symbols('x t y');
    expect(sstr(parse('x/t < 0'))).toBe('x/t < 0');
    expect(sstr(collect(parse('a*x**y - b*x**y'), [pow(new Wild('w1'), parse('y'))]))).toBe('x**y*(a - b)');
    const p = add(pow(x, 2), Piecewise([0, parse('x/t < 0', { symbols: { x, t } } as never)], [1, true]));
    const r1 = integrate(p, t, [Rational.of(4, 5), 1]);
    expect(sstr(r1)).toBe('x**2/5 + Piecewise((0, x < 0), (1, True))/5');
    expect(sstr(integrate(r1, x, [-1, 1]))).toBe('1/3');
    void y;
  });
});

describe('parse', () => {
  const cases: [string, string][] = [
    ['x + 1   ', 'x + 1'],
    ['ln(x)', 'log(x)'],
    ['digamma(x)', 'polygamma(0, x)'],
    ['trigamma(x)', 'polygamma(1, x)'],
    ['E1(x)', 'expint(1, x)'],
    ['RisingFactorial(x, 3)', 'x*(x + 1)*(x + 2)'],
    ['FallingFactorial(x, 3)', 'x*(x - 2)*(x - 1)'],
    ['diff(x**3, x, 2)', '6*x'],
    ['diff(sin(x), x)', 'cos(x)'],
  ];
  for (const [src, want] of cases) it(src, () => expect(s(src)).toBe(want));

  const raw: [string, string][] = [
    ['x - y', 'x - y'],
    ['-x', '-x'],
    ['+x', 'x'],
    ['-2', '-2'],
    ['x + (y + z)', 'x + y + z'],
    ['x*(y*z)', 'x*y*z'],
    ['x/y', 'x/y'],
    ['(x)', 'x'],
  ];
  for (const [src, want] of raw) it(`${src} (evaluate=False)`, () => expect(s(src, { evaluate: false })).toBe(want));

  it('symbols given as a list', () => {
    const x = sj.symbol('x', { positive: true });
    const e = parse('x + 1', { symbols: [x] });
    expect(e.freeSymbols().has(x)).toBe(true);
  });

  it('syntax errors', () => {
    expect(() => parse('x $ y')).toThrow(SyntaxError);
    expect(() => parse('diff(x)')).toThrow('diff() takes at least 2 arguments');
    expect(() => parse('(x')).toThrow("Expected ')'");
    expect(() => parse('2 x')).toThrow('implicit multiplication is not supported');
    expect(() => parse('*x')).toThrow("Unexpected '*'");
    expect(() => parse('x +')).toThrow('Unexpected end of input');
    expect(() => parse('')).toThrow('Unexpected end of input');
  });

  it('ex with an interpolated number', () => {
    const x = sj.symbol('x');
    expect(sj.str(ex`${2}*${x} + 1`)).toBe('2*x + 1');
  });
});

describe('parse', () => {
  it('explains a missing operator', () => {
    const hint = 'implicit multiplication is not supported; use *';
    expect(() => parse('x 2')).toThrow(hint);
    expect(() => parse('2 (3)')).toThrow(hint);
    expect(() => parse('2 0.[3]')).toThrow(hint);
    expect(() => parse('2 )')).toThrow('Unexpected token at 2');
    expect(() => parse('2 )')).not.toThrow(hint);
  });
  it('needs both sides of Eq', () => {
    // SymPy: Eq(x) is a TypeError (missing rhs)
    expect(() => parse('Eq(x)')).toThrow('Eq() takes at least 2 arguments');
    expect(sstr(parse('Eq(x, 1)'))).toBe('Eq(x, 1)');
  });
  it('flattens unevaluated sums and products', () => {
    // SymPy: parse_expr('(x+y)+z', evaluate=False) has the args (x, y, z)
    const s = parse('(x+y)+z', { evaluate: false });
    expect(s).toBeInstanceOf(Add);
    expect([sstr(s), s.args.length]).toEqual(['x + y + z', 3]);
    const p = parse('(x*y)*z', { evaluate: false });
    expect(p).toBeInstanceOf(Mul);
    expect([sstr(p), p.args.length]).toEqual(['x*y*z', 3]);
  });
});

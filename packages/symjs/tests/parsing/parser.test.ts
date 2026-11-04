// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/parsing/parser.ts.

// The expression parser and the ex template tag: errors, unevaluated sums and products, and the deprecated polys
// entry divExact. Expected values are `str(parse_expr(s))` (and `evaluate=False`) of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { Add, Mul, ex, parse, pow, simplify, sstr, symbol, symbols } from '../../src';
import * as sj from '../../src';
import { parserHooks } from '../../src/parsing/parser';

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
    // SymPy 1.14 leaves this Integral unevaluated; the conditions are reduced as SymPy's
    // reduce_inequalities writes them
    expect(sstr(r1)).toBe('x**2/5 + Piecewise((0, (x > -oo) & (x < 0)), (1/5, True))');
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
    // SymPy parse_expr('diff(x)') is 1 (the only free symbol); diff(x*y) is a ValueError
    expect(s('diff(x)')).toBe('1');
    expect(() => parse('diff(x*y)')).toThrow('diff() takes at least 2 arguments');
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

describe('parse: floats (SymPy auto_number makes Float(s))', () => {
  it('parses decimals as Float with the precision of the digits', () => {
    const prec = (e: sj.Expr) => (e instanceof sj.Float ? e.prec : -1);
    const cases: [string, string, number][] = [
      ['2.0', '2.00000000000000', 53],
      ['1e-3', '0.00100000000000000', 53],
      ['.5', '0.500000000000000', 53],
      ['2.', '2.00000000000000', 53],
      ['1E5', '100000.000000000', 53],
      ['1.5e10', '15000000000.0000', 53],
      ['1e20', '100000000000000000000.', 73],
      ['3.14159265358979323846264338', '3.14159265358979323846264338', 93],
    ];
    for (const [src, want, pr] of cases) {
      const e = parse(src);
      expect([src, s(src), prec(e)]).toEqual([src, want, pr]);
    }
    expect(['1.0*y', '2.0**x', '0.1 + 0.2', '2.0*3', '-2.5', '2.5e-3*x', 'x**0.5', 'x + 1.5'].map((src) => s(src))).toEqual([
      '1.0*y',
      '2.0**x',
      '0.300000000000000',
      '6.00000000000000',
      '-2.50000000000000',
      '0.0025*x',
      'x**0.5',
      'x + 1.5',
    ]);
    // evaluate=False: Float('-2.0'); x - 2.5 is Add(x, Mul(-1, 2.5))
    expect(s('-2.0', { evaluate: false })).toBe('-2.00000000000000');
    expect(s('x - 2.5', { evaluate: false })).toBe('x - 1*2.5');
  });
});

describe('parse: tuple arguments (SymPy parse_expr)', () => {
  it('Derivative and diff', () => {
    expect(s('Derivative(f(x), (x, 2))')).toBe('Derivative(f(x), (x, 2))');
    expect(s('Derivative(f(x), x, 2)')).toBe('Derivative(f(x), (x, 2))');
    expect(s('Derivative(f(x), x, x)')).toBe('Derivative(f(x), (x, 2))');
    expect(s('Derivative(f(x, y), x, (y, 2))')).toBe('Derivative(f(x, y), x, (y, 2))');
    expect(s('Derivative(x**2)')).toBe('Derivative(x**2, x)');
    expect(s('Derivative(x**2*y, x, (y, 0))')).toBe('Derivative(x**2*y, x)');
    expect(s('Derivative(f(x), x, 0)')).toBe('f(x)');
    expect(s('diff(f(x), (x, 2))')).toBe('Derivative(f(x), (x, 2))');
    expect(s('diff(f(x, y), x, y, 2)')).toBe('Derivative(f(x, y), x, (y, 2))');
    expect(s('diff(x**3, x, x)')).toBe('6*x');
    expect(s('diff(x**3, x, 2)')).toBe('6*x');
    expect(s('diff(x**2)')).toBe('2*x');
    expect(() => parse('Derivative(f(x), (x, 2, 3))')).toThrow('expected (variable, count)');
    expect(() => parse('Derivative(f(x), (x, y))')).toThrow('expected (variable, count)');
    expect(() => parse('Derivative(f(x), (x, -1))')).toThrow('expected (variable, count)');
    expect(() => parse('Derivative(f(x), x, -1)')).toThrow('expected (variable, count)');
    expect(() => parse('Derivative((x, 1), x)')).toThrow('does not take a tuple as its first argument');
    expect(() => parse('Derivative(2)')).toThrow('takes at least 2 arguments');
  });
  it('Integral', () => {
    expect(s('Integral(f(x), (x, 0, 1))')).toBe('Integral(f(x), (x, 0, 1))');
    expect(s('Integral(x, x)')).toBe('Integral(x, x)');
    expect(s('Integral(x)')).toBe('Integral(x, x)');
    expect(s('Integral(x, (x, 1, 2), (x,))')).toBe('Integral(x, (x, 1, 2), x)');
    expect(s('Integral(x*y, (x, 0, 1), (y, 0, 2))')).toBe('Integral(x*y, (x, 0, 1), (y, 0, 2))');
    expect(s('Integral(exp(-x), (x, 0, oo))')).toBe('Integral(exp(-x), (x, 0, oo))');
    expect(() => parse('Integral(x, (x, 1))')).toThrow('expected x, (x,) or (x, a, b)');
    expect(() => parse('Integral(x, 2)')).toThrow('2 is not a symbol');
  });
  it('Sum, Product and Subs', () => {
    expect(s('Sum(k, (k, 1, n))')).toBe('Sum(k, (k, 1, n))');
    expect(s('Sum(1/k**2, (k, 1, oo))')).toBe('Sum(k**(-2), (k, 1, oo))');
    expect(s('Product(k, (k, 1, n))')).toBe('Product(k, (k, 1, n))');
    // SymPy: ValueError (Sum requires values for lower and upper bounds)
    expect(() => parse('Sum(k, k)')).toThrow('expected limits (k, a, b)');
    expect(() => parse('Sum(k, (k, 1))')).toThrow('expected limits (k, a, b)');
    expect(() => parse('Product(k)')).toThrow('needs limits (k, a, b)');
    expect(s('Subs(f(x), x, 1)')).toBe('Subs(f(x), x, 1)');
    expect(s('Subs(f(x, y), (x, y), (1, 2))')).toBe('Subs(f(x, y), (x, y), (1, 2))');
    expect(s('Subs(x + y, (x,), (1,))')).toBe('Subs(x + y, x, 1)');
    expect(() => parse('Subs(x, x)')).toThrow('takes an expression, variables and points');
    expect(() => parse('Subs(x, x, 1, 2)')).toThrow('takes an expression, variables and points');
  });
  it('Piecewise and True', () => {
    expect(s('Piecewise((x, x > 0), (0, True))')).toBe('Piecewise((x, x > 0), (0, True))');
    expect(s('True')).toBe('True');
    expect(s('False')).toBe('False');
    expect(() => parse('Piecewise(x, y)')).toThrow('expected (expression, condition) pairs');
  });
  it('O', () => {
    expect(s('O(x**2)')).toBe('O(x**2)');
    expect(s('Order(x)')).toBe('O(x)');
    expect(s('O(x, (x, oo))')).toBe('O(x, (x, oo))');
    expect(s('O(x, (x, 0))')).toBe('O(x)');
    expect(s('O(x*y, x, y)')).toBe('O(x*y, x, y)');
    // SymPy: NotImplementedError for different points
    expect(() => parse('O(x*y, (x, 1), (y, 2))')).toThrow(sj.NotImplementedError);
    expect(() => parse('O(x, (x, 1, 2))')).toThrow('expected x or (x, point)');
    expect(() => parse('O(x, 2)')).toThrow('2 is not a symbol');
  });
  it('O reduced to its leading term by a registered constructor', async () => {
    const { O } = await import('../../src/series/series');
    parserHooks.order = (e, vars, point) => O(e, vars.length ? vars : undefined, point);
    try {
      // SymPy parse_expr
      expect(s('O(x + x**2)')).toBe('O(x)');
      expect(s('O(x**2, (x, 1))')).toBe('O(1, (x, 1))');
      expect(s('O(x*y + x**2*y**2, x, y)')).toBe('O(x*y, x, y)');
      expect(s('O(1/x + 1/x**2, (x, oo))')).toBe('O(1/x, (x, oo))');
    } finally {
      delete parserHooks.order;
    }
  });
  it('O without the series module (the core entry) keeps its argument unreduced', () => {
    const saved = parserHooks.order;
    delete parserHooks.order;
    try {
      // SymPy parse_expr (these arguments are already their leading terms)
      expect(s('O(x**2)')).toBe('O(x**2)');
      expect(s('O(x**2, (x, 0))')).toBe('O(x**2)');
      expect(s('O(x - 1, (x, 1))')).toBe('O(x - 1, (x, 1))');
      expect(s('O(x*y, x, y)')).toBe('O(x*y, x, y)');
    } finally {
      if (saved) parserHooks.order = saved;
    }
  });
  it('tuples elsewhere', () => {
    expect(s('f((x + 1)*2, (x))')).toBe('f(2*x + 2, x)');
    expect(() => parse('sin((x, 1))')).toThrow('sin() does not take a tuple argument');
    expect(() => parse('f((x, 1))')).toThrow('f() does not take a tuple argument');
    expect(() => parse('(x, 1)')).toThrow("Expected ')'");
  });
});

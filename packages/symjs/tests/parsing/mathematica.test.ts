// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/parsing/mathematica.ts.
// Parser of Wolfram Mathematica code. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { MathematicaParser, parseMathematica } from '../../src/parsing/mathematica';
import { parserHooks } from '../../src/parsing/parser';

const P = (s: string): string => sj.str(parseMathematica(s));

describe('parse_mathematica', () => {
  it('parses the documented examples', () => {
    expect(P('Sin[x]^2 Tan[y]')).toBe('sin(x)**2*tan(y)');
    expect(P('F[7,5,3]')).toBe('F(7, 5, 3)');
    expect(P('x*(a + b)')).toBe('x*(a + b)');
    expect(P('Times[x, Plus[a, b]]')).toBe('x*(a + b)');
    expect(P('{{a, b}, {c, d}}')).toBe('((a, b), (c, d))');
    expect(String(sj.Matrix.of(parseMathematica('{{a, b}, {c, d}}').args.map((r) => r.args)))).toBe('Matrix([[a, b], [c, d]])');
    expect(P('x_.')).toBe('Optional(Pattern(x, Blank()))');
    expect(P('Plus @@ {x, y, z}')).toBe('Apply(Plus, (x, y, z))');
    expect(P('f[x_, 3] := x^3 /; x > 0')).toBe('SetDelayed(f(Pattern(x, Blank()), 3), Condition(x**3, x > 0))');
  });

  it('parses arithmetic in the standard input form', () => {
    const cases: [string, string][] = [
      ['- 6x', '-6*x'],
      ['-2x^3', '-2*x**3'],
      ['x/y', 'x/y'],
      ['x - y', 'x - y'],
      ['x^2 y', 'x**2*y'],
      ['2 x y + 3', '2*x*y + 3'],
      ['a - b - c', 'a - b - c'],
      ['a/b/c', 'a/(b*c)'],
      ['2.5 x', '2.5*x'],
      ['.5', '0.500000000000000'],
      ['1.', '1.00000000000000'],
      ['x^y^z', 'x**(y**z)'],
      ['(a)(b)', 'a*b'],
      ['2(a+b)', '2*a + 2*b'],
      ['a (b)', 'a*b'],
      ['a b', 'a*b'],
      ['2 3', '6'],
      ['-x', '-x'],
      ['- 3', '-3'],
      ['-(x)', '-x'],
      ['a^-b', 'a**(-b)'],
      ['a + + b', 'a + b'],
      ['+x', 'x'],
      ['I Pi', 'I*pi'],
      ['Pi', 'pi'],
      ['x(*c*)y', 'xy'],
      ['(* comment *) x + 1', 'x + 1'],
      ['α + 1', 'α + 1'],
      ['x\n', 'x'],
    ];
    for (const [s, want] of cases) expect(P(s), s).toBe(want);
  });

  it('converts the functions with an equivalent', () => {
    const cases: [string, string][] = [
      ['Sqrt[2]', 'sqrt(2)'],
      ['Rational[2, 3]', '2/3'],
      ['Log[x]', 'log(x)'],
      ['Log[2, x]', 'log(x)/log(2)'],
      ['Log2[x]', 'log(x)/log(2)'],
      ['Log10[x]', 'log(x)/log(10)'],
      ['Exp[x]', 'exp(x)'],
      ['ArcTan[x]', 'atan(x)'],
      ['ArcTan[x, y]', 'atan2(y, x)'],
      ['Mod[x, 3]', 'Mod(x, 3)'],
      ['Max[1, 2, x]', 'Max(2, x)'],
      ['Min[x, y]', 'Min(x, y)'],
      ['Pochhammer[x, 2]', 'x*(x + 1)'],
      ['ExpIntegralEi[x]', 'Ei(x)'],
      ['SinIntegral[x]', 'Si(x)'],
      ['CosIntegral[x]', 'Ci(x)'],
      ['AiryAi[x]', 'airyai(x)'],
      ['AiryAiPrime[x]', 'airyaiprime(x)'],
      ['AiryBi[x]', 'airybi(x)'],
      ['AiryBiPrime[x]', 'airybiprime(x)'],
      ['LogIntegral[x]', 'li(x)'],
      ['PrimePi[x]', 'primepi(x)'],
      ['Prime[5]', '11'],
      ['PrimeQ[7]', 'True'],
      ['PrimeQ[8]', 'False'],
      ['Cos[x] + Sec[x] + Csc[x] + Cot[x]', 'cos(x) + cot(x) + csc(x) + sec(x)'],
      ['ArcSin[x] + ArcCos[x] + ArcCot[x] + ArcSec[x] + ArcCsc[x]', 'acos(x) + acot(x) + acsc(x) + asec(x) + asin(x)'],
      ['Sinh[x] + Cosh[x] + Tanh[x] + Coth[x] + Sech[x] + Csch[x]', 'sinh(x) + cosh(x) + tanh(x) + coth(x) + csch(x) + sech(x)'],
      ['ArcSinh[x] + ArcCosh[x] + ArcTanh[x] + ArcCoth[x] + ArcSech[x] + ArcCsch[x]', 'acosh(x) + acoth(x) + acsch(x) + asech(x) + asinh(x) + atanh(x)'],
      ['Expand[(x+1)^2]', 'x**2 + 2*x + 1'],
      ['Im[x] + Re[y]', 're(y) + im(x)'],
      ['Polylog[2, x]', 'polylog(2, x)'],
      ['TrigExpand[Sin[x+y]]', 'sin(x)*cos(y) + sin(y)*cos(x)'],
      ['Sign[x]', 'sign(x)'],
      ['Simplify[Sin[x]^2 + Cos[x]^2]', '1'],
      ['Identity[x]', 'x'],
      ['Defer[x]', 'x'],
      ['Null[x]', '0'],
      ['x > y', 'x > y'],
      ['x >= y', 'x >= y'],
      ['x < y', 'x < y'],
      ['x <= y', 'x <= y'],
      ['x == y', 'Eq(x, y)'],
      ['a || b', 'a | b'],
      ['a && b', 'a & b'],
      ['Hold[x + 1]', 'Hold(x + 1)'],
    ];
    for (const [s, want] of cases) expect(P(s), s).toBe(want);
    expect(parseMathematica('Defer[x]')).toBeInstanceOf(sj.UnevaluatedExpr);
    // SymPy's flatten gives a Python list [1, 2, 3]
    expect(P('Flatten[{1, {2, 3}}]')).toBe('(1, 2, 3)');
  });

  it('cancels when the simplification module is loaded', () => {
    // the simplify entry (loaded with the root entry) registers cancel for the parser
    const saved = parserHooks.constructors.get('cancel');
    expect(saved).toBeDefined();
    expect(P('Cancel[(x^2-1)/(x-1)]')).toBe('x + 1');
    expect(sj.str(sj.parse('cancel((x**2 - 1)/(x - 1))'))).toBe('x + 1');
    parserHooks.constructors.delete('cancel');
    expect(() => P('Cancel[x]')).toThrow(TypeError);
    if (saved) parserHooks.constructors.set('cancel', saved);
  });

  it('applies pure functions', () => {
    expect(P('(# + 1)&[x]')).toBe('x + 1');
    expect(P('#^2 + #2&[x, y]')).toBe('x**2 + y');
    expect(P('Function[{u, v}, u + v][a, b]')).toBe('a + b');
    expect(P('Function[u, u^2][3]')).toBe('9');
    expect(P('#0&')).toBe('Lambda((), Slot(0))');
    expect(P('Function[#x + 1]')).toBe('Lambda((), Slot(x) + 1)');
    expect(P('#')).toBe('Slot(1)');
    expect(P('##')).toBe('SlotSequence(1)');
    expect(P('#2')).toBe('Slot(2)');
    expect(P('##2')).toBe('SlotSequence(2)');
    expect(P('(#2 - #1)&[a, b]')).toBe('-a + b');
  });

  it('keeps the other nodes in FullForm', () => {
    const cases: [string, string][] = [
      ['Null', 'Null'],
      ['a; b', 'CompoundExpression(a, b)'],
      ['a;', 'CompoundExpression(a, Null)'],
      ['a = b', 'Set(a, b)'],
      ['a := b', 'SetDelayed(a, b)'],
      ['a = b = c', 'Set(a, Set(b, c))'],
      ['a += b', 'AddTo(a, b)'],
      ['a *= b', 'TimesBy(a, b)'],
      ['a -= b', 'SubtractFrom(a, b)'],
      ['a /= b', 'DivideBy(a, b)'],
      ['a /. b -> c', 'ReplaceAll(a, Rule(b, c))'],
      ['a /. b /. c', 'ReplaceAll(ReplaceAll(a, b), c)'],
      ['a -> b', 'Rule(a, b)'],
      ['a :> b', 'RuleDelayed(a, b)'],
      ['x__', 'Pattern(x, BlankSequence())'],
      ['x___', 'Pattern(x, BlankNullSequence())'],
      ['x_y', 'Pattern(x, Blank(y))'],
      ['x_ y', 'Pattern(x, Blank(y))'],
      ['n!', 'Factorial(n)'],
      ['a!!', 'Factorial2(a)'],
      ['a--', 'Decrement(a)'],
      ['a ? b', 'PatternTest(a, b)'],
      ['a ? b ? c', 'PatternTest(PatternTest(a, b), c)'],
      ['f[[1]]', 'Part(f, 1)'],
      ['f[a][[2]]', 'Part(f(a), 2)'],
      ['a[[1]][[2]]', 'Part(Part(a, 1), 2)'],
      ['{a, b}[[1]]', 'Part((a, b), 1)'],
      ['f[[1, 2]]', 'Part(f, 1, 2)'],
      ['g[f[[1]]]', 'g(Part(f, 1))'],
      ['f[g[[1]]]', 'f(Part(g, 1))'],
      ['f[[g[x]]]', 'Part(f, g(x))'],
      ['f[[g[h[x]]]]', 'Part(f, g(h(x)))'],
      ['f[g[x]]', 'f(g(x))'],
      ['a . b', 'Dot(a, b)'],
      ['a . b f[x]', 'Dot(a, b)*f(x)'],
      ['a | b', 'Alternatives(a, b)'],
      ['a ;; b', 'Span(a, b)'],
      ['a ;; b ;; c', 'Span(Span(a, b), c)'],
      ['a;b;', 'CompoundExpression(a, b, Null)'],
      ['f[x];', 'CompoundExpression(f(x), Null)'],
      ['a . b + c', 'c + Dot(a, b)'],
      ['a . b * c', 'c*Dot(a, b)'],
      ['h[f[[g[x]]]]', 'h(Part(f, g(x)))'],
      ['a === b', 'SameQ(a, b)'],
      ['a =!= b', 'UnsameQ(a, b)'],
      ['a != b', 'Unequal(a, b)'],
      ['a..', 'Repeated(a)'],
      ['a...', 'RepeatedNull(a)'],
      ['x /@ y', 'Map(x, y)'],
      ['x //@ y', 'MapAll(x, y)'],
      ['"hello"', '_Str(hello)'],
      ['"x"', '_Str(x)'],
    ];
    for (const [s, want] of cases) expect(P(s), s).toBe(want);
  });

  it('applies postfix functions and maps over levels (SymPy builds the reversed or an invalid tree)', () => {
    // x // f is f[x] in Mathematica (SymPy 1.14 gives x(f))
    expect(P('x // f')).toBe('f(x)');
    expect(P('x // f // g')).toBe('g(f(x))');
    // a @@@ b @@@ c is Apply[a, Apply[b, c, {1}], {1}] (SymPy 1.14 raises a TypeError)
    expect(P('a @@@ b @@@ c')).toBe('Apply(a, Apply(b, c, (1,)), (1,))');
    // a node after a flat operator (SymPy 1.14 raises a TypeError: unhashable type 'list')
    expect(P('a . b f[x] c')).toBe('c*Dot(a, b)*f(x)');
  });

  it('splits lines into compound expressions', () => {
    const cases: [string, string][] = [
      ['a\nb', 'CompoundExpression(a, b)'],
      ['a + b\nc', 'CompoundExpression(a + b, c)'],
      ['a +\nb', 'a + b'],
      ['a; b\nc', 'CompoundExpression(a, b, c)'],
      ['f[a,\nb]', 'f(a, b)'],
      ['a\n\nb', 'CompoundExpression(a, b)'],
      ['a\nb; c', 'CompoundExpression(a, b, c)'],
      ['a\nb;', 'CompoundExpression(a, b, Null)'],
    ];
    for (const [s, want] of cases) expect(P(s), s).toBe(want);
  });

  it('rejects invalid code', () => {
    const syntax = ['f[[g[x]] + 1]]', '"abc', 'x *) (* y', '(* x', 'f[,x]', 'f[x)', '(x]', '()', '(a, b)', 'f[x', 'a, b', '{f[x]]', '-', '!a', 'Function[a, b, c]'];
    for (const s of syntax) expect(() => P(s), s).toThrow(SyntaxError);
    const type = ["f'[x]", 'a[b][c]', 'Function[#x + 1][2]', 'Function[#x + #y]', 'Rational[x, 2]', 'Power[x]', 'Log[x, y, z]', 'Exp[x, y]', 'Greater[x]', 'x == y == z'];
    for (const s of type) expect(() => P(s), s).toThrow(TypeError);
    for (const s of ['f[x]&', '1&', 'Function[x]']) expect(() => P(s), s).toThrow(RangeError);
    // SymPy raises an IndexError
    for (const s of ['a /; b /;', 'a /; b /;\nc', 'f[[1]]]', ']', 'f[[1]]]]', 'f[[1]', '{f[[1]]]', 'f[[g[x]]]]']) expect(() => P(s), s).toThrow();
    expect(() => P('f["a\\"b"]')).toThrow();
  });

  it('exposes the stages of the parser', () => {
    const m = new MathematicaParser();
    expect(m.fromMathematicaToTokens('\nf[x, "s"] (* c *)\n')).toEqual(['f', '[', 'x', ',', ['_Str', 's'], ']']);
    expect(m.fromTokensToFullformlist(m.fromMathematicaToTokens('a + b c'))).toEqual(['Plus', 'a', ['Times', 'b', 'c']]);
    expect(sj.str(m.fromFullformlistToSympy(['Plus', 'a', ['Times', 'b', 'c']]))).toBe('a + b*c');
    expect(sj.str(m.parse('x^2'))).toBe('x**2');
  });
});

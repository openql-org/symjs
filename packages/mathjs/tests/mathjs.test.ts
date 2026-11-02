// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * Conversion between symjs and math.js. math.js is not a dependency, so
 * the math.js objects are built here with the same structure (node types,
 * BigNumber/Fraction/Complex/Matrix shapes) as math.js 14 produces.
 */

import { describe, expect, it } from 'vitest';
import * as sj from '@symjs/symjs';
import { fromMathjs, fromMathjsMatrix, fromMathjsString, fromMathjsValue, toMathjs, toMathjsMatrix, toMathjsString, toMathjsValue, type MathInstance, type MathNode } from '../src';

const [x, y] = sj.symbols('x y') as [sj.Symbol, sj.Symbol];
const s = (e: sj.Expr): string => sj.str(e);
const bigText = (v: unknown): string => (v as { toString(): string }).toString();

// ---- math.js-shaped objects -------------------------------------------------------
const C = (value: unknown): MathNode => ({ type: 'ConstantNode', value });
const Sy = (name: string): MathNode => ({ type: 'SymbolNode', name });
const Op = (fn: string, ...args: MathNode[]): MathNode => ({ type: 'OperatorNode', fn, op: fn, args });
const Fn = (name: string, ...args: MathNode[]): MathNode => ({ type: 'FunctionNode', fn: Sy(name), args });
const big = (v: string) => ({ isBigNumber: true as const, toString: () => v });
const frac = (s0: number, n: bigint, d: bigint) => ({ isFraction: true as const, s: BigInt(s0), n, d });
const fake: MathInstance & { parsed: string[] } = {
  parsed: [],
  parse(text: string): MathNode {
    this.parsed.push(text);
    return { type: 'Text', value: text };
  },
  bignumber: (v) => big(v),
  fraction: (n, d) => frac(Number(n) < 0 ? -1 : 1, BigInt(Math.abs(Number(n))), BigInt(d ?? 1)),
  complex: (re, im) => ({ isComplex: true as const, re, im }),
  matrix: (data) => ({ isMatrix: true as const, toArray: () => data }),
};

describe('symjs -> math.js', () => {
  it('prints math.js syntax', () => {
    expect(toMathjsString(sj.add(sj.mul(2, sj.pow(x, 2)), sj.Rational.of(1n, 3n)))).toBe('((1 / 3) + (2 * (x ^ 2)))');
    expect(toMathjsString(sj.add(sj.sqrt(x), sj.exp(sj.mul(sj.I, x)), sj.abs(y), sj.conjugate(y)))).toBe('(exp((i * x)) + (x ^ (1 / 2)) + abs(y) + conj(y))');
    expect(toMathjsString(sj.add(sj.pi, sj.E, sj.oo))).toBe('Infinity');
    expect(toMathjsString(sj.mul(sj.pi, sj.E))).toBe('(e * pi)');
    expect(toMathjsString(sj.mul(-3, sj.ceiling(x)))).toBe('((-3) * ceil(x))');
    expect(toMathjsString(new sj.Float(-1.5))).toBe('(-1.50000000000000)');
    expect(toMathjsString(sj.And(sj.Lt(x, 1), sj.Ne(y, 2)))).toBe('((x < 1) and (y != 2))');
    expect(toMathjsString(sj.Not(x))).toBe('(not x)');
    expect(toMathjsString(sj.Function('f')(x))).toBe('f(x)');
    expect(toMathjsString(sj.S.true)).toBe('true');
    expect(toMathjsString(2)).toBe('2');
    expect(() => toMathjsString(sj.S.Catalan)).toThrow(TypeError);
    toMathjs(sj.sin(x), fake);
    expect(fake.parsed.at(-1)).toBe('sin(x)');
  });

  it('converts values and matrices', () => {
    expect(toMathjsValue(sj.Rational.of(1n, 3n), fake, { fraction: true })).toEqual(frac(1, 1n, 3n));
    expect(toMathjsValue(sj.Rational.of(1n, 4n), fake)).toBe(0.25);
    expect(bigText(toMathjsValue(7, fake, { bignumber: true }))).toBe('7');
    expect(bigText(toMathjsValue(sj.Rational.of(1n, 3n), fake, { bignumber: true }))).toBe('0.333333333333333333333333333333');
    expect(bigText(toMathjsValue(sj.evalf(sj.pi, 30), fake, { bignumber: true }))).toBe('3.14159265358979323846264338328');
    expect(toMathjsValue(new sj.Float(2.5), fake)).toBe(2.5);
    expect(toMathjsValue(sj.add(1, sj.I), fake)).toEqual({ isComplex: true, re: 1, im: 1 });
    expect(toMathjsValue(sj.sqrt(2), fake)).toBeCloseTo(Math.SQRT2, 14);
    expect(toMathjsValue(sj.S.false, fake)).toBe(false);
    expect(() => toMathjsValue(x, fake)).toThrow(TypeError);
    const m = toMathjsMatrix(sj.Matrix.of([[1, sj.Rational.of(1n, 2n)]]), fake, { fraction: true });
    expect(m.toArray()).toEqual([[1, frac(1, 1n, 2n)]]);
  });
});

describe('math.js -> symjs', () => {
  it('converts expression trees', () => {
    // 2x^2 + sin(y)/3 - sqrt(x)
    const n = Op('subtract', Op('add', Op('multiply', C(2), Op('pow', Sy('x'), C(2))), Op('divide', Fn('sin', Sy('y')), C(3))), Fn('sqrt', Sy('x')));
    expect(s(fromMathjs(n))).toBe('-sqrt(x) + 2*x**2 + sin(y)/3');
    expect(s(fromMathjs(Op('add', Fn('log', Sy('x'), C(2)), Fn('exp', C(1)), Sy('pi'), Sy('i'), Sy('e'))))).toBe('log(x)/log(2) + pi + 2*E + I');
    expect(s(fromMathjs(Op('add', Fn('log10', Sy('x')), Fn('log2', Sy('y')), Fn('cbrt', Sy('x')), Fn('nthRoot', Sy('y'), C(4)))))).toBe('x**(1/3) + y**(1/4) + log(x)/log(10) + log(y)/log(2)');
    expect(s(fromMathjs(Op('add', Fn('abs', Sy('x')), Fn('ceil', Sy('x')), Fn('conj', Sy('y')), Fn('combinations', Sy('x'), C(2)))))).toBe('conjugate(y) + Abs(x) + binomial(x, 2) + ceiling(x)');
    expect(s(fromMathjs(Op('unaryMinus', { type: 'ParenthesisNode', content: Op('unaryPlus', Sy('x')) })))).toBe('-x');
    expect(s(fromMathjs(Op('add', Op('mod', C(5), C(3)), Op('factorial', C(4)), Op('dotPow', Sy('x'), C(2)))))).toBe('x**2 + 26');
    expect(s(fromMathjs(Op('mod', Sy('x'), C(3))))).toBe('mod(x, 3)');
    expect(s(fromMathjs(Fn('myfun', Sy('x'))))).toBe('myfun(x)');
    expect(s(fromMathjs({ type: 'RelationalNode', conditionals: ['smaller', 'smallerEq'], params: [Sy('x'), Sy('y'), C(3)] }))).toBe('(y <= 3) & (x < y)');
    expect(s(fromMathjs(Op('and', Op('equal', Sy('x'), C(1)), Op('not', Op('larger', Sy('y'), C(0))))))).toBe('Eq(x, 1) & (y <= 0)');
    expect(s(fromMathjs(Op('or', Op('largerEq', Sy('x'), C(1)), Op('xor', Op('unequal', Sy('x'), C(2)), Sy('true')))))).toBe('Eq(x, 2) | (x >= 1)');
    expect(s(fromMathjs(Op('smaller', Sy('x'), Sy('Infinity'))))).toBe('x < oo');
    expect(s(fromMathjs(Sy('NaN')))).toBe('nan');
    expect(s(fromMathjs(Sy('phi')))).toBe('GoldenRatio');
  });

  it('uses given symbols and functions', () => {
    const [p] = sj.symbols('p', { positive: true }) as [sj.Symbol];
    expect(sj.isPositive(fromMathjs(Sy('p'), { symbols: { p } }))).toBe(true);
    expect(s(fromMathjs(Fn('double', Sy('x')), { functions: { double: (a) => sj.mul(2, a) } }))).toBe('2*x');
    expect(s(fromMathjsString('x', { parse: () => Sy('x') }))).toBe('x');
  });

  it('rejects unsupported nodes', () => {
    expect(() => fromMathjs({ type: 'AssignmentNode' })).toThrow(TypeError);
    expect(() => fromMathjs(Op('dotMultiply', C(1), C(2)))).toThrow(TypeError);
    expect(() => fromMathjs({ type: 'SymbolNode' })).toThrow(TypeError);
    expect(() => fromMathjs({ type: 'RelationalNode', conditionals: ['between'], params: [C(1), C(2)] })).toThrow(TypeError);
  });

  it('converts values', () => {
    expect(s(fromMathjsValue(3))).toBe('3');
    expect(s(fromMathjsValue(2.5))).toBe('2.50000000000000');
    expect(s(fromMathjsValue(Infinity))).toBe('oo');
    expect(s(fromMathjsValue(-Infinity))).toBe('-oo');
    expect(s(fromMathjsValue(NaN))).toBe('nan');
    expect(s(fromMathjsValue(5n))).toBe('5');
    expect(s(fromMathjsValue(true))).toBe('True');
    expect(s(fromMathjsValue(big('3.14159265358979323846264338327950288')))).toBe('3.14159265358979323846264338327950288');
    expect(s(fromMathjsValue(big('12')))).toBe('12');
    expect(s(fromMathjsValue(big('-1.5e-30')))).toBe('-1.50000000000000e-30');
    expect(s(fromMathjsValue(big('NaN')))).toBe('nan');
    expect(s(fromMathjsValue(big('-Infinity')))).toBe('-oo');
    expect(s(fromMathjsValue(frac(-1, 2n, 3n)))).toBe('-2/3');
    expect(s(fromMathjsValue({ s: 1, n: 1, d: 4 }))).toBe('1/4');
    expect(s(fromMathjsValue({ isComplex: true, re: 1, im: -2 }))).toBe('1 - 2*I');
    expect(() => fromMathjsValue('text')).toThrow(TypeError);
  });

  it('converts matrices', () => {
    expect(String(fromMathjsMatrix({ isMatrix: true, toArray: () => [[1, frac(1, 1n, 2n)], [3, 4]] }))).toBe('Matrix([[1, 1/2], [3, 4]])');
    expect(String(fromMathjsMatrix({ isMatrix: true, toArray: () => [1, 2, 3] }))).toBe('Matrix([[1], [2], [3]])');
    expect(String(fromMathjsMatrix([[1.5, 2]]))).toBe('Matrix([[1.50000000000000, 2]])');
  });
});

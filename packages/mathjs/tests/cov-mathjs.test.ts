// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * Edge cases of the math.js conversion: the math.js objects are built by hand
 * with the shapes math.js 14 produces (see mathjs.test.ts).
 */

import { describe, expect, it } from 'vitest';
import * as sj from '@symjs/symjs';
import { fromMathjs, fromMathjsValue, toMathjsString, type MathNode } from '../src';

const [x, y] = sj.symbols('x y') as [sj.Sym, sj.Sym];
const s = (e: sj.Expr): string => sj.str(e);
const C = (value: unknown): MathNode => ({ type: 'ConstantNode', value });
const Sy = (name: string): MathNode => ({ type: 'SymbolNode', name });
const Op = (fn: string, ...args: MathNode[]): MathNode => ({ type: 'OperatorNode', fn, op: fn, args });
const big = (v: string) => ({ isBigNumber: true as const, toString: () => v });

describe('symjs -> math.js edge cases', () => {
  it('prints numbers, constants and booleans', () => {
    expect(toMathjsString(new sj.Float(1.5))).toBe('1.50000000000000');
    expect(toMathjsString(sj.mul(-1, sj.oo))).toBe('(-Infinity)');
    expect(toMathjsString(sj.S.false)).toBe('false');
    expect(toMathjsString(sj.Or(sj.Gt(x, 1), sj.Le(y, 2)))).toBe('((y <= 2) or (x > 1))');
    expect(toMathjsString(sj.Xor(x, y))).toBe('(x xor y)');
    expect(toMathjsString(sj.Eq(x, y))).toBe('(x == y)');
    expect(() => toMathjsString(new sj.Integral([x, x]))).toThrow(TypeError);
  });
});

describe('math.js -> symjs edge cases', () => {
  it('values', () => {
    expect(s(fromMathjsValue(false))).toBe('False');
    expect(s(fromMathjsValue(big('Infinity')))).toBe('oo');
    expect(s(fromMathjsValue(big('-Infinity')))).toBe('-oo');
    expect(s(fromMathjsValue(big('NaN')))).toBe('nan');
    expect(() => fromMathjsValue({ s: 1n, n: {}, d: 1n })).toThrow(TypeError);
    expect(() => fromMathjsValue({ a: 1 })).toThrow(/\{"a":1\}/);
    expect(() => fromMathjsValue(Symbol('q'))).toThrow(/symbol/);
    expect(() => fromMathjsValue(() => 1)).toThrow(/function/);
    expect(() => fromMathjsValue('text')).toThrow(/text/);
  });
  it('nodes', () => {
    expect(s(fromMathjs(Op('smallerEq', Sy('x'), C(1))))).toBe('x <= 1');
    expect(s(fromMathjs(Op('largerEq', Sy('x'), C(1))))).toBe('x >= 1');
    expect(s(fromMathjs(Sy('E')))).toBe('E');
    expect(s(fromMathjs(Sy('false')))).toBe('False');
    expect(s(fromMathjs({ type: 'FunctionNode', name: 'sin', args: [Sy('x')] }))).toBe('sin(x)');
    expect(s(fromMathjs({ type: 'OperatorNode', fn: 'add' }))).toBe('0');
    expect(s(fromMathjs({ type: 'FunctionNode', name: 'g' }))).toBe('g()');
    expect(() => fromMathjs(Op('subtract', Sy('x')))).toThrow(TypeError);
    expect(() => fromMathjs({ type: 'ParenthesisNode' })).toThrow(TypeError);
    expect(() => fromMathjs({ type: 'OperatorNode' })).toThrow(TypeError);
    expect(() => fromMathjs(Op('bitAnd', Sy('x'), Sy('y')))).toThrow(TypeError);
    expect(() => fromMathjs({ type: 'FunctionNode', args: [] })).toThrow(TypeError);
    expect(() => fromMathjs({ type: 'FunctionNode', name: 'exp', args: [] })).toThrow(TypeError);
    expect(() => fromMathjs({ type: 'RelationalNode', conditionals: ['bogus'], params: [Sy('x'), Sy('y')] })).toThrow(TypeError);
    expect(() => fromMathjs({ type: 'RelationalNode', conditionals: ['smaller'], params: [Sy('x')] })).toThrow(TypeError);
    expect(() => fromMathjs({ type: 'RelationalNode', conditionals: ['smaller'] })).toThrow(TypeError);
    expect(s(fromMathjs({ type: 'RelationalNode' }))).toBe('True');
  });
});

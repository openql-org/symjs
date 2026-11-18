// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/undef.ts.
// Undefined functions. Expected values are SymPy 1.14's.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';

const [x, y] = sj.symbols('x y');

describe('small core nodes', () => {
  it('creates undefined functions and Subs', () => {
    // SymPy: symbols('f g', cls=Function) = (f, g)
    expect(sj.functions('f g').map((f) => String(f(x)))).toEqual(['f(x)', 'g(x)']);
    expect(() => sj.SymFunction('1f')).toThrow(SyntaxError);
    // SymPy: Subs(x, [], []) = x; mismatched lengths raise ValueError
    expect(String(sj.Subs(x, [], []))).toBe('x');
    expect(() => sj.Subs(x, [x, y], [1])).toThrow(RangeError);
  });
});

it('validates and enforces declared function arities', () => {
  const f = sj.SymFunction('f',{nargs:1}), g = sj.SymFunction('g',{nargs:[2,1,2]});
  expect(String(f(x!))).toBe('f(x)');
  expect(g.arity).toEqual([1,2]);
  expect(String(g(x!,y!))).toBe('g(x, y)');
  expect(() => f()).toThrow(TypeError);
  expect(() => f(x!,y!)).toThrow(TypeError);
  expect(() => sj.SymFunction('f',{nargs:-1})).toThrow(RangeError);
  expect(() => sj.SymFunction('f',{nargs:0.5})).toThrow(RangeError);
  expect(String(sj.SymFunction('z',{nargs:0})())).toBe('z()');
});

describe('function classes', () => {
  it('tells function classes and undefined functions apart', async () => {
    const { isFunctionClass, isUndefinedFunction } = await import('../../src/core/undef');
    const f = sj.SymFunction('f');
    const g = sj.defineFunction('g', {});
    expect(isFunctionClass(f)).toBe(true);
    expect(isFunctionClass(g)).toBe(true);
    expect(isFunctionClass(() => 1)).toBe(false);
    expect(isFunctionClass('f')).toBe(false);
    expect(isUndefinedFunction(f)).toBe(true);
    expect(isUndefinedFunction(g)).toBe(false);
    expect(isUndefinedFunction(x)).toBe(false);
  });
});

it('rejects empty arities and invalid derivative orders and removes zero counts', () => {
  expect(() => sj.SymFunction('f', { nargs: [] })).toThrow(RangeError);
  const f = sj.SymFunction('f')(x);
  expect(sj.derivative(f, [[x, 0]])).toBe(f);
  expect(() => sj.derivative(f, [[x, -1]])).toThrow(RangeError);
  expect(() => sj.derivative(f, [[x, 0.5]])).toThrow(RangeError);
  expect(String(sj.derivative(sj.derivative(f, [[x, 1]]), [[x, 0], [x, 1]]))).toBe('Derivative(f(x), (x, 2))');
});

it('merges and cancels symbolic orders while preserving their free symbols', () => {
  const [x, y, n] = sj.symbols('x y n');
  const f = sj.SymFunction('f')(x, y);
  const d = sj.derivative(f, [[x, n], [y, 1], [x, 2]], true);
  expect(String(d)).toBe('Derivative(f(x, y), (x, n + 2), y)');
  expect([...d.freeSymbols()].map(String)).toEqual(['x', 'y', 'n']);
  expect(sj.derivative(f, [[x, n], [x, n.neg()]])).toBe(f);
  expect(() => sj.derivative(f, [[x, 0.5]])).toThrow(RangeError);
  expect(() => sj.derivative(f, [[x, sj.Rational.of(1, 2)]])).toThrow(RangeError);
  expect(() => sj.derivative(f, [[x, -1]])).toThrow(RangeError);
  expect(sj.derivative(f, [[x, sj.symbol('z', { zero: true })]])).toBe(f);
});

it('compares undefined function classes by their assumptions and arities', () => {
  const f = sj.SymFunction('f');
  const real = sj.SymFunction('f', { assumptions: { real: true } });
  const h = sj.SymFunction('f', { nargs: [1, 2], assumptions: { real: true } });
  expect(f.equals(sj.SymFunction('f', { assumptions: {} }))).toBe(true);
  expect(f.equals(false)).toBe(false);
  expect(f.equals(real)).toBe(false);
  expect(real.equals(h)).toBe(false);
  expect(h.equals(sj.SymFunction('f', { nargs: [2, 1], assumptions: { real: true } }))).toBe(true);
  expect(h.equals(sj.SymFunction('f', { nargs: 2, assumptions: { real: true } }))).toBe(false);
  expect(h.equals(sj.SymFunction('f', { nargs: [1, 3], assumptions: { real: true } }))).toBe(false);
  expect(sj.isReal(real(x))).toBe(true);
  expect(sj.subs(real(x), [[x, 0]]).equals(real(0))).toBe(true);
  expect(sj.SymFunction('g', { assumptions: { commutative: false } })(x).isCommutative).toBe(false);
});

it('keeps symbolic function heads in substitutions', async () => {
  const { FunctionHead } = await import('../../src/core/undef');
  const head = new FunctionHead('f', (...args) => sj.add(...args), [1, 2]);
  expect(head.withArgs()).toBe(head);
  expect(head.key).toBe(new FunctionHead('f').key);
  expect(String(head)).toBe('f');
  expect(head.apply?.(x)).toBe(x);
});

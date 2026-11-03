// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/functions/mod.ts.
//
// Mod. Expected values are str() / latex() results of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { add, Float, latex, Mod, mul, Sym } from '../../src';

const x = new Sym('x');
const y = new Sym('y');
const n = new Sym('n', { integer: true });

describe('Mod', () => {
  it('numbers', () => {
    expect(String(Mod(7, 2))).toBe('1');
    expect(String(Mod(-7, 2))).toBe('1');
    expect(String(Mod(new Float(5.5), 2))).toBe('1.50000000000000');
    expect(String(Mod(new Float(7.5), new Float(2)))).toBe('1.50000000000000');
    expect(String(Mod(5, new Float(2.5)))).toBe('0.0');
    expect(() => Mod(x, 0)).toThrow('Modulo by zero');
  });
  it('symbolic rules', () => {
    expect(String(Mod(0, y))).toBe('0');
    expect(String(Mod(x, x))).toBe('0');
    expect(String(Mod(x, mul(-1, x)))).toBe('0');
    expect(String(Mod(add(x, 1), add(x, 1)))).toBe('0');
    expect(String(Mod(n, 1))).toBe('0');
    expect(String(Mod(x, 1))).toBe('Mod(x, 1)');
    expect(String(Mod(x, y))).toBe('Mod(x, y)');
    expect(latex(Mod(x, y))).toBe('x \\bmod y');
  });
});

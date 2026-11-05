// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/functions/mod.ts.
//
// Mod. Expected values are str() / latex() results of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { add, E, fn, Float, I, latex, Mod, mul, pi, Pow, Rational, sqrt, Sym, SymFunction } from '../../src';

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
    expect(String(Mod(mul(n, x), x))).toBe('0');
    expect(String(Mod(add(mul(n, x), n), n))).toBe('n*Mod(x, 1)');
    expect(String(Mod(add(mul(n, x), n), mul(2, n)))).toBe('n*Mod(x + 1, 2)');
    expect(String(Mod(0, y))).toBe('0');
    expect(String(Mod(x, x))).toBe('0');
    expect(String(Mod(x, mul(-1, x)))).toBe('0');
    expect(String(Mod(add(x, 1), add(x, 1)))).toBe('0');
    expect(String(Mod(n, 1))).toBe('0');
    expect(String(Mod(x, 1))).toBe('Mod(x, 1)');
    expect(String(Mod(x, y))).toBe('Mod(x, y)');
    expect(latex(Mod(x, y))).toBe('x \\bmod y');
  });
  it('terms of a sum and rational ratios (SymPy Mod.eval)', () => {
    const i = new Sym('i', { integer: true });
    const j = new Sym('j', { integer: true });
    const cases: [ReturnType<typeof Mod>, string][] = [
      [Mod(add(x, mul(-1, i), 1), 1), 'Mod(x, 1)'],
      [Mod(add(x, mul(-1, i)), i), 'Mod(x, i)'],
      [Mod(add(x, 5), 2), 'Mod(x + 1, 2)'],
      [Mod(add(x, mul(-1, i), 1), i), 'Mod(x + 1, i)'],
      [Mod(add(x, mul(2, i)), i), 'Mod(x, i)'],
      [Mod(add(x, i, j), i), 'Mod(j + x, i)'],
      [Mod(add(x, mul(3, i)), mul(2, i)), 'Mod(i + x, 2*i)'],
      [Mod(add(mul(2, x), 3), 2), 'Mod(2*x + 1, 2)'],
      [Mod(add(x, y, 2), x), 'Mod(y + 2, x)'],
      [Mod(add(x, Rational.of(1n, 2n)), 1), 'Mod(x + 1/2, 1)'],
      [Mod(add(x, 3), i), 'Mod(x + 3, i)'],
      [Mod(add(x, i), 3), 'Mod(i + x, 3)'],
      [Mod(add(Mod(x, 2), 3), 2), 'Mod(x + 1, 2)'],
      [Mod(add(Mod(x, 2), Mod(y, 3)), 2), 'Mod(Mod(x, 2) + Mod(y, 3), 2)'],
      [Mod(mul(3, x), mul(2, x)), 'x'],
      [Mod(pi, mul(2, pi)), 'pi'],
    ];
    expect(cases.map(([e]) => String(e))).toEqual(cases.map(([, r]) => r));
    // SymPy gives -x and x, which fail at x = 1: Mod(-3, 2) = 1 and Mod(3, -2) = -1
    expect(String(Mod(mul(-3, x), mul(2, x)))).toBe('x');
    expect(String(Mod(mul(3, x), mul(-2, x)))).toBe('-x');
    // SymPy i*(Mod(x, 1)) (gcd extraction), the same value
    expect(String(Mod(add(mul(i, x), i), i))).toBe('i*Mod(x, 1)');
  });
  it('real numbers by the ratio (SymPy Mod by ratio)', () => {
    expect([Mod(pi, 2), Mod(mul(-1, pi, Rational.of(1n, 2n)), mul(2, pi)), Mod(sqrt(2), 1), Mod(mul(-1, sqrt(2)), 3), Mod(pi, -2), Mod(1, pi), Mod(I, 2), Mod(x, pi), Mod(mul(2, pi), pi), Mod(E, mul(E, Rational.of(1n, 2n)))].map(String)).toEqual([
      '-2 + pi',
      '3*pi/2',
      '-1 + sqrt(2)',
      '3 - sqrt(2)',
      '-4 + pi',
      '1',
      'Mod(I, 2)',
      'Mod(x, pi)',
      '0',
      '0',
    ]);
    // a ratio too large for a double is left unevaluated
    expect(String(Mod(mul(Rational.of(10n ** 20n), pi), 3))).toBe('Mod(100000000000000000000*pi, 3)');
  });
  it('unevaluated powers and factorials (SymPy Pow._eval_Mod, factorial._eval_Mod)', () => {
    const pw = (b: number, e: bigint) => new Pow(Rational.of(BigInt(b)), Rational.of(e));
    expect([Mod(pw(2, 10n ** 16n), 97), Mod(pw(3, 200n), 13), Mod(pw(12, 3n), 6), Mod(pw(3, 5n), -7)].map(String)).toEqual(['61', '9', '0', '-2']);
    const f = (k: bigint) => fn('factorial', [Rational.of(k)], { evaluate: false });
    expect(
      [
        [10n ** 9n, 10n ** 9n + 9n],
        [20n, 7n],
        [10n, 11n],
        [12n, 13n],
        [30n, 31n * 37n],
        [9n, 10n],
        [35n, 37n],
        [9n, -11n],
        [3n, 4n],
        [0n, 1n],
        [11n, 13n],
        [8n, 9n],
        [5n, 7n],
        [20n, 143n],
        [5n, 8n],
      ].map(([k, q]) => String(Mod(f(k!), Rational.of(q!)))),
      // SymPy: -4 + factorial(3) for Mod(factorial(3), 4), which is 2
    ).toEqual(['712524808', '0', '10', '12', '309', '0', '1', '-10', '2', '0', '1', '0', '1', '0', '0']);
    expect(String(Mod(fn('factorial', [x], { evaluate: false }), 5))).toBe('Mod(factorial(x), 5)');
    // a number without a numeric value
    expect(String(Mod(SymFunction('f')(1), 2))).toBe('Mod(f(1), 2)');
  });
});

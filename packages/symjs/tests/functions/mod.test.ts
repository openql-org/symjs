// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/functions/mod.ts.
//
// Mod. Expected values are str() / latex() results of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { add, E, fn, Float, Fn, I, latex, Mod, mul, pi, Pow, Rational, sqrt, Sym, SymFunction } from '../../src';

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

describe('Mod symbolic divisibility and denesting', () => {
  const k = new Sym('k', { integer: true });
  const m = new Sym('m', { integer: true, positive: true });
  it('reduces positive integer powers of divisible bases', () => {
    expect(String(Mod(new Pow(k, m), k))).toBe('0');
    expect(String(Mod(new Pow(mul(-2, k), m), k))).toBe('0');
    expect(String(Mod(new Pow(k, m), 2))).toBe('Mod(k**m, 2)');
    expect(String(Mod(new Pow(Rational.of(3n), m), 2))).toBe('1');
    expect(String(Mod(new Pow(k, n), 2))).toBe('Mod(k**n, 2)');
  });
  it('uses the range and divisibility of an inner modulus', () => {
    for (const sign of [1, -1]) {
      expect(String(Mod(mul(sign, Mod(x, mul(2, y))), y))).toBe(String(Mod(mul(sign, x), y)));
    }
    const t = new Sym('t', { positive: true });
    expect(String(Mod(Mod(x, t), mul(2, t)))).toBe('Mod(x, t)');
    expect(String(Mod(mul(-1, Mod(x, t)), mul(-2, t)))).toBe('-Mod(x, t)');
    expect(String(Mod(mul(-1, Mod(x, t)), mul(2, t)))).toBe('Mod(-Mod(x, t), 2*t)');
  });
  it('extracts common integer coefficients and negative signs', () => {
    expect(String(Mod(mul(12, x), mul(15, y)))).toBe('3*Mod(4*x, 5*y)');
    expect(String(Mod(mul(-3, x), mul(-2, y)))).toBe('-Mod(3*x, 2*y)');
    expect(String(Mod(mul(Rational.of(1n, 2n), x), y))).toBe('Mod(x/2, y)');
    expect(String(Mod(x, mul(Rational.of(1n, 2n), y)))).toBe('Mod(x, y/2)');
    expect(String(Mod(mul(new Float(0.6), x), y))).toBe('Mod(0.6*x, y)');
    expect(String(Mod(x, mul(new Float(0.3), y)))).toBe('Mod(1.0*x, 0.3*y)');
  });
});

describe('Mod bounded symbolic and modular arithmetic', () => {
  it('compares symbolic dividends against positive and negative moduli', () => {
    const p = new Sym('p', { positive: true });
    for (const a of [Rational.of(2), add(p, 5)]) {
      expect(String(Mod(a, add(p, 3)))).toBe('2');
      expect(String(Mod(mul(-1, a), add(p, 3)))).toBe('p + 1');
      expect(String(Mod(a, mul(-1, add(p, 3))))).toBe('-p - 1');
      expect(String(Mod(mul(-1, a), mul(-1, add(p, 3))))).toBe('-2');
    }
    expect(String(Mod(100, add(p, 3)))).toBe('Mod(100, p + 3)');
    expect(String(Mod(1, new Sym('m', { integer: true, positive: true, even: true })))).toBe('1');
  });
  it('uses parity, Wilson and symbolic factorial divisibility', () => {
    const even = new Sym('a', { even: true });
    const odd = new Sym('b', { odd: true });
    expect(String(Mod(even, 2))).toBe('0');
    expect(String(Mod(odd, 2))).toBe('1');
    const n = new Sym('n', { integer: true, positive: true });
    const p = new Sym('p', { prime: true });
    const fac = (e: ReturnType<typeof add>) => fn('factorial', [e], { evaluate: false });
    expect(String(Mod(fac(n), n))).toBe('0');
    expect(String(Mod(fac(add(n, 2)), n))).toBe('0');
    expect(String(Mod(fac(add(p, -1)), p))).toBe('p - 1');
    expect(String(Mod(fac(add(p, -1)), mul(-1, p)))).toBe('-1');
    const c = new Sym('c', { composite: true, odd: true });
    expect(String(Mod(fac(add(c, -1)), c))).toBe('0');
    expect(String(Mod(fac(add(n, -1)), n))).toBe('Mod(factorial(n - 1), n)');
  });
  it('extracts floating coefficients without repeated extraction', () => {
    expect(String(Mod(mul(new Float(0.6), pi), mul(new Float(0.3), x, pi)))).toBe('0.3*pi*Mod(2, x)');
    expect(String(Mod(mul(new Float(0.6), pi), mul(new Float(0.31), x, pi)))).toBe('pi*Mod(0.6, 0.31*x)');
    expect(String(Mod(mul(new Float(5), x), mul(new Float(0.1), y)))).toBe('0.1*Mod(50*x, y)');
    expect(String(Mod(add(x, new Float(3)), 1))).toBe('Mod(1.0*x, 1)');
  });
  it('reduces nested powers by Euler and leaves undecidable powers unevaluated', () => {
    const two = Rational.of(2);
    const tower = (height: number): ReturnType<typeof Mod> => height === 1 ? two : new Pow(two, tower(height - 1));
    expect([5, 6, 7].map((h) => String(Mod(tower(h), 59049)))).toEqual(['32191', '18016', '5137']);
    expect(String(Mod(new Pow(new Pow(two, two), new Pow(two, two)), -7))).toBe('-3');
    expect(String(Mod(new Pow(two, new Pow(two, Rational.of(1000000))), 4))).toBe('0');
    expect(String(Mod(new Pow(x, two), 7))).toBe('Mod(x**2, 7)');
    expect(String(Mod(new Pow(two, x), 7))).toBe('Mod(2**x, 7)');
    expect(String(Mod(new Pow(two, Rational.of(-1)), 7))).toBe('1/2');
  });
  it('reduces integer factors and nested remainders', () => {
    const i = new Sym('i', { integer: true });
    expect(String(Mod(mul(3, i), 2))).toBe('Mod(i, 2)');
    expect(String(Mod(mul(Mod(add(i, 2), 4), add(i, 4)), 4))).toBe(String(Mod(mul(i, add(i, 2)), 4)));
  });
});

it('rewrites Mod to floor and reduces numeric factors beside nested remainders', () => {
  expect(String(Mod(x, y).rewrite('floor'))).toBe('x - y*floor(x/y)');
  const k = new Sym('k', { integer: true });
  expect(String(Mod(mul(3, Mod(k, 2)), 2))).toBe('Mod(k, 2)');
  expect(String(Mod(new Pow(Rational.of(2), new Pow(Rational.of(2), Rational.of(2))), 1))).toBe('0');
});

it('leaves unproved factorial residues symbolic and reduces long noncoprime towers', () => {
  const n = new Sym('n', { integer: true });
  const c = new Sym('c', { composite: true, even: true });
  expect(String(Mod(fn('factorial', [n], { evaluate: false }), 5))).toBe('Mod(factorial(n), 5)');
  expect(String(Mod(fn('factorial', [add(c, -1)], { evaluate: false }), c))).toBe('Mod(factorial(c - 1), c)');
  let e: ReturnType<typeof Mod> = Rational.of(2);
  for (let k = 0; k < 10; k++) e = new Pow(Rational.of(2), e);
  expect(String(Mod(e, 8))).toBe('0');
});

it('retains modular power trees when totient evaluation is unavailable', async () => {
  const { impl } = await import('../../src/core/nodes');
  const saved = { ...impl };
  const two = Rational.of(2);
  let tower: ReturnType<typeof Mod> = two;
  for (let i = 0; i < 8; i++) tower = new Pow(two, tower);
  try {
    impl.fn = undefined;
    expect(Mod.isApplied(Mod(tower, 8))).toBe(true);
    impl.fn = (name, args) => new Fn(name, args);
    expect(Mod.isApplied(Mod(new Pow(tower, two), 8))).toBe(true);
    let calls = 0;
    impl.fn = (name, args) => calls++ === 0 ? Rational.of(4) : new Fn(name, args);
    expect(Mod.isApplied(Mod(tower, 8))).toBe(true);
  } finally {
    Object.assign(impl, saved);
  }
});

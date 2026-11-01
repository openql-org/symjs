import { describe, expect, it } from 'vitest';
import { ComplexValue, Expr, I, add, cos, exp, expand, mul, pi, pow, rational, simplify, sin, sqrt, symbols } from '../src';

// Random expressions are built with the canonicalizing constructors while a
// reference numeric value is computed independently with plain JS arithmetic.
// Any wrong automatic rewrite rule shows up as a numeric mismatch.

type C = ComplexValue;
const cm = (a: C, b: C): C => ({ re: a.re * b.re - a.im * b.im, im: a.re * b.im + a.im * b.re });
const ca = (a: C, b: C): C => ({ re: a.re + b.re, im: a.im + b.im });
const cexp = (a: C): C => ({ re: Math.exp(a.re) * Math.cos(a.im), im: Math.exp(a.re) * Math.sin(a.im) });

const [x, y] = symbols('x y', { real: true });
const VX = 0.7;
const VY = -1.3;

function rng(seed: number) {
  let s = seed >>> 0;
  return () => {
    s = (s * 1664525 + 1013904223) >>> 0;
    return s / 2 ** 32;
  };
}

function gen(r: () => number, depth: number): [Expr, C] {
  const leaf = (): [Expr, C] => {
    const k = Math.floor(r() * 8);
    switch (k) {
      case 0:
        return [x, { re: VX, im: 0 }];
      case 1:
        return [y, { re: VY, im: 0 }];
      case 2:
        return [I, { re: 0, im: 1 }];
      case 3:
        return [pi, { re: Math.PI, im: 0 }];
      case 4:
        return [sqrt(2), { re: Math.SQRT2, im: 0 }];
      case 5:
        return [rational(1, 2), { re: 0.5, im: 0 }];
      case 6:
        return [rational(-3), { re: -3, im: 0 }];
      default:
        return [mul(rational(1, 4), pi), { re: Math.PI / 4, im: 0 }];
    }
  };
  if (depth === 0) return leaf();
  const k = Math.floor(r() * 7);
  const [a, va] = gen(r, depth - 1);
  if (k === 0 || k === 1) {
    const [b, vb] = gen(r, depth - 1);
    return [add(a, b), ca(va, vb)];
  }
  if (k === 2 || k === 3) {
    const [b, vb] = gen(r, depth - 1);
    return [mul(a, b), cm(va, vb)];
  }
  if (k === 4) {
    const n = 1 + Math.floor(r() * 3);
    let v: C = { re: 1, im: 0 };
    for (let i = 0; i < n; i++) v = cm(v, va);
    return [pow(a, n), v];
  }
  if (k === 5) return [exp(mul(I, a)), cexp(cm({ re: 0, im: 1 }, va))];
  if (r() < 0.5) {
    // sin of a complex argument
    return [sin(a), { re: Math.sin(va.re) * Math.cosh(va.im), im: Math.cos(va.re) * Math.sinh(va.im) }];
  }
  return [cos(a), { re: Math.cos(va.re) * Math.cosh(va.im), im: -Math.sin(va.re) * Math.sinh(va.im) }];
}

const close = (a: C, b: C) => {
  const tol = 1e-7 * Math.max(1, Math.hypot(b.re, b.im));
  return Math.abs(a.re - b.re) <= tol && Math.abs(a.im - b.im) <= tol;
};

describe('fuzz: automatic simplification preserves values', () => {
  it('canonical form, expand and simplify agree with the reference value', () => {
    const r = rng(2024);
    const values = { x: VX, y: VY };
    let checked = 0;
    for (let i = 0; i < 2000; i++) {
      const [e, ref] = gen(r, 3);
      if (!Number.isFinite(ref.re) || !Number.isFinite(ref.im) || Math.hypot(ref.re, ref.im) > 1e6) continue;
      for (const [name, f] of [
        ['canonical', (z: Expr) => z],
        ['expand', expand],
        ['simplify', simplify],
      ] as const) {
        const v = f(e).toComplex(values);
        if (!close(v, ref)) {
          throw new Error(`${name} mismatch for ${e.toString()}: got ${v.re}+${v.im}i, expected ${ref.re}+${ref.im}i`);
        }
      }
      checked++;
    }
    expect(checked).toBeGreaterThan(1500);
  });
});

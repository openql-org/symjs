// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/calculus/finitediff.ts.
// Finite-difference approximations of derivatives. Expected values are SymPy 1.14's.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { cast } from '../../src/core/guard';
import { Derivative } from '../../src/core/nodes';

const [x, y, h] = sj.symbols('x y h');

const f = sj.SymFunction('f');
const s = (e: unknown): string => String(e);

describe('doit and finite differences', () => {
  it('approximates derivatives', () => {
    const D = (...a: Parameters<typeof sj.Derivative>): Derivative => cast(sj.Derivative(...a), Derivative);
    const d1 = D(f(x), x);
    expect(s(sj.asFiniteDifference(d1, [sj.add(x, -1), x, sj.add(x, 2)]))).toBe('f(x)/2 - 2*f(x - 1)/3 + f(x + 2)/6');
    expect(s(sj.asFiniteDifference(D(f(x), [x, 2]), h))).toBe('-2*f(x)/h**2 + f(-h + x)/h**2 + f(h + x)/h**2');
    expect(s(sj.asFiniteDifference(d1, h, 1))).toBe('-f(1 - h/2)/h + f(h/2 + 1)/h');
    expect(s(sj.asFiniteDifference(D(f(x, y), x, y), h, undefined, y))).toBe('-Derivative(f(x, -h/2 + y), x)/h + Derivative(f(x, h/2 + y), x)/h');
    expect(s(sj.asFiniteDifference(D(f(x), [x, 3]), h))).toBe('-f(-3*h/2 + x)/h**3 + 3*f(-h/2 + x)/h**3 - 3*f(h/2 + x)/h**3 + f(3*h/2 + x)/h**3');
  });
});

describe('apply_finite_diff and differentiate_finite', () => {
  const g = sj.SymFunction('g');
  const dx = sj.SymFunction('dx');
  it('approximates derivatives from values', () => {
    expect(s(sj.applyFiniteDiff(1, [sj.sub(x, h), x, sj.add(x, h)], [f(sj.sub(x, h)), f(x), f(sj.add(x, h))], x))).toBe('-f(-h + x)/(2*h) + f(h + x)/(2*h)');
    expect(s(sj.applyFiniteDiff(2, [0, 1, 2], [0, 1, 4]))).toBe('2');
    expect(s(sj.applyFiniteDiff(1, [0, 1, 2], [0, 1, 4]))).toBe('0');
    expect(() => sj.applyFiniteDiff(1, [1, 2, 3], [4, 5])).toThrow('x_list and y_list not equal in length.');
    // the SymPy doctest with Indexed points
    const X = new sj.Sym('x');
    const Y = new sj.Sym('y');
    const i = sj.Idx(new sj.Sym('i', { integer: true }));
    const at = (b: sj.Sym, j: number): sj.Expr => new sj.Indexed([b, sj.add(i, j)]);
    expect(s(sj.applyFiniteDiff(1, [-1, 0, 1].map((j) => at(X, j)), [-1, 0, 1].map((j) => at(Y, j)), new sj.Indexed([X, i])))).toBe(
      '((x[i + 1] - x[i])/(-x[i - 1] + x[i]) - 1)*y[i]/(x[i + 1] - x[i]) - (x[i + 1] - x[i])*y[i - 1]/((x[i + 1] - x[i - 1])*(-x[i - 1] + x[i])) + (-x[i - 1] + x[i])*y[i + 1]/((x[i + 1] - x[i - 1])*(x[i + 1] - x[i]))',
    );
  });

  it('differentiates by finite differences like SymPy', () => {
    expect(s(sj.differentiateFinite(sj.mul(f(x), g(x)), [x], { points: [sj.sub(x, h), sj.add(x, h)] }))).toBe('-f(-h + x)*g(-h + x)/(2*h) + f(h + x)*g(h + x)/(2*h)');
    expect(s(sj.differentiateFinite(sj.add(f(x), sj.sin(x)), [x, 2]))).toBe('-2*f(x) + f(x - 1) + f(x + 1) - 2*sin(x) + sin(x - 1) + sin(x + 1)');
    expect(s(sj.differentiateFinite(f(x, y), [x, y]))).toBe('f(x - 1/2, y - 1/2) - f(x - 1/2, y + 1/2) - f(x + 1/2, y - 1/2) + f(x + 1/2, y + 1/2)');
    expect(s(sj.differentiateFinite(sj.mul(f(x), sj.diff(g(x), x)), [x]))).toBe('(-g(x) + g(x + 1))*f(x + 1/2) - (g(x) - g(x - 1))*f(x - 1/2)');
    expect(s(sj.differentiateFinite(sj.mul(f(x), sj.diff(g(x), x)), [], { points: dx(x) }))).toBe(
      '-(-g(x - dx(x)/2 - dx(x - dx(x)/2)/2)/dx(x - dx(x)/2) + g(x - dx(x)/2 + dx(x - dx(x)/2)/2)/dx(x - dx(x)/2))*f(x - dx(x)/2)/dx(x) + (-g(x + dx(x)/2 - dx(x + dx(x)/2)/2)/dx(x + dx(x)/2) + g(x + dx(x)/2 + dx(x + dx(x)/2)/2)/dx(x + dx(x)/2))*f(x + dx(x)/2)/dx(x)',
    );
    expect(s(sj.differentiateFinite(sj.mul(f(x), g(x)), [x], { points: h, x0: 1 }))).toBe('-f(1 - h/2)*g(1 - h/2)/h + f(h/2 + 1)*g(h/2 + 1)/h');
    expect(s(sj.differentiateFinite(f(x, y), [x, y], { wrt: x }))).toBe('-Derivative(f(x - 1/2, y), y) + Derivative(f(x + 1/2, y), y)');
    expect(s(sj.differentiateFinite(sj.pow(f(x), 2)))).toBe('-f(x - 1/2)**2 + f(x + 1/2)**2');
    expect(s(sj.differentiateFinite(sj.pow(x, 3), [x], { points: [sj.sub(x, 1), x, sj.add(x, 1)] }))).toBe('-(x - 1)**3/2 + (x + 1)**3/2');
    expect(s(sj.differentiateFinite(5))).toBe('0');
    expect(() => sj.differentiateFinite(f(x, y))).toThrow('Since there is more than one variable in the expression, the variable(s) of differentiation must be supplied to differentiate f(x, y)');
    expect(() => sj.differentiateFinite(f(x), [2])).toThrow('a count must follow a symbol');
  });

  it('approximates every variable of a derivative', () => {
    const D = (...a: Parameters<typeof sj.Derivative>): Derivative => cast(sj.Derivative(...a), Derivative);
    expect(s(sj.asFiniteDifference(D(f(x, y), x, y)))).toBe('f(x - 1/2, y - 1/2) - f(x - 1/2, y + 1/2) - f(x + 1/2, y - 1/2) + f(x + 1/2, y + 1/2)');
    expect(s(sj.asFiniteDifference(D(f(x, y), [x, 2], y), h))).toBe(
      '-2*(-f(x, -h/2 + y)/h + f(x, h/2 + y)/h)/h**2 + (-f(-h + x, -h/2 + y)/h + f(-h + x, h/2 + y)/h)/h**2 + (-f(h + x, -h/2 + y)/h + f(h + x, h/2 + y)/h)/h**2',
    );
    expect(() => sj.asFiniteDifference(D(f(x), [x, 2]), [x])).toThrow('Too few points for order 2');
  });
});


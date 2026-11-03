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

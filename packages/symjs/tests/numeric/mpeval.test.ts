// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/numeric/mpeval.ts.

import { describe, expect, it } from 'vitest';
import { add, evalf, fn, I, parse, sstr } from '../../src';

/**
 * Coverage of numeric/nfloat.ts (nsimplify), mpeval.ts and round.ts.
 * Expected values from SymPy 1.14 / mpmath 1.3.
 */

describe('evalMp', () => {
  it('evaluates a two-argument log', () => {
    // SymPy: log(8, 3, evaluate=False).evalf(20) = 1.8927892607143723113
    expect(sstr(evalf(fn('log', [8, 3], { evaluate: false }), 20))).toBe('1.8927892607143723113');
    // SymPy: N(log(I, 2 + I, evaluate=False), 20)
    expect(sstr(evalf(fn('log', [I, add(2, I)], { evaluate: false }), 20))).toBe('0.8443602876407569357 + 1.4654938711011811226*I');
  });
});

describe('evalAdaptive: parts far below the other part', () => {
  // SymPy 1.14 N(...); SymPy tracks the accuracy of the real and imaginary parts separately
  const n = (s: string) => sstr(evalf(parse(s)));
  it('keeps a stable tiny part', () => {
    expect(n('1 + I*exp(-1000)')).toBe('5.07595889754946e-435*I + 1.0');
    expect(n('exp(-1000)')).toBe('5.07595889754946e-435');
    expect(n('1 + exp(-1000)')).toBe('1.00000000000000');
    expect(n('exp(-1000)*I + exp(-2000)')).toBe('2.57653587296115e-869 + 5.07595889754946e-435*I');
    expect(n('1 - exp(-1000)*I + exp(-2000)')).toBe('1.0 - 5.07595889754946e-435*I');
    expect(n('exp(-1000)*(1 + I)')).toBe('5.07595889754946e-435 + 5.07595889754946e-435*I');
    // negligible at the first working precision only
    expect(n('1 + I*exp(-70)')).toBe('1.0 + 3.97544973590865e-31*I');
  });
  it('keeps a tiny part that needs more working precision', () => {
    // zero at the first working precision
    expect(n('1 + I*(exp(-1000) - exp(-1000)*(1 + exp(-100)))')).toBe('1.0 - 1.88829527500429e-478*I');
    // inaccurate at the first working precision
    expect(n('1 + I*(exp(-1000)*(1 + exp(-40)) - exp(-1000))')).toBe('2.15644715820894e-452*I + 1.0');
  });
  it('is more accurate than SymPy where SymPy loses the tiny part', () => {
    // SymPy: 0.e-434*I + 1.0; the imaginary part is 2*exp(-1000)
    expect(n('(1 + exp(-1000)*I)**2')).toBe('1.01519177950989e-434*I + 1.0');
    // SymPy: 0.e-435 + 1.0*I; the real part is exp(-1000)/2
    expect(n('sqrt(-1 + exp(-1000)*I)')).toBe('2.53797944877473e-435 + 1.0*I');
  });
  it('drops the rounding noise of a cancellation', () => {
    // SymPy: -0.e-124, 1.0 - 0.e-71*I, -0.e-22 + 8.0*I, -0.e-127 - 0.e-127*I
    expect(n('sin(1)**2 + cos(1)**2 - 1')).toBe('0');
    expect(n('1 + I*(sin(1)**2 + cos(1)**2 - 1)')).toBe('1.00000000000000');
    expect(n('(sqrt(3) + I)**3')).toBe('8.0*I');
    expect(n('cos(pi/7) + I*sin(pi/7) - exp(I*pi/7)')).toBe('0');
  });
  it('does not trust a tiny part next to a double-precision value', () => {
    // SymPy (floor(x) + I*exp(-1000)).evalf(subs={x: 5/2}) = 5.07595889754946e-435*I + 2.0; symjs
    // evaluates floor in double precision and cannot tell a tiny part from its rounding error
    expect(sstr(evalf(parse('floor(x) + I*exp(-1000)'), 15, { subs: { x: parse('5/2') } }))).toBe('2.00000000000000');
  });
});

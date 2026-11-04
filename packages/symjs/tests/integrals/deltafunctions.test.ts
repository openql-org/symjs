// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/integrals/deltafunctions.ts.
// deltaintegrate. Expected values are SymPy 1.14's (sympy.integrals.deltafunctions).

import { describe, expect, it } from 'vitest';
import { DiracDelta, Heaviside, parse, symbols } from '../../src';
import { deltaintegrate, integrateDeltas } from '../../src/integrals/deltafunctions';

const [x, y] = symbols('x y');
const P = (q: string) => parse(q, { symbols: [x, y], locals: { DiracDelta, Heaviside } });
const di = (q: string) => {
  const r = deltaintegrate(P(q), x);
  return r === undefined ? 'None' : String(r);
};

describe('deltaintegrate', () => {
  it('integrates DiracDelta', () => {
    expect(di('DiracDelta(x)')).toBe('Heaviside(x)');
    expect(di('DiracDelta(x**2 + x - 2)')).toBe('Heaviside(x - 1)/3 + Heaviside(x + 2)/3');
    expect(di('DiracDelta(x, 1)')).toBe('DiracDelta(x)');
    expect(di('DiracDelta(2*x - 1, 1)')).toBe('DiracDelta(2*x - 1)/2');
    expect(di('DiracDelta(x**2)')).toBe('None');
  });
  it('integrates products with a DiracDelta', () => {
    expect(di('x*DiracDelta(x - 1, 1)')).toBe('-Heaviside(x - 1)');
    expect(di('(x + 1)*DiracDelta(x)')).toBe('Heaviside(x)');
    expect(di('DiracDelta(x)*exp(x)')).toBe('Heaviside(x)');
    expect(di('DiracDelta(x)**2*cos(x)')).toBe('DiracDelta(0)*Heaviside(x)');
    expect(di('DiracDelta(x)**2')).toBe('DiracDelta(0)*Heaviside(x)');
    expect(di('DiracDelta(x)**3')).toBe('DiracDelta(0)**2*Heaviside(x)');
    expect(di('DiracDelta(x**2 - 1)*cos(x)')).toBe('cos(1)*Heaviside(x - 1)/2 + cos(1)*Heaviside(x + 1)/2');
    expect(di('DiracDelta(x**2 - 1)**2*cos(x)')).toBe('cos(1)*DiracDelta(0)*Heaviside(x - 1)/4 + cos(1)*DiracDelta(0)*Heaviside(x + 1)/4');
    expect(di('DiracDelta(2*x)*cos(x)')).toBe('Heaviside(x)/2');
    expect(di('DiracDelta(x)*DiracDelta(x - 1)')).toBe('0');
    expect(di('x**2*DiracDelta(x, 1)')).toBe('0');
    expect(di('DiracDelta(x*y)*x')).toBe('0');
    expect(di('DiracDelta(x**2 - 1)*DiracDelta(y)')).toBe('DiracDelta(y)*Heaviside(x - 1)/2 + DiracDelta(y)*Heaviside(x + 1)/2');
    // SymPy: y*DiracDelta(x), which is wrong (the delta is at x = 1)
    expect(di('y*DiracDelta(x - 1, 1)')).toBe('y*DiracDelta(x - 1)');
  });
  it('does not apply', () => {
    expect(di('sin(x)')).toBe('None');
    expect(di('x + DiracDelta(x)')).toBe('None');
    expect(di('DiracDelta(x**2)*cos(x)')).toBe('None');
    expect(di('DiracDelta(x**2)**2')).toBe('None');
    expect(di('(x + 1)*DiracDelta(x**2)')).toBe('None');
  });
  it('integrateDeltas integrates the other terms with integrate', () => {
    expect(String(integrateDeltas(P('x + DiracDelta(x)'), x))).toBe('x**2/2 + Heaviside(x)');
    expect(String(integrateDeltas(P('x*DiracDelta(x**2) + DiracDelta(x**2)'), x))).toBe('Integral(x*DiracDelta(x**2) + DiracDelta(x**2), x)');
  });
});

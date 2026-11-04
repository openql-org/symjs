// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/integrals/singularityfunctions.ts.
// singularityintegrate. Expected values are SymPy 1.14's.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { SingularityFunction, SymFunction, isNoMatch, parse, singularityintegrate, symbols } from '../../src';
import type { Sym } from '../../src';
import { singularityIntegral } from '../../src/integrals/singularityfunctions';

const [x, a, n] = symbols('x a n');
const f = SymFunction('f');
const P = (q: string) => parse(q, { symbols: [x, a, n], locals: { SingularityFunction, f } as never });
const si = (q: string) => {
  const r = singularityintegrate(P(q), x);
  return isNoMatch(r) ? 'None' : String(r);
};

describe('singularityintegrate', () => {
  it('integrates singularity functions', () => {
    expect(si('SingularityFunction(x, a, 3)')).toBe('SingularityFunction(x, a, 4)/4');
    expect(si('SingularityFunction(x, a, 0)')).toBe('SingularityFunction(x, a, 1)');
    expect(si('SingularityFunction(x, a, -4)')).toBe('SingularityFunction(x, a, -3)');
    expect(si('5*SingularityFunction(x, 5, -2)')).toBe('5*SingularityFunction(x, 5, -1)');
    expect(si('6*SingularityFunction(x, 5, -1)')).toBe('6*SingularityFunction(x, 5, 0)');
    expect(si('x*SingularityFunction(x, 0, -1)')).toBe('0');
    expect(si('SingularityFunction(x, 1, -1)*f(x)')).toBe('f(1)*SingularityFunction(x, 1, 0)');
    expect(si('SingularityFunction(x, 1, -1)**2')).toBe('oo*SingularityFunction(x, 1, 0)');
    expect(si('SingularityFunction(x, 0, 0)**2')).toBe('Integral(SingularityFunction(x, 0, 0)**2, x)');
  });
  it('does not apply', () => {
    expect(si('x')).toBe('None');
    expect(si('SingularityFunction(x, a, n)')).toBe('None');
    expect(si('SingularityFunction(x, 1, 1) + x')).toBe('None');
  });
});

describe('singularityIntegral (the method integrate uses)', () => {
  const [sx] = symbols('x') as Sym[];
  it('applies only to singularity functions of the integration variable', () => {
    const SF = sj.SingularityFunction;
    expect(String(singularityIntegral(SF(sx!, 1, 2), sx!))).toBe('SingularityFunction(x, 1, 3)/3');
    expect(singularityIntegral(SF(sj.sin(sx!), 1, 2), sx!)).toBeUndefined();
    // NoMatch for a sum, and a part left unevaluated
    expect(singularityIntegral(sj.add(SF(sx!, 1, 2), sj.parse('x**x')), sx!)).toBeUndefined();
    expect(singularityIntegral(sj.mul(SF(sx!, 0, 1), sj.parse('x**x')), sx!)).toBeUndefined();
  });
});

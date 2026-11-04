// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/integrals/heurisch.ts (SymPy heurisch for rational functions of sin and cos). Expected values are
// those of SymPy 1.14 heurisch (integrate adds the floor terms of continuous arctangents).

import { describe, expect, it } from 'vitest';
import { Integral, Sym, integrate, parse, sstr } from '../../src';
import { heurischTrig } from '../../src/integrals/heurisch';

const y = new Sym('y');
const H = (s: string): string => {
  const r = heurischTrig(parse(s), y, (g, t) => {
    const G = integrate(g, t);
    return G instanceof Integral ? undefined : G;
  });
  return r === undefined ? 'None' : sstr(r);
};

describe('heurisch in tan(u/2)', () => {
  it.each([
    ['(sin(y) + 1)/(2*(sin(y) - 1))', 'y*tan(y/2)/(2*tan(y/2) - 2) - y/(2*tan(y/2) - 2) + 4/(2*tan(y/2) - 2)'],
    ['1/(1 + sin(y))', '-2/(tan(y/2) + 1)'],
    ['1/(2 + cos(y))', '2*sqrt(3)*atan(sqrt(3)*tan(y/2)/3)/3'],
    ['1/(1 + cos(y))', 'tan(y/2)'],
    ['sin(y)/(1 + sin(y))', 'y*tan(y/2)/(tan(y/2) + 1) + y/(tan(y/2) + 1) + 2/(tan(y/2) + 1)'],
    ['1/(sin(y) + cos(y))', 'sqrt(2)*log(tan(y/2) - 1 + sqrt(2))/2 - sqrt(2)*log(tan(y/2) - sqrt(2) - 1)/2'],
    ['1/(3 + sin(2*y))', 'sqrt(2)*atan(3*sqrt(2)*tan(y)/4 + sqrt(2)/4)/4'],
    ['1/(1 - cos(y))**2', '-1/(2*tan(y/2)) - 1/(6*tan(y/2)**3)'],
  ])('%s', (f, want) => expect(H(f)).toBe(want));

  it('applies only to rational functions of sin(a*x + b) and cos(a*x + b) with a rational a', () => {
    expect(H('y/(1 + sin(y))')).toBe('None');
    expect(H('1/(sin(y) + cos(2*y))')).toBe('None');
    expect(H('1/(1 + sin(y**2))')).toBe('None');
    expect(H('1/(1 + sin(a*y))')).toBe('None');
    expect(H('1/(1 + exp(y))')).toBe('None');
    // the rational function of t is not integrated
    expect(H('1/(1 + sin(y)**5 + sin(y))')).toBe('None');
  });
});

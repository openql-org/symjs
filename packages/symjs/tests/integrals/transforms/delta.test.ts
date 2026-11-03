// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/integrals/transforms/delta.ts.
// Heaviside and DiracDelta. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { S, Sym, diff, DiracDelta, Heaviside, evalf, latex, parse, symbols } from '../../../src';

const half = S.Half;

describe('Heaviside and DiracDelta', () => {
  it('evaluate like SymPy', () => {
    const x = new Sym('x');
    expect(String(Heaviside(0))).toBe('1/2');
    expect(String(Heaviside(-2))).toBe('0');
    expect(String(Heaviside(3))).toBe('1');
    expect(String(Heaviside(0, 1))).toBe('1');
    expect(String(Heaviside(x, half))).toBe('Heaviside(x)');
    expect(String(DiracDelta(x.neg()))).toBe('DiracDelta(x)');
    expect(String(DiracDelta(x.neg(), 1))).toBe('-DiracDelta(x, 1)');
    expect(String(DiracDelta(2))).toBe('0');
    expect(String(diff(Heaviside(x), x))).toBe('DiracDelta(x)');
    expect(String(diff(DiracDelta(x), x))).toBe('DiracDelta(x, 1)');
    expect(() => DiracDelta(x, -1)).toThrow(RangeError);
  });
});

// Heaviside and DiracDelta (integrals/transforms/delta.ts). Expected values
// are the str() / latex() forms printed by SymPy 1.14.

const [x] = symbols('x');
const P = (q: string) => parse(q, { symbols: [x], locals: { Heaviside, DiracDelta } });

describe('Heaviside', () => {
  it('evaluates nan and the sign of the argument', () => {
    expect(String(Heaviside(S.NaN))).toBe('nan');
    expect(String(Heaviside(-2))).toBe('0');
    expect(String(Heaviside(3))).toBe('1');
    expect(String(Heaviside(0))).toBe('1/2');
    expect(String(Heaviside(0, 1))).toBe('1');
    expect(String(Heaviside(x, S.Half))).toBe('Heaviside(x)');
    expect(String(Heaviside(x, 1))).toBe('Heaviside(x, 1)');
  });
  it('derivative and LaTeX', () => {
    expect(String(diff(Heaviside(x), x))).toBe('DiracDelta(x)');
    expect(latex(Heaviside(x))).toBe('\\theta\\left(x\\right)');
  });
  it('numerical value of a numeric argument of unknown sign', () => {
    // SymPy decides the sign of cos(1)**2 + sin(1)**2 - 2 numerically: Heaviside(...) is 0
    expect(String(evalf(Heaviside(P('cos(1)**2 + sin(1)**2 - 2'))))).toBe('0');
    // SymPy: Heaviside(cos(1)**2 + sin(1)**2) is 1 and N(...) 1.00000000000000
    expect(Number(evalf(Heaviside(P('cos(1)**2 + sin(1)**2'))).toNumber())).toBe(1);
  });
});

describe('DiracDelta', () => {
  it('evaluates', () => {
    expect(String(DiracDelta(S.NaN))).toBe('nan');
    expect(String(DiracDelta(2))).toBe('0');
    expect(String(DiracDelta(x, 0))).toBe('DiracDelta(x)');
    expect(String(DiracDelta(mulNeg(x), 1))).toBe('-DiracDelta(x, 1)');
    expect(String(DiracDelta(mulNeg(x), 2))).toBe('DiracDelta(x, 2)');
    expect(String(DiracDelta(mulNeg(x)))).toBe('DiracDelta(x)');
    expect(() => DiracDelta(x, -1)).toThrow(RangeError);
    expect(() => DiracDelta(x, S.Half)).toThrow(RangeError);
    expect(() => DiracDelta(x, x)).toThrow(RangeError);
  });
  it('derivative and LaTeX', () => {
    expect(String(diff(DiracDelta(x), x))).toBe('DiracDelta(x, 1)');
    expect(String(diff(DiracDelta(x, 1), x))).toBe('DiracDelta(x, 2)');
    expect(latex(DiracDelta(x))).toBe('\\delta\\left(x\\right)');
    expect(latex(DiracDelta(P('x + 1'), 3))).toBe('\\delta^{\\left( 3 \\right)}\\left( x + 1 \\right)');
  });
});

function mulNeg(e: ReturnType<typeof P>) {
  return P(`-(${String(e)})`);
}

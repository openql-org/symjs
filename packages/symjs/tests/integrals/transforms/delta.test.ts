// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/integrals/transforms/delta.ts.
// Heaviside, DiracDelta and SingularityFunction. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import { I, S, Sym, diff, DiracDelta, Heaviside, SingularityFunction, evalf, expand, isHeaviside, isSimple, isSingularityFunction, latex, parse, rewrite, subs, symbols } from '../../../src';
import { canonicalCondition } from '../../../src/integrals/transforms/delta';

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

describe('delta functions: rewrites, expansion and isSimple', () => {
  const [y] = symbols('y');
  const xr = new Sym('x', { real: true });
  const Q = (q: string) => parse(q, { symbols: [x], locals: { Heaviside, DiracDelta, SingularityFunction } });
  const rw = (q: string, target: string) => String(rewrite(Q(q), target));
  it('Heaviside as Piecewise', () => {
    expect(rw('Heaviside(x)', 'Piecewise')).toBe('Piecewise((0, x < 0), (1/2, Eq(x, 0)), (1, True))');
    expect(rw('Heaviside(x, nan)', 'Piecewise')).toBe('Piecewise((0, x < 0), (nan, Eq(x, 0)), (1, True))');
    expect(rw('Heaviside(x - 5)', 'Piecewise')).toBe('Piecewise((0, x < 5), (1/2, Eq(x, 5)), (1, True))');
    expect(rw('Heaviside(x**2 - 1)', 'Piecewise')).toBe('Piecewise((0, x**2 < 1), (1/2, Eq(x**2, 1)), (1, True))');
    expect(rw('Heaviside(3 - x)', 'Piecewise')).toBe('Piecewise((0, x > 3), (1/2, Eq(x, 3)), (1, True))');
    expect(rw('Heaviside(x, 0)', 'Piecewise')).toBe('Piecewise((0, x <= 0), (1, True))');
    expect(rw('Heaviside(x - 1, 0)', 'Piecewise')).toBe('Piecewise((0, x <= 1), (1, True))');
    expect(rw('Heaviside(x, 1)', 'Piecewise')).toBe('Piecewise((0, x < 0), (1, True))');
  });
  it('Heaviside as sign, for a real argument', () => {
    expect(String(rewrite(Heaviside(xr), 'sign'))).toBe('sign(x)/2 + 1/2');
    expect(String(rewrite(Heaviside(xr, 0), 'sign'))).toBe('Piecewise((sign(x)/2 + 1/2, Ne(x, 0)), (0, True))');
    expect(String(rewrite(Heaviside(xr, S.NaN), 'sign'))).toBe('Piecewise((sign(x)/2 + 1/2, Ne(x, 0)), (nan, True))');
    expect(String(rewrite(Heaviside(xr.sub(2)), 'sign'))).toBe('sign(x - 2)/2 + 1/2');
    expect(rw('Heaviside(x)', 'sign')).toBe('Heaviside(x)');
  });
  it('Heaviside as SingularityFunction', () => {
    expect(rw('Heaviside(x - 1)', 'SingularityFunction')).toBe('SingularityFunction(x, 1, 0)');
    expect(rw('Heaviside(2*x - 1)', 'SingularityFunction')).toBe('SingularityFunction(x, 1/2, 0)');
    // SymPy: SingularityFunction(x, 2, 0) and SingularityFunction(x, -1, 0), which are 0 for x < 2
    // and for x < -1 where Heaviside(2 - x) and Heaviside(x**2 - 1) are 1: kept
    expect(rw('Heaviside(2 - x)', 'SingularityFunction')).toBe('Heaviside(2 - x)');
    expect(rw('Heaviside(x**2 - 1)', 'SingularityFunction')).toBe('Heaviside(x**2 - 1)');
    expect(() => rewrite(Heaviside(x.mul(y)), 'SingularityFunction')).toThrow(TypeError);
  });
  it('DiracDelta as Piecewise and SingularityFunction', () => {
    expect(rw('DiracDelta(x)', 'Piecewise')).toBe('Piecewise((DiracDelta(0), Eq(x, 0)), (0, True))');
    expect(rw('DiracDelta(x - 5)', 'Piecewise')).toBe('Piecewise((DiracDelta(0), Eq(x, 5)), (0, True))');
    expect(rw('DiracDelta(x**2 - 5)', 'Piecewise')).toBe('Piecewise((DiracDelta(0), Eq(x**2, 5)), (0, True))');
    expect(rw('DiracDelta(x, 1)', 'Piecewise')).toBe('DiracDelta(x, 1)');
    expect(rw('DiracDelta(0)', 'Piecewise')).toBe('DiracDelta(0)');
    expect(rw('DiracDelta(0)', 'SingularityFunction')).toBe('oo');
    expect(rw('DiracDelta(0, 1)', 'SingularityFunction')).toBe('oo');
    expect(rw('DiracDelta(x - 1, 2)', 'SingularityFunction')).toBe('SingularityFunction(x, 1, -3)');
    // SymPy: SingularityFunction(x, 1/2, -1), without the factor 1/2 of DiracDelta(2*x - 1) = DiracDelta(x - 1/2)/2
    expect(rw('DiracDelta(2*x - 1)', 'SingularityFunction')).toBe('SingularityFunction(x, 1/2, -1)/2');
    // SymPy: SingularityFunction(x, -1, -1), one of the two roots: kept
    expect(rw('DiracDelta(x**2 - 1)', 'SingularityFunction')).toBe('DiracDelta(x**2 - 1)');
    // SymPy: ValueError (no singularity function of exponent -5): kept
    expect(rw('DiracDelta(x, 4)', 'SingularityFunction')).toBe('DiracDelta(x, 4)');
    expect(() => rewrite(DiracDelta(x.mul(y)), 'SingularityFunction')).toThrow(TypeError);
  });
  it('expand(diracdelta=True)', () => {
    const dd = (q: string, wrt?: Sym) => String(expand(Q(q), wrt === undefined ? { diracdelta: true } : { diracdelta: true, wrt }));
    expect(dd('DiracDelta(x**2 + x - 2)', x)).toBe('DiracDelta(x - 1)/3 + DiracDelta(x + 2)/3');
    expect(dd('DiracDelta(x**2 + x - 2)')).toBe('DiracDelta(x - 1)/3 + DiracDelta(x + 2)/3');
    expect(String(expand(DiracDelta(x.mul(y)), { diracdelta: true, wrt: x }))).toBe('DiracDelta(x)/Abs(y)');
    expect(String(expand(DiracDelta(x.mul(y)), { diracdelta: true, wrt: y }))).toBe('DiracDelta(y)/Abs(x)');
    expect(String(expand(DiracDelta(y.mul(Q('x**2 - 1'))), { diracdelta: true, wrt: x }))).toBe('DiracDelta(x - 1)/(2*Abs(y)) + DiracDelta(x + 1)/(2*Abs(y))');
    // kept: a double root, non-real roots, a nonpolynomial argument, a derivative, no wrt in the argument
    expect(dd('DiracDelta(x**2 - 2*x + 1)')).toBe('DiracDelta(x**2 - 2*x + 1)');
    expect(dd('DiracDelta(x**2 + 1)')).toBe('DiracDelta(x**2 + 1)');
    expect(dd('DiracDelta(cos(x))')).toBe('DiracDelta(cos(x))');
    expect(dd('DiracDelta(x - 1, 1)')).toBe('DiracDelta(x - 1, 1)');
    expect(String(expand(DiracDelta(y), { diracdelta: true, wrt: x }))).toBe('DiracDelta(y)');
    // SymPy: 0 (roots() finds no root of the quintic); kept
    expect(dd('DiracDelta(x**5 - x - 1)')).toBe('DiracDelta(x**5 - x - 1)');
    expect(() => expand(DiracDelta(x.mul(y)), { diracdelta: true })).toThrow(TypeError);
    expect(() => expand(DiracDelta(x), { diracdelta: true, wrt: 2 })).toThrow(TypeError);
  });
  it('isSimple', () => {
    expect(isSimple(Q('DiracDelta(3*x)'), x)).toBe(true);
    expect(isSimple(Q('DiracDelta(x**2)'), x)).toBe(false);
    expect(isSimple(DiracDelta(x.mul(y)), x)).toBe(true);
    expect(isSimple(DiracDelta(x.mul(y)), y)).toBe(true);
    expect(isSimple(Q('DiracDelta(x**2 + x - 2)'), x)).toBe(false);
    expect(isSimple(Q('DiracDelta(cos(x))'), x)).toBe(false);
    expect(isSimple(DiracDelta(y), x)).toBe(false);
    expect(() => isSimple(x, x)).toThrow(TypeError);
  });
  it('canonical conditions', () => {
    expect(String(canonicalCondition('Lt', Q('-x - 1')))).toBe('x > -1');
    expect(String(canonicalCondition('Eq', S.Zero))).toBe('True');
    // SymPy: Piecewise((1, x + y <= 0)) and Piecewise((1, -a - x + 1 < 0)) give x + y <= 0 and a + x > 1
    expect(String(canonicalCondition('Le', Q('x + y')))).toBe('x + y <= 0');
    expect(String(canonicalCondition('Lt', parse('-a - x + 1')))).toBe('a + x > 1');
    expect(isHeaviside(Heaviside(x))).toBe(true);
    expect(isHeaviside(x)).toBe(false);
  });
});

describe('SingularityFunction', () => {
  const [a, n, y] = symbols('a n y');
  const Q = (q: string) => parse(q, { symbols: [x, a, n], locals: { Heaviside, DiracDelta, SingularityFunction } });
  it('evaluates', () => {
    expect(String(SingularityFunction(x, a, n))).toBe('SingularityFunction(x, a, n)');
    expect(String(SingularityFunction(5, 3, 2))).toBe('4');
    expect(String(SingularityFunction(4, 1, 5))).toBe('243');
    expect(String(SingularityFunction(x, a, S.NaN))).toBe('nan');
    expect(String(SingularityFunction(S.NaN, 1, 2))).toBe('nan');
    expect(String(SingularityFunction(-1, 0, 2))).toBe('0');
    expect(String(SingularityFunction(0, 0, 2))).toBe('0');
    expect(String(SingularityFunction(0, 0, n))).toBe('SingularityFunction(0, 0, n)');
    expect(String(SingularityFunction(3, 1, -1))).toBe('0');
    expect(String(SingularityFunction(3, 1, S.Half))).toBe('sqrt(2)');
    expect(String(SingularityFunction(x, a, -3))).toBe('SingularityFunction(x, a, -3)');
    expect(String(SingularityFunction(x, a, 5))).toBe('SingularityFunction(x, a, 5)');
    expect(String(subs(SingularityFunction(x, 4, -1), [[x, 4]]))).toBe('oo');
    expect(String(subs(SingularityFunction(x, 3, 0), [[x, 3]]))).toBe('1');
    const yp = new Sym('y', { positive: true });
    const yn = new Sym('y', { negative: true });
    const nn = new Sym('n', { nonnegative: true });
    expect(String(SingularityFunction(yp, -10, nn))).toBe('(y + 10)**n');
    expect(String(SingularityFunction(yn, 10, nn))).toBe('0');
    expect(String(SingularityFunction(new Sym('x', { positive: true }), new Sym('a', { negative: true }), nn))).toBe('(-a + x)**n');
    expect(() => SingularityFunction(I, 0, 1)).toThrow(RangeError);
    expect(() => SingularityFunction(x, 0, I)).toThrow(RangeError);
    expect(() => SingularityFunction(x, 0, -5)).toThrow(RangeError);
    expect(isSingularityFunction(SingularityFunction(x, a, n))).toBe(true);
    expect(isSingularityFunction(x)).toBe(false);
  });
  it('derivatives', () => {
    expect(String(diff(Q('SingularityFunction(x, 1, 5) + SingularityFunction(x, 1, 4)'), x))).toBe('4*SingularityFunction(x, 1, 3) + 5*SingularityFunction(x, 1, 4)');
    expect(String(diff(SingularityFunction(x, 4, 0), x, 2))).toBe('SingularityFunction(x, 4, -2)');
    expect(String(diff(SingularityFunction(x, a, -1), x))).toBe('SingularityFunction(x, a, -2)');
    expect(String(diff(SingularityFunction(x, 1, -3), x))).toBe('SingularityFunction(x, 1, -4)');
    expect(String(diff(SingularityFunction(x, a, 2), a))).toBe('Derivative(SingularityFunction(x, a, 2), a)');
    // SymPy: TypeError (fdiff returns None) for the exponent -4 and an exponent of unknown sign
    expect(String(diff(SingularityFunction(x, 1, -4), x))).toBe('Derivative(SingularityFunction(x, 1, -4), x)');
    expect(String(diff(SingularityFunction(x, a, n), x))).toBe('Derivative(SingularityFunction(x, a, n), x)');
    expect(String(diff(SingularityFunction(Q('x**2'), a, n), x))).toBe('2*x*Subs(Derivative(SingularityFunction(_xi_1, a, n), _xi_1), _xi_1, x**2)');
  });
  it('rewrites', () => {
    const rw = (q: string, target: string) => String(rewrite(Q(q), target));
    expect(rw('SingularityFunction(x, 4, 5)', 'Piecewise')).toBe('Piecewise(((x - 4)**5, x >= 4), (0, True))');
    expect(rw('SingularityFunction(x, a, 2)', 'Piecewise')).toBe('Piecewise(((-a + x)**2, a - x <= 0), (0, True))');
    expect(rw('SingularityFunction(x, a, -3)', 'Piecewise')).toBe('Piecewise((oo, Eq(a - x, 0)), (0, True))');
    expect(rw('SingularityFunction(x, 1, -2)', 'Piecewise')).toBe('Piecewise((oo, Eq(x, 1)), (0, True))');
    expect(rw('SingularityFunction(x, a, n)', 'Piecewise')).toBe('SingularityFunction(x, a, n)');
    const expr = Q('SingularityFunction(x, 4, 5) + SingularityFunction(x, -3, -1) - SingularityFunction(x, 0, -2)');
    const expected = '(x - 4)**5*Heaviside(x - 4, 1) + DiracDelta(x + 3) - DiracDelta(x, 1)';
    expect(String(rewrite(expr, 'Heaviside'))).toBe(expected);
    expect(String(rewrite(expr, 'DiracDelta'))).toBe(expected);
    expect(String(rewrite(expr, 'HeavisideDiracDelta'))).toBe(expected);
    expect(rw('SingularityFunction(x, 2, -3)', 'Heaviside')).toBe('DiracDelta(x - 2, 2)');
    expect(rw('SingularityFunction(x, 2, -4)', 'Heaviside')).toBe('DiracDelta(x - 2, 3)');
    expect(rw('SingularityFunction(x, a, n)', 'Heaviside')).toBe('SingularityFunction(x, a, n)');
    expect(String(rewrite(SingularityFunction(y.mul(2), 3, -1), 'Heaviside'))).toBe('2*DiracDelta(2*y - 3)');
    // SymPy: KeyError (a variable without free symbols); kept
    expect(rw('SingularityFunction(2, a, -1)', 'Heaviside')).toBe('SingularityFunction(2, a, -1)');
  });
});

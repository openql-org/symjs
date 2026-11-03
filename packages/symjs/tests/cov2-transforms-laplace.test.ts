// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Coverage of integrals/transforms/laplace.ts. Expected values are the str() forms printed by
// SymPy 1.14 unless a comment says otherwise.

import { describe, expect, it } from 'vitest';
import { DiracDelta, Eq, Ge, Gt, Heaviside, Le, LaplaceTransform, Lt, Ne, Piecewise, and, laplaceTransform, mul, or, parse, symbol, symbols } from '../src';
import type { Expr } from '../src';
import { laplaceDeepCollect, simplifyConds } from '../src/integrals/transforms/laplace';

const a = symbol('a', { positive: true });
const b = symbol('b', { real: true });
const [t, s, x, y] = symbols('t s x y');
const p = symbol('p', { positive: true });
const n = symbol('n', { integer: true, positive: true });
const P = (e: string) => parse(e, { symbols: [a, b, p, n, t, s, x, y], locals: { Heaviside, DiracDelta, Eq, Ne } });
const show = (v: unknown): string => (Array.isArray(v) ? `(${v.map(show).join(', ')})` : String(v));
const L = (e: string): string => show(laplaceTransform(P(e), t, s));
const LE = (e: Expr): string => show(laplaceTransform(e, t, s));

describe('laplace: simplifyConds and laplaceDeepCollect', () => {
  it('_simplifyconds cases', () => {
    const cases: [string, number, string][] = [
      ['Abs(x)*Abs(y) < 1', 1, 'Abs(x*y) < 1'],
      ['Abs(x)*p < 1', 1, 'p*Abs(x) < 1'],
      ['1 < Abs(2*x)', 1, '1 < 2*Abs(x)'],
      ['Abs(x**2) > 1', 1, 'True'],
      ['1 > Abs(x**2)', 1, 'False'],
      ['x < 1', 1, 'x < 1'],
      ['Abs(x) <= 1', 1, 'Abs(x) <= 1'],
      ['Eq(x, 1)', 1, 'Eq(x, 1)'],
      ['1 < Abs(x**I)', 1, '1 < Abs(x**I)'],
      ['Ne(1, 2*x)', 1, 'Ne(1, 2*x)'],
      ['1 < Abs(y)**2', 1, '1 < Abs(y)**2'],
      ['Ne(x, 0)', 1, 'True'],
      ['Ne(x, x**2)', 1, 'Ne(x, x**2)'],
    ];
    for (const [e, A, want] of cases) expect(String(simplifyConds(P(e), x, A)), e).toBe(want);
    // symjs writes Abs(x**2) as Abs(x)**2 and Abs(1/x) as 1/Abs(x) (SymPy: Abs(x) < Abs(x**2), 1 < Abs(1/x))
    expect(String(simplifyConds(P('Abs(x) < Abs(x**2)'), x, 1))).toBe('Abs(x) < Abs(x)**2');
    expect(String(simplifyConds(P('1 < Abs(1/x)'), x, 0))).toBe('1 < 1/Abs(x)');
  });
  it('an atom that is not a polynomial is kept', () => {
    expect(String(laplaceDeepCollect(P('oo'), t))).toBe('oo');
  });
});

describe('laplace: rule table', () => {
  it('table entries', () => {
    const cases: [string, string][] = [
      ['1/(a*sqrt(t)+t**1.5)', '(pi*sqrt(a)*exp(a*s)*erfc(sqrt(a)*sqrt(s)), 0, True)'],
      ['log(a*t)', '(-log(s*exp(EulerGamma)/a)/s, 0, True)'],
      ['log(2*t)', '(-log(s*exp(EulerGamma)/2)/s, 0, True)'],
      // 4.6.9 is skipped as in SymPy; 4.6.11 with n = -1/2 applies
      ['log(t)/sqrt(t)', '(sqrt(pi)*(-log(s) - 2*log(2) - EulerGamma)/sqrt(s), 0, True)'],
      ['log(a*t)**2', '((log(s*exp(EulerGamma)/a)**2 + pi**2/6)/s, 0, True)'],
      ['log(t)**2', '((log(s*exp(EulerGamma))**2 + pi**2/6)/s, 0, True)'],
      ['cosh(a*t)**2', '((-2*a**2 + s**2)/(-4*a**2*s + s**3), 2*a, True)'],
      ['cosh(b*t)**2', '((-2*b**2 + s**2)/(-4*b**2*s + s**3), 2*Abs(b), True)'],
    ];
    for (const [e, want] of cases) expect(L(e), e).toBe(want);
  });
  it('the rational exponent 3/2 of 4.2.18b', () => {
    // SymPy writes the pattern with the float 1.5 and leaves the rational form unevaluated
    // (LaplaceTransform(1/(a*sqrt(t) + t**(3/2)), t, s), -oo, True); the integral has the same value
    expect(L('1/(a*sqrt(t)+t**(3/2))')).toBe('(pi*sqrt(a)*exp(a*s)*erfc(sqrt(a)*sqrt(s)), 0, True)');
  });
});

describe('laplace: DiracDelta and Heaviside', () => {
  it('delta rules', () => {
    const cases: [string, string][] = [
      ['DiracDelta(t**2-1)', '(exp(-s)/2, -oo, True)'],
      ['DiracDelta(t**2+1)*t', '(0, -oo, True)'],
      ['DiracDelta((t-1)**2)*t', '(-Derivative(LaplaceTransform(DiracDelta(t**2 - 2*t + 1), t, s), s), -oo, True)'],
      ['DiracDelta(t**5-t-1)*t', '(-Derivative(LaplaceTransform(DiracDelta(t**5 - t - 1), t, s), s), -oo, True)'],
      ['DiracDelta(t+1)*t', '(0, -oo, True)'],
      ['DiracDelta(-2*t-2)*t', '(0, -oo, True)'],
      ['DiracDelta(t-I)*t', '(0, -oo, True)'],
      ['DiracDelta(t-1)*cos(t)', '(exp(-s)*cos(1), -oo, True)'],
      ['DiracDelta(t-1)*sin(t-1)/(t-1)', '(exp(-s), -oo, True)'],
      ['DiracDelta(t-1)/(t-1)', '(LaplaceTransform(DiracDelta(t - 1)/(t - 1), t, s), -oo, True)'],
      ['DiracDelta(exp(t)-2)*t', '(-Derivative(LaplaceTransform(DiracDelta(exp(t) - 2), t, s), s), -oo, True)'],
      ['DiracDelta(2-2*t)', '(exp(-s)/2, -oo, True)'],
    ];
    for (const [e, want] of cases) expect(L(e), e).toBe(want);
  });
  it('delta rules where SymPy 1.14 is wrong', () => {
    // integral of t*delta(t**2 - 1)*exp(-s*t) = 1*exp(-s)/|2*1|; SymPy gives s*exp(-s)/2
    expect(L('DiracDelta(t**2-1)*t')).toBe('(exp(-s)/2, -oo, True)');
    // delta(1 - t**2) = delta(t**2 - 1); SymPy gives -s*exp(-s)/2
    expect(L('DiracDelta(1-t**2)*t')).toBe('(exp(-s)/2, -oo, True)');
    // delta(2 - 2*t) = delta(t - 1)/2; SymPy gives -exp(-s)/2 and -E*exp(-s)/2
    expect(L('DiracDelta(-2*t+2)*t')).toBe('(exp(-s)/2, -oo, True)');
    expect(L('DiracDelta(2-2*t)*exp(t)')).toBe('(E*exp(-s)/2, -oo, True)');
  });
  it('a delta at an undecided point stays unevaluated', () => {
    // SymPy raises TypeError: cannot determine truth value of Relational: b >= 0
    expect(L('DiracDelta(t-b)')).toBe('(LaplaceTransform(DiracDelta(-b + t), t, s), -oo, True)');
    expect(L('DiracDelta(t-b)*t')).toBe('(-Derivative(LaplaceTransform(DiracDelta(-b + t), t, s), s), -oo, True)');
  });
  it('Heaviside rules', () => {
    // SymPy raises AttributeError ('int' object has no attribute 'xreplace') on the first two;
    // the step vanishes for t > 0
    expect(L('Heaviside(-t-1)')).toBe('(0, 0, True)');
    expect(L('Heaviside(-2*t-3)*t')).toBe('(0, 0, True)');
    expect(L('Heaviside(1-t)*t')).toBe('(-exp(-s)/s + s**(-2) - exp(-s)/s**2, 0, True)');
    expect(L('Heaviside(-1-t)*t')).toBe('(0, 0, True)');
    expect(L('Heaviside((t+1)**2-t**2-2*t)')).toBe('(1/s, 0, True)');
  });
});

describe('laplace: program rules', () => {
  it('time scaling, trigonometric factors, derivatives, polynomial factors', () => {
    const cases: [string, string][] = [
      ['f(2*t)', '(LaplaceTransform(f(t), t, s/2)/2, -oo, True)'],
      ['besselk(1,2*t)', '(LaplaceTransform(besselk(1, 2*t), t, s), -oo, True)'],
      ['sin(t)*sinh(t)', '(2*s/(s**4 + 4), 1, True)'],
      ['cos(t)*cosh(t)', '(s**3/(s**4 + 4), 1, True)'],
      ['t*Derivative(f(t),t)', '(-Derivative(s*LaplaceTransform(f(t), t, s) - f(0), s), -oo, True)'],
      ['Derivative(f(t,x),x)', '(LaplaceTransform(Derivative(f(t, x), x), t, s), -oo, True)'],
      ['Derivative(f(t,t),t)', '(LaplaceTransform(Derivative(f(t, t), t), t, s), -oo, True)'],
      ['Derivative(f(t)*g(t),t)', '(LaplaceTransform(Derivative(f(t)*g(t), t), t, s), -oo, True)'],
      ['((t+1)**2-t**2-2*t)*besselk(1,t)', '(LaplaceTransform(besselk(1, t), t, s), -oo, True)'],
      ['t*besselk(1,t)', '(-Derivative(LaplaceTransform(besselk(1, t), t, s), s), -oo, True)'],
      ['t*DiracDelta(t)', '(0, -oo, True)'],
      ['(t+1)*DiracDelta(t)', '(1, -oo, True)'],
    ];
    for (const [e, want] of cases) expect(L(e), e).toBe(want);
  });
  it('expansion', () => {
    const cases: [string, string][] = [
      // SymPy prints the same terms in the order 2*LaplaceTransform(sqrt(t)*f(t), t, s) + LaplaceTransform(f(t), t, s)
      // - Derivative(LaplaceTransform(f(t), t, s), s) (the str printer's term order is not laplace's)
      ['f(t)*(sqrt(t)+1)**2', '(-Derivative(LaplaceTransform(f(t), t, s), s) + 2*LaplaceTransform(sqrt(t)*f(t), t, s) + LaplaceTransform(f(t), t, s), -oo, True)'],
      // SymPy's match picks the factor exp(t**2), which is not exp(a*t), and gives
      // (LaplaceTransform(f(t)*exp(t)*exp(t**2), t, s), -oo, True); symjs takes exp(t) and shifts s
      ['f(t)*exp(t*(t+1))', '(LaplaceTransform(f(t)*exp(t**2), t, s - 1), -oo, True)'],
      ['f(t)*sin(t**2+t)', '(LaplaceTransform(f(t)*sin(t)*cos(t**2), t, s) + LaplaceTransform(f(t)*sin(t**2)*cos(t), t, s), -oo, True)'],
      ['f(t)*log(2*(t+1))', '(LaplaceTransform(f(t)*log(2*t + 2), t, s), -oo, True)'],
    ];
    for (const [e, want] of cases) expect(L(e), e).toBe(want);
  });
  it('expansion of a logarithm of a positive variable', () => {
    const tp = symbol('t', { positive: true });
    // SymPy prints the second term as LaplaceTransform(f(t), t, s)*log(2) (the str printer's factor order)
    expect(show(laplaceTransform(parse('f(t)*log(2*t)', { symbols: [tp] }), tp, s))).toBe('(LaplaceTransform(f(t)*log(t), t, s) + log(2)*LaplaceTransform(f(t), t, s), -oo, True)');
  });
  it('a symbolic power of t', () => {
    // SymPy: ((-1)**n*Derivative(LaplaceTransform(besselk(1, t), t, s), (s, n)), -oo, True); symjs's
    // Derivative needs a numeric order, so the transform stays unevaluated
    expect(L('t**n*besselk(1,t)')).toBe('(LaplaceTransform(t**n*besselk(1, t), t, s), -oo, True)');
    // SymPy integrates with the Meijer G method: (4*2**(m - 3)*meijerg(((-m/2, 1 - m/2), ()), ((0, 1/2), ()),
    // polar_lift(s)**2)/sqrt(pi), 0, (re(m) > -3) & ...); symjs has no Meijer G integration here
    expect(L('t**y*besselk(1,t)')).toBe('(LaplaceTransform(t**y*besselk(1, t), t, s), -oo, True)');
  });
});

describe('laplace: Piecewise input', () => {
  it('conditions written in any orientation, and linear in t', () => {
    // SymPy's Piecewise canonicalizes 2 < t to t > 2 and 2*t > 5 to t > 5/2
    expect(LE(Piecewise([1, or(Lt(2, t), Lt(t, 1))], [0, true]))).toBe('((1 - exp(-s))/s + exp(-2*s)/s, 0, True)');
    expect(LE(Piecewise([1, and(Lt(1, t), Lt(t, 2))], [0, true]))).toBe('(exp(-s)/s - exp(-2*s)/s, 0, True)');
    expect(LE(Piecewise([1, and(Gt(2, t), Ge(t, 1))], [0, true]))).toBe('(exp(-s)/s - exp(-2*s)/s, 0, True)');
    expect(LE(Piecewise([1, or(Lt(t, 1), Gt(mul(2, t), 5))], [0, true]))).toBe('((1 - exp(-s))/s + exp(-5*s/2)/s, 0, True)');
    expect(LE(Piecewise([1, and(Gt(t, 1), Lt(mul(2, t), 5))], [0, true]))).toBe('(exp(-s)/s - exp(-5*s/2)/s, 0, True)');
    expect(LE(Piecewise([1, Gt(mul(2, t), 1)], [0, true]))).toBe('(exp(-s/2)/s, 0, True)');
  });
  it('a first piece that never applies', () => {
    // SymPy 1.14 gives (0, 0, True): piecewise_exclusive returns t, whose (empty) args
    // _piecewise_to_heaviside turns into 0; the function is t for t > 0
    expect(LE(Piecewise([1, and(Gt(t, 1), Lt(t, 0))], [t, true]))).toBe('(s**(-2), 0, True)');
  });
  it('conditions left to the integration', () => {
    const unevaluated = (e: Expr): string => `(LaplaceTransform(${String(e)}, t, s), -oo, True)`;
    // SymPy integrates to (0, -oo, True) (a single point)
    const eq = Piecewise([1, Eq(t, 1)], [0, true]);
    expect(LE(eq)).toBe(unevaluated(eq));
    // SymPy raises AttributeError: 'Equality' object has no attribute 'gts' (and 'Unequality')
    for (const e of [Piecewise([1, or(Eq(t, 1), Gt(t, 2))], [0, true]), Piecewise([1, and(Ne(t, 1), Lt(t, 2))], [0, true])]) expect(LE(e)).toBe(unevaluated(e));
    // SymPy writes the indicator of t > 2 as Heaviside(t - 1) - Heaviside(2 - t), which is wrong
    const same = Piecewise([1, and(Gt(t, 1), Gt(t, 2))], [0, true]);
    expect(LE(same)).toBe(unevaluated(same));
    // three conditions and a condition that is not linear: SymPy also returns f to the integration
    const three = Piecewise([1, and(Lt(1, t), Lt(t, 2), Le(t, 3))], [0, true]);
    expect(LE(three)).toBe(unevaluated(three));
    const quad = Piecewise([1, Gt(mul(t, t), 1)], [0, true]);
    expect(LE(quad)).toBe(unevaluated(quad));
    // SymPy: (exp(-s*y)/s, 0, True) for y > 0 and unevaluated for (y > 2) | (t < 1); symjs's
    // piecewise_exclusive takes conditions in t only
    const yp = symbol('y', { positive: true });
    for (const e of [Piecewise([1, Gt(t, yp)], [0, true]), Piecewise([1, or(Lt(t, 1), Gt(yp, 2))], [0, true])]) expect(LE(e)).toBe(unevaluated(e));
  });
});

describe('laplace: integration and the LaplaceTransform class', () => {
  it('powers of t whose integral diverges at 0', () => {
    expect(L('1/t')).toBe('(LaplaceTransform(1/t, t, s), -oo, True)');
    expect(L('t**(-3/2)')).toBe('(LaplaceTransform(t**(-3/2), t, s), -oo, True)');
  });
  it('a rule check that cannot be decided', () => {
    // re(zoo) is nan, which cannot be ordered: the rule for besselj is skipped (SymPy raises
    // TypeError: Invalid NaN comparison)
    expect(L('besselj(zoo, t)')).toBe('(LaplaceTransform(besselj(zoo, t), t, s), -oo, True)');
  });
  it('a Heaviside factor with an undecided sign', () => {
    expect(L('Heaviside(y-t)*besselk(1,t)')).toBe('(LaplaceTransform(besselk(1, t)*Heaviside(-t + y), t, s), -oo, True)');
  });
  it('transformName and doit', () => {
    const F = new LaplaceTransform(P('t**2'), t, s);
    expect(F.transformName).toBe('Laplace');
    expect(show(F.doit({ noconds: false }))).toBe('(2/s**3, 0, True)');
    // a function variable that is not a symbol leaves the transform unevaluated
    // (SymPy evaluates LaplaceTransform(2, 2, s).doit() to s**(-2))
    const G = new LaplaceTransform(2, 2, s);
    expect(String(G.doit())).toBe('LaplaceTransform(2, 2, s)');
  });
});

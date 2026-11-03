// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Coverage of calculus/*.ts (diff, doit, finite differences) and of Mul substitution.
// Expected values are SymPy 1.14's str(); comments give SymPy's answer where symjs differs.
import { describe, expect, it } from 'vitest';
import * as sj from '../src';
import { constantsimp } from '../src/solvers/odesimp';
import { Derivative, Integral } from '../src/core/nodes';
import { cast } from '../src/core/guard';

const [x, y, k, n, h, C1, C2] = sj.symbols('x y k n h C1 C2');
const r = sj.symbol('r', { real: true });
const f = sj.SymFunction('f');
const g = sj.SymFunction('g');
const P = (s: string): sj.Expr => sj.parse(s, { symbols: [x, y, k, n, h, r] });
const s = (e: unknown): string => String(e);

describe('diff (SymPy diff)', () => {
  it.each([
    ['asin(x)', '1/sqrt(1 - x**2)'],
    ['acos(x)', '-1/sqrt(1 - x**2)'],
    ['atan(x)', '1/(x**2 + 1)'],
    ['sinh(x)', 'cosh(x)'],
    ['cosh(x)', 'sinh(x)'],
    ['tanh(x)', '1 - tanh(x)**2'],
    ['tan(x)', 'tan(x)**2 + 1'],
    ['log(x)', '1/x'],
    ['2**x', '2**x*log(2)'],
    ['x**x', 'x**x*(log(x) + 1)'],
    ['exp(x**2)', '2*x*exp(x**2)'],
  ])('d/dx %s', (e, expected) => {
    expect(s(sj.diff(P(e), x))).toBe(expected);
  });

  it('differentiates conjugate, re, im and Abs', () => {
    expect(s(sj.diff(sj.Abs(sj.add(sj.pow(r, 2), 1)), r))).toBe('2*r');
    expect(s(sj.diff(sj.conjugate(sj.pow(r, 2)), r))).toBe('2*r');
    expect(s(sj.diff(sj.re(sj.mul(r, sj.I)), r))).toBe('0');
    expect(s(sj.diff(sj.im(sj.mul(r, sj.I)), r))).toBe('1');
    // conjugate is not holomorphic: Derivative(conjugate(x), x) stays unevaluated for a variable that may be complex
    expect(s(sj.diff(sj.conjugate(sj.sin(x)), x))).toBe('cos(conjugate(x))*Derivative(conjugate(x), x)');
    expect(s(sj.diff(sj.re(x), x))).toBe('Derivative(re(x), x)');
    expect(() => sj.diff(sj.Abs(sj.sin(x)), x)).toThrow(sj.NotImplementedError);
    // SymPy 1.14: cos(r)*sign(sin(r)), equal where sin(r) != 0
    expect(s(sj.diff(sj.Abs(sj.sin(r)), r))).toBe('sin(r)*cos(r)/Abs(sin(r))');
    expect(s(sj.diff(sj.conjugate(f(r)), r))).toBe('conjugate(Derivative(f(r), r))');
    expect(s(sj.diff(sj.re(f(r)), r))).toBe('re(Derivative(f(r), r))');
    expect(s(sj.diff(sj.im(f(r)), r))).toBe('im(Derivative(f(r), r))');
  });

  it('differentiates undefined functions, derivatives, sums and piecewise functions', () => {
    expect(s(sj.diff(f(g(x)), x))).toBe('Derivative(f(g(x)), g(x))*Derivative(g(x), x)');
    expect(s(sj.diff(f(x, y), x))).toBe('Derivative(f(x, y), x)');
    expect(s(sj.diff(sj.diff(f(x), x), y))).toBe('0');
    expect(s(sj.diff(sj.diff(f(x), x), x))).toBe('Derivative(f(x), (x, 2))');
    expect(s(sj.diff(sj.Sum(sj.mul(sj.pow(x, k), y), [k, 0, n]), y))).toBe('Sum(x**k, (k, 0, n))');
    expect(() => sj.diff(sj.Sum(sj.pow(x, k), [k, 0, n]), n)).toThrow(sj.NotImplementedError);
    expect(s(sj.diff(sj.Piecewise([sj.pow(x, 2), sj.Gt(x, 0)], [x, true]), x))).toBe('Piecewise((2*x, x > 0), (1, True))');
    expect(s(sj.diff(x, x, 0))).toBe('x');
    expect(s(sj.diff(f(sj.add(x, 1)), x))).toBe('Subs(Derivative(f(_xi_1), _xi_1), _xi_1, x + 1)');
    expect(s(sj.diff(f(sj.add(x, 1), sj.mul(2, x)), x))).toBe(
      'Subs(Derivative(f(_xi_1, 2*x), _xi_1), _xi_1, x + 1) + 2*Subs(Derivative(f(x + 1, _xi_2), _xi_2), _xi_2, 2*x)',
    );
  });

  it('keeps derivatives it does not know unevaluated', () => {
    expect(s(sj.diff(sj.parse('floor(x)', { symbols: [x] }), x))).toBe('Derivative(floor(x), x)');
    expect(s(sj.diff(sj.parse('ceiling(x)', { symbols: [x] }), x))).toBe('Derivative(ceiling(x), x)');
    expect(s(sj.diff(sj.parse('sign(x)', { symbols: [x] }), x))).toBe('Derivative(sign(x), x)');
    expect(s(sj.diff(sj.parse('floor(x**2)', { symbols: [x] }), x))).toBe('Derivative(floor(x**2), x)');
    // SymPy 1.14: 2*DiracDelta(r); DiracDelta is defined above the calculus module (integrals), so it stays unevaluated
    expect(s(sj.diff(sj.parse('sign(r)', { symbols: [r] }), r))).toBe('Derivative(sign(r), r)');
    expect(s(sj.diff(sj.parse('arg(r)', { symbols: [r] }), r))).toBe('0');
    // SymPy 1.14: (re(x)*Derivative(im(x), x) - im(x)*Derivative(re(x), x))/(re(x)**2 + im(x)**2)
    expect(s(sj.diff(sj.parse('arg(x)', { symbols: [x] }), x))).toBe('Derivative(arg(x), x)');
  });

  it('differentiates integrals (Leibniz rule)', () => {
    const I = (...a: sj.ExprLike[]): sj.Expr => new Integral(a.map((v) => sj.sympify(v)));
    expect(s(sj.diff(I(sj.mul(x, y), y, 0, x), x))).toBe('x**2 + Integral(y, (y, 0, x))');
    expect(s(sj.diff(I(sj.mul(x, y), y, x), x))).toBe('x**2 + Integral(y, (y, x))');
    expect(s(sj.diff(I(f(y), y, x, 1), x))).toBe('-f(x)');
    expect(s(sj.diff(I(I(f(y), y), y, x), x))).toBe('Integral(f(y), (y, x))');
    expect(s(sj.diff(I(sj.mul(x, y), y), x))).toBe('Integral(y, y)');
    expect(s(sj.diff(I(f(y), y, 0, 1), x))).toBe('0');
  });

  it('differentiates with respect to functions and derivatives', () => {
    expect(s(sj.diff(sj.pow(f(x), 2), f(x)))).toBe('2*f(x)');
    expect(s(sj.diff(sj.mul(f(x), g(x)), f(x)))).toBe('g(x)');
    expect(s(sj.diff(sj.pow(sj.diff(f(x), x), 2), sj.diff(f(x), x)))).toBe('2*Derivative(f(x), x)');
    expect(s(sj.diff(sj.pow(f(x), 2), f(x), 2))).toBe('2');
  });

  it('differentiates with respect to matrix elements', () => {
    const X = sj.MatrixSymbol('X', 2, 2);
    const Z = sj.MatrixSymbol('Z', n, n);
    expect(s(sj.diff(sj.Trace(X), X.at(0, 0)))).toBe('1');
    expect(s(sj.diff(sj.Trace(X), X.at(0, 1)))).toBe('0');
    expect(s(sj.diff(sj.mul(X.at(0, 0), X.at(1, 1)), X.at(0, 0)))).toBe('X[1, 1]');
    expect(s(sj.diff(sj.Determinant(X), X.at(0, 0)))).toBe('Derivative(Determinant(X), X[0, 0])');
    expect(s(sj.diff(X.asExplicit().det(), X.at(0, 0)))).toBe('X[1, 1]');
    expect(s(sj.diff(X.at(0, 1), X.at(0, 0)))).toBe('0');
    expect(s(sj.diff(Z.at(0, 1), Z.at(0, 0)))).toBe('0');
    expect(s(sj.diff(cast(sj.MatMul(X, X), sj.MatrixExpr).at(0, 0), X.at(0, 0)))).toBe('2*X[0, 0]');
    expect(s(sj.diff(sj.Trace(sj.MatMul(X, X)), X.at(0, 1)))).toBe('2*X[1, 0]');
    expect(s(sj.diff(sj.pow(X.at(0, 0), 3), X.at(0, 0), 2))).toBe('6*X[0, 0]');
    // SymPy 1.14: Sum(KroneckerDelta(0, i, (0, n - 1)), (i, 0, n - 1)); symjs has no KroneckerDelta range and keeps delta**2
    expect(s(sj.diff(sj.Trace(Z), Z.at(0, 0)))).toBe('Sum(KroneckerDelta(0, i)**2, (i, 0, n - 1))');
  });
});

describe('doit and finite differences', () => {
  it('evaluates limits', () => {
    expect(s(sj.doit(new sj.Limit([sj.mul(sj.sin(x), sj.pow(x, -1)), x, sj.S.Zero])))).toBe('1');
  });

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

describe('Mul substitution (SymPy Mul._eval_subs)', () => {
  const R = (p: number, q: number): sj.Expr => sj.Rational.of(BigInt(p), BigInt(q));
  it.each([
    [sj.mul(2, y, sj.pow(C1, -1)), sj.mul(2, sj.pow(C1, -1)), 'C2*y'],
    [sj.mul(4, x), sj.mul(2, x), '2*C2'],
    [sj.mul(6, x), sj.mul(2, x), '3*C2'],
    [sj.mul(3, x), sj.mul(2, x), '3*x'],
    [sj.mul(4, sj.pow(x, 2)), sj.mul(2, x), 'C2**2'],
    [sj.mul(2, sj.pow(x, 2)), sj.mul(2, x), 'C2*x'],
    [sj.mul(8, sj.pow(x, 3)), sj.mul(2, x), 'C2**3'],
    [sj.mul(R(1, 2), x), sj.mul(R(1, 2), x), 'C2'],
    [sj.mul(R(3, 4), x), sj.mul(R(1, 2), x), '3*C2/2'],
    [sj.mul(R(1, 4), x), sj.mul(R(1, 2), x), 'C2/2'],
    [sj.mul(-2, x), sj.mul(2, x), '-C2'],
    [sj.mul(-4, x), sj.mul(-2, x), '2*C2'],
    [sj.mul(2, x), sj.mul(-2, x), '2*x'],
    [sj.mul(6, x, y), sj.mul(3, x), '2*C2*y'],
    [sj.mul(R(9, 2), x), sj.mul(R(3, 2), x), '3*C2'],
    [sj.mul(2, sj.I, x), sj.mul(2, x), 'I*C2'],
    [sj.mul(4, x, y), sj.mul(2, x), '2*C2*y'],
  ])('(%s).subs(%s, C2)', (e, old, expected) => {
    expect(s(sj.subs(e, [[old, C2]]))).toBe(expected);
  });

  it('substitutes sums, powers, noncommutative products and several pairs', () => {
    const A = sj.symbol('A', { commutative: false });
    const B = sj.symbol('B', { commutative: false });
    const z = sj.symbol('z');
    expect(s(sj.subs(sj.mul(x, y), [[sj.mul(2, x), z]]))).toBe('x*y');
    expect(s(sj.subs(sj.mul(A, B, x), [[sj.mul(A, B), z]]))).toBe('x*z');
    expect(s(sj.subs(sj.mul(A, x), [[sj.mul(A, B), z]]))).toBe('x*A');
    expect(s(sj.subs(sj.mul(A, B), [[sj.mul(2, A, B), z]]))).toBe('A*B');
    expect(s(sj.subs(sj.add(x, y, 2), [[sj.add(x, y, 1), z]]))).toBe('z + 1');
    expect(s(sj.subs(sj.add(sj.mul(-1, x), sj.mul(-1, y), 2), [[sj.add(x, y, 1), z]]))).toBe('3 - z');
    expect(s(sj.subs(sj.pow(x, 3), [[sj.pow(x, 2), y]]))).toBe('x**3');
    expect(s(sj.subs(sj.add(x, y), { x: 1, y: 2 }))).toBe('3');
    expect(s(sj.subs(sj.add(x, y), new Map([[x, y], [y, x]]), { simultaneous: true }))).toBe('x + y');
    expect(s(sj.subs(sj.mul(x, y), [[x, y], [y, 2]]))).toBe('4');
    expect(s(sj.subs(sj.diff(f(x), x, 2), [[sj.diff(f(x), x), y]]))).toBe('Derivative(y, x)');
    expect(s(sj.subs(sj.diff(f(x), x), [[sj.diff(f(x), x, 2), y]]))).toBe('Derivative(f(x), x)');
  });

  it('simplifies constants of ODE solutions', () => {
    expect(s(constantsimp(sj.Eq(sj.mul(C1, C2, x), sj.mul(2, y)), [C1, C2]))).toBe('Eq(x, C1*y)');
  });
});

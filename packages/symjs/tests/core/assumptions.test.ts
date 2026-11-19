// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/assumptions.ts.
// Assumption queries on symbols and expressions. Expected values are SymPy 1.14's
// (sympy.core.tests.test_assumptions).

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { isIntegerQ, isMinMax, isNegative, isNonNegative, isNonZero, isPolar, isPositive, isReal, isZero, torf } from '../../src/core/assumptions';
import { at } from '../../src/core/guard';
import { Pow, S, impl } from '../../src/core/nodes';
import { add, mul } from '../../src/core/ops';

const [x] = sj.symbols('x');

const { I } = sj;

it('decides the zeros of unevaluated sinc and cosine of inverse sine', () => {
  const raw = { evaluate: false };
  expect(isZero(sj.fn('sinc', [0], raw))).toBe(false);
  for (const value of [-1, 1]) expect(isZero(sj.fn('cos', [sj.fn('asin', [value], raw)], raw))).toBe(true);
  expect(isZero(sj.fn('cos', [sj.fn('asin', [S.Half], raw)], raw))).toBe(false);
  expect(isZero(sj.fn('cos', [sj.fn('asin', [x], raw)], raw))).toBeUndefined();
});

it('uses the hyperbolic phase to determine real values and signs', () => {
  const raw = { evaluate: false };
  const c = (factor: sj.ExprLike) => sj.fn('cosh', [mul(factor, I, sj.pi)], raw);
  expect(isReal(c(1))).toBe(true);
  expect(isNegative(c(1))).toBe(true);
  expect(isPositive(c(1))).toBe(false);
  expect(isPositive(c(sj.rational(1, 3)))).toBe(true);
  expect(isNegative(c(sj.rational(2, 3)))).toBe(true);
  expect(isReal(sj.fn('tanh', [mul(I, sj.pi, S.Half)], raw))).toBeUndefined();
  expect(isReal(sj.fn('tanh', [add(2, mul(I, sj.pi, S.Half))], raw))).toBe(true);
});

it('leaves phase assumptions undecided without the core function dispatcher', () => {
  const expression = sj.fn('cosh', [x], { evaluate: false });
  const apply = impl.fn;
  delete impl.fn;
  try {
    expect(isReal(expression)).toBeUndefined();
    expect(isPositive(expression)).toBeUndefined();
  } finally {
    if (apply) impl.fn = apply;
  }
});

describe('assumption queries (SymPy test_assumptions)', () => {
  it('knows that 0 to a negative power is not a real number', () => {
    // 0**-1 is zoo; the raw power is not known to be real
    expect(isReal(new Pow(S.Zero, S.NegOne))).toBe(undefined);
  });
  it('knows that a positive power of a nonnegative number is real', () => {
    // SymPy: sqrt(y).is_real is True for nonnegative y
    const yn = new sj.Sym('y', { nonnegative: true });
    expect(isReal(sj.sqrt(yn))).toBe(true);
  });
  it('does not know the sign of Abs(x)', () => {
    // SymPy: Abs(x).is_positive is None
    expect(isPositive(sj.Abs(x))).toBe(undefined);
    expect(isNegative(sj.Abs(x))).toBe(undefined);
    // SymPy gives None for Abs(x).is_positive with zero=False, but the modulus of a nonzero number is positive
    expect(isPositive(sj.Abs(new sj.Sym('x', { zero: false })))).toBe(true);
  });
  it('knows a product with one imaginary factor is not real', () => {
    const p = new sj.Sym('p', { positive: true });
    expect(isReal(mul(I, p))).toBe(false);
    expect(isReal(mul(I, x))).toBe(undefined);
  });
});

describe('signs of numbers and powers (SymPy Expr._eval_is_extended_positive_negative, Pow)', () => {
  const q = new sj.Sym('q', { negative: true });
  const p = new sj.Sym('p', { positive: true });
  const r = new sj.Sym('r', { real: true });
  const P = (t: string): sj.Expr => sj.parse(t, { symbols: { q, p, r, x } } as never);
  it.each([
    // [expr, isPositive, isNegative]; SymPy decides a sum without symbols numerically
    ['pi - 3', true, false],
    ['3 - pi', false, true],
    ['1 + I', false, false],
    ['sqrt(2) + sqrt(3) - sqrt(5 + 2*sqrt(6))', undefined, undefined],
    ['-1 + sin(pi/7)**2 + cos(pi/7)**2', undefined, undefined],
    ['x + 1', undefined, undefined],
    ['1/q', false, true],
    ['q**3', false, true],
    ['q**2', true, false],
    ['q**(-2)', true, false],
    ['sqrt(q)', undefined, false],
    ['p**x', undefined, undefined],
    ['p**r', true, false],
    ['r**2', undefined, false],
    ['sqrt(x)', undefined, false],
  ])('%s', (t, pos, negv) => {
    const e = P(t);
    expect(isPositive(e)).toBe(pos);
    expect(isNegative(e)).toBe(negv);
  });
  it('gives up on sums whose value cannot be computed', () => {
    // a term without a numeric value (an undefined function of a number)
    const f = sj.SymFunction('f');
    expect(isPositive(add(f(1), 1))).toBeUndefined();
    const huge = 10n ** 500n;
    expect(isPositive(new sj.Add([sj.Rational.of(huge), sj.Rational.of(-huge)]))).toBeUndefined();
    expect(isZero(S.NaN)).toBeUndefined();
  });
});

describe('signs of a signed symbol plus a rational (SymPy Add._eval_is_extended_positive, _monotonic_sign)', () => {
  const syms = [
    new sj.Sym('ip', { positive: true, integer: true }),
    new sj.Sym('p', { positive: true }),
    new sj.Sym('ni', { negative: true, integer: true }),
    new sj.Sym('n', { negative: true }),
    new sj.Sym('nn', { nonnegative: true }),
    new sj.Sym('np', { nonpositive: true }),
    new sj.Sym('r', { real: true }),
    new sj.Sym('z', { zero: true }),
    new sj.Sym('zi', { integer: false }),
  ];
  const P = (t: string): sj.Expr => sj.parse(t, { symbols: syms } as never);
  // [expr, is_positive, is_negative, is_nonnegative, is_zero, is_integer] of SymPy 1.14
  const u = undefined;
  it.each<[string, boolean | undefined, boolean | undefined, boolean | undefined, boolean | undefined, boolean | undefined]>([
    ['ip - 1', u, false, true, u, true],
    ['ip - 2', u, u, u, u, true],
    ['ip + 1/2', true, false, true, false, false],
    ['ip - 1/2', true, false, true, false, false],
    ['p - 1', u, u, u, u, u],
    ['p + 1', true, false, true, false, u],
    ['1 - ip', false, u, u, u, true],
    ['2 - ip', u, u, u, u, true],
    // SymPy is_positive is None, while is_nonpositive is True: ni + 1 <= 0
    ['ni + 1', false, u, u, u, true],
    ['ni + 2', u, u, u, u, true],
    ['ni - 1', false, true, false, false, true],
    ['nn - 1', u, u, u, u, u],
    ['nn + 1', true, false, true, false, u],
    ['np + 1', u, u, u, u, u],
    ['np - 1', false, true, false, false, u],
    ['n + 1', u, u, u, u, u],
    ['n - 1', false, true, false, false, u],
    ['1 - p', u, u, u, u, u],
    ['-ip - 1', false, true, false, false, true],
    ['-nn + 1', u, u, u, u, u],
    ['-nn - 1', false, true, false, false, u],
    ['r + 1', u, u, u, u, u],
    ['z + 1', true, false, true, false, true],
    ['z - 1', false, true, false, false, true],
    ['zi + 1', u, u, u, false, false],
    ['ip + zi', u, u, u, false, false],
  ])('%s', (t, pos, negv, nonneg, zero, integer) => {
    const e = P(t);
    expect([isPositive(e), isNegative(e), isNonNegative(e), isZero(e), isIntegerQ(e)]).toEqual([pos, negv, nonneg, zero, integer]);
  });
  it('knows that a non-real number is neither positive nor negative', () => {
    // SymPy: (1 + I).is_positive and (1 + I).is_negative are False
    expect([isPositive(add(1, I)), isNegative(add(1, I))]).toEqual([false, false]);
  });
  it('honours zero=True and integer=False on a symbol', () => {
    const [z, zi] = [at(syms, 7), at(syms, 8)];
    expect([isZero(z), isIntegerQ(z), isPositive(z), isNegative(z), isNonNegative(z), isReal(z)]).toEqual([true, true, false, false, true, true]);
    expect([isZero(zi), isIntegerQ(zi), isReal(zi)]).toEqual([false, false, undefined]);
    expect([sj.isZero(z), sj.isIntegerValued(zi)]).toEqual([true, false]);
  });
});

describe('LambertW and log (SymPy LambertW._eval_is_extended_real, log._eval_is_extended_positive)', () => {
  const P = sj.parse;
  const xp = new sj.Sym('x', { positive: true });
  const r = new sj.Sym('r', { real: true });
  const n = new sj.Sym('n', { negative: true });
  const k = new sj.Sym('k', { integer: true });
  const q = (e: sj.Expr) => [isReal(e), isPositive(e), isNegative(e), isZero(e)];
  it('LambertW', () => {
    // SymPy (is_real, is_positive, is_negative, is_zero); None is undefined
    expect(q(sj.LambertW(xp))).toEqual([true, undefined, undefined, false]);
    expect(q(P('LambertW(1)'))).toEqual([true, true, false, false]);
    expect(q(P('LambertW(-1/4)'))).toEqual([true, false, true, false]);
    expect(q(P('LambertW(-1)'))).toEqual([false, false, false, false]);
    expect(q(P('LambertW(-1/4, -1)'))).toEqual([true, false, true, false]);
    expect(q(P('LambertW(2, 1)'))).toEqual([false, false, false, false]);
    expect(q(sj.LambertW(xp, -1))).toEqual([false, false, false, false]);
    expect(q(sj.LambertW(mul(-1, xp), -1))).toEqual([false, false, false, false]);
    expect(q(sj.LambertW(r))).toEqual([undefined, undefined, undefined, undefined]);
    expect(q(sj.LambertW(add(xp, mul(-1, sj.exp(-1)))))).toEqual([true, undefined, undefined, undefined]);
    // SymPy None, None, None, False
    expect(q(sj.LambertW(n))).toEqual([undefined, undefined, undefined, false]);
    expect(q(sj.LambertW(r, -1))).toEqual([undefined, undefined, undefined, false]);
    expect(q(sj.LambertW(xp, k))).toEqual([undefined, undefined, undefined, false]);
    // SymPy fuzzy_and([x.is_zero, k.is_zero]): False and None
    expect([isZero(sj.LambertW(r, 1)), isZero(sj.LambertW(r, k))]).toEqual([false, undefined]);
    // SymPy False: -x is not zero for a positive x (Mul._eval_is_zero)
    expect(isZero(sj.LambertW(mul(-1, xp)))).toBe(false);
  });
  it('log', () => {
    // SymPy (is_real, is_positive, is_negative)
    const l = (e: sj.Expr) => [isReal(e), isPositive(e), isNegative(e)];
    expect(l(P('-log(2)'))).toEqual([true, false, true]);
    expect(l(P('log(2)'))).toEqual([true, true, false]);
    expect(l(sj.log(xp))).toEqual([true, undefined, undefined]);
    expect(l(sj.log(add(xp, 1)))).toEqual([true, true, false]);
    // log(x) for a real x: SymPy None
    expect(l(sj.log(r))).toEqual([undefined, undefined, undefined]);
    expect(isNegative(sj.log(add(r, 2)))).toBeUndefined();
    // SymPy log(Abs(y) + 1).is_negative = False
    expect(isNegative(sj.log(add(sj.abs(x), 1)))).toBe(false);
    // an extension node that does not say whether it is real
    expect(isReal(sj.defineFunction('g', {})(1))).toBeUndefined();
  });
});

describe('signs of functions of numbers (SymPy Expr._eval_is_extended_positive_negative)', () => {
  const P = sj.parse;
  // [expr, is_positive, is_negative] of SymPy 1.14; None is undefined
  it.each<[string, boolean | undefined, boolean | undefined]>([
    ['sin(1)', true, false],
    ['cos(2)', false, true],
    ['sin(4)', false, true],
    ['sin(10**30)', false, true],
    ['zeta(1/2)', false, true],
    ['asin(-1/3)', false, true],
    // a value that is not real gives None (no _prec on a complex evalf result)
    ['sin(1 + I)', undefined, undefined],
    // the extended sign without finiteness: besselj(1, 5) < 0 is not is_negative in SymPy
    ['besselj(1, 5)', false, undefined],
    ['Ei(-1)', false, undefined],
    ['stieltjes(1)', false, undefined],
    // no value: a function without a numeric implementation
    ['riemann_xi(3)', undefined, undefined],
    // evalf raises (mpmath's ValueError): SymPy None
    ['erfinv(2)', undefined, undefined],
  ])('%s', (t, pos, negv) => {
    const e = P(t);
    expect([isPositive(e), isNegative(e)]).toEqual([pos, negv]);
    // the sign is computed once per expression
    expect([isPositive(e), isNegative(e)]).toEqual([pos, negv]);
  });
  it('decides is_zero of products and powers of nonzero factors (SymPy Mul/Pow._eval_is_zero)', () => {
    const p = new sj.Sym('p', { positive: true });
    const z = new sj.Sym('z', { zero: true });
    expect([isZero(mul(-1, p)), isZero(mul(p, x)), isZero(new Pow(p, sj.Rational.of(1n, 3n))), isZero(new Pow(x, S.Half))]).toEqual([false, undefined, false, undefined]);
    expect([String(mul(z, x)), isNonZero(mul(z, x))]).toEqual(['x*z', false]);
  });
  it('isPolar (SymPy is_polar)', () => {
    const x = sj.symbol('x');
    const y = sj.symbol('y');
    expect(isPolar(sj.polarLift(x))).toBe(true);
    expect(isPolar(new sj.Sym('w', { polar: true }))).toBe(true);
    expect(isPolar(sj.mul(2, sj.polarLift(x)))).toBe(true);
    expect(isPolar(sj.pow(sj.polarLift(x), 2))).toBe(true);
    // SymPy (polar_lift(x)**y).is_polar is True (Pow.is_polar = base.is_polar), and a product is
    // polar when its other factors are positive: (q*polar_lift(x)).is_polar, but not x*polar_lift(x)
    expect(isPolar(sj.pow(sj.polarLift(x), y))).toBe(true);
    expect(isPolar(sj.mul(new sj.Sym('q', { positive: true }), sj.polarLift(x)))).toBe(true);
    expect(isPolar(sj.mul(x, sj.polarLift(x)))).toBe(false);
    expect(isPolar(x)).toBe(false);
  });
});

it('keeps a symbol explicitly known to be nonreal distinct from an unknown realness', () => {
  expect(isReal(sj.symbol('z', { real: false }))).toBe(false);
  expect(isReal(sj.symbol('z'))).toBeUndefined();
});

describe('function assumptions (SymPy test_miscellaneous, test_integers, test_complexes, test_hyperbolic)', () => {
  const r = sj.symbol('r', { real: true });
  const p = sj.symbol('p', { positive: true });
  const n = sj.symbol('n', { negative: true });
  const np = sj.symbol('np', { nonpositive: true });
  const k = sj.symbol('k', { integer: true });
  const i = sj.symbol('i', { imaginary: true });
  const z = sj.symbol('z', { real: false });
  const fn = (name: string, ...args: sj.ExprLike[]): sj.Expr => sj.fn(name as never, args.map((a) => sj.sympify(a)));
  const raw = (name: string, ...args: sj.ExprLike[]): sj.Expr => new sj.AppliedFunction(name as never, args.map((a) => sj.sympify(a)));

  it('decides Max and Min from all of their arguments', () => {
    expect(isReal(sj.Max(r, p))).toBe(true);
    expect(isIntegerQ(sj.Max(k, sj.symbol('m', { integer: true })))).toBe(true);
    expect(isIntegerQ(sj.Max(k, r))).toBeUndefined();
    // Max is positive when one argument is, negative when all are; Min the other way round
    expect(isPositive(sj.Max(p, x))).toBe(true);
    expect(isPositive(sj.Max(n, np))).toBe(false);
    expect(isPositive(sj.Max(n, x))).toBeUndefined();
    expect(isNegative(sj.Max(n, sj.symbol('m', { negative: true })))).toBe(true);
    expect(isNegative(sj.Max(p, x))).toBe(false);
    expect(isNegative(sj.Min(n, x))).toBe(true);
    expect(isPositive(sj.Min(p, x))).toBeUndefined();
    expect(isPositive(sj.Min(p, sj.symbol('q', { positive: true })))).toBe(true);
    expect(isPositive(sj.Min(n, x))).toBe(false);
    expect(isNonNegative(sj.Max(p, x))).toBe(true);
    expect(isNonNegative(sj.Min(p, x))).toBeUndefined();
    expect(isNonNegative(sj.Max(sj.symbol('nn', { nonnegative: true }), x))).toBe(true);
    expect(isZero(sj.Max(p, sj.symbol('q', { positive: true })))).toBe(false);
  });

  it('knows the signs of hyperbolic, inverse and sign functions of real arguments', () => {
    for (const name of ['sinh', 'tanh', 'coth', 'csch', 'atan', 'sign']) {
      expect(isPositive(raw(name, p))).toBe(true);
      expect(isNegative(raw(name, n))).toBe(true);
    }
    expect(isPositive(raw('sinh', x))).toBeUndefined();
    expect(isPositive(raw('cosh', r))).toBe(true);
    expect(isNegative(raw('sech', r))).toBe(false);
    expect(isPositive(raw('cosh', x))).toBeUndefined();
    expect(isNegative(raw('cosh', x))).toBeUndefined();
    expect(isPositive(raw('acot', p))).toBe(true);
    expect(isPositive(raw('acot', n))).toBe(false);
    expect(isNegative(raw('acot', n))).toBe(true);
    expect(isPositive(raw('acot', x))).toBeUndefined();
    expect(isNegative(raw('acot', x))).toBeUndefined();
    expect(isZero(raw('sinh', p))).toBe(false);
    expect(isZero(raw('cosh', r))).toBe(false);
  });

  it('decides sign(x) from its argument', () => {
    expect(isReal(raw('sign', r))).toBe(true);
    expect(isReal(raw('sign', i))).toBe(false);
    expect(isReal(raw('sign', x))).toBeUndefined();
    expect(isReal(raw('sign', mul(S.I, p)))).toBe(false);
    expect(isNonNegative(raw('sign', sj.symbol('nn', { nonnegative: true })))).toBe(true);
    expect(isIntegerQ(raw('sign', r))).toBe(true);
    expect(isIntegerQ(raw('sign', i))).toBe(false);
    expect(isIntegerQ(raw('sign', x))).toBeUndefined();
    expect(isZero(raw('sign', p))).toBe(false);
    expect(isNonNegative(raw('sign', p))).toBe(true);
    expect(isNonNegative(raw('sign', x))).toBeUndefined();
  });

  it('decides floor, ceiling and frac from their arguments', () => {
    expect(isReal(raw('floor', r))).toBe(true);
    expect(isIntegerQ(raw('floor', r))).toBe(true);
    expect(isIntegerQ(raw('ceiling', x))).toBeUndefined();
    expect(isPositive(raw('ceiling', p))).toBe(true);
    expect(isNegative(raw('floor', n))).toBe(true);
    expect(isNegative(raw('frac', x))).toBe(false);
    expect(isNonNegative(raw('floor', p))).toBe(true);
    expect(isNonNegative(raw('frac', r))).toBe(true);
    expect(isNonNegative(raw('frac', x))).toBeUndefined();
    expect(isIntegerQ(raw('frac', k))).toBe(true);
    // frac(x) = 0 exactly for an integer x
    expect(isZero(raw('frac', k))).toBe(true);
    expect(isZero(raw('frac', sj.symbol('w', { integer: false, zero: false })))).toBe(false);
    expect(isZero(raw('frac', x))).toBeUndefined();
  });

  it('decides the realness of the inverse functions on the real axis', () => {
    expect(isReal(raw('asin', sj.Rational.of(1n, 2n)))).toBe(true);
    expect(isReal(raw('acos', 2))).toBe(false);
    expect(isReal(raw('acos', r))).toBeUndefined();
    expect(isReal(raw('asin', x))).toBeUndefined();
    expect(isReal(raw('atanh', sj.Rational.of(-1n, 5n)))).toBe(true);
    expect(isReal(raw('atanh', 1))).toBe(false);
    expect(isReal(raw('acosh', 2))).toBe(true);
    expect(isReal(raw('acosh', sj.Rational.of(1n, 5n)))).toBe(false);
    expect(isReal(raw('asech', sj.Rational.of(2n, 3n)))).toBe(true);
    expect(isReal(raw('acoth', 2))).toBe(true);
    expect(isReal(raw('acoth', -2))).toBe(true);
    expect(isReal(raw('acoth', sj.Rational.of(1n, 2n)))).toBe(false);
    expect(isReal(raw('acoth', r))).toBeUndefined();
    expect(isReal(raw('acoth', x))).toBeUndefined();
    expect(isReal(raw('coth', p))).toBe(true);
    expect(isReal(raw('csch', r))).toBeUndefined();
  });

  it('evaluates functions of numbers that it has no rule for', () => {
    // polylog(1, 2) = -log(-1) = -I*pi
    expect(isReal(raw('polylog', 1, 2))).toBe(false);
    expect(isReal(raw('polylog', 1, -1))).toBeUndefined();
    expect(isReal(raw('polylog', 1, x))).toBeUndefined();
    // no numeric value: Rem has no evaluator
    expect(isReal(raw('Rem', 1, 2))).toBeUndefined();
    expect(isZero(raw('Rem', 1, 2))).toBeUndefined();
    expect(isZero(raw('gamma', 0))).toBeUndefined();
    // an infinite value is no number to compare with 0
    expect(isReal(raw('zeta', 1))).toBeUndefined();
    expect(isZero(raw('cos', sj.Rational.of(1n, 2n)))).toBe(false);
    // a polar number is not decided by its value
    expect(isReal(raw('exp_polar', sj.I))).toBeUndefined();
  });

  it('knows where the elementary functions vanish', () => {
    const zero = sj.symbol('zz', { zero: true });
    expect(isZero(raw('sin', zero))).toBe(true);
    expect(isZero(raw('sin', mul(k, S.Pi)))).toBe(true);
    expect(isZero(raw('cos', add(mul(k, S.Pi), mul(S.Half, S.Pi))))).toBe(true);
    expect(isZero(raw('asinh', p))).toBe(false);
    expect(isZero(raw('atan', x))).toBeUndefined();
    expect(isZero(raw('log', add(1, zero)))).toBe(true);
    expect(isZero(raw('log', n))).toBe(false);
    expect(isZero(raw('log', x))).toBeUndefined();
    expect(isZero(fn('abs', p))).toBe(false);
  });

  it('decides a Piecewise from all of its expressions', () => {
    const pw = sj.piecewise([-1, sj.Lt(x, 1)], [1, true]);
    expect(isZero(pw)).toBe(false);
    expect(isReal(pw)).toBe(true);
    expect(isPositive(pw)).toBeUndefined();
    expect(isNegative(sj.piecewise([-1, sj.Lt(x, 1)], [-2, true]))).toBe(true);
    // oo, -oo and zoo are not real numbers; nan is undecided
    expect(isReal(sj.piecewise([0, sj.Lt(x, 1)], [S.Infinity, true]))).toBeUndefined();
    expect(isReal(sj.piecewise([S.ComplexInfinity, sj.Lt(x, 1)], [S.NegativeInfinity, true]))).toBe(false);
    expect(isReal(sj.piecewise([0, sj.Lt(x, 1)], [S.NaN, true]))).toBeUndefined();
    expect(sj.isFinite(sj.piecewise([0, sj.Lt(x, 1)], [S.Infinity, true]))).toBe('unknown');
  });

  it('counts the imaginary factors of a product', () => {
    expect(isReal(mul(S.I, i))).toBe(true);
    expect(isReal(mul(S.I, i, sj.symbol('j', { imaginary: true })))).toBe(false);
    expect(isReal(mul(S.I, z))).toBeUndefined();
    expect(isReal(mul(S.I, sj.symbol('y', { imaginary: true }), x))).toBeUndefined();
  });

  it('knows that a product with an even number of nonpositive factors is nonnegative', () => {
    expect(isNonNegative(mul(-1, np))).toBe(true);
    expect(isNonNegative(mul(np, np, sj.symbol('q', { nonpositive: true })))).toBeUndefined();
    expect(isNonNegative(mul(np, x))).toBeUndefined();
  });

  it('applies torf to lists', () => {
    expect(torf([p, x], isPositive)).toBeUndefined();
    expect(torf([n, np], isPositive)).toBe(false);
    expect(isMinMax(sj.Max(x, r))).toBe(true);
    expect(isMinMax(x)).toBe(false);
  });
});


it('does not infer the magnitude of the negative of a negative symbol', () => {
  const n = new sj.Sym('n', { negative: true });
  expect(isPositive(sj.add(sj.neg(n), -1))).toBeUndefined();
});

describe('symbols that are not real', () => {
  it('are neither positive nor negative (SymPy Symbol(real=False).is_positive is False)', () => {
    const nr = new sj.Sym('nonreal151', { real: false });
    expect(isPositive(nr)).toBe(false);
    expect(isNegative(nr)).toBe(false);
    expect(isPositive(new sj.Sym('notpositive151', { positive: false }))).toBe(false);
    expect(isNegative(new sj.Sym('notnegative151', { negative: false }))).toBe(false);
    expect(isPositive(new sj.Sym('plain151'))).toBe(undefined);
    expect(isNegative(new sj.Sym('plain151'))).toBe(undefined);
  });
});

it('answers for an undefined function from the facts it was declared with (SymPy Function(name, **assumptions))', () => {
  const x = new sj.Sym('x');
  const f = sj.SymFunction('f', { assumptions: { positive: true } })(x);
  const g = sj.SymFunction('g')(x);
  const k = sj.SymFunction('k', { assumptions: { integer: true, negative: true } })(x);
  expect([isPositive(f), isNegative(f), isNonNegative(f), isReal(f), isZero(f), isNonZero(f)]).toEqual([true, false, true, true, false, true]);
  expect([isPositive(g), isNegative(g), isNonNegative(g), isReal(g), isZero(g), isIntegerQ(g)]).toEqual([undefined, undefined, undefined, undefined, undefined, undefined]);
  expect([isIntegerQ(k), isNegative(k), isPositive(k)]).toEqual([true, true, false]);
  expect(String(sj.sqrt(sj.pow(f, 2)))).toBe('f(x)');
  expect(String(sj.Abs(f))).toBe('f(x)');
  expect(String(sj.sign(f))).toBe('1');
  expect(String(sj.Abs(k))).toBe('-k(x)');
});

it('a sum of real terms and one term that is not real is neither real nor zero', () => {
  const i = new sj.Sym('i', { imaginary: true });
  const r = new sj.Sym('r', { real: true });
  const x = new sj.Sym('x');
  expect([isReal(sj.add(r, i)), isZero(sj.add(r, i)), isReal(sj.add(r, sj.mul(2, i), 1))]).toEqual([false, false, false]);
  expect([isReal(sj.add(r, i, x)), isZero(sj.add(r, i, x)), isReal(sj.add(i, sj.mul(sj.I, r)))]).toEqual([undefined, undefined, undefined]);
  expect(String(sj.Ne(sj.add(r, i), 0))).toBe('True');
});

it('recognizes real powers that include the zero exponent', () => {
  const n = sj.symbol('n', { nonnegative: true });
  const k = sj.symbol('k', { nonnegative: true });
  expect(isReal(sj.pow(n, k))).toBe(true);
  expect(isNonNegative(sj.pow(n, k))).toBe(true);
  expect(isNonNegative(sj.mul(n, k))).toBe(true);
});

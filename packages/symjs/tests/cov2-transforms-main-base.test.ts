// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// The shared machinery of the integral transforms; expected values from SymPy 1.14.

import { describe, expect, it } from 'vitest';
import type { Expr, TransformResult } from '../src';
import { Add, FourierTransform, IntegralTransformError, LaplaceTransform, Rational, Rel, S, Sym, UndefFn, neg, fourierTransform, parse, rewrite, sstr, symbols } from '../src';
import { BoolOp } from '../src/core/boolalg';
import { GenericIntegralTransform, IntegralTransform, decide, diffTransforms, maxPlane, transformArgs } from '../src/integrals/transforms/base';

const [x, k, s, t] = symbols('x k s t');
const y = new Sym('y', { real: true });
const p = new Sym('p', { positive: true });
const ng = new Sym('ng', { negative: true });
const nn = new Sym('nn', { nonnegative: true });
const tuple = (r: TransformResult): string => (Array.isArray(r) ? `(${r.map((e) => sstr(e as Expr)).join(', ')})` : sstr(r as Expr));
const R = (op: 'Eq' | 'Ne' | 'Lt' | 'Le' | 'Gt' | 'Ge', l: Expr, r: Expr | number) => new Rel(op, l, typeof r === 'number' ? Rational.of(r) : r);

describe('decide: the automatic evaluation of relationals', () => {
  it('relationals settled by the assumptions (undefined where SymPy leaves them unevaluated)', () => {
    // [Eq(p, 0), Eq(x, x), Eq(x, 0), Ne(p, 0), Ne(x, x), Ne(x, 0)] -> [False, True, Eq(x, 0), True, False, Ne(x, 0)]
    expect([R('Eq', p, 0), R('Eq', x, x), R('Eq', x, 0), R('Ne', p, 0), R('Ne', x, x), R('Ne', x, 0)].map(decide)).toEqual([false, true, undefined, true, false, undefined]);
    // [Lt(ng, 0), Lt(p, 0), Lt(x, 0), Le(ng, 0), Le(y, y), Le(-nn, 0), Le(p, 0), Le(x, 0)] -> [True, False, x < 0, True, True, True, False, x <= 0]
    expect([R('Lt', ng, 0), R('Lt', p, 0), R('Lt', x, 0), R('Le', ng, 0), R('Le', y, y), R('Le', neg(nn), 0), R('Le', p, 0), R('Le', x, 0)].map(decide)).toEqual([true, false, undefined, true, true, true, false, undefined]);
    // [Gt(p, 0), Gt(ng, 0), Gt(y, y), Gt(-nn, 0), Gt(x, 0), Ge(p, 0), Ge(y, y), Ge(nn, 0), Ge(ng, 0), Ge(x, 0)]
    // -> [True, False, False, False, x > 0, True, True, True, False, x >= 0]
    expect([R('Gt', p, 0), R('Gt', ng, 0), R('Gt', y, y), R('Gt', neg(nn), 0), R('Gt', x, 0), R('Ge', p, 0), R('Ge', y, y), R('Ge', nn, 0), R('Ge', ng, 0), R('Ge', x, 0)].map(decide)).toEqual([
      true,
      false,
      false,
      false,
      undefined,
      true,
      true,
      true,
      false,
      undefined,
    ]);
    // numbers: Lt(1, 2), Ge(0.5, 1/2), Ne(1, 1)
    expect([R('Lt', Rational.of(1), 2), R('Ge', parse('0.5'), Rational.of(1n, 2n)), R('Ne', Rational.of(1), 1)].map(decide)).toEqual([true, true, false]);
  });

  it('boolean combinations', () => {
    // And(1 < 2, x < 1) -> x < 1; Or(x < 1, p > 0) -> True; Or(p < 0, ng > 0) -> False; Or(x < 1, p < 0) -> x < 1
    expect(decide(new BoolOp('And', [R('Lt', Rational.of(1), 2), R('Lt', x, 1)]))).toBe(undefined);
    expect(decide(new BoolOp('And', [R('Lt', Rational.of(1), 2), R('Gt', p, 0)]))).toBe(true);
    // And(p < 0, x < 1) -> False
    expect(decide(new BoolOp('And', [R('Lt', p, 0), R('Lt', x, 1)]))).toBe(false);
    expect(decide(new BoolOp('Or', [R('Lt', x, 1), R('Gt', p, 0)]))).toBe(true);
    expect(decide(new BoolOp('Or', [R('Lt', p, 0), R('Gt', ng, 0)]))).toBe(false);
    expect(decide(new BoolOp('Or', [R('Lt', x, 1), R('Lt', p, 0)]))).toBe(undefined);
    // Not(p > 0) -> False; Not(x < 1) -> x >= 1; Xor(p > 0, x < 1) -> x >= 1
    expect(decide(new BoolOp('Not', [R('Gt', p, 0)]))).toBe(false);
    expect(decide(new BoolOp('Not', [R('Lt', x, 1)]))).toBe(undefined);
    expect(decide(new BoolOp('Xor', [R('Gt', p, 0), R('Lt', x, 1)]))).toBe(undefined);
  });

  it('what is not a condition, and invalid comparisons', () => {
    expect(decide(x)).toBe(undefined);
    // SymPy raises TypeError (invalid comparison) for nan and zoo
    expect(decide(R('Lt', S.NaN, 1))).toBe(undefined);
    expect(decide(R('Lt', S.ComplexInfinity, 1))).toBe(undefined);
  });
});

describe('helpers', () => {
  it('maxPlane keeps the first of equal planes', () => {
    // Max(1/2, 0.5): the two are equal, the first one is kept
    expect(sstr(maxPlane([Rational.of(1n, 2n), parse('0.5')]))).toBe('1/2');
    expect(sstr(maxPlane([S.NegativeInfinity, x]))).toBe('x');
  });

  it('diffTransforms differentiates unevaluated transforms', () => {
    const L = new LaplaceTransform(new UndefFn('f', [t]), t, s);
    // diff(LaplaceTransform(f(t), t, s), s, 2) -> Derivative(LaplaceTransform(f(t), t, s), (s, 2))
    expect(sstr(diffTransforms(L, s, 2))).toBe('Derivative(LaplaceTransform(f(t), t, s), (s, 2))');
  });

  it('rewrite(Integral)', () => {
    // LaplaceTransform(f(t), t, s).rewrite(Integral) -> Integral(f(t)*exp(-s*t), (t, 0, oo))
    const L = new LaplaceTransform(new UndefFn('f', [t]), t, s);
    expect(sstr(rewrite(L, 'Integral'))).toBe('Integral(f(t)*exp(-s*t), (t, 0, oo))');
    // another target leaves the transform
    expect(sstr(rewrite(L, 'sin'))).toBe('LaplaceTransform(f(t), t, s)');
  });
});

describe('the generic doit', () => {
  it('sums term by term, with conditions and without simplification', () => {
    // SymPy computes the sum directly: (sqrt(pi)*(-pi**2*k**2 + 3/2)*exp(-pi**2*k**2), True)
    expect(tuple(fourierTransform(parse('exp(-x**2) + x**2*exp(-x**2)'), x, k, { noconds: false }))).toBe('(sqrt(pi)*(-pi**2*k**2 + 3/2)*exp(-pi**2*k**2), True)');
    // simplify=False: SymPy keeps a long unsimplified expression in erfc; symjs's terms are already
    // simple, and their sum is the transform above expanded
    expect(sstr(fourierTransform(parse('exp(-x**2) + x**2*exp(-x**2)'), x, k, { simplify: false }) as Expr)).toBe('-pi**(5/2)*k**2*exp(-pi**2*k**2) + 3*sqrt(pi)*exp(-pi**2*k**2)/2');
  });

  it('a function variable that is not a symbol', () => {
    // SymPy: ValueError (the limits of the defining Integral are invalid)
    const T = new FourierTransform(parse('exp(-x**2)'), 2, k);
    expect(T.doit()).toBe(T);
  });

  // a transform of x that fails on sums and gives the condition False for x itself
  class Toy extends GenericIntegralTransform {
    constructor(f: Expr, a: Expr, b: Expr) {
      super('Toy', [f, a, b]);
    }
    get transformName(): string {
      return 'Toy';
    }
    get asIntegral(): Expr {
      return this.function;
    }
    withArgs(args: readonly Expr[]): Expr {
      return new Toy(...transformArgs(args));
    }
    protected withFunction(f: Expr): IntegralTransform {
      return new Toy(f, this.functionVariable, this.transformVariable);
    }
    protected computeTransform(f: Expr): TransformResult {
      if (f.key === k.key) throw new TypeError('broken');
      if (f instanceof Add) throw new IntegralTransformError('Toy', f, 'a sum');
      return [f, f.key === x.key ? S.false : S.true];
    }
  }

  it('terms whose conditions contradict leave the transform unevaluated (SymPy _collapse_extra)', () => {
    expect(sstr(new Toy(parse('x + 1'), x, k).doit({ noconds: false }) as Expr)).toBe('Toy(x + 1, x, k)');
    expect(tuple(new Toy(parse('x**2 + 1'), x, k).doit({ noconds: false }))).toBe('(x**2 + 1, True)');
  });

  it('errors other than IntegralTransformError propagate', () => {
    expect(() => new Toy(k, x, k).doit()).toThrow('broken');
    class Toy2 extends Toy {
      protected override collapseExtra(): never {
        throw new TypeError('collapse');
      }
    }
    expect(() => new Toy2(parse('x**2 + 1'), x, k).doit()).toThrow('collapse');
  });
});

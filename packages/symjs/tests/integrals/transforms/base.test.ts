// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/integrals/transforms/base.ts.
// The shared machinery of the integral transforms. Expected values are those of SymPy 1.14.

import { describe, expect, it } from 'vitest';
import * as sj from '../../../src';
import {
  type Expr,
  subs,
  SymFunction,
  S,
  Sym,
  add,
  diff,
  doit,
  exp,
  mul,
  pow,
  sin,
  symbols,
  type TransformResult,
  Add,
  FourierTransform,
  IntegralTransformError,
  LaplaceTransform,
  Rational,
  Rel,
  UndefFn,
  neg,
  fourierTransform,
  parse,
  rewrite,
  sstr,
} from '../../../src';
import {
  CosineTransform,
  HankelTransform,
  InverseCosineTransform,
  InverseFourierTransform,
  InverseHankelTransform,
  InverseLaplaceTransform,
  InverseMellinTransform,
  InverseSineTransform,
  MellinTransform,
  SineTransform,
  hankelTransform,
  inverseLaplaceTransform,
  inverseMellinTransform,
  laplaceTransform,
  mellinTransform,
  sineTransform,
} from '../../../src/integrals/transforms';
import { BoolOp } from '../../../src/core/boolalg';
import {
  GenericIntegralTransform,
  IntegralTransform,
  decide,
  diffTransforms,
  maxPlane,
  transformArgs,
} from '../../../src/integrals/transforms/base';

/** str of a result; tuples print like SymPy's. */
const show = (v: unknown): string => (Array.isArray(v) ? `(${v.map(show).join(', ')})` : String(v));

describe('unevaluated transforms', () => {
  const [t, s, x, k, nu] = symbols('t s x k nu');
  const f = SymFunction('f');

  it('print like SymPy and evaluate with doit', () => {
    expect(String(new LaplaceTransform(f(t), t, s))).toBe('LaplaceTransform(f(t), t, s)');
    expect(String(new InverseLaplaceTransform(f(s), s, t))).toBe('InverseLaplaceTransform(f(s), s, t, _None)');
    expect(String(new InverseLaplaceTransform(f(s), s, t, 0))).toBe('InverseLaplaceTransform(f(s), s, t, 0)');
    expect(String(new MellinTransform(f(x), x, s))).toBe('MellinTransform(f(x), x, s)');
    expect(String(new InverseMellinTransform(f(s), s, x, 0, 1))).toBe('InverseMellinTransform(f(s), s, x, 0, 1)');
    expect(String(new InverseMellinTransform(f(s), s, x))).toBe('InverseMellinTransform(f(s), s, x, _None, _None)');
    expect(String(new FourierTransform(f(x), x, k))).toBe('FourierTransform(f(x), x, k)');
    expect(String(new InverseFourierTransform(f(k), k, x))).toBe('InverseFourierTransform(f(k), k, x)');
    expect(String(new SineTransform(f(x), x, k))).toBe('SineTransform(f(x), x, k)');
    expect(String(new InverseSineTransform(f(k), k, x))).toBe('InverseSineTransform(f(k), k, x)');
    expect(String(new CosineTransform(f(x), x, k))).toBe('CosineTransform(f(x), x, k)');
    expect(String(new InverseCosineTransform(f(k), k, x))).toBe('InverseCosineTransform(f(k), k, x)');
    expect(String(new HankelTransform(f(x), x, k, nu))).toBe('HankelTransform(f(x), x, k, nu)');
    expect(String(new InverseHankelTransform(f(k), k, x, nu))).toBe('InverseHankelTransform(f(k), k, x, nu)');
    expect(String(new LaplaceTransform(exp(t), t, s).doit())).toBe('1/(s - 1)');
    expect(show(new LaplaceTransform(exp(t), t, s).doit({ noconds: false }))).toBe('(1/(s - 1), 1, True)');
    expect(String(doit(add(mul(2, new LaplaceTransform(exp(t), t, s)), -1)))).toBe('-1 + 2/(s - 1)');
    expect(String(new MellinTransform(exp(mul(-1, x)), x, s).doitSelf())).toBe('gamma(s)');
  });

  it('as integrals, free symbols and derivatives', () => {
    expect(String(new LaplaceTransform(f(t), t, s).asIntegral)).toBe('Integral(f(t)*exp(-s*t), (t, 0, oo))');
    expect(String(new FourierTransform(f(x), x, k).asIntegral)).toBe('Integral(f(x)*exp(-2*I*pi*k*x), (x, -oo, oo))');
    expect(String(new MellinTransform(f(x), x, s).asIntegral)).toBe('Integral(x**(s - 1)*f(x), (x, 0, oo))');
    expect([...new LaplaceTransform(f(t), t, s).freeSymbols()].map(String)).toEqual(['s']);
    expect(String(diff(new LaplaceTransform(f(t), t, s), s))).toBe('Derivative(LaplaceTransform(f(t), t, s), s)');
    expect(String(diff(new LaplaceTransform(f(t), t, s), t))).toBe('0');
  });

  it('stay unevaluated or raise like SymPy', () => {
    expect(show(laplaceTransform(f(t), t, s))).toBe('(LaplaceTransform(f(t), t, s), -oo, True)');
    expect(String(inverseLaplaceTransform(f(s), s, t))).toBe('InverseLaplaceTransform(f(s), s, t, _None)');
    expect(String(fourierTransform(add(mul(2, exp(pow(x, 3))), x), x, k))).toBe('FourierTransform(x, x, k) + 2*FourierTransform(exp(x**3), x, k)');
    expect(String(sineTransform(mul(exp(pow(x, 3)), sin(x)), x, k))).toBe('SineTransform(exp(x**3)*sin(x), x, k)');
    expect(String(mellinTransform(mul(exp(pow(x, 3)), sin(x)), x, s))).toBe('MellinTransform(exp(x**3)*sin(x), x, s)');
    expect(String(mellinTransform(pow(add(1, mul(-1, x)), -1), x, s))).toBe('MellinTransform(1/(1 - x), x, s)');
    expect(String(inverseMellinTransform(exp(pow(k, 3)), k, x, [0, 1]))).toBe('InverseMellinTransform(exp(k**3), k, x, 0, 1)');
    expect(() => hankelTransform(mul(exp(pow(x, 3)), sin(x)), x, k, 0)).toThrow(IntegralTransformError);
    expect(() => fourierTransform(exp(pow(x, 3)), x, k, { needeval: true })).toThrow(IntegralTransformError);
  });

});

describe('transform variables that are expressions (values from SymPy 1.14)', () => {
  const t = new Sym('t');
  const s = new Sym('s');
  const a = new Sym('a');
  it('the variables are typed Expr and keep a substituted value', () => {
    const L = subs(new sj.LaplaceTransform(exp(mul(-1, t)), t, s), [[s, 2]]);
    expect(String(L)).toBe('LaplaceTransform(exp(-t), t, 2)');
    expect(L).toBeInstanceOf(sj.LaplaceTransform);
    const v: Expr = L instanceof sj.LaplaceTransform ? L.transformVariable : S.Zero;
    expect(String(v)).toBe('2');
    expect(String(doit(L))).toBe('1/3');
  });
  it('evaluates at an expression', () => {
    expect(String(doit(subs(new sj.LaplaceTransform(exp(mul(-1, t)), t, s), [[s, add(a, 1)]])))).toBe('1/(a + 2)');
    expect(String(sj.laplaceTransform(sin(t), t, add(s, 1), { noconds: true }))).toBe('1/((s + 1)**2 + 1)');
    expect(String(doit(subs(new sj.LaplaceTransform(SymFunction('f')(t), t, s), [[s, 3]])))).toBe('LaplaceTransform(f(t), t, 3)');
    expect(String(doit(subs(new sj.InverseLaplaceTransform(pow(add(s, 1), -1), s, t), [[t, 2]])))).toBe('exp(-2)');
    expect(String(doit(subs(new sj.FourierTransform(exp(mul(-1, pow(t, 2))), t, s), [[s, 1]])))).toBe('sqrt(pi)*exp(-pi**2)');
  });
});

// The shared machinery of the integral transforms; expected values from SymPy 1.14.

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

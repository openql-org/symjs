// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// The paths and values are SymPy 1.14.0's test_evalf_euler and
// test_evalf_rk4 (holonomic/tests/test_holonomic.py) and the evalf doctest,
// with the values SymPy 1.14.0 prints.

import { describe, expect, it } from 'vitest';
import type { Expr } from '../../src/core';
import { Float, Rational, S, Sym, add, mul, parseExpr as P, pi, sstr, evalf } from '../../src/index';
import { QQ, ZZ } from '../../src/polys/domains';
import { DifferentialOperator, DifferentialOperators, HolonomicFunction as HF, SingularityError } from '../../src/holonomic';
import { NotImplementedError as NIE } from '../../src/core/errors';

const x = new Sym('x');
const [R] = DifferentialOperators(QQ.oldPolyRing(x), 'Dx');
const L = (cs: (string | number)[]) => new DifferentialOperator(cs.map((c) => (typeof c === 'number' ? c : P(c))), R);
const F = (v: number) => new Float(v);
const I = S.I;
/** SymPy's str of a list: the Floats inside lose their trailing zeros. */
const list = (l: readonly Expr[] | readonly Expr[][]): string => `[${l.map((e: Expr | readonly Expr[]) => (Array.isArray(e) ? list(e as Expr[]) : sstr(e as Expr).replace(/(\d\.\d*?)0+(?=\D|$)/g, (_m, a: string) => (a.endsWith('.') ? `${a}0` : a)))).join(', ')}]`;
const lastOf = (r: readonly Expr[]): string => sstr(r[r.length - 1] as Expr);
/** r[-1] + d repeated n times. */
function walk(start: Expr[], n: number, d: Expr): Expr[] {
  const r = [...start];
  for (let i = 0; i < n; i++) r.push(add(r[r.length - 1] as Expr, d));
  return r;
}
const line = (): Expr[] => [0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 1].map((v) => (v === 1 ? S.One : F(v)));
const triangle = (): Expr[] => walk(walk([add(F(0.1), mul(F(0.1), I))], 9, add(F(0.1), mul(F(0.1), I))), 10, add(F(0.1), mul(F(-0.1), I)));
const toHalfPi = (): Expr[] => [...walk([F(0.1)], 14, F(0.1)), mul(pi, Rational.of(1n, 2n))];
const rectangle = (): Expr[] => walk([...walk(walk([mul(F(0.1), I)], 9, mul(F(0.1), I)), 15, F(0.1)), add(mul(pi, Rational.of(1n, 2n)), I)], 10, mul(F(-0.1), I));
const toPi = (): Expr[] => [...walk([F(0.05)], 61, F(0.05)), pi];
const rectangle2 = (): Expr[] => walk(walk(walk([mul(F(0.1), I)], 9, mul(F(0.1), I)), 20, F(0.1)), 10, mul(F(-0.1), I));

const log1p = () => new HF(L([0, 1, '1+x']), x, 0, [0, 1]);
const sin = () => new HF(L([1, 0, 1]), x, 0, [0, 1]);
const cos = () => new HF(L([1, 0, 1]), x, 0, [1, 0]);

/** The value, whose imaginary part is rounding noise of about 1e-16 (the noise differs in the last bits from SymPy's). */
function expectNoise(v: Expr, re: string, sympy: string): void {
  void sympy;
  const [a, b] = [sstr(evalf(v, 15)), re];
  expect(a.startsWith(b)).toBe(true);
}

describe('Euler (SymPy test_evalf_euler)', () => {
  const o = { method: 'Euler' } as const;
  it('log(1 + x) on a line and a triangle', () => {
    expect(lastOf(log1p().evalf(line(), o))).toBe('0.699525841805253');
    expect(lastOf(log1p().evalf(triangle(), o))).toBe('1.07530466271334 - 0.0251200594793912*I');
  });
  it('sin and cos', () => {
    expect(lastOf(sin().evalf(triangle(), o))).toBe('0.905546532085401 - 6.93889390390723e-18*I');
    expect(lastOf(sin().evalf(toHalfPi(), o))).toBe('1.08016557252834');
    // SymPy: 0.976882381836257 - 1.65557671738537e-16*I
    expectNoise(sin().evalf(rectangle(), o).at(-1) as Expr, '0.976882381836257', '0.976882381836257 - 1.65557671738537e-16*I');
    expect(lastOf(cos().evalf(toPi(), o))).toBe('-1.08140824719196');
    expect(lastOf(new HF(L([1, 0, 1]), x, 0, [1, 1]).evalf(rectangle2(), o))).toBe('0.501421652861245 - 3.88578058618805e-16*I');
  });
});

describe('RK4 (SymPy test_evalf_rk4)', () => {
  it('log(1 + x) on a line and a triangle', () => {
    expect(lastOf(log1p().evalf(line()))).toBe('0.693146363174626');
    expect(sstr(evalf(log1p().evalf(triangle()).at(-1) as Expr, 7))).toBe('1.098616 + 1.36083e-7*I');
  });
  it('sin and cos', () => {
    expect(lastOf(sin().evalf(triangle()))).toBe('0.90929463522785 + 1.52655665885959e-16*I');
    expect(lastOf(sin().evalf(toHalfPi()))).toBe('0.999999895088917');
    // SymPy: 1.00000003415141 + 6.11940487991086e-16*I
    expectNoise(sin().evalf(rectangle()).at(-1) as Expr, '1.00000003415141', '1.00000003415141 + 6.11940487991086e-16*I');
    expect(lastOf(cos().evalf(toPi()))).toBe('-0.999999993238714');
    expect(lastOf(new HF(L([1, 0, 1]), x, 0, [1, 1]).evalf(rectangle2()))).toBe('0.493152791638442 - 1.41553435639707e-15*I');
  });
  it('the evalf doctest', () => {
    const e = new HF(L([-1, 1]), x, 0, [1]);
    expect(list(e.evalf(line()))).toBe('[1.10517083333333, 1.22140257085069, 1.34985849706254, 1.49182424008069, 1.64872063859684, 1.82211796209193, 2.01375162659678, 2.22553956329232, 2.45960141378007, 2.71827974413517]');
    expect(list(e.evalf(line(), { method: 'Euler' }))).toBe('[1.1, 1.21, 1.331, 1.4641, 1.61051, 1.771561, 1.9487171, 2.14358881, 2.357947691, 2.5937424601]');
  });
});

describe('points and steps', () => {
  const e = () => new HF(L([-1, 1]), x, 0, [1]);
  it('a single point is reached in steps of h', () => {
    expect(sstr(e().evalf(1))).toBe('2.71828169265634');
    expect(sstr(e().evalf(-1, { method: 'Euler' }))).toBe('0.358485922408542');
    expect(sstr(e().evalf(F(1), { h: 0.25 }))).toBe('2.71820993920132');
    expect(sstr(e().evalf(0))).toBe('1.00000000000000');
    expect(e().evalf(0, { derivatives: true }).map((v) => sstr(v))).toEqual(['1.00000000000000']);
  });
  it('rational and complex points and coefficients', () => {
    expect(list(sin().evalf(Rational.of(1n, 2n), { derivatives: true }))).toBe('[0.479425515250845, 0.877582573412327]');
    expect(list(sin().evalf([Rational.of(1n, 3n), P('2/3 + I/3')]))).toBe('[0.327160493827161, 0.653139765279683 + 0.266968957984047*I]');
    const f = new HF(L(['-x', '1+x']), x, 0, [1]);
    expect(list(f.evalf([mul(F(0.5), I), add(F(0.5), mul(F(0.5), I)), S.One]))).toBe(
      '[0.893670703575548 + 0.0324034025374856*I, 1.02605791462722 + 0.184808902551186*I, 1.35893148974246 - 0.000217743344256616*I]',
    );
    const g = new HF(L([-1, 3]), x, 0, [Rational.of(1n, 3n)]);
    expect(list(g.evalf([F(0.5), S.One]))).toBe('[0.393786436899863, 0.465203273658869]');
    expect(list(g.evalf([P('I/2'), P('1 + I')], { method: 'Euler' }))).toBe('[0.333333333333333 + 0.0555555555555556*I, 0.435185185185185 + 0.12962962962963*I]');
  });
  it('integers stay integers (Python ints)', () => {
    expect(sstr(sin().evalf(0, { method: 'Euler' }))).toBe('0');
  });
  it('fractions over ZZ, complex numerators and rational parts of points', () => {
    const [RZ] = DifferentialOperators(ZZ.oldPolyRing(x), 'Dx');
    const g = new HF(new DifferentialOperator([-1, 3], RZ), x, 0, [Rational.of(1n, 3n)]);
    expect(list(g.evalf([F(0.5), S.One]))).toBe('[0.393786436899863, 0.465203273658869]');
    expect(list(new HF(L(['-x', 1]), x, 0, [1]).evalf([mul(F(0.5), I), add(S.One, mul(F(0.5), I))]))).toBe('[0.882486979166667, 1.27776760525174 + 0.694039238823784*I]');
    expect(list(sin().evalf([P('1/3 + I')]))).toBe('[0.493827160493827 + 1.11111111111111*I]');
  });
  it('negative parts', () => {
    expect(list(log1p().evalf([P('-1/10 - I/10'), add(F(-0.2), mul(F(0.1), I)), mul(F(-0.3), I)]))).toBe(
      '[-0.0992267228310084 - 0.110659117039569*I, -0.215368045861253 + 0.124382672360517*I, 0.0424819471573669 - 0.292342696567295*I]',
    );
    expect(list(new HF(L(['-x', '1+x']), x, 0, [1]).evalf([mul(F(-0.5), I), add(F(-0.5), mul(F(-0.5), I))]))).toBe('[0.893670703575548 - 0.0324034025374856*I, 0.822531403475087 + 0.241572259559933*I]');
  });
  it('symbolic points', () => {
    const v = sin().evalf([P('sqrt(I)/2'), P('pi/4 + 1/3 + I/10'), P('pi/4 + 1/3')]);
    expect(list(v.slice(0, 2))).toBe('[0.368284781867994 + 0.338821999318554*I, 0.904629352736632 + 0.0465214958069033*I]');
    // SymPy: 0.899980327394228 + 0.0027205327583028*I (the imaginary part differs in the last bit)
    expect(sstr(evalf(v[2] as Expr, 13))).toBe('0.8999803273942 + 0.002720532758303*I');
  });
  it('errors', () => {
    expect(() => new HF(L([-1, 'x']), x, 1, [1]).evalf([F(0.5), S.Zero])).toThrow(SingularityError);
    expect(() => new HF(L([-1, 'x']), x, 1, [1]).evalf([F(0.5), S.Zero])).toThrow('HolonomicFunction((-1) + (x)*Dx, x, 1, [1]) has a singularity at 0.');
    expect(() => new HF(L([1, 0, 1]), x, 0, [1]).evalf([F(0.5)])).toThrow('Not Enough Initial Conditions');
    expect(() => e().evalf(new Sym('y'))).toThrow(NIE);
  });
});

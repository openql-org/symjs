// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import '../../src/calculus';
import { readFileSync } from 'node:fs';
import { describe, expect, it } from 'vitest';
import { Rational, Sym, parse, str } from '../../src/core';
import { Fn, type ExprLike } from '../../src/core/nodes';
import { first, at, getOrThrow } from '../../src/core/guard';
import { NotImplementedError } from '../../src/core/errors';
import { QQ, EX, ZZ, CoercionFailed, RationalField } from '../../src/polys/domains';
import { PolyElement, PolyRing } from '../../src/polys/rings';
import { PuiseuxRing, PuiseuxPoly } from '../../src/polys/puiseux';
import * as rs from '../../src/polys/ringseries';
import type { SeriesFunction, SeriesPoly } from '../../src/polys/ringseries';

const funcs = new Map<string, SeriesFunction>([
  ['rs_exp', rs.rsExp], ['rs_sin', rs.rsSin], ['rs_cos', rs.rsCos], ['rs_sinh', rs.rsSinh], ['rs_cosh', rs.rsCosh],
  ['rs_asin', rs.rsAsin], ['rs_asinh', rs.rsAsinh], ['rs_atan', rs.rsAtan], ['rs_atanh', rs.rsAtanh],
  ['rs_tan', rs.rsTan], ['rs_tanh', rs.rsTanh], ['rs_cot', rs.rsCot], ['rs_LambertW', rs.rsLambertW],
  ['rs_log', rs.rsLog], ['rs_series_inversion', rs.rsSeriesInversion],
]);
const refs: { fractionalRoot: string; series: { kind: string; domain: string; operation: string; expr: string; precision: number; arg: number | null; expected: string }[] } = JSON.parse(readFileSync(new URL('./ringseries.references.json', import.meta.url), 'utf8'));
const R = new PolyRing('x y', QQ), x = first(R.gens), y = at(R.gens, 1);
const U = new PuiseuxRing('x y', QQ), u = first(U.gens), v = at(U.gens, 1);
const p = (s: string): PolyElement => R.fromExpr(parse(s));
const q = (s: string): PuiseuxPoly => U.fromExpr(parse(s));

describe('sparse series against independently generated SymPy 1.14 references', () => {
  for (const r of refs.series) it(`${r.kind} ${r.domain} ${r.operation}(${r.expr}, ${r.arg ?? ''}, ${r.precision})`, () => {
    const ring = r.kind === 'polynomial' ? new PolyRing('x y', r.domain) : new PuiseuxRing('x y', r.domain);
    const value = ring.fromExpr(parse(r.expr)), variable = first<SeriesPoly>(ring.gens);
    const result = r.arg === null ? getOrThrow(funcs, r.operation)(value, variable, r.precision)
      : r.operation === 'rs_pow' ? rs.rsPow(value, r.arg, variable, r.precision) : rs.rsNthRoot(value, r.arg, variable, r.precision);
    expect(String(result)).toBe(r.expected);
  });
});

describe('finite and truncated algebra', () => {
  it('adjoins trigonometric coefficients for a nonzero constant part', () => {
    const [c, s] = rs.rsCosSin(p('x+y'), x, 3);
    expect(c.ring.fromExpr(parse('cos(y) - x*sin(y) - x**2*cos(y)/2')).equals(c)).toBe(true);
    expect(s.ring.fromExpr(parse('sin(y) + x*cos(y) - x**2*sin(y)/2')).equals(s)).toBe(true);
    const [ch, sh] = rs.rsCoshSinh(q('x+y'), u, 3);
    expect(ch.ring.fromExpr(parse('cosh(y) + x*sinh(y) + x**2*cosh(y)/2')).equals(ch)).toBe(true);
    expect(sh.ring.fromExpr(parse('sinh(y) + x*cosh(y) + x**2*sinh(y)/2')).equals(sh)).toBe(true);
    const tanh = rs.rsTanh(q('x+y'), u, 2);
    expect(tanh.ring.fromExpr(parse('tanh(y) + x*(1-tanh(y)**2)')).equals(tanh)).toBe(true);
  });
  it('adjoins generators after an out-of-range coefficient and propagates unrelated errors', () => {
    class ControlledGround extends RationalField {
      constructor(private readonly error: Error) { super(); }
      override fromSympy(value: ExprLike) {
        if (value instanceof Fn) throw this.error;
        return super.fromSympy(value);
      }
    }
    const limited = new PolyRing('x y', new ControlledGround(new RangeError('coefficient out of range')));
    const result = rs.rsTan(limited.fromExpr(parse('x+y')), first(limited.gens), 2);
    expect(result.ring.fromExpr(parse('tan(y) + x*(1+tan(y)**2)')).equals(result)).toBe(true);
    const unavailable = new PolyRing('x y', new ControlledGround(new NotImplementedError('evaluation unavailable')));
    expect(() => rs.rsTan(unavailable.fromExpr(parse('x+y')), first(unavailable.gens), 2)).toThrow(NotImplementedError);
  });
  it('truncates, multiplies and differentiates in the selected generator', () => {
    expect(String(rs.rsTrunc(p('1+x+x**5+x**10'), x, 10))).toBe('x**5 + x + 1');
    expect(String(rs.rsTrunc(p('x+y**2'), y, 2))).toBe('x');
    expect(String(rs.rsTrunc(p('1+x'), x, 0))).toBe('0');
    expect(String(rs.rsMul(p('1+2*x+x**2'), p('1+x'), x, 3))).toBe('3*x**2 + 3*x + 1');
    expect(String(rs.rsSquare(p('1+2*x+x**2'), x, 3))).toBe('6*x**2 + 4*x + 1');
    expect(String(rs.rsDiff(p('x**2*y**3+x'), x))).toBe('2*x*y**3 + 1');
    expect(String(rs.rsIntegrate(p('x**2*y**3+x'), x))).toBe('1/3*x**3*y**3 + 1/2*x**2');
    expect(String(rs.rsIntegrate(q('x**(-1/2)'), u))).toBe('2*x**(1/2)');
    expect(String(rs.powXin(q('x**(2/5)+x**(2/3)+x'), 0, 15))).toBe('x**6 + x**10 + x**15');
    expect(rs.rsIsPuiseux(q('x**(2/5)+x'), u)).toBe(true);
    expect(rs.rsIsPuiseux(p('x**2+y'), x)).toBe(false);
    expect(String(rs.rsSeriesFromList(p('1+x+x**2'), [1, 2, 3], x, 4))).toBe('6*x**3 + 11*x**2 + 8*x + 6');
    expect(String(rs.rsSeriesFromList(R.zero, [2, 3], x, 5))).toBe('2');
    expect(String(rs.rsSeriesFromList(R.one, [], x, 5))).toBe('0');
  });
  it('substitutes simultaneously and preserves low terms with negative valuations', () => {
    expect(String(rs.rsSubs(p('x**2+y**2'), new Map([[x, x.add(y)], [y, x.add(y.mul(2))]]), x, 3))).toBe('2*x**2 + 6*x*y + 5*y**2');
    expect(String(rs.rsSubs(p('x**2+y**2'), new Map([[y, p('(x+y)**2')]]), x, 3))).toBe('6*x**2*y**2 + x**2 + 4*x*y**3 + y**4');
    expect(String(rs.rsSubs(p('1+x+y'), new Map([[x, R.zero]]), y, 3))).toBe('y + 1');
    // (x+y)^2 with y=x^-2 is x^-4 + 2*x^-1 + x^2, all exact.
    expect(String(rs.rsSubs(q('(x+y)**2'), new Map([[v, q('x**(-2)')]]), u, 3))).toBe('x**(-4) + 2*x**(-1) + x**2');
    expect(String(rs.rsSubs(q('y**(1/2)'), new Map([[v, q('1+x')]]), u, 3))).toBe('1 + 1/2*x + -1/8*x**2');
    expect(String(rs.rsSubs(q('x**(1/2)+y**(1/2)'), new Map(), u, 3))).toBe('y**(1/2) + x**(1/2)');
    expect(String(rs.rsSubs(q('x**(1/2)'), new Map([[u, v.mul(4)]]), u, 3))).toBe('2*y**(1/2)');
    expect(String(rs.rsSubs(q('1/y'), new Map([[v, u.add(1)]]), u, 3))).toBe('1 + -1*x + x**2');
    expect(() => rs.rsSubs(q('x/y'), new Map([[u, U.zero], [v, U.zero]]), u, 3)).toThrow(RangeError);
  });
  it('inverts series and recovers the identity through multiplication', () => {
    for (const expr of ['1+x*y+x**3', '2*x+x**2', 'x**(-2)+x', 'x**(1/3)+x**(2/3)']) {
      const a = q(expr), inverse = rs.rsSeriesInversion(a, u, 9);
      expect(String(rs.rsMul(a, inverse, u, 5))).toBe('1');
    }
    expect(String(rs.rsPow(q('x**(-2)+x'), 3, u, 4))).toBe('x**(-6) + 3*x**(-3) + 3 + x**3');
    expect(String(rs.rsPow(U.zero, 0, u, 3))).toBe('1');
    expect(String(rs.rsPow(U.zero, 2, u, 3))).toBe('');
    expect(rs.rsPow(U.zero, Rational.of(1, 2), u, 3).isZero).toBe(true);
    expect(String(rs.rsNthRoot(u, 0, u, 3))).toBe('1');
    expect(rs.rsPow(x, Rational.of(1, 2), x, 3)).toBeInstanceOf(PuiseuxPoly);
  });
  it('retains enough terms in fractional roots to satisfy the defining power', () => {
    const a = q('8*x+x**2+x**3');
    const root = rs.rsNthRoot(a, 3, u, 5);
    // SymPy 1.14 rs_nth_root stops at x^(10/3), although x^(13/3) has
    // a nonzero coefficient. Its Expr.series includes this required term;
    // the independent generator records that complete reference separately.
    expect(str(root.asExpr())).toBe(refs.fractionalRoot);
    expect(String(rs.rsPow(root, 3, u, Rational.of(17, 3)))).toBe(String(a));
  });
  it('reverts a series and verifies the original composition', () => {
    const a = p('2*x+x**2+x**3*y');
    const reverted = rs.rsSeriesReversion(a, x, 6, y);
    expect(String(rs.rsSubs(a, new Map([[x, reverted]]), y, 6))).toBe('y');
    const simple = rs.rsSeriesReversion(p('x-x**2'), x, 5, y);
    expect(String(simple)).toBe('5*y**4 + 2*y**3 + y**2 + y');
  });
  it('composes algorithms on fractional lattices and at constants', () => {
    expect(String(rs.rsPuiseux(rs.rsExp, q('x**(2/5)+x**(2/3)+x'), u, 1))).toBe('1 + x**(2/5) + x**(2/3) + 1/2*x**(4/5)');
    expect(String(rs.rsPuiseux(rs.rsExp, x, x, 3))).toBe('1/2*x**2 + x + 1');
    expect(String(rs.rsFun(p('x+x*y+x**2*y+x**3*y**2'), rs.rsTan, x, 4))).toBe('1/3*x**3*y**3 + 2*x**3*y**2 + x**3*y + 1/3*x**3 + x**2*y + x*y + x');
    expect(String(rs.rsFun(U.zero, rs.rsExp, u, 3))).toBe('1');
    expect(String(rs.rsFun(q('x**(1/2)'), rs.rsExp, u, 2))).toBe('1 + x**(1/2) + 1/2*x + 1/6*x**(3/2)');
  });
  it('computes Newton sums and the polynomial of pairwise root sums', () => {
    const T = new PolyRing('t', QQ), t = first(T.gens);
    expect(String(rs.rsNewton(t.pow(2).sub(2), t, 5))).toBe('8*t**4 + 4*t**2 + 2');
    expect(String(rs.rsComposeAdd(t.pow(2).sub(2), t.pow(2).sub(3)))).toBe('t**4 - 10*t**2 + 1');
    expect(String(rs.rsComposeAdd(t.pow(2).sub(2), t.pow(2).sub(2)))).toBe('t**4 - 8*t**2');
    const p0 = t.pow(3).add(t.pow(2)).add(t).add(1);
    const transformed = rs.rsHadamardExp(p0);
    expect(String(transformed)).toBe('1/6*t**3 + 1/2*t**2 + t + 1');
    expect(String(rs.rsHadamardExp(transformed, true))).toBe(String(p0));
  });
  it('expands expressions through the public series API', () => {
    const a = new Sym('a');
    expect(String(rs.rsSeries(parse('sin(a)+exp(a)'), a, 5))).toBe('1/24*a**4 + 1/2*a**2 + 2*a + 1');
    expect(str(rs.rsSeries(parse('tan(a+b)*cos(a+c)'), a, 2).asExpr())).toBe('-a*sin(c)*tan(b) + a*cos(c)*tan(b)**2 + a*cos(c) + cos(c)*tan(b)');
    expect(str(rs.rsSeries(parse('exp(a**(1/3)+a**(2/5))'), a, 1).asExpr())).toBe('a**(11/15) + a**(4/5)/2 + a**(2/5) + a**(2/3)/2 + a**(1/3) + 1');
    expect(str(rs.rsSeries(parse('sqrt(2)*a'), a, 3).asExpr())).toBe('sqrt(2)*a');
    expect(String(rs.rsSeries(parse('1.5*a'), a, 3))).toBe('3/2*a');
  });
  it('checks unsupported domains and invalid operations with typed errors', () => {
    expect(() => rs.rsSeriesInversion(R.zero, x, 3)).toThrow(RangeError);
    expect(() => rs.rsSeriesInversion(p('y+x'), x, 3)).toThrow(NotImplementedError);
    expect(() => rs.rsSeriesInversion(p('1+y+x'), x, 3)).toThrow(NotImplementedError);
    expect(() => rs.rsExp(p('y+x'), x, 3)).toThrow(NotImplementedError);
    expect(() => rs.rsExp(p('1+x'), x, 3)).toThrow(CoercionFailed);
    expect(() => rs.rsLog(x, x, 3)).toThrow(NotImplementedError);
    expect(() => rs.rsLog(R.zero, x, 3)).toThrow(RangeError);
    expect(() => rs.rsExp(x, x, 0)).toThrow(RangeError);
    expect(() => rs.rsCos(x, x, 0)).toThrow(RangeError);
    expect(() => rs.rsIntegrate(q('1/x'), u)).toThrow(NotImplementedError);
    expect(() => rs.rsIsPuiseux(q('1/x'), u)).toThrow(RangeError);
    expect(() => rs.rsNthRoot(x, 0.5, x, 3)).toThrow(TypeError);
    expect(() => rs.rsNthRoot(x, 9007199254740993n, x, 3)).toThrow(RangeError);
    expect(() => rs.rsNthRoot(R.zero, 0, x, 3)).toThrow(RangeError);
    expect(() => rs.powXin(x, -1, 2)).toThrow(RangeError);
    expect(() => rs.powXin(x, 3, 2)).toThrow(RangeError);
    expect(() => rs.powXin(x, 0, Rational.of(9007199254740993n))).toThrow(RangeError);
    expect(() => rs.rsMul(x, first(new PolyRing('z', QQ).gens), x, 3)).toThrow(RangeError);
    expect(() => rs.rsSeriesReversion(p('1+x'), x, 3, y)).toThrow(RangeError);
    expect(() => rs.rsSeriesReversion(x, x, 0, y)).toThrow(RangeError);
    expect(() => rs.rsSeriesReversion(q('x**(1/2)'), u, 3, v)).toThrow(NotImplementedError);
    expect(() => rs.rsSeriesReversion(p('x*y+x**2'), x, 3, y)).toThrow(NotImplementedError);
    expect(() => rs.rsSeriesReversion(p('x**2'), x, 3, y)).toThrow(NotImplementedError);
    expect(() => rs.rsFun(q('1/x'), rs.rsExp, u, 3)).toThrow(NotImplementedError);
    expect(() => rs.rsHadamardExp(new PolyRing('x', ZZ).one)).toThrow(NotImplementedError);
    expect(() => rs.rsHadamardExp(q('x**(1/2)'))).toThrow(RangeError);
    expect(() => rs.rsHadamardExp(q('1/x'))).toThrow(RangeError);
    expect(() => rs.rsNewton(p('x+y'), x, 3)).toThrow(RangeError);
    const T = new PolyRing('t', QQ), t = first(T.gens);
    expect(() => rs.rsNewton(T.zero, t, 3)).toThrow(RangeError);
    expect(() => rs.rsComposeAdd(x, t)).toThrow(RangeError);
    expect(() => rs.rsComposeAdd(x, y)).toThrow(RangeError);
    expect(() => rs.rsComposeAdd(T.zero, t)).toThrow(RangeError);
    expect(() => rs.rsSeries(parse('exp(x)'), new Sym('x'), -1)).toThrow(RangeError);
    // SymPy rs_series also leaves logarithms outside the Puiseux ring unsupported.
    expect(() => rs.rsSeries(parse('log(x)'), new Sym('x'), 3)).toThrow(NotImplementedError);
    // EX supports analytic ground constants without coercing them to rationals.
    const E = new PuiseuxRing('x', EX), e = first(E.gens);
    expect(str(rs.rsExp(e.add(1), e, 2).asExpr())).toBe('E*x + E');
  });
});

it('returns paired trigonometric and hyperbolic series', () => {
  const R = new PolyRing([new Sym('x'),new Sym('y')],QQ);
  const x = R.gens[0]!, p = R.fromExpr(parse('x+x*y'));
  expect(rs.rsCosSin(p,x,4).map(String)).toEqual([String(rs.rsCos(p,x,4)), String(rs.rsSin(p,x,4))]);
  expect(rs.rsCoshSinh(p,x,4).map(String)).toEqual([String(rs.rsCosh(p,x,4)), String(rs.rsSinh(p,x,4))]);
});

it('retains the highest Newton power sum after multiplying the logarithmic derivative by x', () => {
  const R = new PolyRing('x', QQ), x = first(R.gens), f = R.fromExpr(parse('x**2 - 2'));
  expect(String(rs.rsNewton(f, x, 4))).toBe('8*x**4 + 4*x**2 + 2');
  expect(String(rs.rsNewton(f, x, 5))).toBe('8*x**4 + 4*x**2 + 2');
});

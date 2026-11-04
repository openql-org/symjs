// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/integrals/prde.ts (parametric Risch differential equation, limited integration and the
// structure theorems), from SymPy's sympy/integrals/tests/test_prde.py. Expected values are SymPy 1.14's;
// polynomials SymPy normalizes over a ring (primitive) and symjs over the field (monic) are compared up
// to that unit where noted.

import { describe, expect, it } from 'vitest';
import { Sym, parse, str } from '../../src';
import type { Expr } from '../../src/core/nodes';
import { NotImplementedError } from '../../src/core/errors';
import { cancel } from '../../src/simplify/rational';
import { DifferentialExtension } from '../../src/integrals/risch';
import type { ExtensionKind } from '../../src/integrals/rischbase';
import { derivation } from '../../src/integrals/rischbase';
import {
  constantSystem,
  isDerivK,
  isLogDerivKTRadical,
  isLogDerivKTRadicalInField,
  limitedIntegrate,
  limitedIntegrateReduce,
  paramPolyRischDE,
  paramRischDE,
  parametricLogDeriv,
  parametricLogDerivHeu,
  polyLinearConstraints,
  prdeCancelLiouvillian,
  prdeLinearConstraints,
  prdeNoCancelBLarge,
  prdeNoCancelBSmall,
  prdeNormalDenom,
  prdeSpde,
  prdeSpecialDenom,
} from '../../src/integrals/prde';
import { KPoly, kNullspace } from '../../src/integrals/rischpoly';

const [x, t, t0, t1, t2] = [new Sym('x'), new Sym('t'), new Sym('t0'), new Sym('t1'), new Sym('t2')];
const P = (s: string, g: Sym = t): KPoly => KPoly.of(parse(s), g);
const E = (p: KPoly | Expr): string => str(p instanceof KPoly ? p.asExpr() : p);
const DE = (...D: KPoly[]): DifferentialExtension => new DifferentialExtension({ D });
const DEx = (D: KPoly[], exts: ExtensionKind[], extargs: string[]): DifferentialExtension =>
  new DifferentialExtension({ D, exts, extargs: extargs.map((a) => parse(a)) });
/** a/b equals the expression e. */
const frac = ([a, b]: readonly [KPoly, KPoly]): string => str(cancel(a.asExpr().div(b.asExpr())));
const M = (A: Expr[][]): string[][] => A.map((r) => r.map((v) => str(v)));

describe('prde_normal_denom', () => {
  it('tan and exp cases (SymPy test_prde_normal_denom)', () => {
    const de = DE(P('1', x), P('1 + t**2'));
    const G: [KPoly, KPoly][] = [
      [P('t'), P('1 + t**2')],
      [P('1'), P('x + x*t**2')],
    ];
    const [a, b, g, h] = prdeNormalDenom(P('1'), P('x'), G, de);
    expect([E(a), frac(b), ...g.map(frac), E(h)]).toEqual(['x', '1', 't*x/(t**2 + 1)', '1/(t**2 + 1)', '1']);
    const de2 = DE(P('1', x), P('t'));
    const G2: [KPoly, KPoly][] = [
      [P('t'), P('t**2 + 2*t + 1')],
      [P('x*t'), P('t**2 + 2*t + 1')],
      [P('x*t**2'), P('t**2 + 2*t + 1')],
    ];
    const [a2, b2, g2, h2] = prdeNormalDenom(P('x'), P('1'), G2, de2);
    expect([E(a2), frac(b2), ...g2.map(frac), E(h2)]).toEqual(['t + 1', 't*x - t + x', 't', 't*x', 't**2*x', 't + 1']);
  });
});

describe('prde_special_denom', () => {
  it('exp and primitive cases (SymPy test_prde_special_denom)', () => {
    const de = DE(P('1', x), P('t'));
    const G: [KPoly, KPoly][] = [
      [P('t'), P('1')],
      [P('t**2'), P('1')],
      [P('t**3'), P('1')],
    ];
    const [A, B, G1, h] = prdeSpecialDenom(P('t + 1'), P('t**2'), P('1'), G, de);
    expect([E(A), E(B), ...G1.map(frac), E(h)]).toEqual(['t + 1', 't**2', 't', 't**2', 't**3', '1']);
    const [A2, B2, G2, h2] = prdeSpecialDenom(P('1'), P('t**2'), P('1'), [
      [P('t'), P('1')],
      [P('1'), P('t')],
    ], de);
    expect([E(A2), E(B2), ...G2.map(frac), E(h2)]).toEqual(['1', 't**2 - 1', 't**2', '1', 't']);
    const dp = DE(P('1', x), P('-2*x*t0', t0));
    dp.decrementLevel();
    const G3: [KPoly, KPoly][] = [
      [P('t'), P('t**2')],
      [P('2*t'), P('t')],
    ];
    const [A3, B3, G3r, h3] = prdeSpecialDenom(P('5*x*t + 1'), P('t**2 + 2*x**3*t'), P('t**3 + 2'), G3, dp);
    expect([E(A3), E(B3), ...G3r.map(frac), E(h3)]).toEqual(['5*t*x + 1', '0', '1/t', '2', '1']);
  });
  it('tan and unknown cases', () => {
    const de = DE(P('1', x), P('(t**2 + 1)*2*x'));
    expect(() => prdeSpecialDenom(P('t + 1'), P('t**2'), P('t**3'), [[P('t'), P('1')]], de)).toThrow(NotImplementedError);
    expect(() => prdeSpecialDenom(P('t + 1'), P('t**2'), P('t**3'), [[P('t'), P('1')]], de, 'other')).toThrow(RangeError);
  });
  it('exp case with nb = 0', () => {
    // b = 1 + t at t = 0 has order 0; alpha = -1 is not a logarithmic derivative of a power of t
    const de = DE(P('1', x), P('t'));
    const [A, B, G, h] = prdeSpecialDenom(P('1'), P('t + 1'), P('1'), [[P('1'), P('t')]], de);
    expect([E(A), E(B), ...G.map(frac), E(h)]).toEqual(['1', 't', '1', 't']);
  });
});

describe('prde_linear_constraints', () => {
  it('base, exp and primitive cases (SymPy test_prde_linear_constraints)', () => {
    const de = DE(P('1', x));
    const [q, A] = prdeLinearConstraints(P('1', x), P('0', x), [
      [P('2*x**3 + 3*x + 1', x), P('x**2 - 1', x)],
      [P('1', x), P('x - 1', x)],
      [P('1', x), P('x + 1', x)],
    ], de);
    expect(q.map(E)).toEqual(['2*x', '0', '0']);
    expect(M(A)).toEqual([
      ['1', '1', '-1'],
      ['5', '1', '1'],
    ]);
    const [q2, A2] = prdeLinearConstraints(P('t + 1'), P('t**2'), [
      [P('t'), P('1')],
      [P('t**2'), P('1')],
      [P('t**3'), P('1')],
    ], DE(P('1', x), P('t')));
    expect([q2.map(E), A2]).toEqual([['t', 't**2', 't**3'], []]);
    const [q3, A3] = prdeLinearConstraints(P('1'), P('0'), [
      [P('2*x'), P('t')],
      [P('-x'), P('t')],
    ], DE(P('1', x), P('1/x')));
    expect([q3.map(E), M(A3)]).toEqual([['0', '0'], [['2*x', '-x']]]);
    expect(polyLinearConstraints([P('t**2'), P('t')], P('t'))[1]).toEqual([]);
  });
});

describe('constant_system', () => {
  it('replaces nonconstant rows by their derivatives (SymPy test_constant_system)', () => {
    const A = [
      ['-(x + 3)/(x - 1)', '(x + 1)/(x - 1)', '1'],
      ['-x - 3', 'x + 1', 'x - 1'],
      ['2*(x + 3)/(x - 1)', '0', '0'],
    ].map((r) => r.map((v) => parse(v)));
    const u = ['(x + 1)/(x - 1)', 'x + 1', '0'].map((v) => parse(v));
    const [B, v] = constantSystem(A, u, DE(P('1', x)));
    expect(M(B)).toEqual([
      ['1', '0', '0'],
      ['0', '1', '0'],
      ['0', '0', '0'],
      ['0', '0', '1'],
    ]);
    expect(v.map(E)).toEqual(['0', '1', '0', '0']);
    expect(constantSystem([], [], DE(P('1', x)))).toEqual([[], []]);
  });
});

describe('prde_spde and the no-cancellation cases', () => {
  it('prde_spde (SymPy test_prde_spde)', () => {
    const [A, B, Q, R, n1] = prdeSpde(P('t'), P('-1/x'), [P('x'), P('-x*t')], 5, DE(P('1', x), P('1/x')));
    expect([E(A), E(B), Q.map(E), R.map(E), n1]).toEqual(['t', '0', ['2*x', '-x'], ['-x**2', '0'], 4]);
  });
  it('prde_no_cancel_b_large (SymPy test_prde_no_cancel)', () => {
    const de = DE(P('1', x));
    const [h1, A1] = prdeNoCancelBLarge(P('1', x), [P('x**2', x), P('1', x)], 2, de);
    expect([h1.map(E), M(A1)]).toEqual([
      ['x**2 - 2*x + 2', '1'],
      [
        ['1', '0', '-1', '0'],
        ['0', '1', '0', '-1'],
      ],
    ]);
    const [h2] = prdeNoCancelBLarge(P('1', x), [P('x**3', x), P('1', x)], 3, de);
    expect(h2.map(E)).toEqual(['x**3 - 3*x**2 + 6*x - 6', '1']);
    const [h3, A3] = prdeNoCancelBLarge(P('x', x), [P('x**2', x), P('1', x)], 1, de);
    expect([h3.map(E), M(A3)]).toEqual([
      ['x', '0'],
      [
        ['1', '-1', '0', '0'],
        ['1', '0', '-1', '0'],
        ['0', '1', '0', '-1'],
      ],
    ]);
  });
  it('prde_no_cancel_b_small (SymPy test_prde_no_cancel)', () => {
    const de = DE(P('1', x), P('t**3 + 1'));
    const G = ['t**6', 'x*t**5', 't**3', 'x*t**2', '1 + x'].map((s) => P(s));
    const [h, A] = prdeNoCancelBSmall(P('x*t'), G, 4, de);
    expect(h.map(E)).toEqual(['t**4/4 - t**3*x/12 + t**2*x**2/24 + t*(-x**3/24 - 11/12) + x/24', 't**3*x/3 - t**2*x**2/6 + t*(x**3/6 - 1/3) - x/6', 't', '0', '0']);
    expect(A.length).toBe(10);
    const de2 = DE(P('1', x), P('1 + t**2'));
    const q = [0, 1].flatMap((i) => [0, 1, 2].map((j) => P(`x**${i}*t**${j}`)));
    const [h2, A2] = prdeNoCancelBSmall(P('-1/x**2'), q, 3, de2);
    const V = kNullspace(A2, 6 + h2.length);
    expect(V.length).toBe(1);
    expect(V[0]?.map(E)).toEqual(['-1/2', '0', '0', '1', '0', '0', '-1/2', '0', '0', '1', '0', '0', '-1/2', '0', '0', '1', '0', '0']);
  });
  it('prde_no_cancel_b_small in the base case', () => {
    const [h, A] = prdeNoCancelBSmall(P('0', x), [P('1', x), P('x', x)], 2, DE(P('1', x)));
    expect([h.map(E), M(A)]).toEqual([
      ['1', 'x', 'x**2/2'],
      [
        ['0', '0', '0', '0', '0'],
        ['1', '0', '0', '-1', '0'],
        ['0', '1', '0', '0', '-1'],
      ],
    ]);
  });
});

describe('prde_cancel_liouvillian', () => {
  it('primitive and exp cases (SymPy test_prde_cancel_liouvillian)', () => {
    const [h, A] = prdeCancelLiouvillian(P('-1/(x - 1)'), [P('-x + 1'), P('1')], 1, DE(P('1', x), P('1/x')));
    expect(h.map(E)).toEqual(['0', '0', 't*(x - 1)', '0', '0', '0', '0', '0', '0', '0', 'x - 1', '-x**2 + x', '0', '0', '0', '0']);
    expect(A.length).toBeGreaterThan(0);
    const [h2, A2] = prdeCancelLiouvillian(P('0'), [P('1')], 0, DE(P('1', x), P('-t')));
    expect([h2.map(E), M(A2)]).toEqual([['1', 'x'], [['-1', '0', '1']]]);
  });
  it('other cases are not implemented', () => {
    // (SymPy fails with UnboundLocalError)
    expect(() => prdeCancelLiouvillian(P('1'), [P('1')], 0, DE(P('1', x), P('t**2 + 1')))).toThrow(NotImplementedError);
  });
});

describe('param_poly_rischDE and param_rischDE', () => {
  it('param_poly_rischDE (SymPy test_param_poly_rischDE)', () => {
    const de = DE(P('1', x));
    const [h, A] = paramPolyRischDE(P('x**2 - x', x), P('1', x), [P('x', x), P('x**2', x)], 3, de);
    expect(kNullspace(A, 4).map((v) => v.map(E))).toEqual([['0', '1', '1', '1']]);
    expect(E(h[0]!.add(h[1]!))).toBe('x');
    const a = P('x**2 - x', x);
    const b = P('x**2 - 5*x + 3', x);
    const [h2, A2] = paramPolyRischDE(a, b, [P('1', x), P('x', x), P('x**2', x)], 3, de);
    expect(kNullspace(A2, 6).map((v) => v.map(E))).toEqual([['3', '-5', '1', '-5', '1', '1']]);
    const p = h2[0]!.mulGround(-5).add(h2[1]!).add(h2[2]!);
    expect(E(a.mul(derivation(p, de)).add(b.mul(p)))).toBe('x**2 - 5*x + 3');
  });
  it('param_poly_rischDE with a negative degree bound and with constant a', () => {
    const de = DE(P('1', x));
    expect(M(paramPolyRischDE(P('1', x), P('1', x), [P('0', x)], -1, de)[1])).toEqual([['0']]);
    expect(M(paramPolyRischDE(P('1', x), P('1', x), [P('x', x)], -1, de)[1])).toEqual([['1'], ['0']]);
    const dt = DE(P('1', x), P('t**2 + 1'));
    expect(() => paramPolyRischDE(P('1'), P('t'), [P('t')], 1, dt)).toThrow(NotImplementedError);
    const dn = DE(P('1', x), P('t**3 + t'));
    expect(() => paramPolyRischDE(P('1'), P('t**2'), [P('t')], 1, dn)).toThrow(NotImplementedError);
    const dl = DE(P('1', x), P('t + 1'));
    expect(() => paramPolyRischDE(P('1'), P('1'), [P('t')], 1, dl)).toThrow(NotImplementedError);
  });
  it('param_rischDE (SymPy test_param_rischDE)', () => {
    const de = DE(P('1', x));
    const G: [KPoly, KPoly][] = [
      [P('1', x), P('x', x)],
      [P('1', x), P('1', x)],
      [P('x', x), P('1', x)],
    ];
    const [h, A] = paramRischDE(P('-1', x), P('x**2', x), G, de);
    expect(h.length).toBe(3);
    const V = kNullspace(A, 6);
    expect(V.length).toBe(2);
    expect(V[0]?.map(E)).toEqual(['-1', '1', '0', '-1', '1', '0']);
    const de2 = DE(P('1', x), P('t'));
    const [h2, A2] = paramRischDE(P('-t - 1'), P('t + x'), [
      [P('t + x'), P('1')],
      [P('0'), P('1')],
    ], de2);
    expect(h2.length).toBe(5);
    const V2 = kNullspace(A2, 7);
    expect(V2.length).toBe(3);
    expect(V2[0]?.map(E)).toEqual(['0', '0', '0', '0', '1', '0', '0']);
  });
  it('param_rischDE without solutions', () => {
    const [h, A] = paramRischDE(P('1', x), P('1', x), [[P('1', x), P('x', x)]], DE(P('1', x)));
    expect([h, M(A)]).toEqual([[], [['1']]]);
  });
});

describe('limited_integrate', () => {
  it('limited_integrate_reduce (SymPy test_limited_integrate_reduce)', () => {
    const [a, b, a2, N, f, V] = limitedIntegrateReduce(P('x'), P('t**2'), [[P('x'), P('t')]], DE(P('1', x), P('1/x')));
    expect([E(a), E(b), E(a2), N, frac(f), V.map(frac)]).toEqual(['t', '-1/x', 't', 1, 'x', ['-t*x']]);
    expect(() => limitedIntegrateReduce(P('x'), P('t**2'), [[P('x'), P('t')]], DE(P('1', x), P('t**2 + 2')))).toThrow(NotImplementedError);
  });
  it('limited_integrate (SymPy test_limited_integrate)', () => {
    const de = DE(P('1', x));
    const r = limitedIntegrate(P('-(1 + x + 5*x**2 - 3*x**3)', x), P('1 - x - x**2 + x**3', x), [[P('x', x), P('x + 1', x)]], de);
    expect(r && [E(r[0][0]), E(r[0][1]), r[1].map(E)]).toEqual(['x**2 - x + 2', 'x - 1', ['2']]);
    const r2 = limitedIntegrate(P('5*x**2', x), P('3', x), [[P('1', x), P('x', x)]], de);
    expect(r2 && [E(r2[0][0]), E(r2[0][1]), r2[1].map(E)]).toEqual(['5*x**3/9', '1', ['0']]);
    // 1/x is not a derivative plus a constant multiple of x
    expect(limitedIntegrate(P('1', x), P('x', x), [[P('x', x), P('1', x)]], de)).toBeUndefined();
  });
});

describe('structure theorems', () => {
  it('is_log_deriv_k_t_radical (SymPy test_is_log_deriv_k_t_radical)', () => {
    expect(isLogDerivKTRadical(P('2*x', x), P('1', x), DEx([P('1', x)], ['none'], ['0']))).toBeUndefined();
    const de = DEx([P('1', x), P('2*t1', t1), P('1/x', t2)], ['none', 'exp', 'log'], ['0', '2*x', 'x']);
    const r = isLogDerivKTRadical(P('x + t2/2', t2), P('1', t2), de);
    expect(r && [r[0].map(([a, b]) => [E(a), E(b)]), E(r[1]), E(r[2]), E(r[3])]).toEqual([[['t1', '1'], ['x', '1']], 't1*x', '2', '0']);
    const de2 = DEx([P('1', x), P('t0', t0), P('1/x')], ['none', 'exp', 'log'], ['0', 'x', 'x']);
    const r2 = isLogDerivKTRadical(P('x + t/2 + 3'), P('1'), de2);
    expect(r2 && [r2[0].map(([a, b]) => [E(a), E(b)]), E(r2[1]), E(r2[2]), E(r2[3])]).toEqual([[['t0', '2'], ['x', '1']], 't0**2*x', '2', '3']);
  });
  it('is_deriv_k (SymPy test_is_deriv_k)', () => {
    const show = (r: ReturnType<typeof isDerivK>) => r && [r[0].map(([a, b]) => [E(a), E(b)]), E(r[1]), E(r[2])];
    const de1 = DEx([P('1', x), P('1/x', t1), P('1/(x + 1)', t2)], ['none', 'log', 'log'], ['0', 'x', 'x + 1']);
    expect(show(isDerivK(P('2*x**2 + 2*x', t2), P('1', t2), de1))).toEqual([[['t1', '1'], ['t2', '1']], 't1 + t2', '2']);
    const de2 = DEx([P('1', x), P('1/x', t1), P('t2', t2)], ['none', 'log', 'exp'], ['0', 'x', 'x']);
    expect(show(isDerivK(P('x**2*t2**3', t2), P('1', t2), de2))).toEqual([[['x', '3'], ['t1', '2']], '2*t1 + 3*x', '1']);
    const de3 = DEx([P('1', x), P('2/x', t1)], ['none', 'log'], ['0', 'x**2']);
    expect(show(isDerivK(P('x', t1), P('1', t1), de3))).toEqual([[['t1', '1/2']], 't1/2', '1']);
    const de4 = DEx([P('1', x), P('2/(1 + x)', t0)], ['none', 'log'], ['0', 'x**2 + 2*x + 1']);
    expect(show(isDerivK(P('1 + x', t0), P('1', t0), de4))).toEqual([[['t0', '1/2']], 't0/2', '1']);
    const de5 = DEx([P('1', x), P('-1/x')], ['none', 'log'], ['0', '1/x']);
    expect(show(isDerivK(P('1'), P('x'), de5))).toEqual([[['t', '1']], 't', '1']);
  });
  it('the structure theorems need the kinds of all monomials', () => {
    // (SymPy raises TypeError when exts is not given, NotImplementedError when it is incomplete)
    expect(() => isDerivK(P('1'), P('x'), DE(P('1', x), P('1/x')))).toThrow(NotImplementedError);
    expect(() => isDerivK(P('1'), P('x'), DE(P('1', x), P('1 + t**2')))).toThrow(NotImplementedError);
    expect(() => isLogDerivKTRadical(P('1'), P('x'), DE(P('1', x), P('t')))).toThrow(NotImplementedError);
    const de = DEx([P('1', x), P('1/x')], ['none', 'log'], ['0', 'x']);
    const r = isDerivK(P('y', x), P('1', x), de);
    expect(r && [r[0].map(([a, b]) => [E(a), E(b)]), E(r[1]), E(r[2])]).toEqual([[['t', '0']], '0', 'y']);
    // a coefficient that is a constant but not a rational number: t = log(x)/y, x = exp(y*t)
    const dy = DEx([P('1', x), P('1/(x*y)')], ['none', 'log'], ['0', 'x']);
    expect(() => isDerivK(P('x', x), P('1', x), dy)).toThrow(NotImplementedError);
  });
  it('is_log_deriv_k_t_radical_in_field (SymPy test_is_log_deriv_k_t_radical_in_field)', () => {
    const show = (r: [Expr, Expr] | undefined) => r && [E(r[0]), E(r[1])];
    const de = DE(P('1', x), P('1/x'));
    expect(show(isLogDerivKTRadicalInField(P('5*t + 1'), P('2*t*x'), de))).toEqual(['2', 't*x**5']);
    expect(show(isLogDerivKTRadicalInField(P('2 + 3*t'), P('5*x*t'), de))).toEqual(['5', 't**2*x**3']);
    const de2 = DE(P('1', x), P('-t/x**2'));
    expect(show(isLogDerivKTRadicalInField(P('-(1 + 2*t)'), P('2*x**2 + 2*x**2*t'), de2))).toEqual(['2', 't**2 + t']);
    expect(show(isLogDerivKTRadicalInField(P('-1'), P('x**2'), de2))).toEqual(['1', 't']);
    expect(show(isLogDerivKTRadicalInField(P('1'), P('2*x**2'), de2))).toEqual(['2', '1/t']);
  });
  it('is_log_deriv_k_t_radical_in_field: no radical', () => {
    const de = DE(P('1', x), P('1/x'));
    // residues that are not rational
    expect(isLogDerivKTRadicalInField(P('1'), P('t**2 + 1'), de)).toBeUndefined();
    // a polynomial part of too high degree
    expect(isLogDerivKTRadicalInField(P('t**2'), P('1'), de)).toBeUndefined();
    expect(isLogDerivKTRadicalInField(P('1', x), P('x**2', x), DE(P('1', x)))).toBeUndefined();
    expect(isLogDerivKTRadicalInField(P('x', x), P('1', x), DE(P('1', x)))).toBeUndefined();
    expect(() => isLogDerivKTRadicalInField(P('1'), P('t'), DE(P('1', x), P('t**2 + 1')))).toThrow(NotImplementedError);
    expect(() => isLogDerivKTRadicalInField(P('1'), P('t'), DE(P('1', x), P('t**2 + 1')), 'other_linear')).toThrow(RangeError);
  });
  it('parametric_log_deriv (SymPy test_parametric_log_deriv)', () => {
    const de = DE(P('1', x), P('1/x'));
    const r = parametricLogDerivHeu(P('5*t**2 + t - 6'), P('2*x*t**2'), P('-1'), P('x*t**2'), de);
    expect(r?.map(E)).toEqual(['2', '6', 't*x**5']);
    expect(parametricLogDeriv(P('t'), P('1'), P('1'), P('1'), de)).toBeUndefined();
  });
});

describe('more cases', () => {
  const db = DE(P('1', x));
  const dp = DE(P('1', x), P('1/x'));
  const de = DE(P('1', x), P('t'));
  it('prde_special_denom with a parametric logarithmic derivative (t = exp(1/x))', () => {
    const ex = DE(P('1', x), P('-t/x**2'));
    const [A, B, G, h] = prdeSpecialDenom(P('1'), P('1 - x + t'), P('x**2'), [[P('1'), P('t')]], ex);
    expect([E(A), E(B), ...G.map(frac), E(h)]).toEqual(['1', 't/x**2 + (2 - x)/x**2', '1', 't']);
  });
  it('no solutions', () => {
    const [h, A] = prdeNoCancelBLarge(P('1', x), [P('0', x)], 1, db);
    expect([h.map(E), M(A)]).toEqual([['0'], [['1', '-1']]]);
    const [h2, A2] = paramRischDE(P('1', x), P('1', x), [[P('y', x), P('x', x)]], db);
    expect([h2, M(A2)]).toEqual([[], [['1']]]);
    expect(limitedIntegrate(P('1', x), P('x**2 + 1', x), [[P('1', x), P('x', x)]], db)).toBeUndefined();
    const r = limitedIntegrate(P('t'), P('1'), [[P('1'), P('x')]], dp);
    expect(r && [E(r[0][0]), E(r[0][1]), r[1].map(E)]).toEqual(['t*x - x', '1', ['0']]);
  });
  it('is_log_deriv_k_t_radical without the derivative (Df = false)', () => {
    expect(isLogDerivKTRadical(P('x'), P('1', x), DEx([P('1', x), P('1/x')], ['none', 'log'], ['0', 'x']), false)).toBeUndefined();
  });
  it('is_log_deriv_k_t_radical_in_field: residues that are not rational, failing recursion', () => {
    expect(isLogDerivKTRadicalInField(P('1'), P('t + x'), dp)).toBeUndefined();
    expect(isLogDerivKTRadicalInField(P('1', x), P('x**2 - 2', x), db)).toBeUndefined();
    expect(isLogDerivKTRadicalInField(P('x'), P('1'), de)).toBeUndefined();
    expect(isLogDerivKTRadicalInField(P('1'), P('1'), dp)).toBeUndefined();
  });
  it('parametric_log_deriv_heu with a constant that is not rational', () => {
    expect(parametricLogDerivHeu(P('x*t'), P('1'), P('t'), P('1'), dp)).toBeUndefined();
  });
});

describe('degenerate cases', () => {
  const db = DE(P('1', x));
  const dp = DE(P('1', x), P('1/x'));
  it('param_poly_rischDE without a solution (SymPy agrees)', () => {
    expect(M(paramPolyRischDE(P('x**2 - x', x), P('1', x), [P('x + 1', x)], 2, db)[1])).toEqual([['1']]);
  });
  it('param_rischDE with zero right-hand sides (SymPy agrees)', () => {
    const [h, A] = paramRischDE(P('0', x), P('1', x), [
      [P('0', x), P('1', x)],
      [P('0', x), P('1', x)],
    ], db);
    expect([h.map(frac), M(A)]).toEqual([
      ['1', '0', '0'],
      [
        ['-1', '0', '0', '1', '0'],
        ['0', '-1', '0', '0', '1'],
      ],
    ]);
    const r = limitedIntegrate(P('0', x), P('1', x), [[P('0', x), P('1', x)]], db);
    expect(r && [E(r[0][0]), E(r[0][1]), r[1].map(E)]).toEqual(['0', '1', ['0']]);
  });
  it('parametric_log_deriv_heu: inconsistent equations for c1 (SymPy agrees)', () => {
    expect(parametricLogDerivHeu(P('t**2'), P('1'), P('t'), P('1'), dp)).toBeUndefined();
    expect(parametricLogDerivHeu(P('t**2 + t'), P('1'), P('t**2 + 2*t'), P('1'), dp)).toBeUndefined();
  });
  it('residues with a parameter are not supported (SymPy: NotImplementedError)', () => {
    expect(() => isLogDerivKTRadicalInField(P('1', x), P('x**2 - y', x), db)).toThrow(NotImplementedError);
  });
  it('prde_no_cancel_b_small with all right-hand sides reduced to zero (SymPy agrees)', () => {
    const [h, A] = prdeNoCancelBSmall(P('t'), [P('0')], 1, DE(P('1', x), P('t**3 + 1')));
    expect([h.map(E), M(A)]).toEqual([['0'], [['1', '-1']]]);
  });
  it('param_rischDE falls back to the bound 5 (bound_degree not implemented over tan)', () => {
    const t1 = new Sym('t1');
    const de = new DifferentialExtension({ D: [P('1', x), KPoly.of(parse('t1**2 + 1'), t1), P('1/x')] });
    expect(() => paramRischDE(P('1/x'), P('1'), [[P('t'), P('1')]], de)).toThrow(NotImplementedError);
  });
});

describe('parametric_log_deriv_heu with consistent equations', () => {
  it('f = 2*w (SymPy: (1, 2, 1))', () => {
    const r = parametricLogDerivHeu(P('2*t**2 + 2*t'), P('1'), P('t**2 + t'), P('1'), DE(P('1', x), P('1/x')));
    expect(r?.map(E)).toEqual(['1', '2', '1']);
  });
});

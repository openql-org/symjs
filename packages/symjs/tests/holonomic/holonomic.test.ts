// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// The cases are SymPy 1.14.0's holonomic/tests/test_holonomic.py and the
// doctests of holonomic/holonomic.py, with the values SymPy 1.14.0 prints.

import { describe, expect, it } from 'vitest';
import type { Expr } from '../../src/core';
import { E, Float, Rational, S, Sym, sstr, parseExpr as P, expand, simplify, hyper, meijerg, hyperexpand, freeSymbols, toComplex } from '../../src/index';
import { CoercionFailed, QQ, ZZ } from '../../src/polys/domains';
import {
  DifferentialOperator,
  DifferentialOperators,
  HolonomicFunction as HF,
  exprToHolonomic as e2h,
  fromHyper,
  fromMeijerg,
  RecurrenceOperators,
  RecurrenceOperator,
  NotHolonomicError,
  NotHyperSeriesError,
} from '../../src/holonomic';
import { NotImplementedError } from '../../src/core/errors';
import { ExprMap } from '../../src/core/exprmap';
import { solveLinear } from '../../src/holonomic/holonomic';

const x = new Sym('x');
const [R, Dx] = DifferentialOperators(ZZ.oldPolyRing(x), 'Dx');
const [RQ] = DifferentialOperators(QQ.oldPolyRing(x), 'Dx');
const L = (cs: (string | number)[], r = R) => new DifferentialOperator(cs.map((c) => (typeof c === 'number' ? c : P(c))), r);
const LQ = (cs: (string | number)[]) => L(cs, RQ);
const pp = () => new HF(L([-1, 1]), x).composition(P('x**2'), 0, [1]);
const qq = () => new HF(L([1, 0, 1]), x, 0, [1, 0]);
const mu = new Sym('mu');
const sd = new Sym('sd', { positive: true });
const ap = new Sym('a', { positive: true });
const bp = new Sym('b', { positive: true });
const xp = new Sym('x', { positive: true });
const nn = new Sym('n');
const [RN] = DifferentialOperators(QQ.polyRing(nn).getField().oldPolyRing(x), 'Dx');
const ni = new Sym('n', { integer: true });
const [RR_, Sn] = RecurrenceOperators(QQ.oldPolyRing(ni), 'Sn');

/** Python's str of a result (lists of tuples as SymPy prints them). */
const fmt = (r: unknown): string => {
  if (Array.isArray(r)) {
    if (r.length && Array.isArray(r[0])) return '[' + r.map((t) => '(' + (t as unknown[]).map(fmt).join(', ') + ')').join(', ') + ']';
    return '[' + r.map(fmt).join(', ') + ']';
  }
  if (r !== null && typeof r === 'object' && 'key' in r) return sstr(r as Expr);
  return String(r);
};

/** Mathematically equal expressions (the forms differ from SymPy's): equal values at sample points. */
function expectSame(a: unknown, b: Expr): void {
  const ea = a as Expr;
  const syms = [...new Set([...freeSymbols(ea), ...freeSymbols(b)].map((s) => s.name))];
  for (const t of [0.3, 0.7]) {
    const values = Object.fromEntries(syms.map((s, i) => [s, s === 'x' ? t : 0.5 + 0.25 * i]));
    const u = toComplex(ea, values);
    const v = toComplex(b, values);
    expect(Math.hypot(u.re - v.re, u.im - v.im)).toBeLessThan(1e-9 * (1 + Math.hypot(v.re, v.im)));
  }
}

describe('SymPy test_holonomic.py', () => {
  it('add1', () => {
    expect(fmt(new HF(L([1, 'x']), x).add(new HF(L([1, 1]), x)))).toBe('HolonomicFunction((x - 2) + (x**2 - 2)*Dx + (x**2 - x)*Dx**2, x)');
  });
  it('add2', () => {
    expect(fmt(new HF(Dx.rmul(x).add(Dx.pow(2).mul(P('x**2+2'))), x).add(new HF(L([-3, 1]), x)))).toBe('HolonomicFunction((-54*x**2 - 126*x - 150) + (-135*x**3 - 252*x**2 - 270*x + 140)*Dx + (-27*x**4 - 24*x**2 + 14*x - 150)*Dx**2 + (9*x**4 + 15*x**3 + 38*x**2 + 30*x + 40)*Dx**3, x)');
  });
  it('add3', () => {
    expect(fmt(new HF(L([-1, 0, 0, 0, 0, 1]), x).add(new HF(L(['x**3', 1]), x)))).toBe('HolonomicFunction((-x**18 + 45*x**14 - 525*x**10 + 1575*x**6 - x**3 - 630*x**2) + (-x**15 + 30*x**11 - 195*x**7 + 210*x**3 - 1)*Dx + (x**18 - 45*x**14 + 525*x**10 - 1575*x**6 + x**3 + 630*x**2)*Dx**5 + (x**15 - 30*x**11 + 195*x**7 - 210*x**3 + 1)*Dx**6, x)');
  });
  it('add4', () => {
    expect(fmt(new HF(L(['-(2*x+3)', 'x**2+3*x+8']), x).add(new HF(L(['-(3*x**2-7)', 'x**3-7*x+5']), x)))).toBe('HolonomicFunction((6*x**2 + 18*x + 14) + (-4*x**3 - 18*x**2 - 62*x + 10)*Dx + (x**4 + 6*x**3 + 31*x**2 - 10*x - 71)*Dx**2, x)');
  });
  it('mul1', () => {
    expect(fmt(new HF(L(['x', 1, 'x']), x).mul(new HF(L([1, '2*x', 1]), x)))).toBe('HolonomicFunction((8*x**6 + 4*x**4 + 6*x**2 + 3) + (24*x**5 - 4*x**3 + 24*x)*Dx + (8*x**6 + 20*x**4 + 12*x**2 + 2)*Dx**2 + (8*x**5 + 4*x**3 + 4*x)*Dx**3 + (2*x**4 + x**2)*Dx**4, x)');
  });
  it('mul2', () => {
    expect(fmt(new HF(L(['1+x', 1, 1]), x).mul(new HF(Dx.mul(x).sub(1).pow(2), x)))).toBe('HolonomicFunction((4*x**7 + 11*x**6 + 16*x**5 + 4*x**4 - 6*x**3 - 7*x**2 - 8*x - 2) + (8*x**6 + 26*x**5 + 24*x**4 - 3*x**3 - 11*x**2 - 6*x - 2)*Dx + (8*x**6 + 18*x**5 + 15*x**4 - 3*x**3 - 6*x**2 - 6*x - 2)*Dx**2 + (8*x**5 + 10*x**4 + 6*x**3 - 2*x**2 - 4*x)*Dx**3 + (4*x**5 + 3*x**4 - x**2)*Dx**4, x)');
  });
  it('mul3', () => {
    expect(fmt(new HF(L([-1, 0, 'x']), x).mul(new HF(Dx.mul(x).sub(x), x)))).toBe('HolonomicFunction((x - 3) + (2 - 2*x)*Dx + (x)*Dx**2, x)');
  });
  it('addic1', () => {
    expect(fmt(new HF(LQ(['-x', 1, 1]), x, 0, [1, 2]).add(new HF(LQ(['x', 0, 1]), x, 0, [1, 0])))).toBe('HolonomicFunction((-x**4 - x**3/4 - x**2 + 1/4) + (x**3 + x**2/4 + 3*x/4 + 1)*Dx + (7/4 - 3*x/2)*Dx**2 + (x**2 - 7*x/4 + 1/4)*Dx**3 + (x**2 + x/4 + 1/2)*Dx**4, x, 0, [2, 2, -2, 2])');
  });
  it('addic2', () => {
    expect(fmt(new HF(LQ(['x**2', '4*x', 1]), x, 0, [3, 4]).add(new HF(LQ([1, 0, 1]), x, 0, [1, 1])))).toBe('HolonomicFunction((x**6 + 2*x**4 - 5*x**2 - 6) + (4*x**5 + 36*x**3 - 32*x)*Dx + (x**6 + 3*x**4 + 5*x**2 - 9)*Dx**2 + (4*x**5 + 36*x**3 - 32*x)*Dx**3 + (x**4 + 10*x**2 - 3)*Dx**4, x, 0, [4, 5, -1, -17])');
  });
  it('addic3', () => {
    expect(fmt(new HF(LQ([-1, 1]), x, 2, [1]).add(new HF(LQ(['x', 0, 0, 1]), x, 2, [3, 0, 1])))).toBe('HolonomicFunction((-x**2 - x + 1) + (x**2 + x)*Dx + (-x - 2)*Dx**3 + (x + 1)*Dx**4, x, 2, [4, 1, 2, -5])');
  });
  it('addic4', () => {
    expect(fmt(e2h(P('sin(x)')).add(e2h(P('1/x'), { x0: 1 })))).toBe('HolonomicFunction((x**2 + 6) + (x**3 + 2*x)*Dx + (x**2 + 6)*Dx**2 + (x**3 + 2*x)*Dx**3, x, 1, [sin(1) + 1, -1 + cos(1), 2 - sin(1)])');
  });
  it('addic5', () => {
    expect(fmt(e2h(P('sqrt(x)')).add(e2h(P('sqrt(x**2-x)'))))).toBe('HolonomicFunction((x/2 - 3/4) + (-x**2/2 + x)*Dx + (x**3 - x**2)*Dx**2, x, 0, {1/2: [1 + I]})');
  });
  it('addic5e', () => {
    // SymPy: sqrt(x)*(-2*C_1*(sqrt(1 - x) - 1) + 1 + I)
    expectSame(e2h(P('sqrt(x)')).add(e2h(P('sqrt(x**2-x)'))).toExpr(), P('sqrt(x)*(-2*C_1*(sqrt(1 - x) - 1) + 1 + I)'));
  });
  it('mulic1', () => {
    expect(fmt(new HF(LQ([-1, 'x', 1]), x, 0, [3, 1]).mul(new HF(LQ([1, 0, 1]), x, 0, [1, 1])))).toBe('HolonomicFunction((x**4 + 14*x**2 + 60) + (4*x)*Dx + (x**4 + 9*x**2 + 20)*Dx**2 + (2*x**3 + 18*x)*Dx**3 + (x**2 + 10)*Dx**4, x, 0, [3, 4, 2, 3])');
  });
  it('mulic2', () => {
    expect(fmt(new HF(LQ(['x', 0, 1]), x, 0, [1, 0]).mul(new HF(LQ(['-x**2', 0, 0, 1]), x, 0, [3, 3, 3])))).toBe('HolonomicFunction((x**8 - 37*x**7/27 - 10*x**6/27 - 164*x**5/9 - 184*x**4/9 + 160*x**3/27 + 404*x**2/9 + 8*x + 40/3) + (6*x**7 - 128*x**6/9 - 98*x**5/9 - 28*x**4/9 + 8*x**3/9 + 28*x**2 + 40*x/9 - 40)*Dx + (3*x**6 - 82*x**5/9 + 76*x**4/9 + 4*x**3/3 + 220*x**2/9 - 80*x/3)*Dx**2 + (-2*x**6 + 128*x**5/27 - 2*x**4/3 - 80*x**2/9 + 200/9)*Dx**3 + (3*x**5 - 64*x**4/9 - 28*x**3/9 + 6*x**2 - 20*x/9 - 20/3)*Dx**4 + (-4*x**3 + 64*x**2/9 + 8*x/3)*Dx**5 + (x**4 - 64*x**3/27 - 4*x**2/3 + 20/9)*Dx**6, x, 0, [3, 3, 3, -3, -12, -24])');
  });
  it('mulic3', () => {
    expect(fmt(new HF(LQ([-1, 1]), x, 0, [2]).mul(new HF(LQ([1, 2, 'x']), x, 0, [0, 1])))).toBe('HolonomicFunction((x - 1) + (2 - 2*x)*Dx + (x)*Dx**2, x, 0, [0, 2])');
  });
  it('mulic4', () => {
    expect(fmt(new HF(LQ([-1, 0, 1]), x, 0, [1, 3]).mul(new HF(LQ([1, 0, 0, 1]), x, 0, [1, 2, 1])))).toBe('HolonomicFunction((6)*Dx + (3)*Dx**2 + (2)*Dx**3 + (-3)*Dx**4 + (1)*Dx**6, x, 0, [1, 5, 14, 17, 17, 2])');
  });
  it('mulic5', () => {
    expect(fmt(e2h(P('sin(x)')).mul(e2h(P('1/x'), { x0: 1 })))).toBe('HolonomicFunction((x) + (2)*Dx + (x)*Dx**2, x, 1, [sin(1), -sin(1) + cos(1)])');
  });
  it('mulic6', () => {
    expect(fmt(e2h(P('sqrt(x)')).mul(e2h(P('sqrt(x**2-x)'))).toExpr())).toBe('I*x*sqrt(1 - x)');
  });
  it('comp1', () => {
    expect(fmt(new HF(L([-1, 1]), x).composition(P('x**2+x')))).toBe('HolonomicFunction((-2*x - 1) + (1)*Dx, x)');
  });
  it('comp2', () => {
    expect(fmt(new HF(L([1, 0, 1]), x).composition(P('x**5+x**2+1')))).toBe('HolonomicFunction((125*x**12 + 150*x**9 + 60*x**6 + 8*x**3) + (-20*x**3 - 2)*Dx + (5*x**4 + 2*x)*Dx**2, x)');
  });
  it('comp3', () => {
    expect(fmt(new HF(Dx.pow(2).mul(x).add(x), x).composition(P('2*x**3+x**2+1')))).toBe('HolonomicFunction((216*x**9 + 324*x**8 + 180*x**7 + 152*x**6 + 112*x**5 + 36*x**4 + 4*x**3) + (24*x**4 + 16*x**3 + 3*x**2 - 6*x - 1)*Dx + (6*x**5 + 5*x**4 + x**3 + 3*x**2 + x)*Dx**2, x)');
  });
  it('comp4', () => {
    expect(fmt(new HF(L([1, 0, 1]), x).composition(P('1-x**2')))).toBe('HolonomicFunction((4*x**3) + (-1)*Dx + (x)*Dx**2, x)');
  });
  it('comp5', () => {
    expect(fmt(new HF(L([1, 0, 1]), x).composition(P('x - 2/(x**2 + 1)')))).toBe('HolonomicFunction((x**12 + 6*x**10 + 12*x**9 + 15*x**8 + 48*x**7 + 68*x**6 + 72*x**5 + 111*x**4 + 112*x**3 + 54*x**2 + 12*x + 1) + (12*x**8 + 32*x**6 + 24*x**4 - 4)*Dx + (x**12 + 6*x**10 + 4*x**9 + 15*x**8 + 16*x**7 + 20*x**6 + 24*x**5 + 15*x**4 + 16*x**3 + 6*x**2 + 4*x + 1)*Dx**2, x)');
  });
  it('fh1', () => {
    expect(fmt(fromHyper(hyper([1, 1], [P('3/2')], P('x**2/4'))))).toBe('HolonomicFunction((4*x) + (5*x**2 - 8)*Dx + (x**3 - 4*x)*Dx**2, x, 1, [2*sqrt(3)*pi/9, -4*sqrt(3)*pi/27 + 4/3])');
  });
  it('fh2', () => {
    expect(fmt(fromHyper(hyper([1], [P('3/2')], P('x**2/4'))))).toBe('HolonomicFunction((-x) + (2 - x**2/2)*Dx + (x)*Dx**2, x, 1, [sqrt(pi)*exp(1/4)*erf(1/2), -sqrt(pi)*exp(1/4)*erf(1/2)/2 + 1])');
  });
  it('fh3', () => {
    expect(fmt(fromHyper(hyper([], [P('3/2')], P('x**2/4'))))).toBe('HolonomicFunction((-x) + (2)*Dx + (x)*Dx**2, x, 1, [sinh(1), -sinh(1) + cosh(1)])');
  });
  it('fm1', () => {
    expect(fmt(fromMeijerg(meijerg([], [P('3/2')], [P('1/2')], [P('1/2'), 1], x)))).toBe('HolonomicFunction((x/2 - 1/4) + (-x**2 + x/4)*Dx + (x**2)*Dx**2 + (x**3)*Dx**3, x, 1, [1/sqrt(pi), 1/(2*sqrt(pi)), -1/(4*sqrt(pi))])');
  });
  it('fm2', () => {
    expect(fmt(fromMeijerg(meijerg([], [], [0], [], x)))).toBe('HolonomicFunction((1) + (1)*Dx, x, 0, [1])');
  });
  it('fm3', () => {
    expect(fmt(fromMeijerg(meijerg([1], [], [P('1/2')], [0], x)))).toBe('HolonomicFunction((x + 1/2)*Dx + (x)*Dx**2, x, 1, [sqrt(pi)*erf(1), exp(-1)])');
  });
  it('fm4', () => {
    expect(fmt(fromMeijerg(meijerg([0], [1], [0], [], P('2*x**2'))))).toBe('HolonomicFunction((3*x**2 - 1)*Dx + (x**3)*Dx**2, x, 1, [1 - exp(-1/2), -exp(-1/2)])');
  });
  it('fm5', () => {
    expect(fmt(fromMeijerg(meijerg([], [], [P('1/2')], [0], P('x**2/4'))))).toBe('HolonomicFunction((1) + (1)*Dx**2, x, 0, [0, 1/sqrt(pi)])');
  });
  it('seq1', () => {
    expect(fmt(new HF(L(['x', 1, 0, 0, 'x**2']), x).toSequence())).toBe('[(HolonomicSequence((1) + (n + 2)Sn**2 + (n**4 + 6*n**3 + 11*n**2 + 6*n)Sn**3, n), u(0) = C_0, u(1) = 0, u(2) = C_2, u(3) = C_3, 0, 1)]');
  });
  it('seq2', () => {
    expect(fmt(new HF(L(['x**3', 0, 1, 0, 'x**2']), x).toSequence())).toBe('[(HolonomicSequence((1) + (n**4 + 14*n**3 + 72*n**2 + 163*n + 140)Sn**5, n), u(0) = C_0, u(1) = C_1, u(2) = 0, u(3) = 0, u(4) = 0, 0, 0)]');
  });
  it('seq3', () => {
    expect(fmt(new HF(L([1, 0, 1, 0, 'x**3']), x).toSequence())).toBe('[(HolonomicSequence((1) + (n**4 - 2*n**3 - n**2 + 2*n)Sn + (n**2 + 3*n + 2)Sn**2, n), u(0) = C_0, u(1) = C_1, 0, 0)]');
  });
  it('seq4', () => {
    expect(fmt(new HF(L([0, '2*x', 0, 'x', '3*x**3']), x).toSequence())).toBe('[(HolonomicSequence((2*n) + (3*n**4 - 6*n**3 - 3*n**2 + 6*n)Sn + (n**3 + 3*n**2 + 2*n)Sn**2, n), u(0) = C_0, u(1) = C_1, u(2) = C_2, 0, 1)]');
  });
  it('seqi1', () => {
    expect(fmt(new HF(LQ([-1, 1]), x, 0, [1]).toSequence())).toBe('[(HolonomicSequence((-1) + (n + 1)Sn, n), u(0) = 1, 0)]');
  });
  it('seqi2', () => {
    expect(fmt(new HF(LQ([1, 0, 1]), x, 0, [0, 1]).toSequence())).toBe('[(HolonomicSequence((1) + (n**2 + 3*n + 2)Sn**2, n), u(0) = 0, u(1) = 1, 0)]');
  });
  it('seqi3', () => {
    expect(fmt(new HF(LQ([1, 'x**3', 1]), x, 0, [2, 3]).toSequence())).toBe('[(HolonomicSequence((n) + (1)Sn**2 + (n**2 + 7*n + 12)Sn**4, n), u(0) = 2, u(1) = 3, u(2) = -1, u(3) = -1/2, u(4) = 1/12, 1)]');
  });
  it('seqi4', () => {
    expect(fmt(new HF(LQ([1, 1, 0, 0, 0, 'x**3']), x).toSequence())).toBe('[(HolonomicSequence((1) + (n + 1)Sn + (n**5 - 5*n**3 + 4*n)Sn**2, n), u(0) = C_0, u(1) = C_1, u(2) = C_2, u(3) = C_3, u(4) = C_4, 0, 3)]');
  });
  it('seqi5', () => {
    expect(fmt(e2h(P('log(1+x**2)')).toSequence())).toBe('[(HolonomicSequence((n**2) + (n**2 + 2*n)Sn**2, n), u(0) = 0, u(1) = 0, u(2) = C_2, 0, 1)]');
  });
  it('seqi6', () => {
    expect(fmt((e2h(P('log(1+x**2)')).diff() as HF).toSequence())).toBe('[(HolonomicSequence((n + 2) + (n + 2)Sn**2, n), u(0) = C_0, u(1) = 0, 1, 0)]');
  });
  it('seqi7', () => {
    expect(fmt(e2h(P('erf(x) + x')).toSequence())).toBe('[(HolonomicSequence((2*n**2 - 2*n) + (n**3 + 2*n**2 - n - 2)Sn**2, n), u(0) = 0, u(1) = 1 + 2/sqrt(pi), u(2) = 0, u(3) = C_3, 0, 2)]');
  });
  it('ser1', () => {
    expect(fmt(new HF(L([0, '2*x', 1]), x, 0, [0, 1]).series(10))).toBe('x - x**3/3 + x**5/10 - x**7/42 + x**9/216 + O(x**10)');
  });
  it('ser2', () => {
    expect(fmt(pp().mul(qq()).series(10))).toBe('1 + x**2/2 + x**4/24 - 31*x**6/720 - 179*x**8/8064 + O(x**10)');
  });
  it('ser3', () => {
    expect(fmt(pp().mul(new HF(L([0, 1, '1+x']), x, 0, [0, 1])).add(qq()).series(10))).toBe('1 + x - x**2 + 4*x**3/3 - 17*x**4/24 + 31*x**5/30 - 481*x**6/720 + 71*x**7/105 - 20159*x**8/40320 + 379*x**9/840 + O(x**10)');
  });
  it('ser4', () => {
    expect(fmt(new HF(L(['6+6*x-3*x**2', '-(10*x-3*x**2-3*x**3)', '4-6*x**3+2*x**4']), x, 0, [0, 1]).series(7))).toBe('x + x**3/6 - 3*x**4/16 + x**5/20 - 23*x**6/960 + O(x**7)');
  });
  it('ser5', () => {
    expect(fmt(new HF(L(['6+6*x-3*x**2', '-(10*x-3*x**2-3*x**3)', '4-6*x**3+2*x**4']), x, 0, [1, 0]).series(7))).toBe('1 - 3*x**2/4 - x**3/4 - 5*x**4/32 - 3*x**5/40 - 17*x**6/384 + O(x**7)');
  });
  it('ser6', () => {
    expect(fmt(e2h(P('erf(x) + x')).series(10))).toBe('x*(1 + 2/sqrt(pi)) + C_3*x**3 - 3*C_3*x**5/10 + C_3*x**7/14 - C_3*x**9/72 + O(x**10)');
  });
  it('ser7', () => {
    expect(fmt(e2h(P('sqrt(x**3 + x)')).series(10))).toBe('sqrt(x) + x**(5/2)/2 - x**(9/2)/8 + x**(13/2)/16 - 5*x**(17/2)/128 + O(x**10)');
  });
  it('ser8', () => {
    expect(fmt(e2h(P('(2*x - 3*x**2)**(1/3)')).series())).toBe('2**(1/3)*x**(1/3) - 2**(1/3)*x**(4/3)/2 - 2**(1/3)*x**(7/3)/4 - 5*2**(1/3)*x**(10/3)/24 - 5*2**(1/3)*x**(13/3)/24 - 11*2**(1/3)*x**(16/3)/48 + O(x**6)');
  });
  it('ser9', () => {
    expect(fmt(e2h(P('sqrt(x**2-x)')).series())).toBe('I*sqrt(x) - I*x**(3/2)/2 - I*x**(5/2)/8 - I*x**(7/2)/16 - 5*I*x**(9/2)/128 - 7*I*x**(11/2)/256 + O(x**6)');
  });
  it('ser10', () => {
    expect(fmt(e2h(P('cos(x)**2/x**2'), { y0: new Map([[-2, [1, 0, -1]]]) }).series(10))).toBe('x**(-2) - 1 + x**2/3 - 2*x**4/45 + x**6/315 - 2*x**8/14175 + O(x**10)');
  });
  it('ser11', () => {
    expect(fmt(e2h(P('cos(x)**2/x**2'), { x0: 1 }).series(10))).toBe('cos(1)**2 + (x - 1)*(-2*sin(1)*cos(1) - 2*cos(1)**2) + (x - 1)**2*(2*cos(1)**2 + sin(1)**2 + 4*sin(1)*cos(1)) + (x - 1)**3*(-14*sin(1)*cos(1)/3 - 2*sin(1)**2 - 2*cos(1)**2) + (x - 1)**4*(7*cos(1)**2/3 + 8*sin(1)**2/3 + 16*sin(1)*cos(1)/3) + (x - 1)**5*(-94*sin(1)*cos(1)/15 - 10*sin(1)**2/3 - 8*cos(1)**2/3) + (x - 1)**6*(133*cos(1)**2/45 + 182*sin(1)**2/45 + 36*sin(1)*cos(1)/5) + (x - 1)**7*(-2554*sin(1)*cos(1)/315 - 214*sin(1)**2/45 - 146*cos(1)**2/45) + (x - 1)**8*(1114*cos(1)**2/315 + 1721*sin(1)**2/315 + 568*sin(1)*cos(1)/63) + (x - 1)**9*(-28138*sin(1)*cos(1)/2835 - 216*sin(1)**2/35 - 134*cos(1)**2/35) + O((x - 1)**10, (x, 1))');
  });
  it('ser12', () => {
    expect(fmt(e2h(P('cos(x-1)**2/(x-1)**2'), { x0: 1, y0: new Map([[-2, [1, 0, -1]]]) }).series(10))).toBe('(x - 1)**(-2) - 1 + (x - 1)**2/3 - 2*(x - 1)**4/45 + (x - 1)**6/315 - 2*(x - 1)**8/14175 + O((x - 1)**10, (x, 1))');
  });
  it('e2h1', () => {
    expect(fmt(e2h(P('(sin(x)/x)**2')))).toBe('HolonomicFunction((8*x) + (4*x**2 + 6)*Dx + (6*x)*Dx**2 + (x**2)*Dx**3, x, 0, [1, 0, -2/3])');
  });
  it('e2h2', () => {
    expect(fmt(e2h(P('1/(1+x**2)**2')))).toBe('HolonomicFunction((4*x) + (x**2 + 1)*Dx, x, 0, [1])');
  });
  it('e2h3', () => {
    expect(fmt(e2h(P('exp(x)*sin(x)+x*log(1+x)')))).toBe('HolonomicFunction((2*x**3 + 10*x**2 + 20*x + 18) + (-2*x**4 - 10*x**3 - 20*x**2 - 18*x)*Dx + (2*x**5 + 6*x**4 + 7*x**3 + 8*x**2 + 10*x - 4)*Dx**2 + (-2*x**5 - 5*x**4 - 2*x**3 + 2*x**2 - x + 4)*Dx**3 + (x**5 + 2*x**4 - x**3 - 7*x**2/2 + x + 5/2)*Dx**4, x, 0, [0, 1, 4, -1])');
  });
  it('e2h4', () => {
    expect(fmt(e2h(P('x*exp(x)+cos(x)+1')))).toBe('HolonomicFunction((-x - 3)*Dx + (x + 2)*Dx**2 + (-x - 3)*Dx**3 + (x + 2)*Dx**4, x, 0, [2, 1, 1, 3])');
  });
  it('e2h4s', () => {
    expect(fmt(e2h(P('x*exp(x)+cos(x)+1')).series(10))).toBe('2 + x + x**2/2 + x**3/2 + 5*x**4/24 + x**5/24 + x**6/144 + x**7/720 + x**8/4480 + x**9/40320 + O(x**10)');
  });
  it('e2h5', () => {
    expect(fmt(e2h(P('log(1 + x)**2 + 1')))).toBe('HolonomicFunction((1)*Dx + (3*x + 3)*Dx**2 + (x**2 + 2*x + 1)*Dx**3, x, 0, [1, 0, 2])');
  });
  it('e2h6', () => {
    expect(fmt(e2h(P('erf(x)**2 + x')))).toBe('HolonomicFunction((8*x**4 - 2*x**2 + 2)*Dx**2 + (6*x**3 - x/2)*Dx**3 + (x**2 + 1/4)*Dx**4, x, 0, [0, 1, 8/pi, 0])');
  });
  it('e2h7', () => {
    expect(fmt(e2h(P('cosh(x)*x')))).toBe('HolonomicFunction((2 - x**2) + (-2*x)*Dx + (x**2)*Dx**2, x, 0, [0, 1])');
  });
  it('e2h8', () => {
    expect(fmt(e2h(P('besselj(2, x)')))).toBe('HolonomicFunction((x**2 - 4) + (x)*Dx + (x**2)*Dx**2, x, 0, [0, 0])');
  });
  it('e2h9', () => {
    expect(fmt(e2h(P('besselj(0, x) + exp(x)')))).toBe('HolonomicFunction((-x**2 - x/2 + 1/2) + (x**2 - x/2 - 3/2)*Dx + (-x**2 + x/2 + 1)*Dx**2 + (x**2 + x/2)*Dx**3, x, 0, [2, 1, 1/2])');
  });
  it('e2h10', () => {
    expect(fmt(e2h(P('sin(x)**2/x')))).toBe('HolonomicFunction((4) + (4*x)*Dx + (3)*Dx**2 + (x)*Dx**3, x, 0, [0, 1, 0])');
  });
  it('e2h11', () => {
    expect(fmt(e2h(P('sin(x)**2/x'), { x0: 2 }))).toBe('HolonomicFunction((4) + (4*x)*Dx + (3)*Dx**2 + (x)*Dx**3, x, 2, [sin(2)**2/2, sin(2)*cos(2) - sin(2)**2/4, -3*sin(2)**2/4 + cos(2)**2 - sin(2)*cos(2)])');
  });
  it('e2h13', () => {
    expect(fmt(e2h(P('x**(1/2)'), { x0: 1 }))).toBe('HolonomicFunction((-1/2) + (x)*Dx, x, 1, [1])');
  });
  it('e2h14', () => {
    expect(fmt(e2h(P('sqrt(1 + x**2)')))).toBe('HolonomicFunction((-x) + (x**2 + 1)*Dx, x, 0, [1])');
  });
  it('e2h15', () => {
    expect(fmt(e2h(P('sqrt(x) + sqrt(2*x)')).toExpr())).toBe('sqrt(x)*(1 + sqrt(2))');
  });
  it('e2h16', () => {
    expect(fmt(e2h(P('3*x+2*sqrt(x)')).toExpr())).toBe('2*sqrt(x) + 3*x');
  });
  it('e2h17', () => {
    expect(fmt(e2h(P('(x**4+x**3+5*x**2+3*x+2)/x**2'), { lenics: 3 }))).toBe('HolonomicFunction((-2*x**4 - x**3 + 3*x + 4) + (x**5 + x**4 + 5*x**3 + 3*x**2 + 2*x)*Dx, x, 0, {-2: [2, 3, 5]})');
  });
  it('e2h18', () => {
    expect(fmt(e2h(P('1/(x-1)**2'), { lenics: 3, x0: 1 }))).toBe('HolonomicFunction((2) + (x - 1)*Dx, x, 1, {-2: [1, 0, 0]})');
  });
  it('e2h19', () => {
    expect(fmt(e2h(P('sqrt(a*x)'), { x }).toExpr())).toBe('sqrt(a)*sqrt(x)');
  });
  it('th1', () => {
    expect(fmt(new HF(LQ([-2, 1]), x, 0, [3]).toHyper())).toBe('3*hyper((), (), 2*x)');
  });
  it('th2', () => {
    expect(fmt(expand(hyperexpand(new HF(LQ([-3, '1+x']), x, 0, [2]).toHyper())))).toBe('2*x**3 + 6*x**2 + 6*x + 2');
  });
  it('th3', () => {
    expect(fmt(new HF(LQ([0, 1, '1+x']), x, 0, [0, 1]).toHyper())).toBe('-x**2*hyper((1, 2), (3,), -x)/2 + x');
  });
  it('th4', () => {
    expect(fmt(new HF(LQ([0, '2*x', 1]), x, 0, [0, P('2/sqrt(pi)')]).toHyper())).toBe('2*x*hyper((1/2,), (3/2,), -x**2)/sqrt(pi)');
  });
  it('th5', () => {
    expect(fmt(hyperexpand(new HF(LQ([0, '2*x', 1]), x, 0, [1, P('-2/sqrt(pi)')]).toHyper()))).toBe('1 - erf(x)');
  });
  it('th6', () => {
    expect(fmt(hyperexpand(new HF(LQ(['x**2-1', 'x', 'x**2']), x, 0, [0, P('1/2')]).toHyper()))).toBe('besselj(1, x)');
  });
  it('th7', () => {
    expect(fmt(hyperexpand(new HF(LQ(['x', 1, 'x']), x, 0, [1, 0]).toHyper()))).toBe('besselj(0, x)');
  });
  it('te1', () => {
    expect(fmt(new HF(L([-1, 0, 1]), x, 0, [1, 0]).toExpr())).toBe('cosh(x)');
  });
  it('te2', () => {
    expect(fmt(expand(new HF(L([2, '4*x-1', 'x**2-x']), x, 0, [1, 2]).toExpr()))).toBe('1/(x**2 - 2*x + 1)');
  });
  it('te3', () => {
    // SymPy: log(x)/2 - Ci(2*x)/2 + EulerGamma/2 + log(2)/2
    expectSame((e2h(P('sin(x)**2/x')).integrate([x, 0, x]) as HF).toExpr(), P('log(x)/2 - Ci(2*x)/2 + EulerGamma/2 + log(2)/2'));
  });
  it('te4', () => {
    expect(fmt(e2h(P('log(1+x**2)')).toExpr())).toBe('C_2*log(x**2 + 1)');
  });
  it('te5', () => {
    expect(fmt((e2h(P('log(1+x**2)')).diff() as HF).toExpr())).toBe('C_0*x/(x**2 + 1)');
  });
  it('te6', () => {
    expect(fmt(e2h(P('erf(x) + x')).toExpr())).toBe('3*C_3*x - 3*sqrt(pi)*C_3*erf(x)/2 + x + 2*x/sqrt(pi)');
  });
  it('te7', () => {
    // SymPy: sqrt(x)
    expectSame(e2h(P('sqrt(x)'), { x0: 1 }).toExpr(), P('sqrt(x)'));
  });
  it('te8', () => {
    expect(fmt(e2h(P('sqrt(x)')).toExpr())).toBe('sqrt(x)');
  });
  it('te9', () => {
    expect(fmt(e2h(P('sqrt(1 + x**2)')).toExpr())).toBe('sqrt(x**2 + 1)');
  });
  it('te10', () => {
    expect(fmt(e2h(P('(2*x**2 + 1)**(2/3)')).toExpr())).toBe('(2*x**2 + 1)**(2/3)');
  });
  it('te11', () => {
    // SymPy: sqrt(x)*sqrt(2 - x)
    expectSame(e2h(P('sqrt(-x**2+2*x)')).toExpr(), P('sqrt(x)*sqrt(2 - x)'));
  });
  it('te12', () => {
    // SymPy: x**(2/3)*(7 - 2*x**2)**(2/3)
    expectSame(e2h(P('(-2*x**3+7*x)**(2/3)')).toExpr(), P('x**(2/3)*(7 - 2*x**2)**(2/3)'));
  });
  it('te13', () => {
    expect(fmt(fromHyper(hyper([-2, -3], [P('1/2')], x)))).toBe('HolonomicFunction((6) + (-4*x - 1/2)*Dx + (x**2 - x)*Dx**2, x, 0, [1, 12])');
  });
  it('te13e', () => {
    // SymPy: (C_0*sqrt(1 - x)*(8*x**2 + 12*x + 1) - D_0*(sqrt(x)*(8*x**3 + 186*x**2 - 81*x - 113) - 15*sqrt(1 - x)*(8*x**2 + 12*x + 1)*asin(sqrt(x)))/128)/sqrt(1 - x)
    expectSame(fromHyper(hyper([-2, -3], [P('1/2')], x)).toExpr(), P('(C_0*sqrt(1 - x)*(8*x**2 + 12*x + 1) - D_0*(sqrt(x)*(8*x**3 + 186*x**2 - 81*x - 113) - 15*sqrt(1 - x)*(8*x**2 + 12*x + 1)*asin(sqrt(x)))/128)/sqrt(1 - x)'));
  });
  it('te14', () => {
    expect(fmt(e2h(P('x**5')).toExpr())).toBe('x**5');
  });
  it('te15', () => {
    expect(fmt(expand(e2h(P('2*x**3-3*x**2')).toExpr()))).toBe('2*x**3 - 3*x**2');
  });
  it('te16', () => {
    expect(fmt(e2h(P('1.4*x')).mul(e2h(P('a*x'), { x })).toExpr())).toBe('1.4*a*x**2');
  });
  it('te17', () => {
    expect(fmt(e2h(P('1.4*x')).add(e2h(P('a*x'), { x })).toExpr())).toBe('x*(a + 1.4)');
  });
  it('te18', () => {
    expect(fmt(e2h(P('1.4*x')).add(e2h(x)).toExpr())).toBe('2.4*x');
  });
  it('int1', () => {
    expect(fmt(e2h(P('sin(x)**2/x'), { x0: 1 }).integrate([x, 2, 3]))).toBe('0.166270406994788');
  });
  it('int2', () => {
    expect(fmt((e2h(P('sin(x)')).integrate([x, 0, x]) as HF).toExpr())).toBe('1 - cos(x)');
  });
  it('int3', () => {
    expect(fmt(e2h(P('sin(x)')).integrate([x, 0, 3]))).toBe('1 - cos(3)');
  });
  it('int4', () => {
    expect(fmt(e2h(P('sin(x)/x'), { x0: 1 }).integrate([x, 1, 2]))).toBe('0.659329913368450');
  });
  it('int5', () => {
    expect(fmt(e2h(P('sin(x)**2/x'), { x0: 1 }).integrate([x, 1, 0]))).toBe('-0.423690480850035');
  });
  it('int6', () => {
    expect(fmt((e2h(P('sin(x)/x')).integrate(x) as HF).toExpr())).toBe('Si(x)');
  });
  it('int7', () => {
    expect(fmt(e2h(P('sin(x)/x')).integrate([x, 0, 2]))).toBe('Si(2)');
  });
  it('int8', () => {
    // SymPy: log(x)/2 - Ci(2*x)/2 + EulerGamma/2 + log(2)/2
    expectSame((e2h(P('sin(x)**2/x')).integrate(x) as HF).toExpr(), P('log(x)/2 - Ci(2*x)/2 + EulerGamma/2 + log(2)/2'));
  });
  it('int9', () => {
    // SymPy: -Ci(2)/2 + EulerGamma/2 + log(2)/2
    expectSame(e2h(P('sin(x)**2/x')).integrate([x, 0, 1]), P('-Ci(2)/2 + EulerGamma/2 + log(2)/2'));
  });
  it('int10', () => {
    // SymPy: log(x)
    expectSame((e2h(P('1/x'), { x0: 1 }).integrate(x) as HF).toExpr(), P('log(x)'));
  });
  it('int11', () => {
    // SymPy: (-x**3 - 6*x**2 - 15*x + 6*exp(x + 1) - 16)*exp(-x)
    expectSame((e2h(P('(x + 1)**3*exp(-x)'), { x0: -1 }).integrate(x) as HF).toExpr(), P('(-x**3 - 6*x**2 - 15*x + 6*exp(x + 1) - 16)*exp(-x)'));
  });
  it('int12', () => {
    // SymPy: -Si(2*x) - cos(x)**2/x
    expectSame((e2h(P('cos(x)**2/x**2'), { y0: new Map([[-2, [1, 0, -1]]]) }).integrate(x) as HF).toExpr(), P('-Si(2*x) - cos(x)**2/x'));
  });
  it('int13', () => {
    // SymPy: (x**(3/2)*(2*x**2 + 3*x + 1) - x*sqrt(x + 1)*asinh(sqrt(x)))/(4*x*sqrt(x + 1))
    expectSame((e2h(P('sqrt(x**2+x)')).integrate(x) as HF).toExpr(), P('(x**(3/2)*(2*x**2 + 3*x + 1) - x*sqrt(x + 1)*asinh(sqrt(x)))/(4*x*sqrt(x + 1))'));
  });
  it('int14', () => {
    // SymPy: (x**3 + x + sqrt(x**2 + 1)*asinh(x))/(2*sqrt(x**2 + 1))
    expectSame((e2h(P('sqrt(x**2+1)')).integrate(x) as HF).toExpr(), P('(x**3 + x + sqrt(x**2 + 1)*asinh(x))/(2*sqrt(x**2 + 1))'));
  });
  it('int15', () => {
    expect(fmt(e2h(P('1/x**2'), { y0: new Map([[-2, [1, 0, 0]]]) }))).toBe('HolonomicFunction((2) + (x)*Dx, x, 0, {-2: [1, 0, 0]})');
  });
  it('int16', () => {
    expect(fmt(e2h(P('1/x**2'), { lenics: 3 }))).toBe('HolonomicFunction((2) + (x)*Dx, x, 0, {-2: [1, 0, 0]})');
  });
  it('int17', () => {
    // SymPy: -Si(2*x) - cos(x)**2/x
    expectSame((e2h(P('1/x**2'), { lenics: 3 }).mul(e2h(P('cos(x)**2'))).integrate(x) as HF).toExpr(), P('-Si(2*x) - cos(x)**2/x'));
  });
  it('d1', () => {
    expect(fmt((new HF(L([1, 0, 'x']), x, 0, [0, 1]).diff() as HF).toExpr())).toBe('besselj(0, 2*sqrt(x))');
  });
  it('d2', () => {
    expect(fmt((new HF(L([-1, 0, 1]), x, 0, [1, 0]).diff(x, 2) as HF).toExpr())).toBe('cosh(x)');
  });
  it('d3', () => {
    expect(fmt((e2h(P('Si(x)')).diff() as HF).toExpr())).toBe('sin(x)/x');
  });
  it('d4', () => {
    expect(fmt(e2h(P('Si(x)')).diff(new Sym('y')))).toBe('0');
  });
  it('d5', () => {
    expect(fmt((e2h(P('Si(x)')).diff(x, 2) as HF).toExpr())).toBe('3*C_0*(-x*cos(x) + sin(x))/x**2');
  });
  it('d6', () => {
    expect(fmt((e2h(P('Si(x)')).diff(x, 3) as HF).series())).toBe('C_3 - 3*C_3*x**2/10 + C_3*x**4/56 + C_0/x**3 + C_0*x/8 - C_0*x**3/72 + C_0*x**5/1920 + O(x**6)');
  });
  it('ext1', () => {
    expect(fmt(e2h(P('1.2*cos(3.1*x)')).toExpr())).toBe('1.2*cos(3.1*x)');
  });
  it('ext2', () => {
    expect(fmt((e2h(P('1.2*cos(3.1*x)')).integrate(x) as HF).toExpr())).toBe('0.387096774193548*sin(3.1*x)');
  });
  it('ext3', () => {
    expect(fmt(e2h(P('1.1329138213*x')))).toBe('HolonomicFunction((-1.13291382130000) + (1.1329138213*x)*Dx, x, 0, {1: [1.1329138213]})');
  });
  it('ext4', () => {
    expect(fmt(e2h(P('1.1329138213*x')).integrate([x, 1, 2]))).toBe('1.69937073195000');
  });
  it('ext5', () => {
    expect(fmt(e2h(P('sin(x*y*z)'), { x }).toExpr())).toBe('sin(x*y*z)');
  });
  it('ext6', () => {
    expect(fmt((e2h(P('sin(x*y*z)'), { x }).integrate(x) as HF).toExpr())).toBe('(1 - cos(x*y*z))/(y*z)');
  });
  it('ext7', () => {
    expect(fmt((e2h(P('sin(x*y + z)'), { x }).integrate(x) as HF).toExpr())).toBe('(cos(z) - cos(x*y + z))/y');
  });
  it('ext8', () => {
    expect(fmt((e2h(P('a*x'), { x }).integrate(x) as HF).toExpr())).toBe('a*x**2/2');
  });
  it('ext9', () => {
    // SymPy: 6.0*D_2*(x - sin(1.0*x)) + x + 1.2*cos(1.0*x)
    expectSame(e2h(x).add(e2h(P('1.2*cos(x)'))).toExpr(), P('6.0*D_2*(x - sin(1.0*x)) + x + 1.2*cos(1.0*x)'));
  });
  it('ext10', () => {
    expect(fmt(e2h(x).mul(e2h(P('1.2*cos(x)'))).toExpr())).toBe('x*(1.0*C_1*sin(1.0*x) + 1.2*cos(1.0*x))');
  });
  it('tm1', () => {
    expect(fmt(e2h(P('sin(x)')).toMeijerg())).toBe('sqrt(pi)*x*meijerg(((), ()), ((0,), (-1/2,)), x**2/4)/2');
  });
  it('tm2', () => {
    expect(fmt(simplify(hyperexpand(e2h(P('log(x)')).toMeijerg())))).toBe('log(x)');
  });
  it('tm3', () => {
    expect(fmt(e2h(P('4*x**2/3 + 7')).toMeijerg())).toBe('4*x**2/3 + 7');
  });
  it('tm4', () => {
    expect(fmt(hyperexpand(e2h(P('besselj(2, x)'), { lenics: 3 }).toMeijerg()))).toBe('besselj(2, x)');
  });
  it('tm5', () => {
    expect(fmt(fromHyper(hyper([P('-1/2'), -3], [], x)).toMeijerg())).toBe('3*x**3/8 - 3*x**2/4 + 3*x/2 + 1');
  });
  it('tm6', () => {
    expect(fmt(hyperexpand(fromHyper(hyper([1, 3], [2], x)).toMeijerg()))).toBe('(x - 2)/(2*(1 - x)*(x - 1))');
  });
  it('tm7', () => {
    expect(fmt(e2h(P('besselj(1/2, x)'), { initcond: false }).toExpr())).toBe('(C_0*cos(x) + C_1*sin(x) + D_0*sin(x))/sqrt(x)');
  });
  it('tm8', () => {
    expect(fmt(e2h(P('besselj(1/2, x)'), { y0: new Map([[P('-1/2'), [P('sqrt(2)/sqrt(pi)'), P('sqrt(2)/sqrt(pi)')]]]) }).toExpr())).toBe('2*sin(x + pi/4)/(sqrt(pi)*sqrt(x))');
  });
  it('gauss', () => {
    expect(fmt(e2h(P('sqrt(2)*exp(-(-mu + x)**2/(2*sd**2))/(2*sqrt(pi)*sd)').subs(new Sym('sd'), sd), { x, domain: QQ.polyRing(mu, sd).getField() }))).toBe('HolonomicFunction((-mu/sd**2 + x/sd**2) + (1)*Dx, x, 0, [sqrt(2)*exp(-mu**2/(2*sd**2))/(2*sqrt(pi)*sd)])');
  });
  it('beta', () => {
    expect(fmt(e2h(P('x**(a - 1)*(-x + 1)**(b - 1)/beta(a, b)').subs({ a: ap, b: bp, x: xp }), { x: xp, domain: QQ.polyRing(ap, bp).getField() }))).toBe('HolonomicFunction((a + x*(-a - b + 2) - 1) + (x**2 - x)*Dx, x, 0, {a - 1: [0**(1 - a)*0**(a - 1)/beta(a, b)]})');
  });
  it('gamma', () => {
    expect(fmt(e2h(P('b**(-a)*x**(a - 1)*exp(-x/b)/gamma(a)').subs({ a: ap, b: bp, x: xp }), { x: xp, domain: QQ.polyRing(ap, bp).getField() }))).toBe('HolonomicFunction((-a + 1 + x/b) + (x)*Dx, x, 0, {a - 1: [0**(1 - a)*0**(a - 1)/(b**a*gamma(a))]})');
  });
  it('spow', () => {
    expect(fmt(new HF(L([-1, 'x'], RN), x).pow(P('-n')))).toBe('HolonomicFunction((n) + (x)*Dx, x)');
  });
  it('npow', () => {
    expect(fmt(new HF(LQ([-1, 'x']), x).pow(-2))).toBe('HolonomicFunction((2) + (x)*Dx, x)');
  });
  it('epow', () => {
    expect(fmt(new HF(L([-1, 'x'], RN), x).pow(P('n - 3')))).toBe('HolonomicFunction((3 - n) + (x)*Dx, x)');
  });
  it('r1', () => {
    expect(fmt(Sn.mul(ni))).toBe('(n + 1)Sn');
  });
  it('r2', () => {
    expect(fmt(Sn.mul(P('n**2').subs(nn, ni)))).toBe('(n**2 + 2*n + 1)Sn');
  });
  it('r3', () => {
    expect(fmt(Sn.pow(2).mul(P('n**2').subs(nn, ni)))).toBe('(n**2 + 4*n + 4)Sn**2');
  });
  it('r4', () => {
    expect(fmt(Sn.pow(3).mul(P('n**2').subs(nn, ni)).add(Sn.mul(ni)).pow(2))).toBe('(n**2 + 3*n + 2)Sn**2 + (2*n**3 + 19*n**2 + 57*n + 52)Sn**4 + (n**4 + 18*n**3 + 117*n**2 + 324*n + 324)Sn**6');
  });
  it('r5', () => {
    expect(fmt(Sn.rmul(ni).mul(ni).add(1).sub(Sn.pow(2).mul(ni)))).toBe('(1) + (n**2 + n)Sn + (-n - 2)Sn**2');
  });
  it('r6', () => {
    expect(fmt(new RecurrenceOperator([0, 1, P('n**2').subs(nn, ni)], RR_))).toBe('(1)Sn + (n**2)Sn**2');
  });
});

// Values from SymPy 1.14.0 unless a comment says otherwise.
describe('the API beyond the SymPy test suite', () => {
  const half = Rational.of(1n, 2n);
  const e = (x0: number, y0: unknown[]) => new HF(LQ([-1, 1]), x, x0, y0 as never);
  const sq = () => new HF(LQ(['-1/2', 'x']), x, 0, new Map([[half, [1]]]));
  it('the Weyl algebra', () => {
    expect(String(R)).toBe('Univariate Differential Operator Algebra in intermediate Dx over the base ring ZZ[x]');
    const D = new Sym('D', { commutative: false });
    const [RD, DD] = DifferentialOperators(ZZ.oldPolyRing(x), D);
    expect(RD.genSymbol).toBe(D);
    expect(DD.pow(2).add(1).toString()).toBe('(1) + (1)*D**2');
    expect(DifferentialOperators(ZZ.oldPolyRing(x))[0].equals(R)).toBe(true);
    expect(RD.equals(R)).toBe(false);
    // a coefficient of another ring is converted
    expect(new DifferentialOperator([RQ.base.fromSympy(P('x/1'))], R).toString()).toBe('(x)');
    expect(new DifferentialOperator([QQ.oldPolyRing(x).fromSympy(P('2*x'))], R).toString()).toBe('(2*x)');
    expect(() => new DifferentialOperator([Dx], R)).toThrow(TypeError);
    expect(Dx.rsub(1).toString()).toBe('(1) + (-1)*Dx');
    expect(Dx.neg().toString()).toBe('(-1)*Dx');
    expect(RQ.derivativeOperator.div(2).toString()).toBe('(1/2)*Dx');
    expect(Dx.pow(1)).toBe(Dx);
    expect(Dx.pow(0).toString()).toBe('(1)');
    expect(Dx.sub(x).toString()).toBe('(-x) + (1)*Dx');
    expect(Dx.equals(R.derivativeOperator)).toBe(true);
    expect(L(['x**2', 0, 0]).equals(P('x**2'))).toBe(true);
    expect(L(['x**2', 1]).equals(R.base.fromSympy(P('x**2')))).toBe(false);
  });
  it('test_DifferentialOperator', () => {
    expect(Dx.equals(new DifferentialOperator([R.base.zero, R.base.one], R))).toBe(true);
    expect(Dx.rmul(x).add(Dx.pow(2).rmul(P('x**2'))).equals(L([0, 'x', 'x**2']))).toBe(true);
    expect(Dx.add(P('x**2 + 1')).add(Dx.pow(5).rmul(x)).equals(L(['x**2 + 1', 1, 0, 0, 0, 'x']))).toBe(true);
    const a = Dx.rmul(x).add(P('x**2 + 1')).sub(Dx.mul(P('x**3 + x'))).pow(3);
    expect(a.toString()).toBe('(-48*x**6) + (-57*x**7)*Dx + (-15*x**8)*Dx**2 + (-x**9)*Dx**3');
    const p = Dx.pow(2).rmul(x).add(Dx.pow(5).rmul(P('x**2 + 3'))).mul(Dx.add(P('x**2')));
    expect(p.toString()).toBe('(2*x) + (4*x**2)*Dx + (x**3)*Dx**2 + (20*x**2 + x + 60)*Dx**3 + (10*x**3 + 30*x)*Dx**4 + (x**4 + 3*x**2)*Dx**5 + (x**2 + 3)*Dx**6');
    // the doctests
    expect(Dx.mul(x).toString()).toBe('(1) + (x)*Dx');
    expect(Dx.rmul(x).mul(x).add(1).sub(Dx.pow(2)).pow(2).toString()).toBe('(2*x**2 + 2*x + 1) + (4*x**3 + 2*x**2 - 4)*Dx + (x**4 - 6*x - 2)*Dx**2 + (-2*x**2)*Dx**3 + (1)*Dx**4');
  });
  it('test_DifferentialOperatorEqPoly and Pow', () => {
    const xi = new Sym('x', { integer: true });
    const [Ri] = DifferentialOperators(QQ.oldPolyRing(xi), 'Dx');
    const xi2 = P('x**2').subs(x, xi);
    const d = new DifferentialOperator([xi2, Ri.base.zero, Ri.base.zero], Ri);
    const d2 = new DifferentialOperator([xi2, 1, xi], Ri);
    expect(d.equals(d2)).toBe(false);
    expect(d2.equals(d2.listofpoly[0] ?? 0)).toBe(false);
    let a = new DifferentialOperator([Ri.base.one], Ri);
    for (let k = 0; k < 10; k++) {
      expect(a.equals(d.pow(k))).toBe(true);
      a = a.mul(d);
    }
  });
  it('test_HolonomicFunction_power and equality', () => {
    const p = new HF(L(['x', 1, 'x']), x);
    let a = new HF(Dx, x);
    for (let k = 0; k < 6; k++) {
      expect(a.equals(p.pow(k))).toBe(true);
      a = a.mul(p);
    }
    expect(new HF(Dx.pow(2).mul(x), x).equals(new HF(L([0, 2, 'x']), x))).toBe(true);
    expect(e(0, [1]).equals(e(0, [2]))).toBe(false);
    expect(e(0, [1]).equals(e(1, [1]))).toBe(false);
    expect(e(0, [1]).equals(new HF(LQ([-1, 1]), new Sym('y')))).toBe(false);
    expect(e(0, [1]).equals(new HF(LQ([-2, 1]), x))).toBe(false);
    expect(sq().equals(e(0, [1]))).toBe(false);
    expect(sq().equals(new HF(LQ(['-1/2', 'x']), x, 0, new Map([[half, [2]]])))).toBe(false);
    expect(sq().equals(new HF(LQ(['-1/2', 'x']), x, 0, new Map([[1, [1]]])))).toBe(false);
    expect(sq().equals(new HF(LQ(['-1/2', 'x']), x, 0, new Map([[half, [1, 2]]])))).toBe(false);
    expect(sq().equals(new HF(LQ(['-1/2', 'x']), x, 0, new Map<Expr, number[]>([[half, [1]], [S.One, [1]]])))).toBe(false);
    expect(e(0, [1]).equals(e(0, [1, 1]))).toBe(false);
    expect(e(0, [1]).degree()).toBe(0);
    expect(sq().isSingularics()).toBe(true);
    expect(e(0, [1]).isSingularics()).toBe(false);
    expect(new HF(LQ([-1, 1]), x).isSingularics()).toBe('unknown');
    expect(new HF(LQ([-1, 1]), x, 0, []).haveInitCond()).toBe(false);
    expect(new HF(LQ([-1, 1]), x, 0, new Map()).haveInitCond()).toBe(false);
    expect(new HF(LQ(['-1/2', 'x']), x, 0, new Map<Expr, number[]>([[half, [1]], [P('3/2'), [1.5]]])).toString()).toBe('HolonomicFunction((-1/2) + (x)*Dx, x, 0, {1/2: [1], 3/2: [1.5]})');
  });
  it('powers', () => {
    expect(new HF(L([1, 0, 1]), x, 0, [0, 1]).pow(0).toString()).toBe('HolonomicFunction((1)*Dx, x, 0, [1])');
    // SymPy raises the exponent 1/2 itself to the power and gives [1/4]; the square of sqrt(x) is x
    expect(sq().pow(2).toString()).toBe('HolonomicFunction((-1) + (x)*Dx, x, 0, {1: [1]})');
    expect(new HF(LQ(['-1/2', 'x']), x).pow(3).toString()).toBe('HolonomicFunction((-3/2) + (x)*Dx, x)');
    expect(e(0, [1]).pow(2).toString()).toBe('HolonomicFunction((-2) + (1)*Dx, x, 0, [1])');
    expect(() => new HF(L([1, 0, 1]), x, 0, [0, 1]).pow(-1)).toThrow(NotHolonomicError);
    expect(() => new HF(L([1, 0, 1]), x, 0, [0, 1]).pow(half)).toThrow(NotImplementedError);
  });
  it('constant factors (SymPy fails with a PolynomialError for a function with initial conditions)', () => {
    expect(e(0, [1]).mul(2).toString()).toBe('HolonomicFunction((-1) + (1)*Dx, x, 0, [2])');
    expect(sq().mul(3).toString()).toBe('HolonomicFunction((-1/2) + (x)*Dx, x, 0, {1/2: [3]})');
    expect(new HF(LQ([-1, 1]), x).mul(3).toString()).toBe('HolonomicFunction((-1) + (1)*Dx, x)');
    expect(() => e(0, [1]).mul(x)).toThrow(NotImplementedError);
    expect(e(0, [1]).neg().toString()).toBe('HolonomicFunction((-1) + (1)*Dx, x, 0, [-1])');
    expect(e(0, [1]).div(2).toString()).toBe('HolonomicFunction((-1) + (1)*Dx, x, 0, [1/2])');
    expect(e(0, [1]).sub(e(0, [1])).toString()).toBe('HolonomicFunction((-1) + (1)*Dx, x, 0, [0])');
  });
  it('sums and products at different points', () => {
    expect(e(0, [1]).add(e(1, [E])).toString()).toBe('HolonomicFunction((-1) + (1)*Dx, x, 0, [2])');
    expect(e(1, [E]).add(e(0, [1])).toString()).toBe('HolonomicFunction((-1) + (1)*Dx, x, 0, [2])');
    const f = new HF(LQ([-2, 1]), x, 2, [P('exp(4)')]);
    expect(e(1, [E]).add(f).toString()).toBe('HolonomicFunction((2) + (-3)*Dx + (1)*Dx**2, x, 1, [E + exp(2), E + 2*exp(2)])');
    expect(e(0, [1]).mul(e(1, [E])).toString()).toBe('HolonomicFunction((-2) + (1)*Dx, x, 0, [1])');
    expect(e(1, [E]).mul(e(0, [1])).toString()).toBe('HolonomicFunction((-2) + (1)*Dx, x, 0, [1])');
    expect(e(1, [E]).mul(f).toString()).toBe('HolonomicFunction((-3) + (1)*Dx, x, 1, [exp(3)])');
    expect(sq().add(e(1, [E])).toString()).toBe('HolonomicFunction((x/2 + 1/4) + (-x**2 - 1/4)*Dx + (x**2 - x/2)*Dx**2, x)');
    expect(sq().mul(e(1, [E])).toString()).toBe('HolonomicFunction((-x - 1/2) + (x)*Dx, x)');
  });
  it('singular initial conditions', () => {
    const third = new HF(LQ(['-1/3', 'x']), x, 0, new Map([[Rational.of(1n, 3n), [2]]]));
    expect(sq().mul(third).toString()).toBe('HolonomicFunction((-5/6) + (x)*Dx, x, 0, {5/6: [2]})');
    expect(sq().add(new HF(LQ(['-1/2', 'x']), x, 0, new Map([[half, [3]]]))).toString()).toBe('HolonomicFunction((-1/2) + (x)*Dx, x, 0, {1/2: [4]})');
    expect(sq().add(e(0, [1])).toString()).toBe('HolonomicFunction((x/2 + 1/4) + (-x**2 - 1/4)*Dx + (x**2 - x/2)*Dx**2, x, 0, {0: [1], 1/2: [1]})');
    expect(e(0, [1]).mul(sq()).toString()).toBe('HolonomicFunction((-x - 1/2) + (x)*Dx, x, 0, {1/2: [1]})');
    // two pairs of exponents with the same sum
    const two = new HF(LQ(['-1/2', 'x']), x, 0, new Map([[half, [1]], [P('3/2'), [1]]]));
    expect(sstr(two.mul(two).y0 instanceof ExprMap ? (two.mul(two).y0 as ExprMap<Expr[]>).get(P('2'))?.[0] ?? S.Zero : S.Zero)).toBe('2');
  });
  it('integrals', () => {
    expect(new HF(LQ([-1, 1]), x).integrate(x).toString()).toBe('HolonomicFunction((-1)*Dx + (1)*Dx**2, x)');
    expect(new HF(LQ([-1, 1]), x).integrate(x, true).toString()).toBe('HolonomicFunction((-1)*Dx + (1)*Dx**2, x, 0, [0])');
    expect(sq().integrate(x).toString()).toBe('HolonomicFunction((-1/2)*Dx + (x)*Dx**2, x, 0, {3/2: [2/3]})');
    expect(() => new HF(LQ([1, 'x']), x, 0, new Map([[-1, [1]]])).integrate(x)).toThrow('logarithmic terms in the series are not supported');
    expect(() => sq().integrate([x, 0, 1])).toThrow('Definite integration for singular initial conditions');
    expect(new HF(LQ([-2, 'x']), x, 0, new Map([[2, [1]]])).integrate(x).toString()).toBe('HolonomicFunction((-2)*Dx + (x)*Dx**2, x, 0, [0, 0, 0, 2])');
    expect(new HF(LQ([-1, 'x']), x, 0, new Map([[1, [0, 1]]])).integrate(x).toString()).toBe('HolonomicFunction((-1)*Dx + (x)*Dx**2, x, 0, [0, 0, 0, 2])');
    // SymPy fails (UnboundLocalError) for limits in another variable
    expect(e(0, [1]).integrate([new Sym('a'), 0, 1]).toString()).toBe('HolonomicFunction((-1)*Dx + (1)*Dx**2, x, 0, [0, 1])');
    expect(e(0, [1]).integrate([x, 1, x]).toString()).toBe('HolonomicFunction((-1)*Dx + (1)*Dx**2, x, 0, [1 - E, 1])');
    expect(e(0, [1]).integrate([x, 0, new Sym('a')]).toString()).toBe('HolonomicFunction((-1)*Dx + (1)*Dx**2, x)');
    expect(e(0, [1]).integrate([x, 1, new Sym('a')]).toString()).toBe('HolonomicFunction((-1)*Dx + (1)*Dx**2, x)');
  });
  it('derivatives', () => {
    expect(sstr(new HF(LQ([0, 1]), x, 0, [3]).diff() as Expr)).toBe('0');
    expect(new HF(LQ([0, 0, 1]), x, 0, [1, 2]).diff().toString()).toBe('HolonomicFunction((1)*Dx, x, 0, [2])');
    expect(new HF(LQ([0, 0, 1]), x).diff().toString()).toBe('HolonomicFunction((1)*Dx, x)');
    expect(new HF(LQ([0, 0, 1]), x, 0, []).diff().toString()).toBe('HolonomicFunction((1)*Dx, x)');
    expect(new HF(LQ(['x', 0, 1]), x).diff().toString()).toBe('HolonomicFunction((x**2) + (-1)*Dx + (x)*Dx**2, x)');
    expect(new HF(LQ(['x', 0, 1]), x, 0, new Map([[0, [1]]])).diff().toString()).toBe('HolonomicFunction((x**2) + (-1)*Dx + (x)*Dx**2, x)');
    expect(sstr(new HF(LQ([0, 1]), x, 0, [3]).diff(x, 2) as Expr)).toBe('0');
  });
  it('recurrences and series', () => {
    // SymPy fails (TypeError) without initial conditions at an ordinary point
    expect(fmt(new HF(LQ([-1, 1]), x).toSequence())).toBe('[(HolonomicSequence((-1) + (n + 1)Sn, n), u(0) = C_0, 0)]');
    expect(fmt(e(0, [1]).toSequence(false))).toBe('[HolonomicSequence((-1) + (n + 1)Sn, n), u(0) = 1]');
    expect(fmt(sq().toSequence(false))).toBe('[(HolonomicSequence((n), n), u(0) = 1, 1/2)]');
    const ind = new HF(LQ([1, '-x', '6*x**2']), x);
    expect(fmt(ind.toSequence())).toBe('[(HolonomicSequence((6*n**2 - 5*n), n), u(0) = C_0, 1/6, 1), (HolonomicSequence((6*n**2 + 5*n), n), u(0) = D_0, 1, 1)]');
    expect(fmt(ind.series())).toBe('[C_0*x**(1/6) + O(x**6), D_0*x + O(x**6)]');
    expect(fmt(e(0, [1]).series(4, { coefficient: true }))).toBe('[1, 1, 1/2, 1/6]');
    expect(fmt(e(0, [1]).series(4, { order: false }))).toBe('x**3/6 + x**2/2 + x + 1');
    expect(fmt(new HF(LQ([-1, 1]), x, 0, new Map([[0, [1]]])).toSequence())).toBe('[(HolonomicSequence((-1) + (n + 1)Sn, n), u(0) = C_0, 0)]');
    const [RA] = DifferentialOperators(QQ.fracField(new Sym('a')).oldPolyRing(x), 'Dx');
    expect(fmt(new HF(L(['-a', 1], RA), x, 0, [1]).series(3))).toBe('1 + a*x + a**2*x**2/2 + O(x**3)');
  });
  it('to_hyper', () => {
    expect(fmt(new HF(L([1, 0, 1]), x, 0, [1]).toHyper())).toBe('C_1*x*hyper((), (3/2,), -x**2/4) + hyper((), (1/2,), -x**2/4)');
    expect(fmt(new HF(LQ([1, 'x', 1]), x, 0, [1, 1]).toHyper())).toBe('-x**2*hyper((1,), (2,), -x**2/2)/2 + x*hyper((1,), (3/2,), -x**2/2) + 1');
    expect(fmt(new HF(LQ(['-x', 0, 0, 1]), x, 0, [1, 0, 0]).toHyper())).toBe('hyper((), (1/2, 3/4), x**4/64)');
    expect(() => new HF(LQ([1, 1, 1]), x, 0, [1, 1]).toHyper()).toThrow(NotHyperSeriesError);
  });
  it('change_ics', () => {
    expect(e(0, [1, 1, 1]).changeIcs(1).toString()).toBe('HolonomicFunction((-1) + (1)*Dx, x, 1, [E, E, E])');
    // SymPy: HolonomicFunction((1) + (x)*Dx + (1)*Dx**2, x, 1, [(2 - sqrt(2)*I*sqrt(pi)*erf(sqrt(2)*I/2))*exp(-1/2)/2, ...]);
    // the expression here has coefficients outside QQ (CoercionFailed), which SymPy does not catch either
    expect(() => new HF(LQ([1, 'x', 1]), x, 0, [1, 1]).changeIcs(1)).toThrow(CoercionFailed);
    // the series is not hypergeometric: the values come from the numerical integration (as in SymPy)
    expect(new HF(LQ([1, 1, 1]), x, 0, [1, 1]).changeIcs(1).x0.toString()).toBe('1');
  });
  it('expr_to_holonomic options', () => {
    expect(() => e2h(P('x*a'))).toThrow('Specify the variable for the function');
    expect(e2h(P('sin(x)'), { y0: [0, 2] }).toString()).toBe('HolonomicFunction((1) + (1)*Dx**2, x, 0, [0, 2])');
    expect(e2h(P('sin(x)'), { initcond: false }).toString()).toBe('HolonomicFunction((1) + (1)*Dx**2, x)');
    expect(e2h(P('sin(x)*x'), { initcond: false }).toString()).toBe('HolonomicFunction((x**2 + 2) + (-2*x)*Dx + (x**2)*Dx**2, x)');
    expect(e2h(P('sin(x)*x'), { y0: [0, 0, 2] }).toString()).toBe('HolonomicFunction((x**2 + 2) + (-2*x)*Dx + (x**2)*Dx**2, x, 0, [0, 0, 2])');
    expect(() => e2h(P('Piecewise((x, x < 1), (1, True))'))).toThrow(NotImplementedError);
    expect(() => e2h(P('f(x)'))).toThrow(NotImplementedError);
    expect(() => e2h(hyper([1], [2], x))).toThrow(NotImplementedError);
    expect(e2h(P('x**1.5')).toString()).toBe('HolonomicFunction((-1.50000000000000) + (1.0*x)*Dx, x, 0, {3/2: [1.0]})');
    expect(e2h(P('sqrt(x)'), { lenics: 2 }).toString()).toBe('HolonomicFunction((-1/2) + (x)*Dx, x, 0, {1/2: [1, 0]})');
    expect(e2h(P('besselj(1, x)'), { y0: [0, half] }).toString()).toBe('HolonomicFunction((x**2 - 1) + (x)*Dx + (x**2)*Dx**2, x, 0, [0, 1/2])');
    expect(e2h(P('besselj(1, x)'), { initcond: false }).toString()).toBe('HolonomicFunction((x**2 - 1) + (x)*Dx + (x**2)*Dx**2, x)');
    expect(e2h(P('besselj(1, x)'), { x0: 1 }).toString()).toBe('HolonomicFunction((x**2 - 1) + (x)*Dx + (x**2)*Dx**2, x, 1, [besselj(1, 1), -besselj(2, 1)/2 + besselj(0, 1)/2])');
    expect(e2h(P('1/x**2 + x')).toString()).toBe('HolonomicFunction((2 - x**3) + (x**4 + x)*Dx, x, 0, {-2: [1]})');
    // SymPy: [-log(2)/2 - EulerGamma/2 + Ci(2)/2, 0, 1, 0]; the limit at 0 stays unevaluated here
    expect(e2h(P('log(x)/2 - Ci(2*x)/2 + Ci(2)/2')).toString()).toContain('Limit');
  });
  it('from_hyper and from_meijerg options', () => {
    expect(fromHyper(hyper([P('1/3')], [P('1/5')], x)).toString()).toBe('HolonomicFunction((-1/3) + (1/5 - x)*Dx + (x)*Dx**2, x, 1, [hyper((1/3,), (1/5,), 1), 5*hyper((4/3,), (6/5,), 1)/3])');
    // SymPy evaluates the values ([4.0262861201631, 4.95112526361392]); hyper at 1 has no numerical value here
    expect(fromHyper(hyper([P('1/3')], [P('1/5')], x), 0, true).toString()).toContain('hyper((0.333333333333333,), (0.2,), 1.0)');
    expect(fromMeijerg(meijerg([], [], [0], [], x), { initcond: false }).toString()).toBe('HolonomicFunction((1) + (1)*Dx, x)');
    // SymPy accepts the value zoo*hyper((13/15,), (37/35,), 0) at 0
    expect(fromMeijerg(meijerg([P('1/3')], [], [P('1/5')], [P('1/7')], x), { evalf: true }).x0.toString()).toBe('1');
    expect(() => fromHyper(x)).toThrow(TypeError);
    expect(() => fromMeijerg(x)).toThrow(TypeError);
  });
  it('unify, changeX and shiftX', () => {
    const p = e(0, [1]);
    expect(p.unify(p)).toEqual([p, p]);
    const [u, v] = new HF(L([-1, 1]), x, 0, [1]).unify(p);
    expect([String(u.annihilator.parent.base), String(v.annihilator.parent.base)]).toEqual(['QQ[x]', 'QQ[x]']);
    expect(new HF(L([-1, 1]), x, 0, [1]).add(p).toString()).toBe('HolonomicFunction((-1) + (1)*Dx, x, 0, [2])');
    expect(new HF(L([-1, 1]), x, 0, [1]).mul(p).toString()).toBe('HolonomicFunction((-2) + (1)*Dx, x, 0, [1])');
    const y = new Sym('y');
    expect(p.changeX(y).toString()).toBe('HolonomicFunction((-1) + (1)*Dx, y, 0, [1])');
    expect(new HF(LQ([-1, 'x']), x).shiftX(1).toString()).toBe('HolonomicFunction((-1) + (x + 1)*Dx, x)');
  });
  it('solveLinear (SymPy solve of the series conditions)', () => {
    expect(sstr(e2h(P('sin(x)**2/x'), { x0: 1 }).integrate([x, 0, 1]) as Expr)).toBe('0.423690480850035');
    expect(fmt(new HF(LQ(['3/4', '-x', 'x**2']), x).toSequence())).toBe('[(HolonomicSequence((n**2 - n), n), u(0) = C_0, u(1) = C_1, 1/2, 2), (HolonomicSequence((n**2 + n), n), u(0) = D_0, 3/2, 1)]');
    expect(fmt(new HF(LQ([2, '-2*x', 'x**2']), x, 0, new Map([[1, [1]]])).toHyper())).toBe('x*(C_1*x + 1)');
    expect(fmt(new HF(LQ(['-1/2', 'x']), x, 0, new Map([[new Float(0.5), [1]]])).toSequence())).toBe('[(HolonomicSequence((n), n), u(0) = 1, 0.500000000000000, 1)]');
    expect(fmt(new HF(LQ(['-1/2', 'x']), x, 0, new Map([[new Sym('a'), [1]]])).toSequence())).toBe('[]');
    // SymPy: HolonomicFunction((1) + (1)*Dx + (3*x)*Dx**2 + (x**2)*Dx**3, x, 1, [meijerg(((), ()), ((0, 0, 0), ()), 1), ...]);
    // the derivative of meijerg is not implemented here
    expect(() => fromMeijerg(meijerg([], [], [0, 0, 0], [], x))).toThrow(NotImplementedError);
    expect(e2h(P('besseli(0, x)')).toString()).toBe('HolonomicFunction((-1) + (-x)*Dx + (2)*Dx**2 + (x)*Dx**3, x, 0, [1, 0, 1/2])');
    expect(new HF(LQ([1, 0, 1]), x, 0, [0, 1]).evalf([new Float(0.5), 1], { derivatives: true }).map((r) => r.map((v) => sstr(v)))).toEqual([
      ['0.479166666666667', '0.877604166666667'],
      ['0.841037326388889', '0.540588378906250'],
    ]);
    const [RA] = DifferentialOperators(QQ.fracField(new Sym('a')).oldPolyRing(x), 'Dx');
    expect(new HF(L(['-a', 1], RA), x, 0, [1]).diff().toString()).toBe('HolonomicFunction((1) + (-1/a)*Dx, x)');
  });
  it('more', () => {
    // the complex roots of the indicial equation fail in to_expr; SymPy raises the CoercionFailed too
    expect(() => new HF(LQ(['-1/2', '3*x/2', '5*x**2/2', 'x**3']), x, 0, [1, 0, 0]).integrate([x, 2, 3])).toThrow(CoercionFailed);
    // complex roots of the indicial equation: SymPy fails as well (CoercionFailed: expected Rational, got -2 + I)
    expect(() => new HF(LQ(['-1/2', '3*x/2', '5*x**2/2', 'x**3']), x).toSequence()).toThrow(CoercionFailed);
    expect(e2h(P('sin(x)/x + cos(x)/x**2')).toString()).toBe(
      'HolonomicFunction((x**2 + 4) + (8*x)*Dx + (2*x**2 + 12)*Dx**2 + (8*x)*Dx**3 + (x**2)*Dx**4, x, 1, [cos(1) + sin(1), -2*sin(1) - cos(1), 3*cos(1) + 5*sin(1), -20*sin(1) - 13*cos(1)])',
    );
    expect(sstr(e2h(P('log(x) + 1')).integrate([x, 0, 1]) as Expr)).toBe('0');
    expect(sstr(e2h(P('cos(x)/x - sin(x)/x**2'), { x0: 1 }).integrate([x, 0, 1]) as Expr)).toBe('-0.158530171972850');
    // SymPy fails too (ValueError: min() of the empty list of real roots)
    expect(() => new HF(LQ([1, 'x', 'x**2']), x).toSequence()).toThrow();
    expect(new HF(LQ(['-1/2', 'x']), x, 0, new Map([[half, [1]]])).changeIcs(1).toString()).toBe('HolonomicFunction((-1/2) + (x)*Dx, x, 1, [1])');
    expect(e2h(P('sqrt(x)*log(x + 1)')).toString()).toBe('HolonomicFunction((x/4 + 3/4) + (-x)*Dx + (x**3 + x**2)*Dx**2, x, 0, [0, 0])');
    expect(e2h(P('Ei(x)')).toString()).toBe('HolonomicFunction((1 - x)*Dx + (x)*Dx**2, x, 1, [Ei(1), E])');
    expect(e2h(P('Ei(x)'), { initcond: false }).toString()).toBe('HolonomicFunction((1 - x)*Dx + (x)*Dx**2, x)');
    expect(() => new HF(L([1, 0, 1]), x, 0, [0, 1]).pow(new Sym('n'))).toThrow(NotImplementedError);
    const [c0, c1] = [new Sym('C_0'), new Sym('C_1')];
    expect(solveLinear([P('C_0 + 1'), P('C_0')].map((t) => t.subs(new Sym('C_0'), c0)), [c0])).toBeUndefined();
    expect(solveLinear([S.Zero], [c0])).toBeUndefined();
    expect(solveLinear([P('C_0 + C_1')], [])).toBeUndefined();
    expect(sstr(solveLinear([P('C_0 + C_1')], [c0, c1])?.get(c0) ?? S.Zero)).toBe('-C_1');
  });
});

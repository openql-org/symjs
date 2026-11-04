// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/logic.ts.
// Relations and Piecewise. Expected values are SymPy 1.14's (sympy.core.tests.test_relational).

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { and } from '../../src/core/boolalg';
import { Eq, Ge, Gt, Le, Lt, Ne, piecewise, rel } from '../../src/core/logic';
import { Expr, Rational, S } from '../../src/core/nodes';
import { add, mul, pow } from '../../src/core/ops';

const [x, y, z] = sj.symbols('x y z');

const { oo, zoo, nan, pi } = sj;

const s = (e: Expr): string => e.toString();
const R = (p: number, q = 1) => Rational.of(p, q);
const negOo = mul(-1, oo);

describe('relations (SymPy test_relational)', () => {
  it('compares with nan', () => {
    // SymPy: Eq(nan, nan) = False, Ne(nan, 1) = True, Lt(nan, 1) raises TypeError
    expect(Eq(nan, nan)).toBe(S.false);
    expect(Ne(nan, 1)).toBe(S.true);
    expect(Eq(nan, x)).toBe(S.false);
    expect(() => Lt(nan, 1)).toThrow('Invalid NaN comparison');
    expect(() => Lt(x, nan)).toThrow(TypeError);
  });
  it('compares infinities', () => {
    // SymPy: Eq(oo, oo) = True, Ne(oo, oo) = False, Le(oo, oo) = True, Lt(oo, oo) = False
    expect(Eq(oo, oo)).toBe(S.true);
    expect(Ne(oo, oo)).toBe(S.false);
    expect(Le(oo, oo)).toBe(S.true);
    expect(Lt(oo, oo)).toBe(S.false);
    // SymPy: Lt(-oo, oo) = True, Gt(oo, 1) = True, Eq(oo, 1) = False, Ne(-oo, 2) = True
    expect(Lt(negOo, oo)).toBe(S.true);
    expect(Gt(oo, 1)).toBe(S.true);
    expect(Ge(negOo, 1)).toBe(S.false);
    expect(Eq(oo, 1)).toBe(S.false);
    expect(Ne(negOo, 2)).toBe(S.true);
  });
  it('compares with zoo', () => {
    // SymPy: Eq(zoo, 1) = False, Ne(zoo, 1) = True, Eq(zoo, zoo) = True, Eq(zoo, oo) = False
    expect(Eq(zoo, 1)).toBe(S.false);
    expect(Ne(zoo, 1)).toBe(S.true);
    expect(Eq(zoo, zoo)).toBe(S.true);
    expect(Eq(zoo, oo)).toBe(S.false);
    // SymPy: Lt(zoo, 1) and Le(zoo, zoo) raise TypeError
    expect(() => Lt(zoo, 1)).toThrow('Invalid comparison of non-real zoo');
    expect(() => Le(zoo, zoo)).toThrow(TypeError);
  });
  it('compares numbers', () => {
    // SymPy: Lt(Float(1.5), 2) = True, Ne(pi, 3) = True
    expect(Lt(1.5, 2)).toBe(S.true);
    expect(Ne(pi, 3)).toBe(S.true);
    expect(Eq(pi, 3)).toBe(S.false);
    // SymPy: Eq(sin(pi/7)**2 + cos(pi/7)**2, 1) stays (the difference is 0 only numerically)
    const t = mul(pi, R(1, 7));
    expect(s(Eq(add(pow(sj.sin(t), 2), pow(sj.cos(t), 2)), 1))).toBe('Eq(sin(pi/7)**2 + cos(pi/7)**2, 1)');
    expect(s(rel('Le', x, y))).toBe('x <= y');
  });
});

describe('Piecewise (SymPy Piecewise.eval)', () => {
  it('drops False conditions and gives nan when none is left', () => {
    // SymPy: Piecewise((x, False), (1, True)) = 1; Piecewise((x, False)) = nan
    expect(s(piecewise([x, false], [1, true]))).toBe('1');
    expect(piecewise([x, false])).toBe(nan);
    expect(piecewise([x, S.false], [y, false])).toBe(nan);
  });
  it('turns a boolean Piecewise condition into ITE', () => {
    // SymPy: Piecewise((1, Piecewise((True, x > 0), (And(y > 0, z > 0), True))), (0, True))
    //   = Piecewise((1, ITE(x > 0, True, (y > 0) & (z > 0))), (0, True))
    const inner = piecewise([S.true, Gt(x, 0)], [and(Gt(y, 0), Gt(z, 0)), true]);
    expect(s(piecewise([1, inner], [0, true]))).toBe('Piecewise((1, ITE(x > 0, True, (y > 0) & (z > 0))), (0, True))');
    // SymPy: Piecewise((1, Piecewise((Lt(2, y), x > 0), (Lt(3, z), True))), (0, True))
    //   = Piecewise((1, ITE(x > 0, y > 2, z > 3)), (0, True))
    const inner2 = piecewise([Lt(2, y), Gt(x, 0)], [Lt(3, z), true]);
    expect(s(piecewise([1, inner2], [0, true]))).toBe('Piecewise((1, ITE(x > 0, y > 2, z > 3)), (0, True))');
  });
});

describe('ordering relations decided like SymPy (is_lt, is_le, is_gt, is_ge)', () => {
  const s = (e: Expr): string => String(e);
  it('by the assumptions of the difference', () => {
    const p = new sj.Sym('p', { positive: true });
    const n = new sj.Sym('n', { nonnegative: true });
    const q = new sj.Sym('q', { negative: true });
    const x = new sj.Sym('x');
    expect([Gt(p, 0), Ge(p, 0), Lt(p, 0), Le(p, 0)].map(s)).toEqual(['True', 'True', 'False', 'False']);
    expect([Gt(q, 0), Ge(q, 0), Lt(q, 0), Le(q, 0)].map(s)).toEqual(['False', 'False', 'True', 'True']);
    expect([Ge(n, 0), Lt(n, 0)].map(s)).toEqual(['True', 'False']);
    expect([Le(mul(-1, n), 0), Gt(mul(-1, n), 0)].map(s)).toEqual(['True', 'False']);
    expect([Gt(x, 0), Le(x, 0)].map(s)).toEqual(['x > 0', 'x <= 0']);
  });
  it('numerically for real numbers', () => {
    const r = (t: string): Expr => sj.parse(t);
    expect([Lt(r('sqrt(2)'), 2), Le(r('sqrt(2)'), 1), Gt(r('pi'), 3), Ge(r('E'), 3)].map(s)).toEqual(['True', 'False', 'True', 'False']);
    const e1 = r('sqrt(2) + sqrt(3)');
    expect([Ge(e1, r('pi')), Gt(e1, r('pi')), Le(e1, r('pi')), Lt(e1, r('pi'))].map(s)).toEqual(['True', 'True', 'False', 'False']);
    const c1 = r('cos(1)');
    expect([Ge(c1, S.Half), Gt(c1, S.Half), Le(c1, S.Half), Lt(c1, S.Half)].map(s)).toEqual(['True', 'True', 'False', 'False']);
    // undecided: complex, near zero, not evaluable
    expect(s(Lt(r('I + 1'), 2))).toBe('1 + I < 2');
    expect(s(Lt(r('sqrt(2) + sqrt(3)'), r('sqrt(5 + 2*sqrt(6))')))).toBe('sqrt(2) + sqrt(3) < sqrt(2*sqrt(6) + 5)');
    expect(s(Lt(r('f(1)'), 2))).toBe('f(1) < 2');
    expect(s(Lt(r('oo'), 2))).toBe('False');
  });
});

describe('Piecewise conditions made canonical and collapsed (SymPy Piecewise.eval, _piecewise_collapse_arguments)', () => {
  const [x, y] = [new sj.Sym('x'), new sj.Sym('y')];
  const a = new sj.Sym('a', { positive: true });
  const s = (e: Expr): string => sj.str(e);
  const neg = (e: Expr): Expr => mul(-1, e);
  it('canonical relations', () => {
    expect(s(piecewise([0, Lt(x, a)], [1, true]))).toBe('Piecewise((0, a > x), (1, True))');
    expect(s(piecewise([0, sj.or(Lt(neg(x), -1), Gt(y, 2))], [1, true]))).toBe('Piecewise((0, (x > 1) | (y > 2)), (1, True))');
    expect(s(piecewise([0, Lt(neg(x), y)], [1, true]))).toBe('Piecewise((0, x > -y), (1, True))');
    expect(s(piecewise([0, Eq(neg(x), y)], [1, true]))).toBe('Piecewise((0, Eq(x, -y)), (1, True))');
    expect(s(piecewise([0, Gt(add(mul(2, x), 1), 3)], [1, true]))).toBe('Piecewise((0, x > 1), (1, True))');
    expect(s(piecewise([0, Gt(add(mul(-2, x), 1), 3)], [1, true]))).toBe('Piecewise((0, x < -1), (1, True))');
  });
  it('repeated and redundant conditions', () => {
    expect(s(piecewise([0, Lt(x, 1)], [1, Lt(x, 1)], [2, true]))).toBe('Piecewise((0, x < 1), (2, True))');
    expect(s(piecewise([0, Lt(x, 1)], [1, and(Lt(x, 1), Gt(y, 0))], [2, true]))).toBe('Piecewise((0, x < 1), (2, True))');
    expect(s(piecewise([0, Lt(x, 1)], [1, and(Ge(x, 1), Gt(y, 0))], [2, true]))).toBe('Piecewise((0, x < 1), (1, y > 0), (2, True))');
    expect(s(piecewise([0, Le(x, 1)], [1, and(Lt(x, 1), Gt(y, 0))], [2, true]))).toBe('Piecewise((0, x <= 1), (2, True))');
    expect(s(piecewise([0, Lt(x, 1)], [1, Ge(x, 1)]))).toBe('Piecewise((0, x < 1), (1, True))');
    expect(s(piecewise([0, Eq(x, 1)], [1, Ne(x, 1)]))).toBe('Piecewise((0, Eq(x, 1)), (1, True))');
  });
  it('more canonical forms (SymPy)', () => {
    expect(s(piecewise([0, Eq(y, neg(x))], [1, true]))).toBe('Piecewise((0, Eq(x, -y)), (1, True))');
    const z = new sj.Sym('z');
    expect(s(piecewise([0, Eq(z, neg(x))], [1, true]))).toBe('Piecewise((0, Eq(x, -z)), (1, True))');
    expect(s(piecewise([0, Lt(z, neg(x))], [1, true]))).toBe('Piecewise((0, x < -z), (1, True))');
    expect(s(piecewise([0, Lt(add(1, mul(-2, x)), 0)], [1, true]))).toBe('Piecewise((0, x > 1/2), (1, True))');
    expect(s(piecewise([0, and(Gt(x, 1), Lt(y, 2))], [1, true]))).toBe('Piecewise((0, (x > 1) & (y < 2)), (1, True))');
    expect(s(piecewise([0, Lt(add(3, mul(-2, x)), y)], [1, true]))).toBe('Piecewise((0, y > 3 - 2*x), (1, True))');
    expect(s(piecewise([0, Gt(add(1, mul(-2, x)), y)], [1, true]))).toBe('Piecewise((0, y < 1 - 2*x), (1, True))');
    expect(s(piecewise([0, Lt(add(mul(-2, x), y), 1)], [1, true]))).toBe('Piecewise((0, 2*x - y > -1), (1, True))');
    expect(s(piecewise([0, Gt(add(mul(-2, x), y), 3)], [1, true]))).toBe('Piecewise((0, 2*x - y < -3), (1, True))');
    expect(s(piecewise([0, Lt(x, 1)], [1, and(Gt(x, 1), sj.or(Lt(y, 0), Gt(y, 2)))], [2, true]))).toBe('Piecewise((0, x < 1), (1, (x > 1) & ((y > 2) | (y < 0))), (2, True))');
  });
  it('successive pairs with the same expression or condition', () => {
    expect(s(piecewise([0, Lt(x, 1)], [0, Gt(x, 2)], [1, sj.or(Gt(x, 2), Lt(x, 1))], [2, true]))).toBe('Piecewise((0, (x > 2) | (x < 1)), (2, True))');
    expect(s(piecewise([0, Lt(x, 1)], [0, Gt(x, 2)], [1, true]))).toBe('Piecewise((0, (x > 2) | (x < 1)), (1, True))');
    expect(s(piecewise([0, Lt(x, 1)], [1, Gt(x, 2)], [1, Gt(x, 3)], [2, true]))).toBe('Piecewise((0, x < 1), (1, (x > 2) | (x > 3)), (2, True))');
  });
});

describe('relations decided by the assumptions (SymPy is_eq, real values are finite)', () => {
  const a = new sj.Sym('a', { positive: true });
  const r = new sj.Sym('r', { real: true });
  const x = new sj.Sym('x');
  const s = (e: Expr): string => sj.str(e);
  it('equality by is_zero of the difference', () => {
    expect(s(Eq(a, 0))).toBe('False');
    expect(s(Ne(a, mul(-1, a)))).toBe('True');
    expect(s(Eq(a, 1))).toBe('Eq(a, 1)');
    expect(s(Ne(mul(sj.sqrt(sj.pi), a), 0))).toBe('True');
  });
  it('a real value against oo and -oo', () => {
    expect(s(Ge(r, S.NegativeInfinity))).toBe('True');
    expect(s(Lt(r, S.Infinity))).toBe('True');
    expect(s(Gt(r, S.Infinity))).toBe('False');
    expect(s(Le(S.NegativeInfinity, r))).toBe('True');
    expect(s(Eq(r, S.Infinity))).toBe('False');
    // 1/r may be infinite, x may be complex (SymPy keeps both)
    expect(s(Ge(pow(r, -1), S.NegativeInfinity))).toBe('1/r >= -oo');
    expect(s(Ge(x, S.NegativeInfinity))).toBe('x >= -oo');
  });
});

describe('relations between oo and -oo (SymPy)', () => {
  it('the difference is infinite', () => {
    expect(Lt(S.NegativeInfinity, S.Infinity)).toBe(S.true);
    expect(Gt(S.Infinity, S.NegativeInfinity)).toBe(S.true);
    expect(Ge(S.NegativeInfinity, S.Infinity)).toBe(S.false);
  });
});

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/strategies/util.ts (SymPy sympy/strategies/util.py).
// Expected values are SymPy 1.14's (Basic.__new__ keeps a node unevaluated).

import { describe, expect, it } from 'vitest';
import { BasicNode, FiniteSet, Float, Interval, Rational, S, str, symbols } from '../../src';
import { BoolOp } from '../../src/core/boolalg';
import { Concrete } from '../../src/core/concrete';
import { Add, Derivative, Dummy, Fn, Integral, Limit, Mul, Order, Piecewise, Pow, Rel, UndefFn, Wild } from '../../src/core/nodes';
import type { Expr } from '../../src/core/nodes';
import { assoc, basicFns, basicNew, exprFns, funcName } from '../../src/strategies/util';
import * as util from '../../src/strategies/util';

const [x, y] = symbols('x y');
const n = (v: number): Expr => Rational.of(v);

describe('Basic.__new__', () => {
  it('builds each class without evaluation', () => {
    expect(str(basicNew(new Add([x, y]), [n(1), n(2)]))).toBe('1 + 2');
    expect(basicNew(new Mul([x, y]), [n(2), n(3)]).args).toEqual([n(2), n(3)]);
    expect(str(basicNew(new Pow(x, y), [n(2), n(3)]))).toBe('2**3');
    expect(() => basicNew(new Pow(x, y), [n(2)])).toThrow(TypeError);
    expect(str(basicNew(new Fn('sin', [x]), [S.Pi]))).toBe('sin(pi)');
    expect(str(basicNew(new UndefFn('f', [x]), [n(1)]))).toBe('f(1)');
    expect(str(basicNew(new Rel('Lt', x, y), [n(1), n(2)]))).toBe('1 < 2');
    expect(() => basicNew(new Rel('Lt', x, y), [n(1)])).toThrow('Lt takes 2 arguments (1 given)');
    expect(basicNew(new BoolOp('And', [x, y]), [S.true, x])).toBeInstanceOf(BoolOp);
    expect(basicNew(new Piecewise([x, S.true]), [y, S.true])).toBeInstanceOf(Piecewise);
    expect(str(basicNew(new Integral([x, x]), [y, y]))).toBe('Integral(y, y)');
    expect(str(basicNew(new Derivative([x, x, n(1)]), [y, y, n(1)]))).toBe('Derivative(y, y)');
    expect(basicNew(new Order([x]), [y])).toBeInstanceOf(Order);
    const lim = basicNew(new Limit([x, x, n(0)], '-'), [y, y, n(1)]);
    expect(lim).toBeInstanceOf(Limit);
    expect((lim as Limit).dir).toBe('-');
    const sum = basicNew(new Concrete('Product', [x, new BasicNode([x, n(1), n(2)], 'Tuple')]), [y, new BasicNode([y, n(1), n(2)], 'Tuple')]);
    expect((sum as Concrete).kind2).toBe('Product');
    expect(str(basicNew(new BasicNode([x]), [n(1), n(0)]))).toBe('Basic(1, 0)');
    // sets (a higher layer) are rebuilt with evaluation; atoms stay as they are
    expect(str(basicNew(FiniteSet.of(x), [n(2), n(1), n(2)]))).toBe('{1, 2}');
    expect(basicNew(x, [])).toBe(x);
  });
  it('is util.new', () => {
    expect(util.new).toBe(basicNew);
  });
});

describe('class names', () => {
  it('names the SymPy class of a node', () => {
    expect(funcName(new BasicNode([x], 'T'))).toBe('T');
    expect(funcName(new Fn('sin', [x]))).toBe('sin');
    expect(funcName(new Fn('abs', [x]))).toBe('Abs');
    expect(funcName(new UndefFn('f', [x]))).toBe('f');
    expect(funcName(new BoolOp('Or', [x, y]))).toBe('Or');
    expect(funcName(new Rel('Eq', x, y))).toBe('Equality');
    expect(funcName(new Rel('Ne', x, y))).toBe('Unequality');
    expect(funcName(new Rel('Lt', x, y))).toBe('StrictLessThan');
    expect(funcName(new Rel('Le', x, y))).toBe('LessThan');
    expect(funcName(new Rel('Gt', x, y))).toBe('StrictGreaterThan');
    expect(funcName(new Rel('Ge', x, y))).toBe('GreaterThan');
    expect(funcName(new Concrete('Sum', [x]))).toBe('Sum');
    expect(funcName(new Wild('w'))).toBe('Wild');
    expect(funcName(new Dummy('d'))).toBe('Dummy');
    expect(funcName(x)).toBe('Symbol');
    expect(funcName(n(2))).toBe('Integer');
    expect(funcName(Rational.of(1, 2))).toBe('Rational');
    expect(funcName(Interval.of(0, 1))).toBe('Interval');
    expect(funcName(new Float(0.5))).toBe('Float');
    expect(funcName(new Add([x, y]))).toBe('Add');
  });
});

describe('tree functions', () => {
  it('assoc copies a map', () => {
    const d = new Map([['a', 1]]);
    const e = assoc(d, 'b', 2);
    expect([...e]).toEqual([
      ['a', 1],
      ['b', 2],
    ]);
    expect(d.size).toBe(1);
  });
  it('basic_fns and expr_fns', () => {
    const e = new Add([x, n(1)]);
    expect(basicFns.op(e)).toBe(e);
    expect(basicFns.children(e)).toBe(e.args);
    expect(basicFns.leaf(x)).toBe(true);
    expect(basicFns.leaf(e)).toBe(false);
    expect(str(basicFns.new(e, [n(1), n(2)]))).toBe('1 + 2');
    expect(str(exprFns.new(e, [n(1), n(2)]))).toBe('3');
  });
});

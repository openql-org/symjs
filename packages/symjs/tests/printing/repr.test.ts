// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/printing/repr.ts. Expected values from SymPy 1.14 srepr(...).

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { Dummy, Float, Integral, Limit, Order, Rational, S, Sym, Wild, WildFunction } from '../../src/core/nodes';
import type { Expr } from '../../src/core/nodes';
import { basicView, pyRepr, srepr, symbolAssumptionFacts } from '../../src/printing/repr';
import type { ReprPrintable } from '../../src/printing/repr';
import * as Sets from '../../src/sets/sets';
import { fromStr } from '../../src/numeric/mpf';

const [x, y] = sj.symbols('x y') as [Sym, Sym];
const f = sj.SymFunction('f');
const R = (p: number, q = 1): Rational => Rational.of(BigInt(p), BigInt(q));
const X = "Symbol('x')";
const Y = "Symbol('y')";

describe('srepr (SymPy srepr)', () => {
  const cases: [string, () => ReprPrintable, string][] = [
    ['x + 2', () => sj.add(x, 2), `Add(${X}, Integer(2))`],
    ['x - y', () => sj.sub(x, y), `Add(${X}, Mul(Integer(-1), ${Y}))`],
    ['-x', () => sj.mul(-1, x), `Mul(Integer(-1), ${X})`],
    ['-2*x + 3', () => sj.add(sj.mul(-2, x), 3), `Add(Integer(3), Mul(Integer(-1), Integer(2), ${X}))`],
    ['-x*y', () => sj.mul(-1, x, y), `Mul(Integer(-1), ${X}, ${Y})`],
    ['7/3*x*y', () => sj.mul(R(7, 3), x, y), `Mul(Rational(7, 3), ${X}, ${Y})`],
    ['x/2', () => sj.mul(x, R(1, 2)), `Mul(Rational(1, 2), ${X})`],
    ['sqrt(x)', () => sj.sqrt(x), `Pow(${X}, Rational(1, 2))`],
    ['1/x', () => sj.pow(x, -1), `Pow(${X}, Integer(-1))`],
    ['2**x', () => sj.pow(2, x), `Pow(Integer(2), ${X})`],
    ['exp(x)', () => sj.exp(x), `exp(${X})`],
    ['S.Half', () => S.Half, 'Rational(1, 2)'],
    ['-3/4', () => R(-3, 4), 'Rational(-3, 4)'],
    ['Float(2)', () => new Float(2), "Float('2.0', precision=53)"],
    ['Float(0.1)', () => new Float(0.1), "Float('0.10000000000000001', precision=53)"],
    ["Float('0.1', 30)", () => new Float(fromStr('0.1', 103), 103), "Float('0.0999999999999999999999999999999951', precision=103)"],
    ['I', () => sj.I, 'I'],
    ['E', () => sj.E, 'E'],
    ['-oo', () => S.NegativeInfinity, '-oo'],
    ['zoo', () => S.ComplexInfinity, 'zoo'],
    ['true', () => S.true, 'true'],
    ['false', () => S.false, 'false'],
    ["Symbol('n', integer=True, positive=True)", () => sj.symbol('n', { integer: true, positive: true }), "Symbol('n', integer=True, positive=True)"],
    ["Symbol('n', integer=True, nonnegative=True)", () => sj.symbol('n', { integer: true, nonnegative: true }), "Symbol('n', integer=True, nonnegative=True)"],
    ["Symbol('x', nonnegative=True)", () => sj.symbol('x', { nonnegative: true }), "Symbol('x', nonnegative=True)"],
    ["Symbol('x', nonpositive=True)", () => sj.symbol('x', { nonpositive: true }), "Symbol('x', nonpositive=True)"],
    ["Symbol('x', real=True)", () => sj.symbol('x', { real: true }), "Symbol('x', real=True)"],
    ["Symbol('x', integer=False)", () => sj.symbol('x', { integer: false }), "Symbol('x', integer=False)"],
    ["Symbol('x', zero=True)", () => sj.symbol('x', { zero: true }), "Symbol('x', zero=True)"],
    ["Symbol('x', zero=False)", () => sj.symbol('x', { zero: false }), "Symbol('x', zero=False)"],
    ["Symbol('x', polar=True)", () => sj.symbol('x', { polar: true }), "Symbol('x', polar=True)"],
    ["Symbol('x', negative=True)", () => sj.symbol('x', { negative: true }), "Symbol('x', negative=True)"],
    ["Symbol('z', commutative=False)", () => new Sym('z', { commutative: false }), "Symbol('z', commutative=False)"],
    ["Wild('w')", () => new Wild('w'), "Wild('w')"],
    ["WildFunction('F')", () => new WildFunction('F'), "WildFunction('F')"],
    ['f(x)', () => f(x), `Function('f')(${X})`],
    ['Abs(x)', () => sj.Abs(x), `Abs(${X})`],
    ['Heaviside(x)', () => sj.Heaviside(x), `Heaviside(${X})`],
    ['Eq(x, 1)', () => sj.Eq(x, 1), `Equality(${X}, Integer(1))`],
    ['x < 1', () => sj.Lt(x, 1), `StrictLessThan(${X}, Integer(1))`],
    ['(x < 1) & (y < 1)', () => sj.And(sj.Lt(x, 1), sj.Lt(y, 1)), `And(StrictLessThan(${X}, Integer(1)), StrictLessThan(${Y}, Integer(1)))`],
    ['(x > 1) | (y > 1)', () => sj.Or(sj.Gt(x, 1), sj.Gt(y, 1)), `Or(StrictGreaterThan(${X}, Integer(1)), StrictGreaterThan(${Y}, Integer(1)))`],
    ['O(x)', () => sj.O(x), `Order(${X}, Tuple(${X}, Integer(0)))`],
    ['O(x*y)', () => sj.O(sj.mul(x, y)), `Order(Mul(${X}, ${Y}), Tuple(${X}, Integer(0)), Tuple(${Y}, Integer(0)))`],
    ['O(x, (x, oo))', () => sj.O(x, x, S.Infinity), `Order(${X}, Tuple(${X}, oo))`],
    ['O(1)', () => sj.O(1), 'Order(Integer(1))'],
    ['Limit(x, x, 0)', () => new Limit([x, x, S.Zero]), `Limit(${X}, ${X}, Integer(0), Symbol('+'))`],
    ['Derivative(sin(x), x, (y, 2))', () => sj.Derivative(sj.sin(x), x, [y, 2]), `Derivative(sin(${X}), Tuple(${X}, Integer(1)), Tuple(${Y}, Integer(2)))`],
    ['Derivative(x**3, (x, 2))', () => sj.Derivative(sj.pow(x, 3), [x, 2]), `Derivative(Pow(${X}, Integer(3)), Tuple(${X}, Integer(2)))`],
    ['Integral(x, x)', () => new Integral([x, x]), `Integral(${X}, Tuple(${X}))`],
    [
      'Integral(x*y, (x, 0, 1), (y, 0, 2))',
      () => new Integral([new Integral([sj.mul(x, y), x, S.Zero, S.One]), y, S.Zero, S.Two]),
      `Integral(Mul(${X}, ${Y}), Tuple(${X}, Integer(0), Integer(1)), Tuple(${Y}, Integer(0), Integer(2)))`,
    ],
    ['Sum(x, (x, 1, 3))', () => sj.Sum(x, [x, 1, 3]), `Sum(${X}, Tuple(${X}, Integer(1), Integer(3)))`],
    ['Product(x, (x, 1, 3))', () => sj.Product(x, [x, 1, 3]), `Product(${X}, Tuple(${X}, Integer(1), Integer(3)))`],
    [
      'Piecewise((x, x < 0), (0, True))',
      () => sj.Piecewise([x, sj.Lt(x, 0)], [0, true]),
      `Piecewise(ExprCondPair(${X}, StrictLessThan(${X}, Integer(0))), ExprCondPair(Integer(0), true))`,
    ],
    ['Tuple(x, 1)', () => sj.Tuple(x, 1), `Tuple(${X}, Integer(1))`],
    ['Tuple()', () => sj.Tuple(), 'Tuple()'],
    ['Lambda(x, x**2)', () => sj.Lambda(x, sj.pow(x, 2)), `Lambda(Tuple(${X}), Pow(${X}, Integer(2)))`],
    ['Lambda((x, y), x + y)', () => sj.Lambda([x, y], sj.add(x, y)), `Lambda(Tuple(${X}, ${Y}), Add(${X}, ${Y}))`],
    ['Subs(f(x), x, 1)', () => sj.Subs(f(x), x, 1), `Subs(Function('f')(${X}), Tuple(${X}), Tuple(Integer(1)))`],
    ["MatrixSymbol('A', 2, 2)", () => sj.MatrixSymbol('A', 2, 2), "MatrixSymbol(Str('A'), Integer(2), Integer(2))"],
    ['Q.positive(x)', () => sj.Q.positive(x), `AppliedPredicate(Q.positive, ${X})`],
    ['ImmutableMatrix([[1]])', () => sj.ImmutableMatrix([[1]]), 'ImmutableDenseMatrix([[Integer(1)]])'],
    ['Reals', () => Sets.Reals, 'Reals'],
    ['EmptySet', () => Sets.EmptySet, 'EmptySet'],
    ['Integers', () => Sets.Integers, 'Integers'],
    ['Interval.Lopen(0, 1)', () => Sets.Lopen(0, 1), 'Interval(Integer(0), Integer(1), true, false)'],
    ['FiniteSet(1, 2)', () => Sets.finiteSet(2, 1), 'FiniteSet(Integer(1), Integer(2))'],
    ['Union(Interval(0, 1), FiniteSet(3))', () => Sets.union(Sets.interval(0, 1), Sets.finiteSet(3)), 'Union(Interval(Integer(0), Integer(1), false, false), FiniteSet(Integer(3)))'],
    [
      'ImageSet(Lambda(x, x**2), Naturals)',
      () => new Sets.ImageSet(x, sj.pow(x, 2), Sets.Naturals),
      `ImageSet(Lambda(Tuple(${X}), Pow(${X}, Integer(2))), Naturals)`,
    ],
    ['ConditionSet(x, x > 0, Reals)', () => new Sets.ConditionSet(x, sj.Gt(x, 0), Sets.Reals), `ConditionSet(${X}, StrictGreaterThan(${X}, Integer(0)), Reals)`],
    ['Matrix([[x, 1], [2, y]])', () => sj.Matrix.of([[x, 1], [2, y]]), `MutableDenseMatrix([[${X}, Integer(1)], [Integer(2), ${Y}]])`],
    ['Matrix(0, 3, [])', () => sj.Matrix.zeros(0, 3), 'MutableDenseMatrix(0, 3, [])'],
    ['{x: 1}', () => new Map<ReprPrintable, ReprPrintable>([[x, 1]]), `{${X}: 1}`],
    ['[x, 1]', () => [x, 1], `[${X}, 1]`],
    ['{1, 2}', () => new Set([1, 2]), '{1, 2}'],
    ['set()', () => new Set(), 'set()'],
    ["'a'", () => 'a', "'a'"],
    ['"it\'s"', () => "it's", '"it\'s"'],
    ['None', () => null, 'None'],
    ['True', () => true, 'True'],
    ['False', () => false, 'False'],
    ['2', () => 2, '2'],
    ['2n', () => 2n, '2'],
  ];
  it.each(cases)('%s', (_label, build, expected) => {
    expect(srepr(build())).toBe(expected);
  });
  it('an Order of an expression in several symbols, at 0 for all of them', () => {
    expect(srepr(new Order([sj.mul(y, x)]))).toBe(`Order(Mul(${X}, ${Y}), Tuple(${X}, Integer(0)), Tuple(${Y}, Integer(0)))`);
    const z = sj.symbol('z');
    expect(srepr(new Order([sj.mul(z, x, y)]))).toBe(`Order(Mul(${X}, ${Y}, Symbol('z')), Tuple(${X}, Integer(0)), Tuple(${Y}, Integer(0)), Tuple(Symbol('z'), Integer(0)))`);
  });
  it('a Dummy prints its index like an assumption', () => {
    const d = new Dummy('d', { positive: true });
    expect(srepr(d)).toBe(`Dummy('d', positive=True, dummy_index=${d.dummyIndex})`);
  });
  it('an extension node prints its name and arguments', () => {
    class Node extends sj.ExtensionExpr {
      constructor(args: readonly Expr[]) {
        super('Node', args);
      }
      withArgs(args: readonly Expr[]): Expr {
        return new Node(args);
      }
    }
    expect(srepr(new Node([x, R(1)]))).toBe(`Node(${X}, Integer(1))`);
  });
});

describe('pyRepr (Python repr of a string)', () => {
  it('quotes and escapes', () => {
    expect(pyRepr('a')).toBe("'a'");
    expect(pyRepr("it's")).toBe('"it\'s"');
    expect(pyRepr('a\'b"c\\\n')).toBe("'a\\'b\"c\\\\\\n'");
  });
});

describe('basicView (SymPy class names and args)', () => {
  it('sums and products in SymPy argument order (Basic.compare) or printing order', () => {
    expect(basicView(sj.add(x, 2)).args.map((a) => a.str)).toEqual(['2', 'x']);
    expect(basicView(sj.add(x, 2), true).args.map((a) => a.str)).toEqual(['x', '2']);
    expect(basicView(sj.mul(-2, x), true).args.map((a) => a.str)).toEqual(['-1', '2', 'x']);
    expect(basicView(sj.mul(new Float(-2.5), x), true).args.map((a) => a.str)).toEqual(['-1', '2.50000000000000', 'x']);
  });
  it('whether the class derives from Expr', () => {
    expect(basicView(x).isExpr).toBe(true);
    expect(basicView(sj.Lt(x, 1)).isExpr).toBe(false);
    expect(basicView(sj.Tuple(x)).isExpr).toBe(false);
    expect(basicView(Sets.Reals).isExpr).toBe(false);
    expect(basicView(sj.MatrixSymbol('A', 2, 2)).args[0]?.isExpr).toBe(false);
  });
  it('the assumptions a symbol is created with (SymPy _assumptions_orig and commutative)', () => {
    expect(symbolAssumptionFacts(x)).toEqual({ commutative: true });
    expect(symbolAssumptionFacts(sj.symbol('p', { positive: true }))).toEqual({ commutative: true, positive: true });
    expect(symbolAssumptionFacts(new Sym('A', { commutative: false }))).toEqual({ commutative: false });
    expect(symbolAssumptionFacts(new WildFunction('F'))).toBeUndefined();
    expect(symbolAssumptionFacts(sj.add(x, 1))).toBeUndefined();
  });
});

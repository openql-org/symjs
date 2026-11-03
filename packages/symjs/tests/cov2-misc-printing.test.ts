// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * Coverage of printing/sets.ts, sortkey.ts, str.ts and the pretty printer
 * (pretty.ts, stringpict.ts, symbology.ts). Expected strings from SymPy 1.14
 * (str, pretty with and without unicode, latex, default_sort_key).
 */

import { describe, expect, it } from 'vitest';
import * as sj from '../src';
import { Implies, ITE } from '../src/logic';
import * as Sets from '../src/sets/sets';
import { Add, ExtensionExpr, Pow, WildFunction } from '../src/core/nodes';
import type { Expr } from '../src/core/nodes';
import { PrettyForm, PrettyTuple, StringPict } from '../src/printing';
import { asOrderedTerms, compareKeys, sortKey } from '../src/printing/sortkey';
import { precedence, str } from '../src/printing/str';

const x = sj.symbol('x');
const y = sj.symbol('y');
const z = sj.symbol('z');
const uni = (e: unknown): string => sj.pretty(e as Expr, { useUnicode: true });
const asc = (e: unknown): string => sj.pretty(e as Expr, { useUnicode: false });
const ONE_KEY = [[1, 0, 'Number'], [0, []], [], 1];

/** An extension node printed Name(args) with a declared str precedence. */
class Ext extends ExtensionExpr {
  constructor(
    name: string,
    args: readonly Expr[],
    readonly prec: unknown,
  ) {
    super(name, args);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new Ext(this.name, args, this.prec);
  }
  strPrecedence(): unknown {
    return this.prec;
  }
}

/** An extension node with its own str form. */
class Tagged extends ExtensionExpr {
  withArgs(args: readonly Expr[]): Expr {
    return new Tagged(this.name, args);
  }
  override printStr(print: (e: Expr) => string): string {
    return `<${this.args.map(print).join(' ')}>`;
  }
}

describe('sets: argument order of Union and Intersection', () => {
  const I = (a: sj.ExprLike, b: sj.ExprLike) => Sets.interval(a, b);
  const F = (...a: sj.ExprLike[]) => Sets.finiteSet(...a);
  it('orders by infimum, then by node count and sort key', () => {
    const cases: [Expr, string, string][] = [
      // SymPy str, pretty(use_unicode=True)
      [Sets.union(I(sj.mul(-1, sj.oo), 0), F(5)), 'Union({5}, Interval(-oo, 0))', '(-∞, 0] ∪ {5}'],
      [Sets.union(F(1, sj.oo), I(2, 3)), 'Union({1, oo}, Interval(2, 3))', '{1, ∞} ∪ [2, 3]'],
      [Sets.union(F(sj.zoo), I(0, 1)), 'Union({zoo}, Interval(0, 1))', '[0, 1] ∪ {zoo}'],
      [Sets.union(F(sj.I), I(0, 1)), 'Union({I}, Interval(0, 1))', '[0, 1] ∪ {ⅈ}'],
      [Sets.union(F(sj.nan), I(0, 1)), 'Union({nan}, Interval(0, 1))', '[0, 1] ∪ {nan}'],
      [Sets.intersection(Sets.union(I(0, 1), F(x)), I(y, 2)), 'Union(Intersection({x}, Interval(y, 2)), Intersection(Interval(0, 1), Interval(y, 2)))', '({x} ∩ [y, 2]) ∪ ([0, 1] ∩ [y, 2])'],
      // both infima unknown: SymPy's ordered() puts the one with fewer nodes first
      [
        Sets.intersection(Sets.union(I(0, 1), F(x)), Sets.union(I(5, 6), F(y))),
        'Union(Intersection({x}, Union({y}, Interval(5, 6))), Intersection({y}, Interval(0, 1)))',
        '([0, 1] ∩ {y}) ∪ ({x} ∩ ([5, 6] ∪ {y}))',
      ],
    ];
    for (const [e, s, p] of cases) expect([sj.str(e), uni(e)]).toEqual([s, p]);
    const last = Sets.intersection(Sets.union(I(0, 1), F(x)), Sets.union(I(5, 6), F(y)));
    expect(sj.latex(last)).toBe(
      '\\left(\\left[0, 1\\right] \\cap \\left\\{y\\right\\}\\right) \\cup \\left(\\left\\{x\\right\\} \\cap \\left(\\left[5, 6\\right] \\cup \\left\\{y\\right\\}\\right)\\right)',
    );
  });
});

describe('sort keys', () => {
  it('gives a WildFunction the class key of a Function', () => {
    // SymPy WildFunction('F').sort_key()
    expect(sortKey(new WildFunction('F'))).toEqual([[4, 0, 'WildFunction'], [1, ['F_']], ONE_KEY, 1]);
  });
  it('takes oo, -oo as the coefficient of a product', () => {
    // SymPy: sorted([oo*x, x, -oo*x, 2*x], key=default_sort_key) = [-oo*x, x, 2*x, oo*x]
    const xs = [sj.mul(sj.oo, x), x, sj.mul(-1, sj.oo, x), sj.mul(2, x)];
    expect(xs.sort((a, b) => compareKeys(sortKey(a), sortKey(b))).map(str)).toEqual(['-oo*x', 'x', '2*x', 'oo*x']);
    expect(sj.str(sj.add(sj.mul(sj.oo, x), sj.mul(sj.zoo, y), sj.sin(x)))).toBe('oo*x + zoo*y + sin(x)');
  });
  it('keys the booleans by their class', () => {
    // SymPy: S.true.sort_key() = ((5, 0, 'BooleanTrue'), (0, ()), ((1, 0, 'Number'), (0, ()), (), 1), 1)
    expect(sortKey(sj.S.true)).toEqual([[5, 0, 'BooleanTrue'], [0, []], ONE_KEY, 1]);
    expect(sortKey(sj.S.false)).toEqual([[5, 0, 'BooleanFalse'], [0, []], ONE_KEY, 1]);
  });
  it('orders powers with a Float in the exponent', () => {
    // SymPy decompose_power(x**(2.5*y)) = (x**(2.5*y), 1)
    expect(sj.str(sj.add(sj.pow(x, sj.mul(2.5, y)), sj.pow(x, 2), x))).toBe('x**2 + x + x**(2.5*y)');
  });
  it('as_ordered_terms of a single term', () => {
    expect(asOrderedTerms(x)).toEqual([x]);
  });
});

describe('str precedence', () => {
  it('follows PRECEDENCE_VALUES for relations', () => {
    // SymPy precedence(Eq(x, y)) = precedence(Ne(x, y)) = 50, precedence(x < y) = 35
    expect(precedence(sj.Eq(x, y))).toBe(50);
    expect(precedence(sj.Ne(x, y))).toBe(50);
    expect(precedence(sj.Lt(x, y))).toBe(35);
  });
  it('reads the precedence an extension node declares', () => {
    // a declared precedence that is not a number is ignored (atom)
    expect(precedence(new Ext('Foo', [x], 'high'))).toBe(1000);
    expect(precedence(new Ext('Foo', [x], 10))).toBe(10);
    // a term binding looser than Add is parenthesized
    expect(str(new Add([x, new Ext('Foo', [y], 10)]))).toBe('x + (Foo(y))');
  });
});

describe('pretty', () => {
  it('prints the boolean values', () => {
    expect([uni(false), uni(true), uni(sj.S.false)]).toEqual(['False', 'True', 'False']);
  });
  it('sorts dict keys by default_sort_key', () => {
    // SymPy pretty({'b': 1, x: 2, 3: 4, 'a': 5}), pretty({True: 1, False: 2}), pretty({(2, 1): 'a', (1, 5): 'b'})
    expect(uni(new Map<unknown, unknown>([['b', 1], [x, 2], [3, 4], ['a', 5]]))).toBe('{a: 5, b: 1, 3: 4, x: 2}');
    expect(uni(new Map([[true, 1], [false, 2]]))).toBe('{False: 2, True: 1}');
    expect(uni(new Map([[new PrettyTuple(2, 1), 'a'], [new PrettyTuple(1, 5), 'b']]))).toBe('{(1, 5): b, (2, 1): a}');
    expect(uni(new Map([[[2n], 'a'], [[1n], 'b']]))).toBe('{[1]: b, [2]: a}');
    // keys Python could not hash keep their order
    const m = new Map([[1, 2]]);
    expect(uni(new Map<unknown, unknown>([[m, 'a'], [x, 'b']]))).toBe('{{1: 2}: a, x: b}');
    expect(uni(new Map<unknown, unknown>([[[m], 'a'], [x, 'b']]))).toBe('{[{1: 2}]: a, x: b}');
  });
  it('rejects a value it cannot print', () => {
    expect(() => uni(null)).toThrow(TypeError);
    expect(() => uni(Symbol('s'))).toThrow(TypeError);
  });
  it('prints factorials', () => {
    // SymPy pretty(factorial(x)), pretty(factorial2(x + 1)), pretty(subfactorial(x))
    expect(uni(sj.factorial(x))).toBe('x!');
    expect(uni(sj.factorial2(sj.add(x, 1)))).toBe('(x + 1)!!');
    expect(uni(sj.subfactorial(x))).toBe('!x');
    // SymPy pretty(factorial(-3, evaluate=False)), factorial(5, evaluate=False), subfactorial(-2, evaluate=False)
    expect(uni(sj.fn('factorial', [-3], { evaluate: false }))).toBe('(-3)!');
    expect(uni(sj.fn('factorial', [5], { evaluate: false }))).toBe('5!');
    expect(uni(sj.fn('subfactorial', [-2], { evaluate: false }))).toBe('!(-2)');
  });
  it('prints square roots of integers with the root sign', () => {
    expect(uni(sj.sqrt(10))).toBe('√10');
    expect(asc(sj.sqrt(10))).toBe('  ____\n\\/ 10 ');
  });
  it('prints noncommutative powers as powers', () => {
    const A = sj.symbol('A', { commutative: false });
    // SymPy pretty(A**-2), pretty(A**(1/2))
    expect(uni(sj.pow(A, -2))).toBe(' -2\nA  ');
    expect(uni(sj.pow(A, sj.Rational.of(1, 2)))).toBe(' 1/2\nA   ');
  });
  it('parenthesizes relations in sums and powers', () => {
    // SymPy refuses Add and Pow of a Relational, but its _print_Add and
    // _print_Pow parenthesize one; symjs nodes built directly print the same way
    expect(uni(new Add([sj.Eq(x, y), sj.S.One]))).toBe('(x = y) + 1');
    expect(uni(new Pow(sj.Eq(x, y), sj.Rational.of(2)))).toBe('       2\n(x = y) ');
  });
  it('prints ITE as a Piecewise', () => {
    // SymPy pretty(ITE(x, y, z)) and pretty(And(x, ITE(y, x, z)))
    expect(uni(ITE(x, y, z))).toBe('⎧y    for x  \n⎨            \n⎩z  otherwise');
    expect(asc(ITE(x, y, z))).toBe('/y    for x  \n<            \n\\z  otherwise');
    expect(uni(sj.And(x, ITE(y, x, z)))).toBe('    ⎛⎧x    for y  ⎞\nx ∧ ⎜⎨            ⎟\n    ⎝⎩z  otherwise⎠');
    expect(uni(sj.Not(Implies(x, y)))).toBe('x ↛ y');
    // a Piecewise condition that is a boolean Piecewise becomes the core ITE
    // SymPy pretty(Piecewise((1, Piecewise((y > 2, x > 0), (z < 1, True))), (0, True)))
    const pw = sj.Piecewise([1, sj.Piecewise([sj.Gt(y, 2), sj.Gt(x, 0)], [sj.Lt(z, 1), true])], [0, true]);
    expect(uni(pw)).toBe('⎧       ⎧y > 2  for x > 0\n⎪1  for ⎨                \n⎨       ⎩z < 1  otherwise\n⎪                        \n⎩0        otherwise      ');
  });
  it('prints an unknown extension node as a function or by its str form', () => {
    expect(uni(new Ext('Foo', [x, y], 0))).toBe('Foo(x, y)');
    expect(uni(new Tagged('Tag', [x, y]))).toBe('<x y>');
  });
});

describe('stringPict', () => {
  it('renders with the default of 80 columns', () => {
    expect(new StringPict('abc').render()).toBe('abc');
  });
  it('parenthesizes a fraction over a fraction', () => {
    // SymPy (ASCII): (prettyForm('1')/prettyForm('2'))/prettyForm('x')
    const half = new PrettyForm('1').div(new PrettyForm('2'));
    expect(half.div(new PrettyForm('x')).render({ wrapLine: false })).toBe('/1\\\n|-|\n\\2/\n---\n x ');
  });
});

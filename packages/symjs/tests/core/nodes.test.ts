// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/nodes.ts.
// The node classes and numbers. Expected values are SymPy 1.14's.

import { describe, expect, it } from 'vitest';
import { inspect } from 'node:util';
import * as sj from '../../src';


import { Rational } from '../../src';
import { InvariantError } from '../../src/core/errors';
import {
  Add,
  BoolAtom,
  Expr,
  ExtensionExpr,
  Float,
  Mul,
  S,
  WildFunction,
  asRational,
  compareExpr,
} from '../../src/core/nodes';
import { add, mul, pow } from '../../src/core/ops';
import * as nodes from '../../src/core/nodes';

const [x, y] = sj.symbols('x y');

const { I, oo, nan, pi } = sj;

const s = (e: Expr): string => e.toString();
const R = (p: number, q = 1) => Rational.of(p, q);

/** A minimal extension node (the extension API defaults). */
class Box extends ExtensionExpr {
  constructor(args: readonly Expr[]) {
    super('Box', args);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new Box(args);
  }
}

it('uses the default printing, expansion, matching and kind hooks of an extension', () => {
  const box = new Box([x, S.One]);
  expect(x.toLatex()).toBe('x');
  expect(box.printLatex(String)).toBe('\\operatorname{Box}\\left(x, 1\\right)');
  expect(box.kindSelf()).toBeUndefined();
  expect(box.matchesSelf(x)).toBeUndefined();
  expect(box.expandSelf('basic', {})).toBeUndefined();
  expect(box.diffSelf(x, sj.diff)).toBeUndefined();
});

it('encodes fermionic assumptions in symbol identities', () => {
  const above = sj.symbol('a', { aboveFermi: true });
  const below = sj.symbol('a', { belowFermi: true });
  expect(above.key).not.toBe(below.key);
  expect(above.assumptions0.get('above_fermi')).toBe(true);
  expect(below.assumptions0.get('below_fermi')).toBe(true);
});

it('reports a missing rewrite implementation at the core entry point', () => {
  const rewrite = nodes.impl.rewrite;
  delete nodes.impl.rewrite;
  try {
    expect(() => x.rewrite('exp')).toThrow(/rewrite/);
  } finally {
    if (rewrite) nodes.impl.rewrite = rewrite;
  }
});

describe('numeric', () => {
  it('rational objects', () => {
    expect(Rational.of(6, -4).toString()).toBe('-3/2');
  });
});

describe('node classes', () => {
  it('has fluent methods', () => {
    expect(s(sj.sin(x).div(x).limit(x, 0))).toBe('1');
    expect(s(pi.n())).toBe('3.14159265358979');
    expect(() => I.toNumber()).toThrow(RangeError);
    expect(inspect(x)).toBe('Expr(x)');
    expect(pi.isComparable).toBe(true);
    expect(s(x.sub(1))).toBe('x - 1');
    expect(s(x.neg())).toBe('-x');
    expect(s(x.add(1).pow(2).expand())).toBe('x**2 + 2*x + 1');
    expect(I.conjugate().equals(mul(-1, I))).toBe(true);
    const subs1 = x.subs.bind(x) as unknown as (from: Expr) => Expr;
    expect(() => subs1(x)).toThrow(TypeError);
  });
  it('checks constructor arguments', () => {
    expect(() => asRational(x)).toThrow(InvariantError);
    expect(() => Rational.of(1, 0)).toThrow(RangeError);
    expect(() => new Float(Infinity)).toThrow(RangeError);
    expect(new sj.Sym('').name).toBe('');
    expect(() => Reflect.construct(sj.Sym, [5])).toThrow(SyntaxError);
  });
  it('keys Wild properties and WildFunction arities', () => {
    const w = new sj.Wild('a', { properties: [(e: Expr) => e.isNumber] });
    expect(w.key).toContain('{1}');
    expect(s(w)).toBe('a_');
    expect(new WildFunction('F', [1, 2]).key).toBe('?FF[1,2]');
    expect(new WildFunction('F').key).toBe('?FF[]');
  });
  it('tells infinities from nan', () => {
    expect((oo as sj.Expr & { isInfinite: boolean }).isInfinite).toBe(true);
    expect((nan as sj.Expr & { isInfinite: boolean }).isInfinite).toBe(false);
  });
  it('orders numbers first', () => {
    expect(compareExpr(S.One, x)).toBe(-1);
    expect(compareExpr(x, S.One)).toBe(1);
    expect(compareExpr(x, x)).toBe(0);
    expect(compareExpr(y, x)).toBe(1);
  });
  it('has type guards', () => {
    expect(sj.isRational(R(1, 2))).toBe(true);
    expect(sj.isFloat(new Float(0.5))).toBe(true);
    expect(sj.isSymbol(x)).toBe(true);
    expect(sj.isAdd(add(x, 1))).toBe(true);
    expect(sj.isMul(mul(2, x))).toBe(true);
    expect(sj.isPow(pow(x, 2))).toBe(true);
    expect(sj.isFunction(sj.sin(x))).toBe(true);
    expect(sj.isFunction(sj.sin(x), 'sin')).toBe(true);
    expect(sj.isFunction(sj.sin(x), 'cos')).toBe(false);
    expect(sj.isFunction(x)).toBe(false);
    expect(sj.isInteger(R(2))).toBe(true);
    expect(sj.isInteger(R(1, 2))).toBe(false);
    expect(sj.isInteger(x)).toBe(false);
  });
  it('gives extension nodes default behaviour', () => {
    const b = new Box([x]);
    // no numeric value of its own: evalf evaluates the arguments
    expect(s(new Box([R(1)]).evalf())).toBe('Box(1.0)');
    // SymPy: the adjoint of a scalar is its conjugate
    expect(s(sj.adjoint(b))).toBe('conjugate(Box(x))');
    expect(s(sj.transpose(b))).toBe('Box(x)');
    // not a function application with a Taylor series
    expect(b.isTaylorExpandable).toBe(false);
    expect(x.prettyForm).toBeUndefined();
    expect(b.kindSelf()).toBeUndefined();
    expect(b.matchesSelf(x)).toBeUndefined();
    expect(b.expandSelf('custom', {})).toBeUndefined();
    expect(b).toBeInstanceOf(Expr);
    expect(new BoolAtom(true).key).toBe('!true');
    expect(add(x, y)).toBeInstanceOf(Add);
    expect(mul(x, y)).toBeInstanceOf(Mul);
  });
});

describe('symbol assumptions zero and integer', () => {
  it('derives the facts SymPy derives from zero=True and integer=False', () => {
    // SymPy: Symbol('z', zero=True) is an integer, nonnegative and nonpositive; integer=False implies zero=False
    const z = new sj.Sym('z', { zero: true });
    expect(z.assumptions).toEqual({ real: true, nonnegative: true, nonpositive: true, integer: true, zero: true });
    const w = new sj.Sym('w', { integer: false });
    expect(w.assumptions).toEqual({ integer: false, zero: false });
    // the assumptions are part of the identity of a symbol
    expect(new Set([z.key, w.key, new sj.Sym('z').key, new sj.Sym('w').key]).size).toBe(4);
    // Zero cannot also be strictly positive.
    expect(() => new sj.Sym('p', { zero: true, positive: true })).toThrow(RangeError);
  });
});

it('reports defined function names but leaves anonymous constructors unnamed', () => {
  expect(nodes.headName(sj.SymFunction('oscillation'))).toBe('oscillation');
  expect(nodes.headName(() => S.One)).toBeUndefined();
});

it('distinguishes indefinite integration from explicit bounds', () => {
  expect(new sj.Integral([x, x]).limits).toBeUndefined();
  expect(new sj.Integral([x, x, S.Zero, S.One]).limits).toEqual([S.Zero, S.One]);
});

describe('ExtensionExpr.expandTop', () => {
  it('is no override by default', () => {
    expect(sj.Tuple(1, 2).expandTop({})).toBeUndefined();
  });
});

describe('Integral over a matrix symbol', () => {
  it('is commutative when its integrand is (SymPy is_commutative of the function)', () => {
    const H = sj.MatrixSymbol('_H', 2, 2);
    const I = new sj.Integral([sj.exp(sj.mul(-1, sj.Trace(H.pow(2)))), H]);
    expect(I.isCommutative).toBe(true);
    expect(sj.str(sj.pow(I, -1))).toBe('1/Integral(exp(-Trace(_H**2)), _H)');
  });
});

describe('makeArgs (SymPy AssocOp.make_args)', () => {
  it('splits an instance of the class into its arguments', () => {
    expect(sj.Mul.makeArgs(sj.mul(x, y)).map(s)).toEqual(['x', 'y']);
    expect(sj.Add.makeArgs(sj.mul(x, y)).map(s)).toEqual(['x*y']);
    expect(sj.Add.makeArgs(3).map(s)).toEqual(['3']);
  });
});

describe('fromiter and the Add/Mul kinds of extension nodes', () => {
  it('fromiter applies the evaluating constructor (SymPy Add.fromiter([x, y]) is x + y)', () => {
    expect(s(sj.Add.fromiter([x, y]))).toBe('x + y');
    expect(s(sj.Mul.fromiter([x, 2]))).toBe('2*x');
    expect(s(sj.Pow.fromiter([x, 2]))).toBe('x**2');
    expect(() => sj.Sym.fromiter([x])).toThrow('Sym.fromiter is not supported');
    expect(() => sj.Add.fromiter(['x'])).toThrow(TypeError);
  });
  it('isAddLike and isMulLike', () => {
    const [isAddLike, isMulLike] = [nodes.isAddLike, nodes.isMulLike];
    expect([isAddLike(add(x, y)), isAddLike(mul(x, y)), isMulLike(mul(x, y)), isMulLike(x)]).toEqual([true, false, true, false]);
    const lam = sj.Lambda(x, x) as nodes.ExtensionExpr;
    expect(lam.assocOp).toBe('none');
    expect([isAddLike(lam), isMulLike(lam)]).toEqual([false, false]);
    expect(lam.asRealImagSelf()).toBe(undefined);
  });
});


it('lets an extension specify free symbols independently of its displayed arguments', () => {
  class BoundBox extends Box {
    override freeSymbolsSelf(): ReadonlySet<sj.Sym> {
      return new Set([y]);
    }
  }
  // The extension contract permits opaque bound arguments, as in CRootOf.
  // An ordinary extension continues to traverse all its arguments.
  expect([...sj.freeSymbols(new Box([x, y]))]).toEqual([x, y]);
  expect([...sj.freeSymbols(new BoundBox([x]))]).toEqual([y]);
  expect([...sj.freeSymbols(sj.add(new BoundBox([x]), y))]).toEqual([y]);
});

it('provides assumption facts and strict/weak relation variants', async () => {
  const a = await import('../../src');
  const v = new a.Sym('v');
  expect(v.assumptions0).toEqual(new Map([['commutative',true]]));
  expect(new a.Sym('p',{positive:true}).assumptions0.get('finite')).toBe(true);
  expect(new a.Sym('n',{commutative:false}).assumptions0.get('commutative')).toBe(false);
  for (const [op, text, strict, weak] of [['Eq','==','Eq','Eq'],['Ne','!=','Ne','Ne'],['Lt','<','Lt','Le'],['Le','<=','Lt','Le'],['Gt','>','Gt','Ge'],['Ge','>=','Gt','Ge']] as const) {
    const r = new a.Rel(op,v,a.S.One);
    expect(r.relOp).toBe(text); expect(r.strict.op).toBe(strict); expect(r.weak.op).toBe(weak);
  }
  const inner = new a.Integral([v,v]);
  expect(inner.function).toBe(v);
  expect(new a.Integral([inner,v]).function).toBe(v);
});

it('collects only bound variables of nested integrals', async () => {
  const a = await import('../../src');
  const [i,j,k] = a.symbols('i j k');
  const inner = new a.Integral([a.S.One,i!,a.S.One,a.S.Two]);
  const outer = new a.Integral([new a.Integral([inner,j!,a.S.Two]),k!]);
  expect(outer.boundSymbols).toEqual([i,j]);
  expect(new a.Integral([a.S.One,k!]).boundSymbols).toEqual([]);
});

it('Order.contains reports a missing calculus registration', () => {
  const previous = sjImpl.orderContains;
  try {
    sjImpl.orderContains = undefined;
    expect(() => new sj.Order([sj.S.One]).contains(1)).toThrow(sj.NotLoadedError);
  } finally { sjImpl.orderContains = previous; }
});
import { impl as sjImpl } from '../../src/core/nodes';

it('retains constructor facts, explicit false values and their consequences in symbol identities', () => {
  const odd = new sj.Sym('n', { odd: true });
  expect(odd.assumptions.integer).toBe(true);
  expect(odd.assumptions0.get('even')).toBe(false);
  expect(odd.equals(new sj.Sym('n', { integer: true, even: false }))).toBe(true);
  expect(odd.equals(new sj.Sym('n', { even: true }))).toBe(false);
  expect(new sj.Sym('x', { real: false }).equals(new sj.Sym('x'))).toBe(false);
  expect(new sj.Sym('x', { positive: false }).assumptions0.get('positive')).toBe(false);
  expect(new sj.Sym('x', { rational: true }).assumptions.real).toBe(true);
  expect(new sj.Sym('p', { prime: true }).assumptions.positive).toBe(true);
  expect(new sj.Sym('n', { finite: false }).assumptions0.get('infinite')).toBe(true);
  expect(new sj.Sym('x', { commutative: true }).key).toBe(new sj.Sym('x').key);
  const extended = new sj.Sym('x', { extendedPositive: true, aboveFermi: false, belowFermi: false });
  expect(extended.assumptions0.get('extended_positive')).toBe(true);
  expect(extended.assumptions0.get('above_fermi')).toBe(false);
  expect(extended.assumptions0.get('below_fermi')).toBe(false);
  expect(extended.equals(new sj.Sym('x', { extendedPositive: true }))).toBe(false);
  expect(new sj.Sym('p', { aboveFermi: true }).key).toContain('[A');
  expect(new sj.Sym('p', { belowFermi: true }).key).toContain('[B');
  expect(() => new sj.Sym('n', { odd: true, even: true })).toThrow(RangeError);
});

it('recognizes numerical expressions, including definite integrals', () => {
  const x = sj.symbol('x');
  for (const e of [sj.S.Pi, sj.S.I, sj.S.Infinity, sj.parse('sin(1)**2 + cos(1)**2 - 1'), sj.add(2, new sj.Integral([sj.sympify(2), x, sj.S.One, sj.sympify(2)]))]) {
    expect(e.isNumber).toBe(true);
  }
  for (const e of [x, sj.SymFunction('f')(1), sj.add(2, new sj.Integral([sj.sympify(2), x])), sj.parse('sin(x)'), sj.parse('x**2')]) expect(e.isNumber).toBe(false);
});

describe('bitwise operations of integers (SymPy Integer.__lshift__, __rshift__, __and__, __or__, __xor__)', () => {
  const n = (v: number): Rational => Rational.of(v);
  it('shifts and combines the bits like Python integers', () => {
    expect([n(3).lshift(n(2)), n(-3).lshift(2), n(3).lshift(0n)].map(String)).toEqual(['12', '-12', '3']);
    expect([n(12).rshift(2), n(-3).rshift(n(2)), n(3).rshift(2n)].map(String)).toEqual(['3', '-1', '0']);
    expect([n(0b01010101).and(0b11011011), n(-0b01010101).and(n(0b11011011)), n(0b01010101).and(-0b11011011)].map(String)).toEqual(['81', '139', '5']);
    expect([n(0b01010101).or(0b11011011), n(-0b01010101).or(0b11011011)].map(String)).toEqual(['223', '-5']);
    expect([n(0b01010101).xor(0b11011011), n(0b01010101).xor(n(-0b11011011))].map(String)).toEqual(['142', '-144']);
  });
  it('rejects a negative shift count and operands that are not integers', () => {
    expect(() => n(1).lshift(-1)).toThrow(RangeError);
    expect(() => n(1).rshift(n(-1))).toThrow(RangeError);
    expect(() => n(2).lshift(0.5)).toThrow(TypeError);
    expect(() => Rational.of(1, 2).and(1)).toThrow(TypeError);
    expect(() => n(2).or(Rational.of(1, 2))).toThrow(TypeError);
  });
});

describe('func (SymPy Basic.func)', () => {
  const [x, y] = sj.symbols('x y');
  it('is the public constructor of the node and rebuilds it from its arguments', () => {
    const s = sj.add(x, y);
    expect(sj.func(s)).toBe(sj.Add);
    expect(s.func).toBe(sj.Add);
    expect(sj.func(sj.mul(2, x, y))).toBe(sj.Mul);
    expect(sj.func(sj.pow(x, 3))).toBe(sj.Pow);
    for (const e of [s, sj.mul(2, x, y), sj.pow(x, 3), sj.sin(x), sj.log(x), sj.Eq(x, y)]) {
      expect(sj.str(e.func(...e.args))).toBe(sj.str(e));
    }
    // the constructors evaluate, as SymPy's do: Add(x, x) is 2*x
    expect(sj.str(sj.Add(x, x))).toBe('2*x');
    expect(sj.str(sj.Mul(x, x))).toBe('x**2');
    expect(sj.str(sj.Pow(2, 3))).toBe('8');
    expect(sj.str(sj.Add(x, x, { evaluate: false }))).toBe('x + x');
    expect(sj.str(sj.Mul(x, x, { evaluate: false }))).toBe('x*x');
    expect(sj.str(sj.Pow(x, 1, { evaluate: false }))).toBe('x**1');
    expect(() => sj.Add(x, { evaluate: false }, x)).toThrow(TypeError);
  });
  it('is the class of an atom, as in SymPy', () => {
    expect(sj.func(x)).toBe(sj.Sym);
    const d = sj.Dummy('d');
    expect(d.func).toBe(sj.Dummy);
    expect(sj.isPositive(sj.Sym('z', { positive: true }))).toBe(true);
    expect(new sj.Sym('z') instanceof sj.Sym).toBe(true);
  });
  it('is the public function of an applied function', () => {
    expect(sj.func(sj.sin(x))).toBe(sj.sin);
    expect(sj.func(sj.log(x))).toBe(sj.log);
    expect(sj.func(sj.cos(x))).not.toBe(sj.func(sj.sin(x)));
    expect(sj.func(sj.Eq(x, y))).toBe(sj.Eq);
    expect(sj.func(sj.Lt(x, y))).toBe(sj.Lt);
  });
  it('rebuilds a node without a registered constructor like the node', () => {
    const t = sj.Tuple(x, y);
    const head = sj.func(t);
    expect(sj.func(sj.Tuple(1, 2))).toBe(head);
    expect(sj.str(head(1, 2))).toBe('(1, 2)');
    // an applied function without a registered public function keeps its name
    const A = sj.symbol('A', { commutative: false });
    const B = sj.symbol('B', { commutative: false });
    const g = sj.adjoint(A);
    expect(sj.str(sj.func(g)(B))).toBe('adjoint(B)');
    expect(sj.func(sj.adjoint(B))).toBe(sj.func(g));
  });
});

it('matches contiguous noncommuting factors and preserves their order', () => {
  const a = sj.symbol('a', { commutative: false });
  const b = sj.symbol('b', { commutative: false });
  const c = sj.symbol('c', { commutative: false });
  const product = sj.mul(2, a, b, c);
  expect(product.has(sj.mul(a, b))).toBe(true);
  expect(product.has(sj.mul(b, a))).toBe(false);
  expect(product.has(sj.mul(a, c))).toBe(false);
  expect(product.has(sj.mul(3, a))).toBe(false);
  expect(() => Reflect.construct(sj.Sym, ['x', { commutative: null }])).toThrow(RangeError);
  expect(Rational.of(-2).bitNot().p).toBe(1n);
  expect(() => Rational.of(1, 2).bitNot()).toThrow(TypeError);
});

it('exposes symbol forms, integral bounds and optional extension hooks', () => {
  const x = sj.symbol('x');
  expect(x.prettyForm).toBeUndefined();
  expect(x.conjugate().key).toBe(sj.conjugate(x).key);
  expect(new sj.Sym('i', { aboveFermi: true }).key).toContain('A');
  expect(new sj.Sym('j', { belowFermi: true }).key).toContain('B');
  expect(new sj.Integral([x, x, S.Zero, S.One]).limits).toEqual([S.Zero, S.One]);
  expect(new sj.Integral([x, x]).limits).toBeUndefined();
  const box = new Box([x]);
  expect(box.trigsimpSelf((e) => e)).toBeUndefined();
  expect(box.kindSelf()).toBeUndefined();
  expect(box.matchesSelf(x)).toBeUndefined();
  expect(box.expandSelf('custom', {})).toBeUndefined();
});

it('computes rational cofactors and promotes mixed inputs to the wider float precision', () => {
  expect(R(1, 2).cofactors(R(3, 4)).map(String)).toEqual(['1/4', '2', '3']);
  expect(R(0).cofactors(R(-2)).map(String)).toEqual(['2', '0', '-1']);
  expect(() => R(0).cofactors(R(0))).toThrow(RangeError);
  const low = new Float(3, 30);
  const high = new Float(2, 100);
  expect(low.cofactors(high).map((f) => [f.value, f.prec])).toEqual([[1, 100], [3, 100], [2, 100]]);
  expect(R(4).cofactors(high).map((n) => n.key)).toEqual([new Float(1, 100), new Float(4, 100), high].map((f) => f.key));
});

it('preserves explicit rational content and detects nonconcrete derivative counts', () => {
  const x = sj.symbol('x');
  const n = sj.symbol('n');
  expect(Rational.of(2, 4, { gcd: 1n }).q).toBe(4n);
  expect(() => Rational.of(2, 4, { gcd: 0n })).toThrow(RangeError);
  expect(() => Rational.of(3, 4, { gcd: 2n })).toThrow(RangeError);
  expect(() => Rational.of(2, 3, { gcd: 2n })).toThrow(RangeError);
  expect(() => new sj.Derivative([x, x, n]).variableCount).toThrow(RangeError);
  expect(() => new sj.Derivative([x, x, Rational.of(1, 2)]).variableCount).toThrow(RangeError);
  expect(() => new sj.Derivative([x, x, Rational.of(2n ** 55n)]).variableCount).toThrow(RangeError);
  expect(new sj.Derivative([x, x, n]).derivativeOrder.key).toBe(n.key);
});

it('delegates fluent queries and preserves the integral limits', () => {
  expect(x.isComparable).toBe(false);
  expect(pi.isComparable).toBe(true);
  expect(x.expand()).toBe(x);
  expect(x.conjugate().equals(sj.conjugate(x))).toBe(true);
  expect(x.toLatex()).toBe('x');
  expect(new sj.Integral([x, x, S.Zero, S.One]).limits).toEqual([S.Zero, S.One]);
  expect(new sj.Integral([x, x]).limits).toBeUndefined();
});

it('exposes the default extension hooks', () => {
  const box = new Box([x]);
  const identity = (e: Expr) => e;
  expect(box.key).toBe(new Box([x]).key);
  expect(box.printLatex(String)).toBe('\\operatorname{Box}\\left(x\\right)');
  expect(box.trigsimpSelf(identity)).toBeUndefined();
  expect(box.asRealImagSelf()).toBeUndefined();
  expect(box.kindSelf()).toBeUndefined();
  expect(box.expandSelf('complex', {})).toBeUndefined();
  expect(box.doitSelf()).toBeUndefined();
  expect(box.matchesSelf(x)).toBeUndefined();
  expect(box.integrateSelf(x, undefined, identity)).toBeUndefined();
  expect(box.simplifySelf(identity)).toBeUndefined();
});

describe('conversion to JavaScript primitives', () => {
  const x = new sj.Sym('x');
  const asNumber = (e: sj.Expr): number => Number(e);
  it('prints the expression where JavaScript wants a string', () => {
    expect(`${sj.I}`).toBe('I');
    expect('x = ' + String(x)).toBe('x = x');
    expect(['value', x].join(' ')).toBe('value x');
  });
  it('gives the value of a real number', () => {
    expect(asNumber(sj.factorial(50))).toBe(3.0414093201713376e64);
    expect(asNumber(sj.sqrt(2))).toBeCloseTo(Math.SQRT2, 15);
    expect(asNumber(sj.pi)).toBeCloseTo(Math.PI, 15);
  });
  it('rejects JavaScript arithmetic on other expressions', () => {
    const message = /Cannot convert I to a JavaScript number: JavaScript operators .* use the methods \.add\(\)/;
    expect(() => asNumber(sj.I)).toThrow(TypeError);
    expect(() => asNumber(sj.I)).toThrow(message);
    expect(() => asNumber(x)).toThrow(/Cannot convert x to a JavaScript number/);
    expect(() => asNumber(sj.parse('3 + 2*I'))).toThrow(TypeError);
  });
});

describe('subs with a symbol name (SymPy 1.14)', () => {
  const [a, b, c, x] = ['a', 'b', 'c', 'x'].map((n) => new sj.Sym(n)) as [sj.Sym, sj.Sym, sj.Sym, sj.Sym];
  const e = a.mul(x.pow(2)).add(b.mul(x)).add(c);
  it('takes a string as the symbol of that name', () => {
    expect(sj.sstr(e.subs('x', 3))).toBe('9*a + 3*b + c');
    expect(sj.sstr(sj.subs(e, [['x', 3]] as unknown as sj.Substitution))).toBe('9*a + 3*b + c');
    expect(sj.sstr(e.subs({ x: 3 }))).toBe('9*a + 3*b + c');
  });
  it('rejects an old value that is not an expression', () => {
    expect(() => e.subs(globalThis.Symbol('x') as unknown as sj.Expr, 3)).toThrow(sj.SympifyError);
  });
  it('names a symbol without assumptions', () => {
    const y = new sj.Sym('y', { real: true });
    expect(sj.sstr(y.add(1).subs('y', 2))).toBe('y + 1');
  });
});

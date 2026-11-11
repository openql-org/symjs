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
    const subs1 = x.subs.bind(x) as unknown as (from: Expr) => Expr;
    expect(() => subs1(x)).toThrow(TypeError);
  });
  it('checks constructor arguments', () => {
    expect(() => asRational(x)).toThrow(InvariantError);
    expect(() => Rational.of(1, 0)).toThrow(RangeError);
    expect(() => new Float(Infinity)).toThrow(RangeError);
    // SymPy accepts Symbol(''); symjs requires a non-empty name
    expect(() => new sj.Sym('')).toThrow(SyntaxError);
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
    // zero together with a sign is ignored (SymPy raises InconsistentAssumptions)
    expect(new sj.Sym('p', { zero: true, positive: true }).assumptions.zero).toBe(false);
  });
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

it('recognizes numerical expressions, including definite integrals', () => {
  const x = sj.symbol('x');
  for (const e of [sj.S.Pi, sj.S.I, sj.S.Infinity, sj.parse('sin(1)**2 + cos(1)**2 - 1'), sj.add(2, new sj.Integral([sj.sympify(2), x, sj.S.One, sj.sympify(2)]))]) {
    expect(e.isNumber).toBe(true);
  }
  for (const e of [x, sj.SymFunction('f')(1), sj.add(2, new sj.Integral([sj.sympify(2), x])), sj.parse('sin(x)'), sj.parse('x**2')]) expect(e.isNumber).toBe(false);
});

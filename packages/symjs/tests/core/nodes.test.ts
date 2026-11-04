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

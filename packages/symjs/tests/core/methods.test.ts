// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/methods.ts.
// Structural Expr methods: coeff, as_independent, extract_*, as_numer_denom, ... Expected values
// are SymPy 1.14's.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import {
  Expr,
  Float,
  SymFunction,
  abs,
  add,
  asCoefficientsDict,
  asContentPrimitive,
  asIndependent,
  asNumerDenom,
  coeff,
  extractAdditively,
  extractMultiplicatively,
  isConstant,
  isMeromorphic,
  log,
  mul,
  pi,
  pow,
  rational,
  sqrt,
  str,
  symbols,
} from '../../src';
import { InvariantError } from '../../src/core/errors';
import { impl } from '../../src/core/nodes';

const [x, y, z] = symbols('x y z');

const [A, B, C] = ['A', 'B', 'C'].map((n) => new sj.Sym(n, { commutative: false })) as [sj.Sym, sj.Sym, sj.Sym];
const E = sj.parse;
const M = sj.mul;
const Ad = sj.add;
const show = (r: unknown): string => (Array.isArray(r) ? `[${r.map(show).join(', ')}]` : r instanceof Map ? show([...r]) : String(r));

const f = SymFunction('f');
const s = (e: unknown): string => (e instanceof Expr ? str(e) : 'None');
const pairStr = (p: readonly unknown[]): string => `(${p.map(s).join(', ')})`;

describe('keepCoeff and argsCnc', () => {
  it('_keep_coeff', () => {
    expect(String(sj.keepCoeff(E('x + 1'), E('2')))).toBe('2*(x + 1)');
    expect(String(sj.keepCoeff(E('1/2'), E('2*x*y')))).toBe('x*y');
    expect(String(sj.keepCoeff(E('3'), E('x*y')))).toBe('3*x*y');
    expect(String(sj.keepCoeff(E('2'), E('sqrt(2)')))).toBe('2*sqrt(2)');
    expect(String(sj.keepCoeff(x, y))).toBe('x*y');
  });
  it('args_cnc', () => {
    expect(show(sj.argsCncSplit(M(-2, x, A, B)))).toBe('[[-1, 2, x], [A, B]]');
    expect(show(sj.argsCncSplit(M(-2, x, A), false))).toBe('[[-2, x], [A]]');
    expect(show(sj.argsCnc(E('-oo')))).toBe('[-1, oo]');
  });
});

describe('coeff', () => {
  it('commutative', () => {
    expect(String(sj.coeff(E('x + 1'), 0))).toBe('0');
    expect(String(sj.coeff(x, x))).toBe('1');
    expect(String(sj.coeff(x, x, 2))).toBe('0');
    expect(String(sj.coeff(E('x + 2*y + 3'), 1))).toBe('x');
    expect(String(sj.coeff(Ad(M(x, E('y + 1')), 3), E('y + 1'), 0))).toBe('3');
    expect(String(sj.coeff(E('2*x + y + 1'), E('x + y'), 0))).toBe('0');
    expect(String(sj.coeff(E('x**2 + 3*x + 2'), x, 0))).toBe('2');
    expect(String(sj.coeff(E('2*x'), A))).toBe('0');
  });
  it('non-commutative', () => {
    const cases: [sj.Expr, sj.Expr, boolean, string][] = [
      [Ad(M(A, B), M(2, A, C)), A, false, '1'],
      [Ad(M(A, B), M(2, C, A)), A, true, '0'],
      [Ad(M(A, B), M(C, B)), B, true, '1'],
      [Ad(M(x, A), M(y, A)), A, false, 'x + y'],
      [Ad(M(x, A, B), M(y, A, B)), A, false, 'x + y'],
      [Ad(M(x, A, B), M(y, A, B)), B, true, '1'],
      [Ad(M(x, A, B), M(y, A, C)), A, false, '1'],
      [Ad(M(x, A, B), M(y, A, C)), A, true, 'x*B + y*C'],
      [Ad(M(x, B, A), M(y, C, A)), A, false, 'x*B + y*C'],
      [Ad(M(x, B, A), M(y, C, A)), A, true, '1'],
      [Ad(M(A, B), C), B, false, 'A'],
      [Ad(M(A, B, C), C), B, true, 'C'],
      [Ad(M(A, B), M(B, C)), B, false, '0'],
      [M(A, B), C, false, '0'],
      [Ad(A, B), M(x, A, B), false, '0'],
      [Ad(M(A, B), M(A, C), x), M(A, B), false, '1'],
      [Ad(M(x, A, B), A), M(A, B), false, 'x'],
    ];
    for (const [e, c, right, r] of cases) expect(String(sj.coeff(e, c, 1, right))).toBe(r);
  });
});

describe('as_independent, as_coeff_add, as_coeff_mul', () => {
  it('as_independent', () => {
    expect(show(sj.asIndependent(0, [x]))).toBe('[0, 0]');
    expect(show(sj.asIndependent(E('sin(x) + y'), [E('sin(x)')]))).toBe('[y, sin(x)]');
    expect(show(sj.asIndependent(E('2*y + 3'), [E('sin(x)')]))).toBe('[2*y + 3, 0]');
    expect(show(sj.asIndependent(M(x, y, A, B), [y]))).toBe('[x*A*B, y]');
    expect(show(sj.asIndependent(M(x, A, y, B), [A]))).toBe('[x*y, A*B]');
    expect(show(sj.asIndependent(E('x*y*z'), [x], { asAdd: false }))).toBe('[y*z, x]');
    expect(show(sj.asIndependent(E('x*y*z'), [x], { asAdd: true }))).toBe('[0, x*y*z]');
    expect(show(sj.asIndependent(E('x + x*y + z'), [x]))).toBe('[z, x*y + x]');
    expect(show(sj.asIndependent(E('x*y*sin(x)*z'), [x]))).toBe('[y*z, x*sin(x)]');
  });
  it('as_coeff_add / as_coeff_mul', () => {
    expect(show(sj.asCoeffAdd(E('x + 3')))).toBe('[3, [x]]');
    expect(show(sj.asCoeffAdd(3))).toBe('[3, []]');
    expect(show(sj.asCoeffAdd(x))).toBe('[0, [x]]');
    expect(show(sj.asCoeffAdd(E('x + y')))).toBe('[0, [x, y]]');
    expect(show(sj.asCoeffAdd(E('x + y + 3'), [x]))).toBe('[y + 3, [x]]');
    expect(show(sj.asCoeffAdd(E('x*y'), [x]))).toBe('[0, [x*y]]');
    expect(show(sj.asCoeffAdd(y, [x]))).toBe('[y, []]');
    expect(show(sj.asCoeffMul(3))).toBe('[3, []]');
    expect(show(sj.asCoeffMul(E('2*x*y')))).toBe('[2, [x, y]]');
    expect(show(sj.asCoeffMul(E('x*y')))).toBe('[1, [x, y]]');
    expect(show(sj.asCoeffMul(E('2*x*y'), [x]))).toBe('[2*y, [x]]');
    expect(show(sj.asCoeffMul(E('x + y'), [x]))).toBe('[1, [x + y]]');
    expect(show(sj.asCoeffMul(y, [x]))).toBe('[y, []]');
  });
});

describe('primitive and as_content_primitive', () => {
  it('primitive', () => {
    expect(show(sj.primitive(E('2*x + 4*y')))).toBe('[2, x + 2*y]');
    expect(show(sj.primitive(E('x/2 + y/3')))).toBe('[1/6, 3*x + 2*y]');
    expect(show(sj.primitive(E('x + y')))).toBe('[1, x + y]');
    expect(show(sj.primitive(E('x + sqrt(2)*y')))).toBe('[1, x + sqrt(2)*y]');
    expect(show(sj.primitive(0))).toBe('[1, 0]');
    expect(show(sj.primitive(E('-6*x')))).toBe('[6, -x]');
    expect(show(sj.primitive(x))).toBe('[1, x]');
  });
  it('as_content_primitive', () => {
    const acp = (e: sj.Expr, o: { clear?: boolean; radical?: boolean } = {}) => show(sj.asContentPrimitive(e, o));
    expect(acp(E('0'))).toBe('[1, 0]');
    expect(acp(E('-3/2'))).toBe('[3/2, -1]');
    expect(acp(E('2*x + 4'))).toBe('[2, x + 2]');
    expect(acp(E('x/2 + y/3'), { clear: false })).toBe('[1/6, 3*x + 2*y]');
    expect(acp(E('3*x/2 + y'), { clear: false })).toBe('[1, 3*x/2 + y]');
    expect(acp(E('sqrt(2) + 2*sqrt(10)'), { radical: true })).toBe('[1, sqrt(2)*(1 + 2*sqrt(5))]');
    expect(acp(E('sqrt(2) + x'), { radical: true })).toBe('[1, x + sqrt(2)]');
    expect(acp(E('sqrt(2) + sqrt(3)'), { radical: true })).toBe('[1, sqrt(2) + sqrt(3)]');
    expect(acp(M(2, x, Ad(M(3, y), 6)))).toBe('[6, x*(y + 2)]');
    expect(acp(sj.pow(E('2*x + 4'), 2))).toBe('[4, (x + 2)**2]');
    expect(acp(E('2**(x + 3/2)'))).toBe('[2, 2**((2*x + 1)/2)]');
    expect(acp(E('(4*x + 8)**(1/2)'))).toBe('[2, sqrt(x + 2)]');
    expect(acp(E('3**(2*x)'))).toBe('[1, 3**(2*x)]');
    expect(acp(sj.pow(E('2*x*y'), 3))).toBe('[8, x**3*y**3]');
    expect(acp(E('2**(-1/2 + x)'))).toBe('[1/2, 2**((2*x + 1)/2)]');
    expect(acp(E('sin(2*x + 2)'))).toBe('[1, sin(2*x + 2)]');
  });
});

describe('extract_multiplicatively / extract_additively / as_coefficient', () => {
  it('extract_multiplicatively', () => {
    const em = (e: sj.ExprLike | string, c: sj.ExprLike | string) => String(sj.extractMultiplicatively(typeof e === 'string' ? E(e) : e, typeof c === 'string' ? E(c) : c));
    const cases: [sj.ExprLike | string, sj.ExprLike | string, string][] = [
      ['nan', 2, 'NoMatch'],
      [x, 1, 'x'],
      [x, x, '1'],
      ['2*x + 2', '2*x + 2', '1'],
      ['4*x + 4', '2*x + 2', '2'],
      ['6*x*y', '2*x', '3*y'],
      ['6*y', '2*x', 'NoMatch'],
      ['3/2', 3, '1/2'],
      [3, 2, 'NoMatch'],
      [3, -1, 'NoMatch'],
      [3, x, 'NoMatch'],
      [new sj.Float(3), 2, '1.50000000000000'],
      [new sj.Float(3), -2, 'NoMatch'],
      [new sj.Float(3), x, 'NoMatch'],
      ['oo', 2, 'oo'],
      ['oo', -2, 'NoMatch'],
      ['zoo', 2, 'NoMatch'],
      [x, 2, 'NoMatch'],
      [x, 'x/2', '2'],
      ['pi', 2, 'NoMatch'],
      ['2*x', x, '2'],
      ['4*x + 6', 2, '2*x + 3'],
      ['4*x + 6', -2, '-2*x - 3'],
      ['4*x + 6', 4, 'NoMatch'],
      ['x + y', 2, 'NoMatch'],
      ['-x - y', -1, 'x + y'],
      ['2*x + 2*y', 'x + y', '2'],
      ['x*y + x*z', x, 'y + z'],
      ['2*x*y + 2*x*z', x, '2*y + 2*z'],
      ['x*y + z', x, 'NoMatch'],
      ['2*x*sin(y)', 'sin(y)', '2*x'],
      ['2*x*sin(y)', 'cos(y)', 'NoMatch'],
      ['x**3', 'x**2', 'x'],
      ['x**3', x, 'x**2'],
      ['x**y', 'x**z', 'NoMatch'],
      ['x**y', x, 'NoMatch'],
      ['sin(x)', 2, 'NoMatch'],
    ];
    for (const [e, c, r] of cases) expect(em(e, c)).toBe(r);
  });
  it('extract_additively', () => {
    const ea = (e: sj.ExprLike | string, c: sj.ExprLike | string) => String(sj.extractAdditively(typeof e === 'string' ? E(e) : e, typeof c === 'string' ? E(c) : c));
    const cases: [sj.ExprLike | string, sj.ExprLike | string, string][] = [
      ['nan', 2, 'NoMatch'],
      [x, 0, 'x'],
      [x, x, '0'],
      [0, 1, 'NoMatch'],
      [5, 2, '3'],
      [-5, -2, '-3'],
      [5, 7, 'NoMatch'],
      [5, x, 'NoMatch'],
      [5, sj.I, 'NoMatch'],
      ['x + 5', 2, 'x + 3'],
      ['x + 5', 7, 'NoMatch'],
      [x, 2, 'NoMatch'],
      ['2*x + 3', 'x + 1', 'x + 2'],
      ['x + y + 3', 'y + 1', 'x + 2'],
      ['x + 3', 'y + 1', 'NoMatch'],
      ['x + y + 1', 'y + 3', 'NoMatch'],
      [Ad(M(3, E('x + 1')), y), 'x + 1', '2*x + y + 2'],
      [M(-1, E('x + 1')), 'x + 1', 'NoMatch'],
      ['3*x + y', x, '2*x + y'],
      ['2*x*y + z', 'x*y', 'x*y + z'],
      ['-x + y', x, 'NoMatch'],
      ['2*x + 3*y + z', 'x + y', 'x + 2*y + z'],
      ['2*x + z', 'x + y', 'NoMatch'],
      ['-x + 3*y', 'x + y', 'NoMatch'],
    ];
    for (const [e, c, r] of cases) expect(ea(e, c)).toBe(r);
  });
  it('as_coefficient', () => {
    expect(String(sj.asCoefficient(E('2*x'), x))).toBe('2');
    expect(String(sj.asCoefficient(E('2*x + 1'), x))).toBe('NoMatch');
    expect(String(sj.asCoefficient(E('x**2'), x))).toBe('NoMatch');
  });
});

describe('predicates', () => {
  it('is_polynomial, is_rational_function, is_constant, is_algebraic_expr', () => {
    expect(sj.isPolynomial(E('x**2 + sin(y)'), [x])).toBe(true);
    expect(sj.isPolynomial(3)).toBe(true);
    expect(sj.isPolynomial(E('sin(x)'), [x])).toBe(false);
    expect(sj.isPolynomial(E('x**y'), [x, y])).toBe(false);
    expect(sj.isPolynomial(E('x**-1'), [x])).toBe(false);
    expect(sj.isRationalFunction(E('1/x + y'), [x])).toBe(true);
    expect(sj.isRationalFunction(E('oo'))).toBe(false);
    expect(sj.isRationalFunction(3)).toBe(true);
    expect(sj.isRationalFunction(E('2**x'), [x])).toBe(false);
    expect(sj.isRationalFunction(E('sqrt(x)'), [x])).toBe(false);
    expect(sj.isRationalFunction(E('sin(x)'), [x])).toBe(false);
    expect(sj.isConstant(E('sin(x)**2 + cos(x)**2'))).toBe(true);
    expect(sj.isConstant(x)).toBe(false);
    expect(sj.isConstant(2)).toBe(true);
    expect(sj.isConstant(E('x*y'), [z])).toBe(true);
    expect(sj.isConstant(E('x*y'), [y])).toBe(false);
    expect(sj.isAlgebraicExpr(E('sqrt(x) + x**2'), [x])).toBe(true);
    expect(sj.isAlgebraicExpr(E('y + 1'), [x])).toBe(true);
    expect(sj.isAlgebraicExpr(E('sqrt(x) + y'))).toBe(true);
    // SymPy gives None for sin(x)
    expect(sj.isAlgebraicExpr(E('sin(x)'), [x])).toBe(false);
    expect(sj.isAlgebraicExpr(E('x**y'), [x])).toBe(false);
    expect(sj.isAlgebraicExpr(E('x*y**(1/3)'), [x, y])).toBe(true);
  });
  it('has_free, has_xfree', () => {
    expect(sj.hasFree(E('x + y'), y)).toBe(true);
    expect(sj.hasFree(E('f(x) + 1'), { fn: 'f' })).toBe(true);
    expect(sj.hasFree(E('g(x) + 1'), { fn: 'f' })).toBe(false);
    expect(sj.hasFree(E('x + y + 1'), E('y + 1'))).toBe(true);
    expect(sj.hasFree(E('x + y + 1'), E('z + 1'))).toBe(false);
    expect(sj.hasFree(E('2*x*y*z'), E('x*y'))).toBe(true);
    expect(sj.hasFree(E('sin(2*x*y*z)'), E('x*z'))).toBe(true);
    expect(sj.hasFree(E('sin(x)'), E('sin(x)'))).toBe(true);
    expect(sj.hasFree(E('sin(x)'), E('cos(x)'))).toBe(false);
    expect(sj.hasXfree(E('x + sin(y)'), [E('sin(y)')])).toBe(true);
    expect(sj.hasXfree(E('x + sin(y)'), [E('y + 1')])).toBe(false);
  });
  it('is_meromorphic', () => {
    const mero = (e: string, a: string) => sj.isMeromorphic(E(e), x, E(a));
    const cases: [string, string, boolean | 'unknown'][] = [
      ['1/x', '0', true],
      ['log(x)', '0', false],
      ['log(x)', '1', true],
      ['sin(x)', 'oo', false],
      ['sqrt(x)', '0', false],
      ['sqrt(x)', '1', true],
      ['sqrt(x)', 'y', 'unknown'],
      ['sqrt(x)', 'zoo', false],
      ['x**sin(x)', '1', true],
      ['2**x', '1', true],
      ['x**x', '1', true],
      ['log(x)**(1/2)', '0', false],
      ['log(x)**x', '2', true],
      ['x*log(x)', '0', false],
      ['x + gamma(x)', '0', true],
      ['gamma(x)', '0', true],
      ['besselj(x, x)', '0', false],
      ['sin(sqrt(x))', '0', 'unknown'],
      ['sin(x)', 'pi', true],
      ['atan(x)', 'I', false],
      ['atan(x)', '0', true],
      ['atan(x)', 'y', 'unknown'],
      ['sin(x)', 'y', 'unknown'],
      ['y + 1', '0', true],
      ['x', '0', true],
    ];
    for (const [e, a, r] of cases) expect([e, a, mero(e, a)]).toEqual([e, a, r]);
  });
});

describe('as_real_imag, as_numer_denom', () => {
  it('as_real_imag', () => {
    expect(show(sj.asRealImag(E('log(x)')))).toBe('[log(Abs(x)), arg(x)]');
    expect(show(sj.asRealImag(E('exp(x)')))).toBe('[exp(re(x))*cos(im(x)), exp(re(x))*sin(im(x))]');
    expect(show(sj.asRealImag(E('x + I*y')))).toBe('[re(x) - im(y), re(y) + im(x)]');
    expect(show(sj.asRealImag(E('sin(x)')))).toBe('[sin(re(x))*cosh(im(x)), cos(re(x))*sinh(im(x))]');
  });
  it('as_numer_denom', () => {
    const p = new sj.Sym('p', { positive: true });
    const n = new sj.Sym('n', { negative: true });
    const r = new sj.Sym('r', { real: true });
    const k = new sj.Sym('k', { integer: true });
    const q = (u: sj.Expr) => M(x, sj.pow(u, -1));
    const nd = (e: sj.Expr) => show(sj.asNumerDenom(e));
    expect(nd(M(A, B))).toBe('[A*B, 1]');
    expect(nd(E('exp(-x)'))).toBe('[1, exp(x)]');
    expect(nd(E('exp(-2*x*y)'))).toBe('[1, exp(2*x*y)]');
    expect(nd(E('exp(x)'))).toBe('[exp(x), 1]');
    expect(nd(sj.pow(q(y), M(-1, k)))).toBe('[y**k, x**k]');
    expect(nd(sj.pow(q(y), z))).toBe('[(x/y)**z, 1]');
    expect(nd(sj.pow(q(r), z))).toBe('[(x/r)**z, 1]');
    expect(nd(sj.pow(q(p), z))).toBe('[x**z, p**z]');
    expect(nd(sj.pow(q(n), k))).toBe('[(-x)**k, (-n)**k]');
    expect(nd(E('x**(-2*y)'))).toBe('[1, x**(2*y)]');
    expect(nd(E('2*x/3 + 4*y/3'))).toBe('[2*x + 4*y, 3]');
    expect(nd(E('x/y + 1/z'))).toBe('[x*z + y, y*z]');
    expect(nd(E('x/y + z/y'))).toBe('[x + z, y]');
    expect(nd(E('1/2 + x/2'))).toBe('[x + 1, 2]');
    expect(nd(E('sin(x)'))).toBe('[sin(x), 1]');
  });
});

describe('atoms, as_coeff_exponent, powers and coefficient dicts', () => {
  it('atoms and as_coeff_exponent', () => {
    expect(sj.atoms(E('x + 2*y + sin(x)')).map(String).sort()).toEqual(['2', 'x', 'y']);
    expect(sj.atoms(E('x + 2*y + sin(x)'), (q) => q instanceof sj.Sym).map(String).sort()).toEqual(['x', 'y']);
    expect(show(sj.asCoeffExponent(E('3*x**2'), x))).toBe('[3, 2]');
    expect(show(sj.asCoeffExponent(E('3*x'), x))).toBe('[3, 1]');
    expect(show(sj.asCoeffExponent(E('3*sin(x)'), x))).toBe('[3*sin(x), 0]');
    expect(show(sj.asCoeffExponent(E('3*x**y'), x))).toBe('[3, y]');
  });
  it('as_powers_dict, as_coefficients_dict, as_two_terms', () => {
    expect(show(sj.asPowersDict(E('x**2*y**3*x')))).toBe('[[x, 3], [y, 3]]');
    expect(show(sj.asPowersDict(E('2*x**y*z')))).toBe('[[2, 1], [z, 1], [x, y]]');
    const cd = (e: string, s: sj.Expr[] = []) => new Map([...sj.asCoefficientsDict(E(e), s)].map(([k, v]) => [String(k), String(v)]));
    expect(cd('3*x + 2*x*y + 5')).toEqual(new Map([['1', '5'], ['x', '3'], ['x*y', '2']]));
    expect(cd('3*a*x + 2*a*x*y + b*y + 5 + x', [x, y])).toEqual(new Map([['x', '3*a + 1'], ['y', 'b'], ['x*y', '2*a'], ['1', '5']]));
    expect(cd('a*x + b*x', [x])).toEqual(new Map([['x', 'a + b']]));
    expect(cd('x*y + 3', [x])).toEqual(new Map([['x', 'y'], ['1', '3']]));
    expect(show(sj.asTwoTerms(E('x + y + z')))).toBe('[x, y + z]');
    expect(show(sj.asTwoTerms(E('2*x*y')))).toBe('[2, x*y]');
    expect(show(sj.asTwoTerms(x))).toBe('[1, x]');
  });
});

describe('equal_valued, is_same, dummy_eq, as_terms', () => {
  it('equal_valued and is_same', () => {
    expect(sj.equalValued(new sj.Float(2), 2)).toBe(true);
    expect(sj.equalValued(new sj.Float(2.5), E('5/2'))).toBe(true);
    expect(sj.equalValued(x, x)).toBe(true);
    expect(sj.equalValued(new sj.Float(0.1), E('1/10'))).toBe(false);
    expect(sj.equalValued(new sj.Float(4), 2)).toBe(false);
    // SymPy: Float(0.1, 9) and Float(0.1, 10) round 0.1 to different binary values, so
    // equal_valued and is_same(..., equal_valued) are False
    const f9 = new sj.Float(0.1, 33);
    const f10 = new sj.Float(0.1, 37);
    expect(sj.equalValued(f9, f10)).toBe(false);
    expect(sj.isSame(f9, f10, sj.equalValued)).toBe(false);
    expect(sj.isSame(f9, new sj.Float(0.1, 33), sj.equalValued)).toBe(true);
    const fx = M(new sj.Float(2), x);
    expect(sj.isSame(fx, E('2*x'))).toBe(false);
    expect(sj.isSame(fx, E('2*x'), sj.equalValued)).toBe(true);
    expect(sj.isSame(fx, E('3*x'), sj.equalValued)).toBe(false);
    expect(sj.isSame(3, 3)).toBe(true);
    expect(sj.isSame(sj.Matrix.of([[1]]), sj.Matrix.of([[1]]))).toBe(true);
  });
  it('dummy_eq', () => {
    const d = new sj.Dummy('d');
    const e = new sj.Dummy('e');
    expect(sj.dummyEq(Ad(d, 1), Ad(x, 1))).toBe(true);
    expect(sj.dummyEq(Ad(d, 1), Ad(x, 2))).toBe(false);
    expect(sj.dummyEq(Ad(d, y), Ad(x, y), x)).toBe(true);
    expect(sj.dummyEq(Ad(d, y), Ad(x, z))).toBe(false);
    expect(sj.dummyEq(Ad(d, e), Ad(x, y))).toBe(false);
    expect(sj.dummyEq(Ad(x, 1), Ad(x, 1))).toBe(true);
  });
  it('as_terms', () => {
    const at = (e: sj.Expr) => JSON.stringify(sj.asTerms(e), (_k, v: unknown) => (v instanceof sj.Expr ? String(v) : v));
    expect(at(E('3*x**2 + 2*I*y + sin(x)'))).toBe(
      '[[["2*I*y",[[0,2],[0,1,0],[]]],["3*x**2",[[3,0],[2,0,0],[]]],["sin(x)",[[1,0],[0,0,1],[]]]],["x","y","sin(x)"]]',
    );
    expect(at(Ad(M(2, x, A), y))).toBe('[[["y",[[1,0],[0,1],[]]],["2*x*A",[[2,0],[1,0],["A"]]]],["x","y"]]');
    expect(at(E('x**(3/2) + x**(2*y) + x**y'))).toBe('[[["x**y",[[1,0],[0,1],[]]],["x**(2*y)",[[1,0],[0,2],[]]],["x**(3/2)",[[1,0],[3,0],[]]]],["sqrt(x)","x**y"]]');
    expect(at(E('sqrt(2)*x + pi'))).toBe('[[["pi",[[3.141592653589793,0],[0],[]]],["sqrt(2)*x",[[1.4142135623730951,0],[1],[]]]],["x"]]');
  });
});

describe('further cases', () => {
  it('keepCoeff, coeff and as_independent edge cases', () => {
    expect(String(sj.keepCoeff(sj.S.Zero, x))).toBe('0*x');
    expect(String(sj.keepCoeff(E('1/2'), E('2*x')))).toBe('x');
    expect(String(sj.coeff(E('x + y'), 1))).toBe('x + y');
    expect(String(sj.coeff(E('2*x + 3*y'), 1))).toBe('0');
    expect(String(sj.coeff(E('2*x + 2*y + 1'), E('x + y'), 0, true))).toBe('0');
    expect(String(sj.coeff(Ad(M(2, A, B), M(2, A, C)), A, 1, true))).toBe('B + C');
    expect(String(sj.coeff(M(A, B), M(x, C)))).toBe('0');
    expect(String(sj.coeff(Ad(M(x, A), M(y, B)), M(A, B)))).toBe('0');
    expect(String(sj.coeff(Ad(M(x, A), y), A))).toBe('x');
    expect(show(sj.asIndependent(E('y*z'), [x]))).toBe('[y*z, 1]');
    expect(show(sj.asCoeffMul(x))).toBe('[1, [x]]');
    expect(show(sj.primitive(M(new sj.Float(2.5), x)))).toBe('[1, 2.5*x]');
  });
  it('extract_* edge cases', () => {
    expect(String(sj.extractMultiplicatively(E('6*x*y*z'), E('2*x*y')))).toBe('3*z');
    expect(String(sj.extractMultiplicatively(E('3*x'), E('2*y')))).toBe('NoMatch');
    expect(String(sj.extractMultiplicatively(E('pi'), E('pi/2')))).toBe('2');
    expect(String(sj.extractMultiplicatively(E('4*x + 6'), -4))).toBe('NoMatch');
    expect(String(sj.extractMultiplicatively(sj.pow(E('x**y'), z), E('x**y')))).toBe('NoMatch');
    expect(String(sj.extractAdditively(M(E('y + 2'), E('x + 1')), E('x + 1')))).toBe('(x + 1)*(y + 1)');
  });
  it('as_coefficients_dict and as_terms edge cases', () => {
    expect(show(sj.asCoefficientsDict(E('3*x')))).toBe('[[x, 3]]');
    expect(show(sj.asCoefficientsDict(E('5'), [x]))).toBe('[[1, 5]]');
    expect(new Map([...sj.asCoefficientsDict(E('x*y + 2*x'), [x, y])].map(([k, v]) => [String(k), String(v)]))).toEqual(
      new Map([['x', '2'], ['x*y', '1']]),
    );
    const at = (e: sj.Expr) => JSON.stringify(sj.asTerms(e), (_k, v: unknown) => (v instanceof sj.Expr ? String(v) : v));
    expect(at(E('3 + x'))).toBe('[[["3",[[3,0],[0],[]]],["x",[[1,0],[1],[]]]],["x"]]');
    expect(at(E('2*x'))).toBe('[[["2*x",[[2,0],[1],[]]]],["x"]]');
  });
  it('is_meromorphic edge cases', () => {
    const mero = (e: string, a: string) => sj.isMeromorphic(E(e), x, E(a));
    const cases: [string, string, boolean | 'unknown'][] = [
      ['cos(x)', '0', true],
      ['sqrt(x)', 'oo', false],
      ['sqrt(x)', '-oo', false],
      ['x + sqrt(x)', 'y', 'unknown'],
      ['log(x)**log(x)', '0', 'unknown'],
      ['sqrt(x)**sqrt(x)', 'y', 'unknown'],
      ['2**log(x)', '0', false],
      ['Abs(x)', '0', false],
      ['re(x)', '1', false],
      ['floor(x)', '0', 'unknown'],
      ['tan(x)', '0', true],
      ['cot(x)', 'oo', false],
      // sinh, cosh and erf are entire: SymPy leaves these undecided (None)
      ['sinh(x)', '0', true],
      ['cosh(x)', 'zoo', false],
      ['erf(x)', '1', true],
      ['erfc(x)', '0', 'unknown'],
    ];
    for (const [e, a, r] of cases) expect([e, a, mero(e, a)]).toEqual([e, a, r]);
  });
  it('the core reaches higher layers through registered hooks', () => {
    const hooks: { fn?: unknown; expandMul?: unknown; asRealImagExpand?: unknown } = impl;
    const saved = { ...hooks };
    try {
      hooks.fn = undefined;
      expect(() => sj.asRealImag(E('log(x)'))).toThrow(InvariantError);
      hooks.fn = saved.fn;
      hooks.expandMul = undefined;
      expect(() => sj.asRealImag(E('x + y'))).toThrow(InvariantError);
      hooks.expandMul = saved.expandMul;
      hooks.asRealImagExpand = undefined;
      expect(() => sj.asRealImag(E('sin(x)'))).toThrow(InvariantError);
    } finally {
      Object.assign(hooks, saved);
    }
  });
});

describe('coeff', () => {
  it('takes the independent part of a sum with right', () => {
    const e = add(mul(z, add(x, 1)), 3);
    expect(s(coeff(e, add(x, 1), 0, true))).toBe('3');
    expect(s(coeff(e, add(x, 1), 0))).toBe('3');
  });
  it('finds no coefficient of a noncommutative factor that is absent', () => {
    expect(s(coeff(mul(A, B), mul(2, C)))).toBe('0');
    expect(s(coeff(add(mul(A, B), 2), C))).toBe('0');
    expect(s(coeff(add(mul(A, B), x), C))).toBe('0');
    // (A*B + 2).coeff(C, 1, False, False): the term 2 has no noncommutative part
    expect(s(coeff(add(mul(A, B), 2), C, 1, false, false))).toBe('0');
  });
});

describe('asContentPrimitive of powers', () => {
  it('takes the content out of a power of a sum', () => {
    expect(pairStr(asContentPrimitive(sqrt(add(mul(4, x), mul(4, y)))))).toBe('(2, sqrt(x + y))');
    // 4**(3/4) = 2*sqrt(2) is not a power with the exponent 3/4: the power stays as it is
    expect(pairStr(asContentPrimitive(pow(add(mul(4, x), mul(4, y)), rational(3, 4))))).toBe('(1, 2*sqrt(2)*(x + y)**(3/4))');
    expect(pairStr(asContentPrimitive(pow(add(mul(2, x), mul(2, y)), rational(3, 2))))).toBe('(1, 2*sqrt(2)*(x + y)**(3/2))');
    expect(pairStr(asContentPrimitive(pow(add(mul(2, x), mul(2, y)), rational(1, 3))))).toBe('(1, 2**(1/3)*(x + y)**(1/3))');
  });
  it('takes the integer part of a rational exponent of a number', () => {
    expect(pairStr(asContentPrimitive(pow(2, add(x, rational(3, 2)))))).toBe('(2, 2**((2*x + 1)/2))');
    expect(pairStr(asContentPrimitive(pow(4, add(x, rational(1, 2)))))).toBe('(2, 4**x)');
    expect(pairStr(asContentPrimitive(pow(2, add(x, rational(-3, 2)))))).toBe('(1/4, 2**((2*x + 1)/2))');
  });
});

describe('extractMultiplicatively', () => {
  it('extracts from symbols, constants and powers', () => {
    expect(s(extractMultiplicatively(x, rational(1, 2)))).toBe('2*x');
    expect(s(extractMultiplicatively(pi, mul(pi, rational(1, 2))))).toBe('2');
    expect(s(extractMultiplicatively(pi, 3))).toBe('None');
    expect(s(extractMultiplicatively(pow(pow(x, y), add(z, 1)), pow(x, y)))).toBe('(x**y)**z');
  });
});

describe('extractAdditively', () => {
  it('extracts from numbers', () => {
    expect(s(extractAdditively(3, 1))).toBe('2');
    expect(s(extractAdditively(3, -1))).toBe('None');
    expect(s(extractAdditively(-3, -1))).toBe('-2');
    expect(s(extractAdditively(-3, 1))).toBe('None');
    expect(s(extractAdditively(3, 4))).toBe('None');
    expect(s(extractAdditively(new Float(2.5), 1))).toBe('1.50000000000000');
  });
  it('takes c off once when the rest contains it', () => {
    // e - (x + 1) = z + (x + 1)*(y + 2); SymPy 1.14 answers z + (x + 1)*(y + 1), which is e - 2*(x + 1)
    const e = add(mul(add(y, 2), add(x, 1)), x, 1, z);
    expect(s(extractAdditively(e, add(x, 1)))).toBe('x + z + (x + 1)*(y + 1) + 1');
    // SymPy: x + y + (x + y)*(z + 1)
    expect(s(extractAdditively(add(mul(add(z, 2), add(x, y)), x, y), add(x, y)))).toBe('x + y + (x + y)*(z + 1)');
  });
});

describe('other methods', () => {
  it('isConstant is false when the derivative is not known', () => {
    expect(isConstant(abs(x))).toBe(false);
  });
  it('isConstant is false when the derivative cannot be taken', () => {
    // diff of a product whose limits depend on x is not implemented; SymPy: Product(k, (k, 1, x)).is_constant() = False
    expect(isConstant(E('Product(k, (k, 1, x))'))).toBe(false);
  });
  it('asNumerDenom of a sum', () => {
    expect(pairStr(asNumerDenom(add(mul(x, rational(1, 2)), mul(y, rational(1, 3)))))).toBe('(3*x + 2*y, 6)');
  });
  it('asNumerDenom of exp (SymPy ExpBase.as_numer_denom)', () => {
    // SymPy 1.14: exp(-x - 1) -> (1, exp(x + 1)), exp(1 - x) -> (1, exp(x - 1)), exp(x - 1) -> (exp(x - 1), 1),
    // exp(-x - I) -> (1, exp(x + I)), exp(-n) -> (exp(-n), 1) and exp(-n - 1) -> (1, exp(n + 1)) for a negative n
    const n = new sj.Sym('n', { negative: true });
    const P = (src: string) => sj.parse(src, { locals: { n } });
    expect(['exp(-x - 1)', 'exp(1 - x)', 'exp(x - 1)', 'exp(-x - I)', 'exp(-n)', 'exp(-n - 1)', 'exp(-pi)'].map((e) => pairStr(asNumerDenom(P(e))))).toEqual([
      '(1, exp(x + 1))', '(1, exp(x - 1))', '(exp(x - 1), 1)', '(1, exp(x + I))', '(exp(-n), 1)', '(1, exp(n + 1))', '(1, exp(pi))',
    ]);
  });
  it('asCoefficientsDict of a sum', () => {
    const d = asCoefficientsDict(add(mul(2, x), mul(3, y), 4));
    expect([...d].map(([k, v]) => `${s(k)}: ${s(v)}`).sort()).toEqual(['1: 4', 'x: 2', 'y: 3']);
  });
  it('isMeromorphic is unknown for undefined functions and unknown zeros', () => {
    // SymPy None
    expect(isMeromorphic(f(x), x, 0)).toBe('unknown');
    // log(4) - 2*log(2) is zero, but its is_zero is None in SymPy
    expect(isMeromorphic(log(x), x, add(log(4), mul(-2, log(2))))).toBe('unknown');
  });
  it('isMeromorphic of a power whose base is undecided is unknown', () => {
    // SymPy (floor(x)**y).is_meromorphic(x, 0) is None
    expect(isMeromorphic(sj.parse('floor(x)**y'), x, 0)).toBe('unknown');
  });
});

describe('coeff and as_independent with non-commutative symbols (SymPy)', () => {
  const [n, m, n1, n2, n3] = symbols('n m n1 n2 n3', { commutative: false });
  it('coeff', () => {
    expect(String(coeff(add(mul(n, m), mul(m, n, m)), n))).toBe('1 + m');
    expect(String(coeff(add(mul(n, m), mul(m, n, m)), n, 1, true))).toBe('m');
    expect(String(coeff(add(mul(n, m), mul(m, n)), n))).toBe('0');
    expect(String(coeff(add(mul(n, m), mul(x, m, n)), mul(m, n)))).toBe('x');
    expect(String(coeff(add(mul(n, m), mul(x, m, n)), mul(m, n), 1, true))).toBe('1');
  });
  it('as_independent', () => {
    expect(asIndependent(mul(n1, n2, n3), [n1]).map(String)).toEqual(['1', 'n1*n2*n3']);
    expect(asIndependent(mul(n1, n2, n3), [n2]).map(String)).toEqual(['n1', 'n2*n3']);
  });
});

describe('Basic and Expr methods without structure of their own (SymPy)', () => {
  const R = (n: number) => sj.Rational.of(n);
  it('as_dummy', () => {
    // SymPy Integral(x, (x, 1, 2)).as_dummy() is Integral(_0, (_0, 1, 2))
    expect(s(sj.asDummy(new sj.Integral([x, x, R(1), R(2)])))).toBe('Integral(_0, (_0, 1, 2))');
    expect(s(sj.asDummy(sj.Lambda(x, Ad(x, y))))).toBe('Lambda(_0, _0 + y)');
    expect(s(sj.asDummy(Ad(x, y)))).toBe('x + y');
    expect(s(sj.asDummy(R(3)))).toBe('3');
    expect(s(sj.asDummy(new sj.Integral([x, x])))).toBe('Integral(x, x)');
    // a bound symbol that is also free in the limits is masked: Integral(_0*y, (_0, 0, x))
    expect(s(sj.asDummy(new sj.Integral([M(x, y), x, R(0), x])))).toBe('Integral(_0*y, (_0, 0, x))');
    // nested objects get distinct canonical symbols (SymPy Integral(_0*_1, (_0, 1, _1), (_1, 0, 1)))
    expect(s(sj.asDummy(new sj.Integral([new sj.Integral([M(x, y), x, R(1), y]), y, R(0), R(1)])))).toBe('Integral(_0*_1, (_0, 1, _1), (_1, 0, 1))');
    // the canonical names avoid the free symbols: SymPy Lambda(x, x + _0).as_dummy() is Lambda(_1, _0 + _1)
    expect(s(sj.asDummy(sj.Lambda(x, Ad(x, new sj.Sym('_0')))))).toBe('Lambda(_1, _0 + _1)');
    const r = sj.asDummy(new sj.Sym('r', { real: true }));
    expect(r).toBeInstanceOf(sj.Dummy);
    expect(s(r)).toBe('_r');
    expect(sj.isReal(r)).toBe('unknown');
    expect(sj.asDummy(A).isCommutative).toBe(false);
  });
  it('as_expr, copy, removeO, normal, prod', () => {
    expect(s(sj.asExpr(Ad(x, y), x))).toBe('x + y');
    expect(s(sj.copy(Ad(x, y)))).toBe('x + y');
    const o = sj.O(x.pow(2));
    expect(s(sj.removeO(Ad(1, x, o)))).toBe('x + 1');
    expect(s(sj.removeO(o))).toBe('0');
    expect(s(sj.removeO(x))).toBe('x');
    expect(s(sj.normal(Ad(x.div(y), 1)))).toBe('(x + y)/y');
    expect(s(sj.normal(Ad(sj.pow(Ad(x, 1), -1), 2)))).toBe('(2*x + 3)/(x + 1)');
    expect(s(sj.normal(Ad(x.div(2), y.div(2))))).toBe('(x + y)/2');
    expect(s(sj.normal(x))).toBe('x');
    expect([sj.prod([1, 2, 3]), sj.prod([x, y]), sj.prod([]), sj.prod([2, 3], x)].map(s)).toEqual(['6', 'x*y', '1', '6*x']);
  });
  it('nseries', () => {
    expect(s(sj.nseries(sj.sin(x), x, 0, 6))).toBe('x - x**3/6 + x**5/120 + O(x**6)');
    expect(s(sj.nseries(sj.cos(x)))).toBe('1 - x**2/2 + x**4/24 + O(x**6)');
    expect(s(sj.nseries(sj.exp(x), y))).toBe('exp(x)');
    expect(s(sj.nseries(R(2)))).toBe('2');
    expect(() => sj.nseries(Ad(x, y))).toThrow('x must be given for multivariate functions.');
  });
  it('rcall', () => {
    const z2 = new sj.Sym('z');
    expect(s(sj.rcall(sj.Lambda(y, y.pow(2)), 2))).toBe('4');
    expect(s(sj.rcall(Ad(x, y), 2))).toBe('x + y');
    // SymPy (x + Lambda(y, 2*y)).rcall(z) is x + 2*z
    expect(s(sj.rcall(Ad(x, sj.Lambda(y, M(2, y))), z2))).toBe('x + 2*z');
    expect(s(sj.rcall(f(x), y))).toBe('f(x)');
  });
});

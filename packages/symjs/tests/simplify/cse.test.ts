// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/simplify/cse.ts (SymPy sympy/simplify/cse_main.py).

// Expected values are the str() forms printed by SymPy 1.14 (sympy/simplify/tests/test_cse.py and
// cse runs of SymPy) unless a comment says otherwise.

import { describe, expect, it } from 'vitest';
import {
  CRootOf,
  Dummy,
  Wild,
  Idx,
  IndexedBase,
  Eq,
  Expr,
  Inverse,
  MatAdd,
  MatMul,
  MatPow,
  Matrix,
  MatrixSymbol,
  Mul,
  MutableDenseMatrix,
  Rational,
  Transpose,
  UnevaluatedExpr,
  add,
  cos,
  cse,
  exp,
  mul,
  numberedSymbols,
  parse,
  pow,
  series,
  sin,
  str,
  sub,
  subs,
  symbol,
  symbols,
} from '../../src';
import type { CseReduced, CseReplacement } from '../../src';
import { FuncArgTracker, basicCompare, cseSeparate, postprocessForCse, preprocessForCse, repsToposort, sympyArgs, sympyClassBases, sympyClassName } from '../../src/simplify/cse';
import { MatMulNode, MatrixSymbolNode } from '../../src/matrices/expressions/matexpr';
import { subPost, subPre } from '../../src/simplify/exprtools';

const [x, y, z] = symbols('x y z');

const fmt = (v: unknown): string => (v instanceof Expr ? str(v) : v instanceof Matrix ? v.toString() : String(v));
const show = ([r, e]: [CseReplacement[], CseReduced[]]): string => `([${r.map(([s, v]) => `(${str(s)}, ${str(v)})`).join(', ')}], [${e.map(fmt).join(', ')}])`;

/** [exprs, options, SymPy's str(cse(exprs, **options))]. */
const TABLE: [string | string[], { optimizations?: 'basic'; ignore?: string[]; order?: 'none' }, string][] = [
  ["(x + y)**2 + sqrt(x + y)", {}, "([(x0, x + y)], [sqrt(x0) + x0**2])"],
  ["42", {}, "([], [42])"],
  ["x + y", {}, "([], [x + y])"],
  ["(w*x + y)**2 + sqrt(w*x + y)", {}, "([(x0, w*x + y)], [sqrt(x0) + x0**2])"],
  ["((w + x + y + z)*(w - y - z))/(w + x)**3", {}, "([(x0, w + x), (x1, y + z)], [(w - x1)*(x0 + x1)/x0**3])"],
  ["((w + x + y + z)*(w + y + z))/(w + x)**3", {}, "([(x0, y + z), (x1, w + x)], [(w + x0)*(x0 + x1)/x1**3])"],
  [["(x + y)*z", "(x + y)*w"], {}, "([(x0, x + y)], [x0*z, w*x0])"],
  [["w*x*y + z", "w*y"], {}, "([(x0, w*y)], [x*x0 + z, x0])"],
  [["w*y", "w*x*y + z"], {}, "([(x0, w*y)], [x0, x*x0 + z])"],
  [["w*x*y", "w*x*y + z", "w*y"], {}, "([(x0, w*y), (x1, x*x0)], [x1, x1 + z, x0])"],
  [["w*y", "w*x*y + z", "w*x*y"], {}, "([(x0, w*y), (x1, x*x0)], [x0, x1 + z, x1])"],
  [["(x - z)*(y - z)", "x - z", "y - z"], {}, "([(x0, -z), (x1, x + x0), (x2, x0 + y)], [x1*x2, x1, x2])"],
  [["y - z", "x - z", "(x - z)*(y - z)"], {}, "([(x0, -z), (x1, x0 + y), (x2, x + x0)], [x1, x2, x1*x2])"],
  [["w*y + w + x + y + z", "w*x*y"], {}, "([(x0, w*y)], [w + x + x0 + y + z, x*x0])"],
  [["x + y", "x + y + z"], {}, "([(x0, x + y)], [x0, x0 + z])"],
  [["x + y", "x + z"], {}, "([], [x + y, x + z])"],
  [["x*y", "z + x*y", "x*y*z + 3"], {}, "([(x0, x*y)], [x0, x0 + z, x0*z + 3])"],
  ["w/(x - y) + z/(y - x)", {"optimizations": "basic"}, "([], [(w - z)/(x - y)])"],
  ["x**5 + x**4 + x**3 + x**2", {"optimizations": "basic"}, "([(x0, x**2)], [x0*(x**3 + x + x0 + 1)])"],
  ["sin(x**x)/x**x", {}, "([(x0, x**x)], [sin(x0)/x0])"],
  ["1/x**2 + x**2", {}, "([(x0, x**2)], [x0 + 1/x0])"],
  ["x**2 + (1 + 1/x**2)/x**2", {}, "([(x0, x**2), (x1, 1/x0)], [x0 + x1*(x1 + 1)])"],
  ["1/x**2 + (1 + 1/x**2)*x**2", {}, "([(x0, x**2), (x1, 1/x0)], [x0*(x1 + 1) + x1])"],
  ["cos(1/x**2) + sin(1/x**2)", {}, "([(x0, x**(-2))], [sin(x0) + cos(x0)])"],
  ["cos(x**2) + sin(x**2)", {}, "([(x0, x**2)], [sin(x0) + cos(x0)])"],
  ["y/(2 + x**2) + z/x**2/y", {}, "([(x0, x**2)], [y/(x0 + 2) + z/(x0*y)])"],
  ["exp(x**2) + x**2*cos(1/x**2)", {}, "([(x0, x**2)], [x0*cos(1/x0) + exp(x0)])"],
  ["(1 + 1/x**2)/x**2", {}, "([(x0, x**(-2))], [x0*(x0 + 1)])"],
  ["x**(2*y) + x**(-2*y)", {}, "([(x0, x**(2*y))], [x0 + 1/x0])"],
  [["x + 3", "x + 4"], {}, "([], [x + 3, x + 4])"],
  [["x + y", "2 + x + y", "x + y + z", "3 + x + y + z"], {}, "([(x0, x + y), (x1, x0 + z)], [x0, x0 + 2, x1, x1 + 3])"],
  ["x/(-4*x**2 + y**2)", {}, "([], [x/(-4*x**2 + y**2)])"],
  [["y**2*(x + 1)", "3*y**2*(x + 1)"], {"ignore": ["y"]}, "([(x0, x + 1)], [x0*y**2, 3*x0*y**2])"],
  [["exp(y)*(3*y + 3*sqrt(x+1))", "exp(y)*(5*y + 5*sqrt(x+1))"], {}, "([(x0, exp(y)), (x1, sqrt(x + 1))], [x0*(3*x1 + 3*y), x0*(5*x1 + 5*y)])"],
  [["exp(y)*(3*y + 3*sqrt(x+1))", "exp(y)*(5*y + 5*sqrt(x+1))"], {"ignore": ["y"]}, "([(x0, sqrt(x + 1))], [(3*x0 + 3*y)*exp(y), (5*x0 + 5*y)*exp(y)])"],
  [["w*exp(x)*exp(-z)", "exp(y)*exp(x)*exp(-z)"], {"ignore": ["x"]}, "([(x0, exp(-z))], [w*x0*exp(x), x0*exp(x)*exp(y)])"],
  ["Piecewise((-z + x*y, Eq(y, 0)), (-z - x*y, True))", {}, "([(x0, x*y)], [Piecewise((x0 - z, Eq(y, 0)), (-x0 - z, True))])"],
  [["(x - y)*(z - y) + exp((x - y)*(z - y))"], {"optimizations": "basic"}, "([(x0, (x - y)*(y - z))], [-x0 + exp(-x0)])"],
  [["-(x - y)*(z - y) + exp(-(x - y)*(z - y))"], {"optimizations": "basic"}, "([(x0, (x - y)*(y - z))], [x0 + exp(x0)])"],
  ["(-1 + 1/x)/x/(1 - 1/x)**2 - 1/(-1 + 1/x)/x", {"optimizations": "basic"}, "([], [0])"],
  ["exp(x) + exp(-x) + exp(2*x)", {}, "([], [exp(2*x) + exp(x) + exp(-x)])"],
  ["exp(x + y) + sin(x + y) + exp(-x - y)", {}, "([(x0, x + y)], [exp(x0) + sin(x0) + exp(-x0)])"],
  [["a*b*f*k*l", "a*i*k**2*l", "f*i*k**2*l"], {}, "([(x0, a*l), (x1, i*k**2)], [b*f*k*x0, x0*x1, f*l*x1])"],
  [["a + b + c + d", "a + b + c + e", "a + b + f", "b + c + d + e"], {}, "([(x0, a + b), (x1, c + x0)], [d + x1, e + x1, f + x0, b + c + d + e])"],
  [["a*b*c*d", "a*b*c*e", "a*b*f", "b*c*d*e"], {}, "([(x0, a*b), (x1, c*x0)], [d*x1, e*x1, f*x0, b*c*d*e])"],
  [["x*y*z + x*y", "x*y*z*w", "sin(x*y)"], {}, "([(x0, x*y), (x1, x0*z)], [x0 + x1, w*x1, sin(x0)])"],
  [["x*y*z + x*y", "x*y*z*w", "sin(x*y)"], {"order": "none"}, "([(x0, x*y), (x1, x0*z)], [x0 + x1, w*x1, sin(x0)])"],
  [["(x + y)*(x - y)", "(x - y)**2", "1/(x - y)"], {}, "([(x0, x - y)], [x0*(x + y), x0**2, 1/x0])"],
  [["-x - y", "x + y", "-2*x - 2*y + z"], {}, "([(x0, x + y)], [-x0, x0, -2*x - 2*y + z])"],
  [["2*x*y", "-2*x*y", "3*x*y*z"], {}, "([(x0, x*y), (x1, 2*x0)], [x1, -x1, 3*x0*z])"],
  [["x**(-2) + y", "x**(-2)*z", "x**2"], {}, "([(x0, x**2), (x1, 1/x0)], [x1 + y, x1*z, x0])"],
  [["sqrt(x)*y + sqrt(x)", "1/sqrt(x)"], {}, "([(x0, sqrt(x))], [x0*y + x0, 1/x0])"],
  [["Eq(x + y, z)", "x + y"], {}, "([(x0, x + y)], [Eq(x0, z), x0])"],
  [["F(x + y) + G(x + y)"], {}, "([(x0, x + y)], [F(x0) + G(x0)])"],
  [["cos(x)*sin(x) + cos(x)**2", "sin(x)*cos(x)"], {}, "([(x0, cos(x)), (x1, x0*sin(x))], [x0**2 + x1, x1])"],
  [["x**2*y**2 + x*y", "x**2*y**2*z"], {}, "([(x0, x**2*y**2)], [x*y + x0, x0*z])"],
  [["(a + b)*(c + d) + (a + b)*(c + e)", "a + b + c"], {}, "([(x0, a + b)], [x0*(c + d) + x0*(c + e), c + x0])"],
  [["x - y + z - w", "y - x + w - z", "x - y"], {}, "([(x0, w - x + y - z)], [-x0, x0, x - y])"],
  [["1/(x + y) + 1/(x + y)**2", "x + y"], {}, "([(x0, x + y)], [1/x0 + x0**(-2), x0])"],
  [["2*x + 2*y", "4*x + 4*y"], {"optimizations": "basic"}, "([(x0, x + y)], [2*x0, 4*x0])"],
  [["x0 + y", "cos(x0 + y)", "x1 + x2"], {}, "([(x3, x0 + y)], [x3, cos(x3), x1 + x2])"],
  [["I*x + I*y", "exp(I*x + I*y)"], {}, "([(x0, I*x + I*y)], [x0, exp(x0)])"],
  [["pi*x + pi*y", "sin(pi*x + pi*y)"], {}, "([(x0, pi*x + pi*y)], [x0, sin(x0)])"],
  [["x*y*z", "x*y*w", "x*z*w", "y*z*w"], {}, "([(x0, x*y), (x1, w*z)], [x0*z, w*x0, x*x1, x1*y])"],
  [["x + y + z", "x + y + w", "x + z + w", "y + z + w"], {}, "([(x0, x + y), (x1, w + z)], [x0 + z, w + x0, x + x1, x1 + y])"],
  [["x*y", "y*z", "x*z", "x*y*z"], {}, "([(x0, x*y)], [x0, y*z, x*z, x0*z])"],
  [["x + y", "y + z", "x + z", "x + y + z"], {}, "([(x0, x + y)], [x0, y + z, x + z, x0 + z])"],
  [["x**y + x**(2*y)", "x**(-y)"], {}, "([(x0, x**y)], [x**(2*y) + x0, 1/x0])"],
  [["Abs(x + y) + sign(x + y)", "x + y"], {}, "([(x0, x + y)], [Abs(x0) + sign(x0), x0])"],
  [["1.5*x + 1.5*y", "sin(1.5*x + 1.5*y)"], {}, "([(x0, 1.5*x + 1.5*y)], [x0, sin(x0)])"],
  [["x/2 + y/2", "sin(x/2 + y/2)"], {}, "([(x0, x/2 + y/2)], [x0, sin(x0)])"],
];

describe('cse: SymPy results', () => {
  it.each(TABLE)('cse(%j, %j)', (exprs, opts, expected) => {
    const input = Array.isArray(exprs) ? exprs.map((s) => parse(s)) : parse(exprs);
    expect(show(cse(input, { ...opts, ignore: opts.ignore?.map((n) => symbol(n)) }))).toBe(expected);
  });
});

describe('cse (test_cse.py)', () => {
  it('a single expression, a number, a Float, a matrix', () => {
    expect(show(cse(parse('(x + y)**2 + sqrt(x + y)')))).toBe('([(x0, x + y)], [sqrt(x0) + x0**2])');
    expect(show(cse([42]))).toBe('([], [42])');
    expect(show(cse(42n))).toBe('([], [42])');
    expect(show(cse(0.5))).toBe('([], [0.500000000000000])');
    expect(cse(Matrix.of([[1]]))[1][0]).toBeInstanceOf(Matrix);
  });

  it('subtraction is optimized by sub_pre/sub_post', () => {
    const opts = { optimizations: [[subPre, subPost]] as const };
    expect(show(cse([parse('(x - y)*(z - y) + exp((x - y)*(z - y))')], opts))).toBe('([(x0, (x - y)*(y - z))], [-x0 + exp(-x0)])');
    expect(show(cse([parse('-(x - y)*(z - y) + exp(-(x - y)*(z - y))')], opts))).toBe('([(x0, (x - y)*(y - z))], [x0 + exp(x0)])');
    // issue 4077
    expect(show(cse(parse('(-1 + 1/x)/x/(1 - 1/x)**2 - 1/(-1 + 1/x)/x'), opts))).toBe('([], [0])');
    expect(str(subPost(subPre(parse('(-x - y)*z - x - y'))))).toBe('-x - y - z*(x + y)');
  });

  it('reversed lists give the same replacements', () => {
    const l = [parse('w*x*y'), parse('w*x*y + z'), parse('w*y')];
    expect(show(cse([...l].reverse()))).toBe('([(x0, w*y), (x1, x*x0)], [x0, x1 + z, x1])');
    // an iterable that is not an array
    expect(show(cse(new Set(l)))).toBe('([(x0, w*y), (x1, x*x0)], [x1, x1 + z, x0])');
  });

  it('non-commutative products are not split', () => {
    const [A, B, C] = symbols('A B C', { commutative: false });
    for (const l of [[mul(A, B, C), mul(A, C)], [mul(A, B, C), mul(A, B)], [mul(B, C), mul(A, B, C)]]) {
      const [r, e] = cse(l);
      expect(r).toEqual([]);
      expect(e.map(fmt)).toEqual(l.map(fmt));
    }
    // SymPy prints the unevaluated product (2*x)*A*B
    expect(show(cse([mul(2, x, A, B), mul(3, x)]))).toBe('([], [2*x*A*B, 3*x])');
    expect(show(cse([mul(-2, x, A, B), mul(-2, x, A, B)]))).toBe('([(x0, -2*x*A*B)], [x0, x0])');
    expect(show(cse([mul(x, A, B), mul(x, A, B), mul(y, x, A)]))).toBe('([(x0, x*A*B)], [x0, x0, x*y*A])');
    expect(show(cse([add(mul(-1, A, B), 1), mul(-1, A, B)]))).toBe('([(x0, -A*B)], [x0 + 1, x0])');
    // raw products: Mul(2, 1/2, A, B, evaluate=False) and Mul(1, A, B, evaluate=False)
    expect(show(cse([new Mul([Rational.of(2), Rational.of(1, 2), A, B]), mul(A, B)]))).toBe('([], [A*B, A*B])');
    expect(show(cse([new Mul([Rational.of(1), A, B]), mul(A, B)]))).toBe('([], [A*B, A*B])');
  });

  it('issue 6263: an equation that becomes True', () => {
    expect(show(cse(Eq(parse('x*(-x + 1) + x*(x - 1)'), 0), { optimizations: 'basic' }))).toBe('([], [True])');
  });

  it('issue 25043: generated names do not clash with symbols of other assumptions', () => {
    const c = symbol('c');
    const x0 = symbol('x0', { real: true });
    expect(show(cse(add(mul(c, pow(x0, 2)), mul(c, sub(pow(x0, 4), pow(x0, 2))))))).toBe('([(x1, x0**2)], [c*x1 + c*(x0**4 - x1)])');
  });

  it('tuples (Subs) are not replaced', () => {
    expect(show(cse(parse('Subs(f(x, y), (x, y), (0, 1)) + Subs(g(x, y), (x, y), (0, 1))')))).toBe(
      '([], [Subs(f(x, y), (x, y), (0, 1)) + Subs(g(x, y), (x, y), (0, 1))])',
    );
    expect(show(cse(parse('Subs(f(x, y), (x, y), (0, x + y)) + Subs(g(x, y), (x, y), (0, x + y))')))).toBe(
      '([(x0, x + y)], [Subs(f(x, y), (x, y), (0, x0)) + Subs(g(x, y), (x, y), (0, x0))])',
    );
  });

  it('postprocess: cse_separate', () => {
    const eq = parse('x + 1 + exp((x + 1)/(y + 1)) + cos(y + 1)');
    const [r, e] = cse([eq, Eq(x, parse('z + 1')), parse('z - 2'), parse('(z + 1)*(x + 1)')], { postprocess: cseSeparate });
    expect(show([r as CseReplacement[], e])).toBe('([(x0, y + 1), (x2, z + 1), (x, x2), (x1, x + 1)], [x1 + exp(x1/x0) + cos(x0), z - 2, x1*x2])');
    const [r2, e2] = cseSeparate([[x, parse('y + 1')], [z, parse('x + 2')]], [Eq(y, 2), add(x, z)]);
    expect(show([r2 as CseReplacement[], e2])).toBe('([(y, 2), (x, y + 1), (z, x + 2)], [x + z])');
    expect(repsToposort([[x, parse('y + 1')], [y, Rational.of(2)]]).map(([k, v]) => `${str(k)}=${str(v)}`)).toEqual(['y=2', 'x=y + 1']);
  });

  it('issue 4499: 16 expressions', () => {
    const t = [
      'a', 'a + 1/2', '2*a', 'b', '2*a - b + 1',
      '(sqrt(z)/2)**(1 - 2*a)*B(2*a - b, sqrt(z))*B(b - 1, sqrt(z))*G(b)*G(2*a - b + 1)',
      'sqrt(z)*(sqrt(z)/2)**(1 - 2*a)*B(b, sqrt(z))*B(2*a - b, sqrt(z))*G(b)*G(2*a - b + 1)',
      'sqrt(z)*(sqrt(z)/2)**(1 - 2*a)*B(b - 1, sqrt(z))*B(2*a - b + 1, sqrt(z))*G(b)*G(2*a - b + 1)',
      '(sqrt(z)/2)**(1 - 2*a)*B(b, sqrt(z))*B(2*a - b + 1, sqrt(z))*G(b)*G(2*a - b + 1)',
      '1', '0', '1/2', 'z/2', '1 - b', '-2*a + b', '-2*a',
    ].map((s) => parse(s));
    expect(show(cse(t))).toBe(
      '([(x0, 2*a), (x1, -b + x0), (x2, x1 + 1), (x3, b - 1), (x4, sqrt(z)), (x5, B(x3, x4)), (x6, (x4/2)**(1 - x0)*G(b)*G(x2)), (x7, x6*B(x1, x4)), (x8, B(b, x4)), (x9, x6*B(x2, x4))], ' +
        '[a, a + 1/2, x0, b, x2, x5*x7, x4*x7*x8, x4*x5*x9, x8*x9, 1, 0, 1/2, z/2, -x3, -x1, -x0])',
    );
  });

  it('issues 6169 and 18203: CRootOf is not searched', () => {
    const r = new CRootOf(parse('x**6 - 4*x**5 - 2'), 1);
    expect(show(cse(r))).toBe('([], [CRootOf(x**6 - 4*x**5 - 2, 1)])');
    const eq = add(new CRootOf(parse('x**5 + 11*x - 2'), 0), new CRootOf(parse('x**5 + 11*x - 2'), 1));
    expect(show(cse(eq))).toBe(`([], [${str(eq)}])`);
  });

  it('Indexed objects', () => {
    const [yb, xb] = [new IndexedBase('y'), new IndexedBase('x')];
    const i = Idx('i', 4);
    const dx = sub(xb.at(add(i, 1)), xb.at(i));
    // SymPy: ([(x0, 1/(x[i + 1] - x[i]))], [x0*(y[i + 1] - y[i]), x0]); an Indexed object is an atom
    // (symjs prints the sums with the terms in another order: -x[i] + x[i + 1])
    const [r, e] = cse([mul(sub(yb.at(add(i, 1)), yb.at(i)), pow(dx, -1)), pow(dx, -1)]);
    const x0 = symbol('x0');
    expect(r.length).toBe(1);
    expect(r[0]?.[1].equals(pow(dx, -1))).toBe(true);
    expect(e.map((v) => (v as Expr).equals(mul(x0, sub(yb.at(add(i, 1)), yb.at(i)))) || (v as Expr).equals(x0))).toEqual([true, true]);
  });

  it('MatrixSymbols and their elements', () => {
    const A = MatrixSymbol('A', 3, 3);
    expect(show(cse(A))).toBe('([], [A])');
    const B = MatrixSymbol('B', symbol('n', { integer: true }), symbol('n', { integer: true }));
    expect(show(cse(B))).toBe('([], [B])');
    const a = (i: number, j: number) => A.entry(Rational.of(i), Rational.of(j));
    expect(show(cse(mul(a(0, 0), a(0, 0))))).toBe('([], [A[0, 0]**2])');
    expect(show(cse(add(mul(a(0, 0), a(0, 1)), mul(a(0, 0), a(0, 1), a(0, 2)))))).toBe('([(x0, A[0, 0]*A[0, 1])], [x0*A[0, 2] + x0])');
  });

  it('matrix expressions get MatrixSymbols', () => {
    const [A, B, C] = [MatrixSymbol('A', 3, 3), MatrixSymbol('B', 3, 3), MatrixSymbol('C', 3, 3)];
    const [r] = cse([add(A, B, C), add(A, B)]);
    expect(show(cse([add(A, B, C), add(A, B)]))).toBe('([(x0, A + B)], [C + x0, x0])');
    expect(r[0]?.[0]).toBeInstanceOf(MatrixSymbolNode);
    expect(show(cse([MatAdd(A, B, C), MatAdd(A, B)]))).toBe('([(x0, A + B)], [C + x0, x0])');
    const D = MatrixSymbol('D', 3, 3);
    expect(show(cse([MatAdd(A, B, C), MatAdd(A, B, D)]))).toBe('([(x0, A + B)], [x0 + C, x0 + D])');
    expect(show(cse([mul(-2, A, B), mul(-2, A, B)]))).toBe('([(x0, -2*A*B)], [x0, x0])');
    // SymPy: cse(MatMul(1, A, B)) == ([], [MatMul(1, A, B)]), printed 1*A*B
    const m1 = new MatMulNode([Rational.of(1), A, B]);
    const [rm1, [em1]] = cse(m1);
    expect(rm1).toEqual([]);
    expect((em1 as Expr).equals(m1)).toBe(true);
    const [rAB] = cse([add(mul(A, B), C), mul(A, B)]);
    expect(show(cse([add(mul(A, B), C), mul(A, B)]))).toBe('([(x0, A*B)], [C + x0, x0])');
    expect(rAB[0]?.[0]).toBeInstanceOf(MatrixSymbolNode);
    expect(show(cse([mul(A, B, C), mul(A, B)]))).toBe('([], [A*B*C, A*B])');
    expect(show(cse([MatMul(A, B, C), MatMul(A, B)]))).toBe('([], [A*B*C, A*B])');
    expect(show(cse([pow(A, 2), add(A, pow(A, 2))]))).toBe('([(x0, A**2)], [x0, A + x0])');
    expect(show(cse([MatPow(A, 2), MatAdd(A, MatPow(A, 2))]))).toBe('([(x0, A**2)], [x0, A + x0])');
    expect(show(cse([MatPow(A, -2), MatAdd(A, MatPow(A, 2))]))).toBe('([(x0, A**2)], [x0**(-1), A + x0])');
    const y1 = MatrixSymbol('y', 3, 1);
    // SymPy writes (A.T*A).I as A**(-1)*A.T**(-1) and replaces A.T; symjs keeps the inverse of the product
    const e1 = MatMul(Inverse(MatMul(Transpose(A), A)), A, y1);
    const e2 = MatMul(MatMul(Transpose(A), A), A, y1);
    expect(cse([e1, e2])[0].length).toBeGreaterThan(0);
    expect(cse([MatAdd(e1, e2), e1])[0].length).toBeGreaterThan(0);
  });

  it('explicit matrices inside matrix expressions', () => {
    const M = (p: string, r: number, c: number) => Matrix.fromFunction(r, c, (i, j) => symbol(`${p}${i * c + j}`));
    const A = M('A', 2, 2);
    const B = M('B', 2, 2);
    const b = M('b', 2, 1);
    for (const e of [Inverse(A), MatMul(Inverse(A), b), MatMul(-1, A), MatMul(-1, A, B)]) {
      const [r, [red]] = cse(e);
      expect(r).toEqual([]);
      expect((red as Expr).equals(e)).toBe(true);
    }
    // single-argument products and sums collapse
    expect(show(cse(MatMul(MatMul(MatMul(A)))))).toBe(show(cse(MatMul(A))));
    expect(show(cse(MatAdd(MatAdd(MatAdd(MatAdd(A))))))).toBe('([], [Matrix([[A0, A1], [A2, A3]])])');
    const X = M('X', 2, 2);
    const y = M('y', 2, 1);
    const [r, [red]] = cse(MatMul(Inverse(MatMul(Transpose(X), X)), Transpose(X), y));
    const x0 = MatrixSymbol('x0', 2, 2);
    expect(r.map(([s, v]) => [str(s), str(v)])).toEqual([['x0', str(Transpose(X))]]);
    expect((red as Expr).equals(MatMul(Inverse(MatMul(x0, X)), x0, y))).toBe(true);
  });

  it('the Kalman filter', () => {
    const M = (p: string, r: number, c: number) => Matrix.fromFunction(r, c, (i, j) => symbol(`${p}${i * c + j}`));
    const [mu, Sigma, H, R, data] = [M('mu', 2, 1), M('Sigma', 2, 2), M('H', 2, 2), M('R', 2, 2), M('data', 2, 1)];
    const inv = Inverse(MatAdd(R, MatMul(H, Sigma, Transpose(H))));
    const newMu = MatAdd(mu, MatMul(Sigma, Transpose(H), inv, MatAdd(MatMul(H, mu), MatMul(-1, data))));
    const newSigma = MatAdd(Sigma, MatMul(-1, Sigma, Transpose(H), inv, H, Sigma));
    const [r, e] = cse([newMu, newSigma]);
    const x0 = MatrixSymbol('x0', 2, 2);
    const x1 = MatrixSymbol('x1', 2, 2);
    const expectedR = [[x0, Transpose(H)], [x1, Inverse(MatAdd(R, MatMul(H, Sigma, x0)))]];
    expect(r.length).toBe(2);
    r.forEach(([s, v], i) => {
      expect(s.equals(expectedR[i]?.[0] as Expr)).toBe(true);
      expect(str(v)).toBe(str(expectedR[i]?.[1] as Expr));
    });
    const expectedE = [
      MatAdd(mu, MatMul(Sigma, x0, x1, MatAdd(MatMul(H, mu), MatMul(-1, data)))),
      MatAdd(Sigma, MatMul(-1, Sigma, x0, x1, H, Sigma)),
    ];
    // the rebuilt sums and products have their arguments in canonical order
    expect(e.map(fmt)).toEqual(expectedE.map(fmt));
  });

  it('Order terms are not searched', () => {
    const eq = add(series(exp(x), x, 0, 3), sin(parse('y + x**3')), -1);
    expect(show(cse(eq))).toBe('([], [sin(x**3 + y) + x + x**2/2 + O(x**3)])');
  });

  it('name conflicts with the symbols of the expressions', () => {
    const l = [parse('cos(x0 + y) + x0 + y'), parse('cos(x2 + x3) + x2 + x3'), parse('x0 + x2')];
    for (const opts of [{}, { symbols: symbols('x:10') }]) {
      const [r, e] = cse(l, opts);
      expect(show([r, e])).toBe('([(x1, x0 + y), (x4, x2 + x3)], [x1 + cos(x1), x4 + cos(x4), x0 + x2])');
      expect(e.map((v) => str(subs(v as Expr, [...r].reverse())))).toEqual(l.map((v) => str(v)));
    }
    expect(show(cse([parse('x + y'), parse('(x + y)**2')], { symbols: numberedSymbols('t') }))).toBe('([(t0, x + y)], [t0, t0**2])');
  });

  it('an exhausted symbols iterator is an error', () => {
    expect(() => cse(parse('cos(x+y)+x+y+cos(w+y)+sin(w+y)'), { symbols: [x, y, z] })).toThrow(RangeError);
  });

  it('issue 7840: nested Piecewise', () => {
    const C393 = parse('Piecewise((C391 - 1.65, C390 < 0.5), (Piecewise((C391 - 1.65, C391 > 2.35), (C392, True)), True))');
    const C391 = parse('Piecewise((2.05*C390**(-1.03), C390 < 0.5), (2.5*C390**(-0.625), True))');
    const e = subs(C393, [[symbol('C391'), C391]]);
    const values: [Expr, Expr][] = [[symbol('C390'), parse('0.703451854')], [symbol('C392'), parse('1.01417794')]];
    const direct = subs(e, values);
    const [r, [red]] = cse(e);
    for (const [s, v] of r) values.push([s, subs(v, values)]);
    expect(str(subs(red as Expr, values))).toBe(str(direct));
    const g = parse('Piecewise((ON, Eq(mode, ON)), (Piecewise((Piecewise((OFF, x < threshold), (ON, True)), Eq(mode, AUTO)), (OFF, True)), True))');
    const [r2, [red2]] = cse(g);
    expect(r2).toEqual([]);
    expect((red2 as Expr).equals(g)).toBe(true);
  });

  it('issue 8891: explicit matrices keep their mutability', () => {
    for (const make of [(rows: Expr[][]) => Matrix.of(rows), (rows: Expr[][]) => MutableDenseMatrix.of(rows)]) {
      const m = make([[parse('x + y'), Rational.of(0)], [Rational.of(0), Rational.of(0)]]);
      const [r, e] = cse([parse('x + y'), m]);
      expect(show([r, e])).toBe('([(x0, x + y)], [x0, Matrix([[x0, 0], [0, 0]])])');
      expect(e[1]?.constructor).toBe(m.constructor);
    }
  });

  it('issue 11230: no products or sums left in the arguments, and the substitution gives the input back', () => {
    const s = symbols('a:m');
    const pick = (i: number, j: number) => s[(i * 7 + j * 3 + i * j) % 13] as Expr;
    const muls = Array.from({ length: 7 }, (_v, i) => mul(...Array.from({ length: 5 }, (_u, j) => pick(i, j))));
    const adds = Array.from({ length: 7 }, (_v, i) => add(...Array.from({ length: 5 }, (_u, j) => s[(i * 3 + j * 5 + i * j) % 7] as Expr)));
    for (const [ex, isHead] of [[muls, (v: Expr) => v instanceof Mul], [adds, (v: Expr) => v.kind === 'Add']] as const) {
      for (let i = 0; i < 7; i++) {
        for (let j = i + 1; j < 7; j++) {
          const p = [ex[i], ex[j], ex[(i + j) % 7]] as Expr[];
          const [R, C] = cse(p);
          expect(C.some((c) => (c as Expr).args.some(isHead))).toBe(false);
          const back = C.map((c) => R.reduceRight((acc, [k, v]) => subs(acc, [[k, v]]), c as Expr));
          expect(back.map((v) => str(parse(str(v))))).toEqual(p.map((v) => str(v)));
        }
      }
    }
  });

  it('ignore: substitutions containing ignored symbols are skipped', () => {
    const exprs = [parse('exp(y)*(3*y + 3*sqrt(x+1))'), parse('exp(y)*(5*y + 5*sqrt(x+1))')];
    const [subst1] = cse(exprs);
    expect(subst1.some(([, v]) => v.has(y))).toBe(true);
    const [subst2] = cse(exprs, { ignore: [y] });
    expect(subst2.some(([, v]) => v.has(y))).toBe(false);
    expect(subst2.some(([, v]) => v.equals(parse('sqrt(x + 1)')))).toBe(true);
    // issue 15002
    const l = [parse('w*exp(x)*exp(-z)'), parse('exp(y)*exp(x)*exp(-z)')];
    const [r, e] = cse(l, { ignore: [x] });
    expect(e.map((v) => str(subs(v as Expr, [...r].reverse())))).toEqual(l.map((v) => str(v)));
  });

  it('UnevaluatedExpr', () => {
    const xp1 = new UnevaluatedExpr(parse('x + 1'));
    const [[rep], [red]] = cse([mul(sub(-1, xp1), pow(sub(1, xp1), -1))]);
    expect(rep?.[1].equals(xp1)).toBe(true);
    expect(str(red as Expr)).toBe('(-x0 - 1)/(1 - x0)');
  });

  it('a larger sum of alternating signs', () => {
    const xs = symbols('x:20');
    const exprs = [0, 1, 2].map((i) => add(...xs.map((s, j) => mul((i + j) % 2 ? -1 : 1, s))));
    const [subst, red] = cse(exprs);
    expect(subst.length).toBeGreaterThan(0);
    red.forEach((e, i) => expect(str(subs(e as Expr, [...subst].reverse()))).toBe(str(exprs[i] as Expr)));
  });

  it('unevaluated products', () => {
    expect(show(cse(new Mul([parse('x + y'), parse('x + y')])))).toBe('([(x0, x + y)], [x0**2])');
    expect(show(cse([new Mul([Rational.of(1), Rational.of(2)])]))).toBe('([], [1*2])');
  });

  it('list: false keeps the type of the input', () => {
    expect(cse(x, { list: false })).toEqual([[], x]);
    const [r1, e1] = cse(parse('(x+y)**2 + sqrt(x+y)'), { list: false });
    expect(r1.length).toBe(1);
    expect(str(e1)).toBe('sqrt(x0) + x0**2');
    const [, e2] = cse([parse('x+y'), parse('sin(x+y)')], { list: false });
    expect(e2.map(fmt)).toEqual(['x0', 'sin(x0)']);
    const [, e3] = cse(new Set([parse('x+y'), parse('sin(x+y)')]), { list: false });
    expect(e3).toBeInstanceOf(Set);
    expect([...e3].map(fmt)).toEqual(['x0', 'sin(x0)']);
    const [, e4] = cse(new Map([[1, parse('x+y')], [2, parse('sin(x+y)')]]), { list: false });
    expect([...e4].map(([k, v]) => `${k}: ${fmt(v)}`)).toEqual(['1: x0', '2: sin(x0)']);
    expect(cse('x+y+sin(x+y)', { list: false })[1]).toBe('x0 + sin(x0)');
    expect(cse('x', { list: false })).toEqual([[], 'x']);
    const [, e6] = cse(Matrix.of([[parse('x+y'), parse('sin(x+y)')]]), { list: false });
    expect(fmt(e6)).toBe('Matrix([[x0, sin(x0)]])');
    // a postprocess returning the pair
    const [r7, e7] = cse([parse('x+y'), parse('sin(x+y)')], { list: false, postprocess: (r, e) => [[...r].reverse(), e] });
    expect(r7.length).toBe(1);
    expect(e7.map(fmt)).toEqual(['x0', 'sin(x0)']);
    expect(() => cse([x], { list: false, postprocess: (() => 1) as never })).toThrow();
  });

  it('issue 12070', () => {
    const [subst, red] = cse([parse('x + y'), parse('2 + x + y'), parse('x + y + z'), parse('3 + x + y + z')]);
    expect(show([subst, red])).toBe('([(x0, x + y), (x1, x0 + z)], [x0, x0 + 2, x1, x1 + 3])');
  });

  it('a generic postprocess and invalid input', () => {
    expect(cse([parse('x + y'), parse('sin(x + y)')], { postprocess: (r, e) => r.length + e.length })).toBe(3);
    expect(() => cse([{} as never])).toThrow(TypeError);
    expect(() => cse({} as never)).toThrow(TypeError);
  });
});

describe('cse helpers', () => {
  const opt1 = (e: Expr): Expr => add(e, y);
  const opt2 = (e: Expr): Expr => mul(e, z);

  it('preprocess_for_cse and postprocess_for_cse (test_cse.py)', () => {
    expect(str(preprocessForCse(x, [[opt1, null]]))).toBe('x + y');
    expect(str(preprocessForCse(x, [[null, opt1]]))).toBe('x');
    expect(str(preprocessForCse(x, [[null, null]]))).toBe('x');
    expect(str(preprocessForCse(x, [[opt1, opt2]]))).toBe('x + y');
    expect(str(preprocessForCse(x, [[opt1, null], [opt2, null]]))).toBe('z*(x + y)');
    expect(str(postprocessForCse(x, [[opt1, null]]))).toBe('x');
    expect(str(postprocessForCse(x, [[null, opt1]]))).toBe('x + y');
    expect(str(postprocessForCse(x, [[null, null]]))).toBe('x');
    expect(str(postprocessForCse(x, [[opt1, opt2]]))).toBe('x*z');
    // the postprocessors run in reverse order
    expect(str(postprocessForCse(x, [[null, opt1], [null, opt2]]))).toBe('x*z + y');
  });

  it('SymPy class names and their superclasses', () => {
    const cases: [string, string, string][] = [
      ['0', 'Zero', 'IntegerConstant'],
      ['1', 'One', 'IntegerConstant'],
      ['-1', 'NegativeOne', 'IntegerConstant'],
      ['1/2', 'Half', 'RationalConstant'],
      ['2', 'Integer', 'Rational'],
      ['1/3', 'Rational', 'Number'],
      ['1.5', 'Float', 'Number'],
      ['E', 'Exp1', 'NumberSymbol'],
      ['pi', 'Pi', 'NumberSymbol'],
      ['I', 'ImaginaryUnit', 'AtomicExpr'],
      ['EulerGamma', 'EulerGamma', 'NumberSymbol'],
      ['oo', 'Infinity', 'Number'],
      ['-oo', 'NegativeInfinity', 'Number'],
      ['zoo', 'ComplexInfinity', 'AtomicExpr'],
      ['nan', 'NaN', 'Number'],
      ['x', 'Symbol', 'AtomicExpr'],
      ['x + 1', 'Add', 'Expr'],
      ['2*x', 'Mul', 'Expr'],
      ['x**2', 'Pow', 'Expr'],
      ['exp(x)', 'exp', 'ExpBase'],
      ['sin(x)', 'sin', 'DefinedFunction'],
      ['Abs(x)', 'Abs', 'DefinedFunction'],
      ['f(x)', 'f', 'AppliedUndef'],
      ['True', 'BooleanTrue', 'BooleanAtom'],
      ['False', 'BooleanFalse', 'BooleanAtom'],
      ['Eq(x, 1)', 'Equality', 'Relational'],
      ['x < 1', 'StrictLessThan', 'Relational'],
      ['Piecewise((x, x > 0))', 'Piecewise', 'DefinedFunction'],
      ['Integral(x, x)', 'Integral', 'Expr'],
    ];
    for (const [src, name, base] of cases) {
      const e = parse(src);
      expect(sympyClassName(e)).toBe(name);
      expect(sympyClassBases(e)[0]).toBe(base);
    }
    expect([sympyClassName(new Dummy('d')), ...sympyClassBases(new Dummy('d')).slice(0, 2)]).toEqual(['Dummy', 'Symbol', 'AtomicExpr']);
    expect([sympyClassName(new Wild('u')), ...sympyClassBases(new Wild('u')).slice(0, 2)]).toEqual(['Wild', 'Symbol', 'AtomicExpr']);
  });

  it('Basic.compare orders the arguments of sums and products like SymPy', () => {
    // SymPy (x**2 + x + 1 + sin(x) + cos(x) + f(x) + y).args
    expect(sympyArgs(parse('x**2 + x + 1 + sin(x) + cos(x) + f(x) + y')).map((e) => str(e))).toEqual(['1', 'x', 'y', 'x**2', 'cos(x)', 'f(x)', 'sin(x)']);
    // SymPy (2*x*y**2*sin(x)*exp(x)).args
    expect(sympyArgs(parse('2*x*y**2*sin(x)*exp(x)')).map((e) => str(e))).toEqual(['2', 'x', 'y**2', 'exp(x)', 'sin(x)']);
    expect(sympyArgs(exp(x)).map((e) => str(e))).toEqual(['x']);
    expect(basicCompare(x, x)).toBe(0);
    expect(basicCompare(parse('x + y'), parse('x + y'))).toBe(0);
    expect(basicCompare(parse('x + y'), parse('x + y + z'))).toBe(-1);
    expect(basicCompare(parse('1.5'), parse('2.5'))).toBe(-1);
    expect(basicCompare(cos(x), sin(x))).toBe(-1);
    expect(basicCompare(parse('2'), parse('3'))).toBe(-1);
  });

  it('FuncArgTracker: the common argument candidates (checked against SymPy)', () => {
    const [a, b, c, d, e, f, g, h, i] = symbols('a b c d e f g h i');
    // the largest funcset is iterated (it is not larger than the counts)
    const t1 = new FuncArgTracker([add(a, b, c), add(a, d), add(a, e), add(b, f), add(b, g), add(c, h), add(c, i)]);
    expect(t1.getCommonArgCandidates(t1.funcToArgset[0] as Set<number>)).toEqual(new Map([[0, 3]]));
    // the counts are iterated
    const t2 = new FuncArgTracker([add(a, b, c), add(a, b), add(a, c), add(b, c), add(a, d), add(a, e)]);
    expect(t2.getCommonArgCandidates(t2.funcToArgset[0] as Set<number>)).toEqual(new Map([[0, 3], [1, 2], [3, 2], [2, 2]]));
  });

  it('FuncArgTracker', () => {
    const t = new FuncArgTracker([parse('x + y + z'), parse('x + y'), parse('w + x + y')]);
    expect(t.getCommonArgCandidates(new Set())).toEqual(new Map());
    expect(t.getCommonArgCandidates(t.funcToArgset[0] as Set<number>)).toEqual(new Map([[0, 3], [1, 2], [2, 2]]));
    expect(t.getCommonArgCandidates(t.funcToArgset[1] as Set<number>, 1)).toEqual(new Map([[1, 2], [2, 2]]));
    expect([...t.getSubsetCandidates(new Set([0, 1]))]).toEqual([0, 1, 2]);
    expect([...t.getSubsetCandidates(new Set([0, 1]), new Set([2]))]).toEqual([2]);
    expect(t.getArgsInValueOrder(new Set([1, 0])).map((e) => str(e as Expr))).toEqual(['x', 'y']);
    t.updateFuncArgset(0, [0, 3]);
    expect([...(t.funcToArgset[0] as Set<number>)]).toEqual([0, 3]);
    t.stopArgTracking(0);
    expect([...(t.argToFuncset[0] as Set<number>)]).toEqual([1, 2]);
  });
});

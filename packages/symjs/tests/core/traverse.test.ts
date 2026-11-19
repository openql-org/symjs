// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/traverse.ts.
// Substitution (subs, xreplace) and bound variables. Expected values are SymPy 1.14's.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { ExtensionExpr, Sym } from '../../src/core/nodes';
import {
  Derivative,
  type Expr,
  Integral,
  Lambda,
  O,
  Subs,
  Sum,
  add,
  exp,
  freeSymbols,
  mul,
  pi,
  pow,
  rational,
  rebuild,
  sin,
  sqrt,
  str,
  subs,
  symbols,
  xreplace,
} from '../../src';
import { boundSymbols, piecewiseFold } from '../../src/core/traverse';
import { BoolOp } from '../../src/core/boolalg';
import { at } from '../../src/core/guard';

const [x, y, C1, C2, z, w, n] = symbols('x y C1 C2 z w n');

const f = sj.SymFunction('f');
const s = (e: unknown): string => String(e);

const [pp] = symbols('p', { positive: true });
const p = pp as Expr;

const s2 = (e: unknown): string => str(e as Expr);
const sb = (e: Expr, from: Expr, to: Expr | number): string => s2(subs(e, [[from, to]]));

describe('bound variables', () => {
  const I = new Integral([mul(x, y), x, mul(0), y]);
  const S = Sum(mul(x, y), [x, 0, y]);

  it('are not free', () => {
    expect([...freeSymbols(I)].map(String)).toEqual(['y']);
    expect([...freeSymbols(S)].map(String)).toEqual(['y']);
    // the variable of an indefinite integral stays free (SymPy)
    expect([...freeSymbols(new Integral([mul(x, y), x]))].map(String).sort()).toEqual(['x', 'y']);
  });

  it('are not substituted', () => {
    expect(subs(I, [[x, 2]]).toString()).toBe('Integral(x*y, (x, 0, y))');
    expect(subs(S, [[x, 2]]).toString()).toBe('Sum(x*y, (x, 0, y))');
    expect(subs(I, [[y, 2]]).toString()).toBe('Integral(2*x, (x, 0, 2))');
    expect(subs(S, [[y, 2]]).toString()).toBe('Sum(2*x, (x, 0, 2))');
  });
});

describe('Mul substitution (SymPy Mul._eval_subs)', () => {
  const R = (p: number, q: number): sj.Expr => sj.Rational.of(BigInt(p), BigInt(q));
  it.each([
    [sj.mul(2, y, sj.pow(C1, -1)), sj.mul(2, sj.pow(C1, -1)), 'C2*y'],
    [sj.mul(4, x), sj.mul(2, x), '2*C2'],
    [sj.mul(6, x), sj.mul(2, x), '3*C2'],
    [sj.mul(3, x), sj.mul(2, x), '3*x'],
    [sj.mul(4, sj.pow(x, 2)), sj.mul(2, x), 'C2**2'],
    [sj.mul(2, sj.pow(x, 2)), sj.mul(2, x), 'C2*x'],
    [sj.mul(8, sj.pow(x, 3)), sj.mul(2, x), 'C2**3'],
    [sj.mul(R(1, 2), x), sj.mul(R(1, 2), x), 'C2'],
    [sj.mul(R(3, 4), x), sj.mul(R(1, 2), x), '3*C2/2'],
    [sj.mul(R(1, 4), x), sj.mul(R(1, 2), x), 'C2/2'],
    [sj.mul(-2, x), sj.mul(2, x), '-C2'],
    [sj.mul(-4, x), sj.mul(-2, x), '2*C2'],
    [sj.mul(2, x), sj.mul(-2, x), '2*x'],
    [sj.mul(6, x, y), sj.mul(3, x), '2*C2*y'],
    [sj.mul(R(9, 2), x), sj.mul(R(3, 2), x), '3*C2'],
    [sj.mul(2, sj.I, x), sj.mul(2, x), 'I*C2'],
    [sj.mul(4, x, y), sj.mul(2, x), '2*C2*y'],
  ])('(%s).subs(%s, C2)', (e, old, expected) => {
    expect(s(sj.subs(e, [[old, C2]]))).toBe(expected);
  });

  it('substitutes sums, powers, noncommutative products and several pairs', () => {
    const A = sj.symbol('A', { commutative: false });
    const B = sj.symbol('B', { commutative: false });
    const z = sj.symbol('z');
    expect(s(sj.subs(sj.mul(x, y), [[sj.mul(2, x), z]]))).toBe('x*y');
    expect(s(sj.subs(sj.mul(A, B, x), [[sj.mul(A, B), z]]))).toBe('x*z');
    expect(s(sj.subs(sj.mul(A, x), [[sj.mul(A, B), z]]))).toBe('x*A');
    expect(s(sj.subs(sj.mul(A, B), [[sj.mul(2, A, B), z]]))).toBe('A*B');
    expect(s(sj.subs(sj.add(x, y, 2), [[sj.add(x, y, 1), z]]))).toBe('z + 1');
    expect(s(sj.subs(sj.add(sj.mul(-1, x), sj.mul(-1, y), 2), [[sj.add(x, y, 1), z]]))).toBe('3 - z');
    expect(s(sj.subs(sj.pow(x, 3), [[sj.pow(x, 2), y]]))).toBe('x**3');
    expect(s(sj.subs(sj.add(x, y), { x: 1, y: 2 }))).toBe('3');
    expect(s(sj.subs(sj.add(x, y), new Map([[x, y], [y, x]]), { simultaneous: true }))).toBe('x + y');
    expect(s(sj.subs(sj.mul(x, y), [[x, y], [y, 2]]))).toBe('4');
    expect(s(sj.subs(sj.diff(f(x), x, 2), [[sj.diff(f(x), x), y]]))).toBe('Derivative(y, x)');
    expect(s(sj.subs(sj.diff(f(x), x), [[sj.diff(f(x), x, 2), y]]))).toBe('Derivative(f(x), x)');
  });
});

describe('xreplace and rebuild', () => {
  it('accepts a Map, pairs or an object keyed by symbol name', () => {
    const e = add(sin(x), y);
    expect(s2(xreplace(e, { x: 2 }))).toBe('y + sin(2)');
    expect(s2(xreplace(e, new Map([[x, 2]])))).toBe('y + sin(2)');
    expect(s2(xreplace(e, [[x, 2]]))).toBe('y + sin(2)');
    expect(s2(subs(e, { x: 2 }))).toBe('y + sin(2)');
    expect(s2(subs(e, new Map([[x, 2]])))).toBe('y + sin(2)');
  });
  it('rebuilds an Order term', () => {
    expect(s2(xreplace(O(x), [[x, y]]))).toBe('O(y)');
  });
  it('keeps a rebuilt derivative unevaluated', () => {
    expect(sb(Derivative(f(x), x), f(x), pow(x, 2))).toBe('Derivative(x**2, x)');
    expect(s2(xreplace(Derivative(f(x), x), [[f(x), pow(x, 2)]]))).toBe('Derivative(x**2, x)');
  });
  it('returns an atom as it is', () => {
    expect(rebuild(x, [])).toBe(x);
    expect(rebuild(x)).toBe(x);
  });
  it('rebuilds the whole tree without args (SymPy strategies.rl.rebuild)', () => {
    // SymPy: rebuild(Basic.__new__(Add, S(1), S(2))) == 3; rebuild(Basic.__new__(Mul, x, Basic.__new__(Add, x, x))) == 2*x**2
    expect(s2(rebuild(new sj.Add([sj.Rational.of(1), sj.Rational.of(2)])))).toBe('3');
    expect(s2(rebuild(new sj.Mul([x, new sj.Add([x, x])])))).toBe('2*x**2');
  });
});

describe('subs of powers (SymPy Pow._eval_subs)', () => {
  it('substitutes a power of the same base', () => {
    expect(sb(pow(x, 4), pow(x, 2), w)).toBe('w**2');
    expect(sb(pow(x, 3), pow(x, 2), w)).toBe('x**3');
    // a positive base: (p**2)**(3/2) == p**3
    expect(sb(pow(p, 3), pow(p, 2), w)).toBe('w**(3/2)');
    expect(sb(pow(x, mul(6, y)), pow(x, mul(3, y)), w)).toBe('w**2');
    expect(sb(pow(x, mul(y, z)), pow(x, y), w)).toBe('x**(y*z)');
    expect(sb(pow(x, mul(2, pi)), pow(x, pi), w)).toBe('w**2');
  });
  it('substitutes term by term in a sum exponent', () => {
    expect(sb(exp(add(x, y)), exp(x), w)).toBe('w*exp(y)');
    expect(sb(exp(add(mul(2, x), y)), exp(x), w)).toBe('w**2*exp(y)');
    expect(sb(exp(add(x, y, z)), exp(x), w)).toBe('w*exp(y + z)');
    // the terms of exp(x + y) are not terms of x + y + z one by one
    expect(sb(exp(add(x, y, z)), exp(add(x, y)), w)).toBe('exp(x + y + z)');
    expect(sb(pow(x, add(mul(6, y), z)), pow(x, mul(3, y)), w)).toBe('w**2*x**z');
    expect(sb(pow(x, add(mul(6, y), 1)), pow(x, mul(3, y)), w)).toBe('w**2*x');
    expect(sb(pow(p, add(mul(3, x), 1)), pow(p, mul(2, x)), w)).toBe('p**(3*x + 1)');
  });
});

describe('subs of derivatives (SymPy Derivative._eval_subs)', () => {
  const fxy = f(x, y);
  it('substitutes a lower derivative', () => {
    expect(sb(Derivative(fxy, x, y), Derivative(fxy, y, x), w)).toBe('w');
    expect(sb(Derivative(fxy, x, x, y), Derivative(fxy, x, y), w)).toBe('Derivative(w, x)');
    expect(sb(Derivative(fxy, x, y), Derivative(fxy, x, x), w)).toBe('Derivative(f(x, y), x, y)');
  });
});

describe('subs of sums (SymPy Add._eval_subs)', () => {
  it('matches the terms and the numeric coefficient', () => {
    expect(sb(add(x, y, z), add(mul(-1, x), mul(-1, y)), w)).toBe('-w + z');
    expect(sb(add(x, y, 2), add(x, y, 3), w)).toBe('w - 1');
    expect(sb(add(x, y, 2), add(mul(-1, x), mul(-1, y), 3), w)).toBe('5 - w');
    // a Float coefficient only combines with an equal one
    expect(sb(add(x, y, 2.5), add(x, y), z)).toBe('x + y + 2.5');
    expect(sb(add(x, y, z, 2.5), add(x, y, 2.5), w)).toBe('w + z');
    expect(sb(add(x, y, z, 2.5), add(x, y, 1.5), w)).toBe('x + y + z + 2.5');
    expect(sb(add(x, y, 2), add(x, 1), w)).toBe('w + y + 1');
    expect(sb(add(x, 2), add(y, 1), w)).toBe('x + 2');
    expect(sb(add(x, 2), add(x, 3), w)).toBe('w - 1');
    // pi is not a numeric coefficient
    expect(sb(add(pi, x, y), add(x, y), z)).toBe('z + pi');
  });
});

describe('subs of products (SymPy Mul._eval_subs)', () => {
  it('substitutes factors with symbolic exponents', () => {
    expect(sb(mul(2, pow(x, y), z), mul(pow(x, y), z), w)).toBe('2*w');
    // sqrt(x**y) and x**(2*y) are both powers of x**y: SymPy answers w*x**(3*y/2), which is
    // not equal in general ((x**y)**(3/2) != x**(3*y/2) for complex x**y); z*x**y*(x**y)**(3/2) is
    expect(sb(mul(z, sqrt(pow(x, y)), pow(x, mul(2, y))), mul(z, pow(x, y)), w)).toBe('w*(x**y)**(3/2)');
  });
  it('needs one denominator to divide the other', () => {
    expect(sb(mul(sqrt(x), y), mul(pow(x, rational(1, 3)), y), z)).toBe('sqrt(x)*y');
  });
  it('handles negative coefficients', () => {
    expect(sb(mul(-4, x, y), mul(-2, x), w)).toBe('2*w*y');
    expect(sb(mul(4, x, y), mul(-2, x), w)).toBe('4*x*y');
    expect(sb(mul(x, y), mul(-2, x), w)).toBe('x*y');
    expect(sb(mul(x, y), mul(2, x), w)).toBe('x*y');
    expect(sb(mul(6, x, y), mul(4, x), w)).toBe('6*x*y');
  });
});

describe('subs of bound variables', () => {
  it('substitutes only the limits', () => {
    expect(sb(new Integral([x, x, rational(0), x]), x, y)).toBe('Integral(x, (x, 0, y))');
    expect(sb(new Integral([x, x, rational(0), y]), x, y)).toBe('Integral(x, (x, 0, y))');
    expect(sb(Sum(x, [x, 1, n]), x, 2)).toBe('Sum(x, (x, 1, n))');
    expect(sb(Sum(x, [x, 1, x]), x, 2)).toBe('Sum(x, (x, 1, 2))');
    expect(sb(Subs(Derivative(f(x), x), x, 2), x, 3)).toBe('Subs(Derivative(f(x), x), x, 2)');
    expect(sb(Subs(Derivative(f(x), x), x, add(x, 1)), x, 2)).toBe('Subs(Derivative(f(x), x), x, 3)');
    expect(sb(Lambda(x, add(x, y)), y, 2)).toBe('Lambda(x, x + 2)');
  });
});

describe('subs of powers with related numeric bases (SymPy issue 10829)', () => {
  const [u, v] = sj.symbols('u v');
  const P = (t: string): sj.Expr => sj.parse(t, { symbols: { u, v } } as never);
  it.each([
    ['4**u', '2**u', 'v**2'],
    ['8**u', '2**u', 'v**3'],
    ['(1/4)**u', '2**u', 'v**(-2)'],
    ['9**u', '3**u', 'v**2'],
    ['4**u - 3*v + 2', '2**u', 'v**2 - 3*v + 2'],
    // log(4, 2) needs the same exponent, log(2, 4), log(6, 2) and log(4, 1/2) are not numbers in SymPy
    ['4**u', '2**(2*u)', '4**u'],
    ['2**u', '4**u', '2**u'],
    ['6**u', '2**u', '6**u'],
    ['4**u', '(1/2)**u', '4**u'],
    ['(2/3)**u', '2**u', '(2/3)**u'],
    ['4**(u + 1)', '2**u', '4**(u + 1)'],
    ['4**(2*u)', '2**u', '4**(2*u)'],
    ['4**u', '2**(-u)', '4**u'],
  ])('(%s).subs(%s, v) = %s', (e, o, want) => expect(sj.str(P(e).subs(P(o), v))).toBe(want));
});

describe('use and preorderTraversal (SymPy sympy.core.traversal)', () => {
  const [x, y] = [sj.symbol('x'), sj.symbol('y')];
  const P = (e: string) => sj.parse(e);
  it('use', () => {
    expect(String(sj.use(P('x*(x + y)**2 + 1'), sj.expand, 2))).toBe('x*(x**2 + 2*x*y + y**2) + 1');
    expect(String(sj.use(P('x*(x + y)**2 + 1'), sj.expand))).toBe('x**3 + 2*x**2*y + x*y**2 + 1');
    expect(String(sj.use(P('sin(x + y)*(x + 1)**2'), sj.expand, 1))).toBe('(x**2 + 2*x + 1)*sin(x + y)');
    // atoms above the level are kept
    expect(String(sj.use(P('x**2*(1 + x)**2'), sj.expand, 5))).toBe('x**2*(x + 1)**2');
  });
  it('preorderTraversal', () => {
    const e = P('(x + y)*z');
    expect([...sj.preorderTraversal(e)].map(String)).toEqual(['z*(x + y)', 'z', 'x + y', 'x', 'y']);
    expect([...sj.preorderTraversal(P('x*y + 1'), true)].map(String)).toEqual(['x*y + 1', '1', 'x*y', 'x', 'y']);
    expect([...sj.preorderTraversal(e, true)].map(String)).toEqual(['z*(x + y)', 'z', 'x + y', 'x', 'y']);
    // a key function (SymPy ordered(args, keys, default=False)): equal keys keep their order
    expect([...sj.preorderTraversal(P('x + y + z'), (a) => -String(a).length)].map(String)).toEqual(['x + y + z', 'x', 'y', 'z']);
    expect([...sj.preorderTraversal(sj.add(x, y), (a) => (a === x ? sj.sympify(2) : sj.sympify(1)))].map(String)).toEqual(['x + y', 'y', 'x']);
    expect([...sj.preorderTraversal(sj.add(x, y), (a) => String(a))].map(String)).toEqual(['x + y', 'x', 'y']);
    expect([...sj.preorderTraversal(sj.add(x, y), (a) => [a])].map(String)).toEqual(['x + y', 'x', 'y']);
    // skip(): the arguments of the last node are not visited
    const pt = sj.preorderTraversal(P('(x + y*z)*z'));
    const out: string[] = [];
    for (const n of pt) {
      out.push(String(n));
      if (String(n) === 'x + y*z') pt.skip();
    }
    expect(out.sort()).toEqual(['x + y*z', 'z', 'z*(x + y*z)'].sort());
    expect(sj.preorderTraversal(1).node.equals(sj.sympify(1))).toBe(true);
  });
});

describe('piecewiseFold (SymPy piecewise_fold)', () => {
  const P = sj.Piecewise([x, sj.Gt(x, 0)], [mul(-1, x), true]);
  const Q = sj.Piecewise([1, sj.Gt(y, 0)], [2, true]);
  it('flattens nested values and translates conditional Boolean branches', () => {
    const args = [sj.Gt(x, 0), sj.Lt(y, 1), sj.Gt(y, 1)] as const;
    for (const condition of [new BoolOp('ITE', args), sj.ITE(...args, { evaluate: false })]) {
      expect(str(piecewiseFold(sj.piecewise([x, condition]))))
        .toBe('Piecewise((x, ((x <= 0) | (y < 1)) & ((x > 0) | (y > 1))))');
    }
    const p = sj.piecewise([sj.cos(x), sj.Lt(x, 0)], [0, true]);
    expect(str(piecewiseFold(sj.piecewise([0, sj.Eq(p, 0)], [pow(p, -1), true]))))
      .toBe('Piecewise((0, (x >= 0) | Eq(cos(x), 0)), (1/cos(x), x < 0), (zoo, True))');
    const nested = sj.piecewise([sj.Tuple(add(P, 1), 2), sj.Lt(y, 0)], [0, true]);
    expect(str(piecewiseFold(nested)))
      .toBe('Piecewise(((Piecewise((x + 1, x > 0), (1 - x, True)), 2), y < 0), (0, True))');
    const incomplete = sj.piecewise([sj.piecewise([1, sj.Gt(x, 0)]), sj.Gt(y, 0)], [2, true]);
    const inside = [[x, -1], [y, 1]] as const;
    expect(piecewiseFold(incomplete).subs(inside)).toBe(incomplete.subs(inside));
    const complete = sj.piecewise([P, sj.Gt(y, 0)], [2, true]);
    expect(piecewiseFold(complete).subs(inside).equals(complete.subs(inside))).toBe(true);
  });
  it('combines shared branch conditions before expanding independent choices', () => {
    const c = sj.Gt(x, 0);
    const terms = Array.from({ length: 40 }, (_, i) => sj.piecewise([i + 1, c], [0, true]));
    expect(str(piecewiseFold(add(...terms)))).toBe('Piecewise((820, x > 0), (0, True))');
    expect(str(piecewiseFold(mul(sj.piecewise([2, c], [3, true]), sj.piecewise([5, c], [7, true]))))).toBe('Piecewise((10, x > 0), (21, True))');
  });

  it('folds the Piecewise arguments of an expression', () => {
    expect(str(piecewiseFold(add(P, 1)))).toBe('Piecewise((x + 1, x > 0), (1 - x, True))');
    expect(str(piecewiseFold(mul(P, Q)))).toBe('Piecewise((x, (x > 0) & (y > 0)), (2*x, x > 0), (-x, y > 0), (-2*x, True))');
    expect(str(piecewiseFold(sin(P)))).toBe('Piecewise((sin(x), x > 0), (-sin(x), True))');
    const plain = add(x, 1);
    expect(piecewiseFold(plain)).toBe(plain);
    expect(piecewiseFold(P)).toBe(P);
    expect(piecewiseFold(x)).toBe(x);
  });
  it('rebuilds extension nodes and connectives without folding them', () => {
    // SymPy folds a Tuple too: Piecewise(((x, 1), x > 0), ((-x, 1), True))
    expect(str(piecewiseFold(sj.Tuple(add(P, 1), 1)))).toBe('(Piecewise((x + 1, x > 0), (1 - x, True)), 1)');
    const t = sj.Tuple(P, 1);
    expect(piecewiseFold(t)).toBe(t);
    // SymPy folds the connective too: Piecewise(((y > 0) & (x + 1 > 0), x > 0), ((y > 0) & (1 - x > 0), True))
    expect(str(piecewiseFold(sj.And(sj.Gt(add(P, 1), 0), sj.Gt(y, 0))))).toBe('(y > 0) & Piecewise((x + 1 > 0, x > 0), (1 - x > 0, True))');
  });
});

describe('symbol-like nodes with arguments (Sym.substituteInner)', () => {
  it('a plain symbol has nothing inside', () => {
    expect(new sj.Sym('x').substituteInner((e) => e)).toBeUndefined();
    expect(new sj.Sym('x').sortPriority).toBe(2);
    expect(xreplace(x, [[y, 1]])).toBe(x);
  });
});

it('excludes differentiation variables and composite bound integration variables', () => {
  const a = new sj.Sym('a'), b = new sj.Sym('b');
  expect([...sj.freeSymbols(new sj.Derivative([a, b]))]).toEqual([a]);
  const f = sj.SymFunction('f')(a), g = sj.SymFunction('g')(b);
  expect([...sj.freeSymbols(new sj.Integral([f, f, sj.S.One, g]))]).toEqual([b]);
});

it('rebuilds limits and substitutes into indefinite integration limits', () => {
  const limit = new sj.Limit([x, x, sj.S.Zero], '-');
  expect(sj.rebuild(limit, [y, x, sj.S.Zero])).toEqual(new sj.Limit([y, x, sj.S.Zero], '-'));
  expect(sj.subs(new Integral([x, x]), [[x, 2]])).toEqual(new Integral([x, x, rational(2)]));
  expect(sj.subs(new Integral([x, x]), [[x, y]])).toEqual(new Integral([y, y]));
  expect(String(sj.subs(mul(rational(1, 2), x), [[mul(2, x), y]]))).toBe('x/2');
});

it('honors extension substitution hooks and symbols with inner free symbols', () => {
  class InnerSymbol extends Sym {
    override innerFreeSymbols(): readonly Sym[] { return [y]; }
  }
  class Wrapper extends ExtensionExpr {
    constructor(args: readonly sj.Expr[]) { super('Wrapper', args); }
    withArgs(args: readonly sj.Expr[]): sj.Expr { return new Wrapper(args); }
    override subsSelf(_old: sj.Expr, _nw: sj.Expr, sub: (e: sj.Expr) => sj.Expr): sj.Expr { return sub(this.args[0] ?? sj.S.Zero); }
  }
  expect([...sj.freeSymbols(new InnerSymbol('inner'))].map(String)).toEqual(['inner', 'y']);
  const random = sj.Normal('X', y, 1);
  expect(sj.pspace(sj.subs(random, [[y, 2]])).key).toBe(sj.pspace(sj.Normal('X', 2, 1)).key);
  expect(String(sj.subs(new Wrapper([x]), [[x, 2]]))).toBe('2');
  expect(String(sj.subs(sj.interval(x, y), [[x, 1]]))).toBe('Interval(1, y)');
  const condition = new sj.ConditionSet(x, sj.Gt(x, y), sj.Reals);
  expect(sj.subs(condition, [[x, 1]])).toBe(condition);
  const derivative = new sj.Derivative([sj.SymFunction('f')(x), x, sj.S.One]);
  expect(sj.subs(derivative, [[x, 2]])).toBeInstanceOf(sj.Subs);
});

it('checks for variable capture only when substitution changes the differentiated expression', () => {
  const f = sj.SymFunction('f');
  const single = sj.derivative(f(x), [[x, 1]]);
  const multiple = sj.derivative(f(x, y), [[x, 1]]);
  const point = y.add(x);
  expect(sj.subs(single, [[y, point]])).toBe(single);
  expect(sj.subs(multiple, [[y, point]])).toBeInstanceOf(sj.Subs);
});

it('substitutes only unbound arguments of an extension binder', () => {
  class Binder extends ExtensionExpr {
    constructor(args: readonly sj.Expr[]) { super('Binder', args); }
    withArgs(args: readonly sj.Expr[]): sj.Expr { return new Binder(args); }
    override bindings(): { variables: readonly number[]; scope: readonly number[] } { return { variables: [0], scope: [1] }; }
  }
  const binder = new Binder([x, x.mul(y), x]);
  expect(boundSymbols(binder)).toEqual([x]);
  expect([...sj.freeSymbols(binder)].map(String).sort()).toEqual(['x', 'y']);
  expect(sj.subs(binder, [[x, 2]]).args.map(String)).toEqual(['x', 'x*y', '2']);
  const independent = new Binder([x, x.mul(y), y]);
  expect(sj.subs(independent, [[x, 2]])).toBe(independent);
});

it('stops substitution after a true Piecewise branch', () => {
  const expression = sj.piecewise([1, sj.Eq(pow(x, 2), -1)], [2, sj.Lt(x, 0)]);
  expect(String(sj.subs(expression, [[x, sj.I]]))).toBe('1');
  const excluded = sj.piecewise([sj.Lt(x, 0), sj.Eq(x, 0)], [1, true]);
  expect(String(sj.subs(excluded, [[x, sj.I]]))).toBe('1');
});

it('orders complex substitutions before their constituents and delegates extension substitution', () => {
  expect(sj.subs(add(x, y), new Map<sj.Expr, sj.Expr>([[x, sj.S.One], [add(x, y), z]]))).toBe(z);
  const q = sj.Quaternion(x, 1, 2, 3).subs(x, y);
  expect(q.args[0]).toBe(y);
});

it('honors substitution and free-symbol hooks of extension expressions', () => {
  class Container extends sj.ExtensionExpr {
    constructor(readonly value: Expr) {
      super('Container', [value]);
    }
    withArgs(args: readonly Expr[]): Expr {
      return new Container(at(args, 0));
    }
    override subsSelf(_old: Expr, _nw: Expr, substitute: (e: Expr) => Expr): Expr {
      return new Container(substitute(this.value));
    }
    override freeSymbolsSelf(): ReadonlySet<Expr> {
      return new Set([y]);
    }
  }
  const wrapped = new Container(x);
  expect(sj.subs(wrapped, [[x, 3]])).toEqual(new Container(rational(3)));
  expect([...sj.freeSymbols(wrapped)]).toEqual([y]);
  expect(sj.subs(sj.finiteSet(x), [[x, 3]])).toEqual(sj.finiteSet(3));
  const set = new sj.ConditionSet(x, sj.Gt(x, y), sj.Reals);
  expect(String(sj.subs(set, [[y, z]]))).toBe('ConditionSet(x, x > z, Reals)');
  expect(sj.subs(set, [[z, 1]])).toBe(set);
  class InnerSymbol extends sj.Sym {
    override innerFreeSymbols(): readonly sj.Sym[] {
      return [y];
    }
    override substituteInner(substitute: (e: Expr) => Expr): Expr {
      return substitute(y);
    }
  }
  const inner = new InnerSymbol('inner');
  expect(sj.subs(inner, [[y, 3]])).toEqual(rational(3));
  expect([...sj.freeSymbols(inner)]).toEqual([inner, y]);
});

it('substitutes noncommutative words and integral power blocks in order', () => {
  const A = new sj.Sym('A', { commutative: false });
  const B = new sj.Sym('B', { commutative: false });
  const C = new sj.Sym('C', { commutative: false });
  const pair = mul(A, B);
  expect(subs(mul(pair, pair), [[pair, C]]).key).toBe(pow(C, 2).key);
  expect(subs(mul(pow(A, 2), pow(B, 2)), [[pair, C]]).key).toBe(mul(A, C, B).key);
  expect(subs(mul(pow(A, 2), B, pow(A, 2), B, pow(A, 2)), [[mul(A, B, A), C]]).key).toBe(mul(A, pow(C, 2), A).key);
  for (let p = 1; p <= 4; p++) for (let k = 0; k < 10; k++) {
    expect(subs(mul(B, pow(A, k)), [[pow(A, p), C]]).key).toBe(mul(B, pow(C, Math.floor(k / p)), pow(A, k % p)).key);
  }
  expect(subs(pow(A, -5), [[pow(A, 3), C]]).key).toBe(mul(pow(C, -1), pow(A, -2)).key);
  expect(subs(pow(A, sj.S.Half), [[pow(A, sj.S.NegHalf), C]]).key).toBe(pow(A, sj.S.Half).key);
  const integer = new sj.Sym('integer', { integer: true });
  expect(subs(pow(A, mul(3, integer)), [[pow(A, mul(2, integer)), C]]).key).toBe(mul(C, pow(A, integer)).key);
  expect(subs(mul(x, y, A), [[mul(x, y), z]]).key).toBe(mul(z, A).key);
  expect(subs(mul(pow(x, 2), pow(A, 3)), [[mul(x, A), C]]).key).toBe(mul(pow(C, 2), A).key);
  expect(subs(mul(x, A, B), [[mul(x, A), y]]).key).toBe(mul(y, B).key);
  expect(subs(mul(x, A), [[mul(y, A), C]]).key).toBe(mul(x, A).key);
  expect(subs(mul(pow(x, sj.S.Half), A), [[mul(x, A), C]]).key).toBe(mul(pow(x, sj.S.Half), A).key);
  expect(subs(mul(x, A, B, A), [[mul(A, B), C]]).key).toBe(mul(x, C, A).key);
  expect(subs(mul(A, B), [[mul(A, B, C), x]]).key).toBe(mul(A, B).key);
  expect(subs(mul(A, pow(B, 2), C), [[mul(A, B, C), x]]).key).toBe(mul(A, pow(B, 2), C).key);
  expect(subs(pow(mul(x, y), -1), [[mul(x, y), z]]).key).toBe(pow(z, -1).key);
  expect(subs(mul(x, y, add(1, mul(x, y))), [[mul(x, y), 2]]).key).toBe(sj.S.Two.mul(3).key);
});

it('keeps derivative substitutions independent and avoids capturing existing variables', () => {
  const fx = f(x, y);
  const derivative = sj.derivative(fx, [[y, 1]]);
  expect(subs(derivative, [[y, x]]).key).toBe(sj.Subs(derivative, y, x).key);
  expect(subs(derivative, [[x, y]]).key).toBe(sj.Subs(derivative, x, y).key);
  const g = sj.SymFunction('g');
  expect(subs(derivative, [[y, g(y)]]).key).toBe(sj.derivative(f(x, g(y)), [[g(y), 1]]).key);
  expect(subs(derivative, [[x, z]]).key).toBe(sj.derivative(f(z, y), [[y, 1]]).key);
  expect(subs(derivative, [[y, 0]]).key).toBe(sj.Subs(derivative, y, 0).key);
  expect(subs(derivative, [[z, x]]).key).toBe(derivative.key);
  const A = new sj.Sym('A', { commutative: false });
  const B = new sj.Sym('B', { commutative: false });
  expect(subs(mul(pow(x, -1), A), [[mul(x, A), B]]).key).toBe(mul(pow(x, -1), A).key);
  const integer = new sj.Sym('integer', { integer: true });
  expect(subs(pow(A, add(mul(4, integer), 1)), [[pow(A, mul(3, integer)), B]]).key).toBe(mul(B, pow(A, add(integer, 1))).key);
});

it('substitutes function heads with arity checks and valid derivative variables', () => {
  const g = sj.SymFunction('g');
  const replace = (e: Expr) => sj.subsFunction(e, 'f', (...args) => g(...args));
  expect(replace(add(f(x), f(y))).key).toBe(add(g(x), g(y)).key);
  expect(sj.subsFunction(f(x, y), 'f', sj.sin, [1]).key).toBe(f(x, y).key);
  expect(sj.subsFunction(f(x), 'f', sj.sin, [1]).key).toBe(sj.sin(x).key);
  expect(sj.subsFunction(sj.exp(x), 'exp', sj.sin).key).toBe(sj.sin(x).key);
  expect(sj.subsFunction(sj.sin(x), 'sin', (...args) => g(...args)).key).toBe(g(x).key);
  expect(replace(sj.derivative(f(x), [[x, 1]])).key).toBe(sj.derivative(g(x), [[x, 1]]).key);
  const derivative = sj.derivative(f(x), [[f(x), 1]]);
  const replaced = sj.subsFunction(derivative, 'f', sj.cos);
  expect(replaced.key).toBe(sj.Subs(sj.derivative(y, [[y, 1]]), y, sj.cos(x)).key);
  expect(replace(derivative).key).toBe(sj.derivative(g(x), [[g(x), 1]]).key);
});

it('rebuilds symbols carrying arguments and finds symbols under explicit binders', async () => {
  const { registerHeadResolver } = await import('../../src/core/nodes');
  class AppliedSymbol extends sj.Sym {
    override readonly args: readonly Expr[];
    constructor(value: Expr) { super('applied'); this.args = [value]; }
  }
  registerHeadResolver(AppliedSymbol, () => (value: Expr) => new AppliedSymbol(value));
  const applied = new AppliedSymbol(x);
  expect(sj.rebuild(applied, [y])).toBeInstanceOf(sj.Sym);
  class Binder extends sj.ExtensionExpr {
    constructor(args: readonly Expr[]) { super('Binder', args); }
    withArgs(args: readonly Expr[]): Expr { return new Binder(args); }
    override bindings() { return { variables: [0], scope: [1] }; }
  }
  expect([...sj.freeSymbols(new Binder([x, add(x, y), z]))].map(String).sort()).toEqual(['y', 'z']);
  const A = new sj.Sym('A', { commutative: false });
  expect(subs(mul(x, A), [[mul(x, y), z]]).key).toBe(mul(x, A).key);
  const conditional = sj.piecewise([x, sj.Lt(x, 0)], [y, sj.Gt(x, 0)], [z, true]);
  expect(String(subs(conditional, [[y, 2]]))).toBe('Piecewise((x, x < 0), (2, x > 0), (z, True))');
});

it('substitutes inverse powers and roots without choosing unknown branches', () => {
  const positive = new sj.Sym('positive', { positive: true });
  expect(subs(x, [[pow(x, -1), y]]).key).toBe(pow(y, -1).key);
  expect(subs(positive, [[pow(positive, 2), y]]).key).toBe(sj.sqrt(y).key);
  expect(subs(x, [[pow(x, 2), y]]).key).toBe(x.key);
  expect(subs(add(x, -1), [[sj.S.One, y]]).key).toBe(add(x, mul(-1, y)).key);
  expect(subs(add(x, 2), [[sj.S.One, y]]).key).toBe(add(x, 2).key);
  expect(subs(add(x, sj.S.NegativeInfinity), [[sj.S.Infinity, y]]).key).toBe(add(x, mul(-1, y)).key);
});

it('exposes the registered rebuild operation and preserves identity substitutions', async () => {
  const { impl } = await import('../../src/core/nodes');
  expect(impl.rebuild?.(new sj.Add([x, x]), [x, x]).key).toBe(mul(2, x).key);
  const A = new sj.Sym('A', { commutative: false });
  const old = mul(x, y);
  expect(subs(mul(old, A), [[old, old]]).key).toBe(mul(old, A).key);
});

it('does not extract noncommutative power blocks from nonintegral exponents', () => {
  const A = new sj.Sym('A', { commutative: false });
  const B = new sj.Sym('B', { commutative: false });
  const alpha = new sj.Sym('alpha');
  const integer = new sj.Sym('integer', { integer: true });
  for (const [exponent, old] of [[add(mul(2, alpha), 2), sj.S.Two], [add(alpha, mul(2, integer)), integer], [sj.S.Two, alpha]] as const) {
    const expression = pow(A, exponent);
    expect(subs(expression, [[pow(A, old), B]]).key).toBe(expression.key);
  }
});

it('counts large noncommutative power runs exactly', () => {
  const A = new sj.Sym('A', { commutative: false });
  const B = new sj.Sym('B', { commutative: false });
  const count = 9007199254740993n;
  expect(subs(mul(pow(x, count), pow(A, count)), [[mul(x, A), B]]).key).toBe(pow(B, count).key);
  expect(subs(mul(pow(x, 3), A), [[mul(x, A), B]]).key).toBe(mul(pow(x, 2), B).key);
});

it('uses an integral float exponent only when the coefficient ratio is exactly integral', () => {
  const x = sj.symbol('x');
  const y = sj.symbol('y');
  const z = sj.symbol('z');
  const power = (coefficient: sj.Expr) => sj.pow(x, sj.mul(coefficient, y));
  expect(power(new sj.Float(6)).subs(power(sj.Rational.of(3)), z).key).toBe(sj.pow(z, new sj.Float(2)).key);
  expect(power(sj.Rational.of(6)).subs(power(new sj.Float(3)), z).key).toBe(sj.pow(z, new sj.Float(2)).key);
  const nearSix = sj.Rational.of(6n * 10n ** 20n + 1n, 10n ** 20n);
  expect(power(nearSix).subs(power(new sj.Float(3)), z).key).toBe(power(nearSix).key);
});

it('visits limits, piecewise branches and derivative specifications as tuples', () => {
  const [x, n] = sj.symbols('x n');
  const limit = new sj.Integral([x, x, sj.S.Zero, sj.S.One]);
  expect([...sj.iterArgs(limit)].map(String)).toEqual(['Integral(x, (x, 0, 1))', 'x', '(x, 0, 1)', 'x', '0', '1']);
  const d = sj.derivative(x, [[x,n]]);
  expect([...sj.iterArgs(d)].map(String)).toContain('(x, n)');
  expect([...sj.iterArgs(sj.Sum(x, [x, 1, n]))].map(String)).toContain('(x, 1, n)');
  expect([...sj.iterArgs(sj.Piecewise([x, sj.Lt(x, 0)], [n, true]))].map(String)).toContain('(x, x < 0)');
});

it('does not replace a derivative with respect to a different independent variable', () => {
  const [x, y, z] = sj.symbols('x y z');
  const f = sj.SymFunction('f')(x, y);
  const a = sj.derivative(f, [[x, 2]]);
  expect(a.subs(sj.derivative(f, [[y, 1]]), z).key).toBe(a.key);
});

it('orders derivative replacements by their full orders and restores split symbolic powers', async () => {
  const sj = await import('../../src');
  const x = sj.symbol('x'), y = sj.symbol('y'), t = sj.symbol('t');
  const a = sj.SymFunction('a')(t);
  const first = a.diff(t);
  const second = a.diff(t, 2);
  expect(sj.subs(sj.add(a, first, second), new Map<sj.Expr, sj.Expr>([[a, x], [first, y], [second, sj.S.One]])).equals(sj.add(1, x, y))).toBe(true);
  const product = sj.parse('x**2*y**(3*x/2)');
  expect(String(sj.subs(product, [[sj.parse('x*y**(x/2)'), 2]]))).toBe('4*y**(x/2)');
  const exponential = sj.exp(sj.mul(x, sj.log(2)));
  expect(sj.subs(sj.pow(2, x), [[exponential, y]]).equals(y)).toBe(true);
});

it('matches exponential patterns only when the resulting power divides the source', async () => {
  const sj = await import('../../src');
  const { countOps } = await import('../../src/core/traverse');
  const x = sj.symbol('x');
  const y = sj.symbol('y');
  const a = sj.symbol('a');
  const raw = new sj.Mul([new sj.Pow(sj.S.One, x), y]);
  expect(countOps(raw)).toBe(5);
  expect(sj.subs(sj.pow(y, x), [[sj.exp(sj.mul(x, sj.log(2))), a]])).toEqual(sj.pow(y, x));
  const p = new sj.Mul([new sj.Pow(sj.S.One, x), sj.pow(y, x), sj.pow(y, x)]);
  const pattern = new sj.Mul([sj.pow(y, x), y]);
  const unmatched = sj.subs(p, [[pattern, a]]);
  const nested = new sj.Mul([new sj.Pow(new sj.Pow(y, x), sj.S.Half), new sj.Pow(y, sj.mul(2, x)), x]);
  expect(String(sj.subs(nested, [[sj.mul(sj.pow(y, x), x), 2]]))).toBe('2*(y**x)**(3/2)');
  expect(unmatched.has(a)).toBe(false);
  const f = sj.SymFunction('f')(x);
  const order = sj.symbol('m', { integer: true, nonnegative: true });
  const derivative = sj.derivative(f, [[x, order]]);
  expect(sj.subs(sj.add(derivative, f), new Map<sj.Expr, sj.Expr>([[f, x], [derivative, y]])).equals(sj.add(x, y))).toBe(true);
});

it('leaves unrelated exponential substitution patterns alone', () => {
  const [x, y, z] = sj.symbols('x y z');
  const power = sj.pow(x, y);
  for (const exponent of [y, new sj.Fn('log', [x])]) {
    expect(power.subs(new sj.Pow(sj.S.E, exponent), z).key).toBe(power.key);
  }
});

it('binds the free symbols of a compound limit variable only in the body', () => {
  const variable = sj.add(x, y);
  const expression = new sj.Limit([sj.add(variable, z), variable, x], '-');
  expect([...expression.freeSymbols()].map(String).sort()).toEqual(['x', 'z']);
  const pattern = new sj.Pow(sj.E, new sj.Fn('log', [y]));
  expect(x.pow(2).subs(pattern, z)).toEqual(x.pow(2));
});

it('keeps substitutions inside bound function arguments capture-free', () => {
  const [x, y] = sj.symbols('x y');
  const fy = sj.SymFunction('f')(y);
  const sum = sj.Sum(x.mul(fy), [x, 0, 2], [y, 0, 2]);
  expect(() => sum.subs(fy, x.add(y))).toThrow('dummy dependencies');
  expect(sum.subs(fy, y).equals(sj.Sum(x.mul(y), [x, 0, 2], [y, 0, 2]))).toBe(true);
  const ly = sj.log(y);
  expect(sj.Sum(ly, [x, 0, ly], [y, 0, ly]).subs(ly, y).equals(sj.Sum(ly, [x, 0, ly], [y, 0, y]))).toBe(true);
});

it('keeps powers distinct from unrelated exponential substitution patterns', () => {
  const [x, y] = sj.symbols('x y');
  const power = sj.pow(x, y);
  const logarithm = sj.fn('log', [x, 2], { evaluate: false });
  for (const exponent of [sj.sin(x), logarithm, sj.log(x)]) {
    expect(power.subs(new sj.Pow(sj.S.E, exponent), y).equals(power)).toBe(true);
  }
});

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

/**
 * User-defined functions and classes (SymPy Function/Expr subclasses), the
 * sympify protocol, and the small SymPy classes Factors, Monomial,
 * MutableDenseMatrix and Basic.
 */

import { describe, expect, it } from 'vitest';
import * as sj from '../src';
import { Expr } from '../src';

const [x, y, z] = sj.symbols('x y z') as [sj.Sym, sj.Sym, sj.Sym];
const s = (e: unknown) => sj.str(e as Expr);
const half = sj.Rational.of(1n, 2n);

describe('defineFunction', () => {
  const mysin = sj.defineFunction('mysin', {
    nargs: 1,
    eval: (a) => (a.key === sj.S.Zero.key ? 0 : undefined),
    fdiff: ([a]) => sj.cos(a!),
    rewrite: { cos: (a) => sj.fn('cos', [sj.sub(sj.mul(sj.pi, half), a)], { evaluate: false }) },
    expand: { twice: (self) => sj.mul(2, self) },
    evalf: Math.sin,
    latex: ([a]) => `\\operatorname{msin}{${a}}`,
  });

  it('evaluates, prints and recognizes its applications', () => {
    expect(s(mysin(0))).toBe('0');
    expect(s(mysin(x))).toBe('mysin(x)');
    expect(sj.latex(mysin(x))).toBe('\\operatorname{msin}{x}');
    expect(mysin.functionName).toBe('mysin');
    expect(mysin.isApplied(mysin(x))).toBe(true);
    expect(mysin.isApplied(sj.sin(x))).toBe(false);
    expect(() => mysin(x, y)).toThrow(TypeError);
    expect(() => sj.defineFunction('1bad')).toThrow(SyntaxError);
  });

  it('differentiates by the chain rule', () => {
    expect(s(sj.diff(mysin(sj.pow(x, 2)), x))).toBe('2*x*cos(x**2)');
    expect(s(sj.diff(mysin(y), x))).toBe('0');
  });

  it('rewrites, expands and evaluates numerically', () => {
    expect(s(sj.rewrite(mysin(x), 'cos'))).toBe('cos(-x + pi/2)');
    expect(s(sj.expand(sj.add(mysin(x), 1), { twice: true }))).toBe('2*mysin(x) + 1');
    expect(sj.evalf(mysin(1)).toNumber()).toBeCloseTo(Math.sin(1), 12);
    // substitution rebuilds through eval
    expect(s(sj.subs(mysin(x), [[x, 0]]))).toBe('0');
  });

  it('implementedFunction is symbolic until evaluated numerically', () => {
    const f = sj.implementedFunction('f', (t) => t * t + 1);
    expect(s(f(x))).toBe('f(x)');
    expect(sj.evalf(f(2)).toNumber()).toBe(5);
  });
});

describe('ExtensionExpr hooks', () => {
  class MyScalar extends sj.ExtensionExpr {
    constructor() {
      super('MyScalar', []);
    }
    withArgs(): Expr {
      return new MyScalar();
    }
  }
  class MyMatrixLike extends sj.ExtensionExpr {
    constructor() {
      super('MyMatrixLike', []);
    }
    withArgs(): Expr {
      return new MyMatrixLike();
    }
    override get isScalar(): boolean {
      return false;
    }
  }
  class Twice extends sj.ExtensionExpr {
    constructor(...args: sj.ExprLike[]) {
      super('Twice', args.map((a) => sj.sympify(a)));
    }
    withArgs(args: readonly Expr[]): Expr {
      return new Twice(...args);
    }
    override expandSelf(hint: string, hints: Readonly<Record<string, unknown>>): Expr | undefined {
      if (hint !== 'double') return undefined;
      if (!hints['force'] && this.args.length > 2) return this;
      return new Twice(...this.args, ...this.args);
    }
    override rewriteSelf(target: string, args: readonly Expr[]): Expr | undefined {
      return target === 'Add' ? sj.add(...args) : undefined;
    }
  }

  it('differentiates with respect to a node', () => {
    expect(s(sj.diff(new MyScalar(), new MyScalar()))).toBe('1');
    expect(s(sj.diff(new MyMatrixLike(), new MyMatrixLike()))).toBe('Derivative(MyMatrixLike(), MyMatrixLike())');
  });

  it('expands by custom hints, deep or not', () => {
    const a = new Twice(1, new Twice(2));
    expect(s(sj.expand(a, { double: true }))).toBe('Twice(1, Twice(2, 2), 1, Twice(2, 2))');
    expect(s(sj.expand(a, { double: true, deep: false }))).toBe('Twice(1, Twice(2), 1, Twice(2))');
    expect(s(sj.expand(new Twice(1, 2, 3), { double: true }))).toBe('Twice(1, 2, 3)');
    expect(s(sj.expand(new Twice(1, 2, 3), { double: true, force: true }))).toBe('Twice(1, 2, 3, 1, 2, 3)');
  });

  it('substitutes, integrates and simplifies generically without their own hooks', () => {
    expect(s(sj.subs(new Twice(x, y), [[x, 2]]))).toBe('Twice(2, y)');
    expect(s(sj.integrate(new Twice(x), x))).toBe('Integral(Twice(x), x)');
    expect(s(sj.simplify(new Twice(sj.add(sj.pow(sj.sin(x), 2), sj.pow(sj.cos(x), 2)))))).toBe('Twice(1)');
  });

  it('rewrites by target name, also inside other expressions', () => {
    expect(s(sj.rewrite(sj.sin(new Twice(x, y)), 'Add'))).toBe('sin(x + y)');
    expect(s(sj.rewrite(new Twice(x, y), 'Add', { pattern: ['Other'] }))).toBe('Twice(x, y)');
  });
});

describe('sympify', () => {
  it('uses the conversion method and the converter registry', () => {
    class Pair {
      [sj.sympifyMethod]() {
        return sj.Matrix.of([[1], [2]]);
      }
    }
    expect(String(sj.sympify(new Pair()))).toBe('Matrix([[1], [2]])');
    class Celsius {
      constructor(readonly t: number) {}
    }
    sj.converter.set(Celsius, (c: Celsius) => sj.add(c.t, sj.Rational.of(27315n, 100n)));
    expect(s(sj.sympify(new Celsius(10) as never))).toBe('5663/20');
    sj.converter.delete(Celsius);
  });

  it('converts containers element by element', () => {
    expect((sj.sympify([1, 2.5]) as Expr[]).map(s)).toEqual(['1', '2.50000000000000']);
    const m = sj.sympify(new Map([[1, 2]]));
    expect([...m].map(([k, v]) => [s(k), s(v)])).toEqual([['1', '2']]);
    expect([...sj.sympify(new Set([3]))].map(s)).toEqual(['3']);
    expect(() => sj.sympify({} as never)).toThrow(TypeError);
  });

  it('parse takes local names: values and functions', () => {
    const bitcount = (n: Expr) => (n as sj.Rational).p.toString(2).length;
    expect(s(sj.parse('bitcount(42) + O', { locals: { bitcount, O: new sj.Sym('O') } }))).toBe('O + 6');
    expect(s(sj.parse('k', { locals: { k: 3 } }))).toBe('3');
  });
});

describe('simplify options', () => {
  const [a, b] = sj.symbols('a b', { positive: true }) as [sj.Sym, sj.Sym];
  const g = sj.add(sj.log(a), sj.log(b), sj.mul(sj.log(a), sj.log(sj.pow(b, -1))));
  it('uses the measure for logarithms and rejects longer results', () => {
    const powHeavy = (e: Expr) => sj.subs(sj.countOps(e, { visual: true }), [[new sj.Sym('POW'), 10]]).subs([...sj.freeSymbols(sj.countOps(e, { visual: true }))].map((v) => [v, 1] as [Expr, number]));
    expect(s(sj.simplify(g, { measure: powHeavy }))).toBe('-log(a)*log(b) + log(a) + log(b)');
    expect(s(sj.simplify(g, { measure: () => 1, ratio: 0.5 }))).toBe(s(g));
  });
  it('countOps visual', () => {
    expect(s(sj.countOps(sj.add(sj.sin(x), sj.pow(x, 2)), { visual: true }))).toBe('ADD + POW + SIN');
  });
});

describe('Factors', () => {
  const a = new sj.Factors(sj.asPowersDict(sj.mul(x, sj.pow(y, 2))));
  it('divides like SymPy', () => {
    expect(String(a)).toBe('Factors({x: 1, y: 2})');
    expect(s(a.asExpr())).toBe('x*y**2');
    expect(a.div(a).map(String)).toEqual(['Factors({})', 'Factors({})']);
    expect(a.div(sj.mul(x, z)).map(String)).toEqual(['Factors({y: 2})', 'Factors({z: 1})']);
    expect(String(a.quo(x))).toBe('Factors({y: 2})');
    expect(String(a.rem(sj.mul(x, z)))).toBe('Factors({z: 1})');
    expect(new sj.Factors(sj.pow(2, sj.add(sj.mul(2, x), 2))).div(8).map(String)).toEqual(['Factors({2: 2*x + 2})', 'Factors({8: 1})']);
  });
  it('builds from numbers, maps and products', () => {
    expect(String(new sj.Factors(0))).toBe('Factors({0: 1})');
    expect(String(new sj.Factors(sj.Rational.of(-3n, 4n)))).toBe('Factors({-1: 1, 3: 1, 4: -1})');
    // SymPy 1.14 prints the bases in sorted order: Factors({2: 1, I: 1, x: 1})
    expect(String(new sj.Factors(sj.mul(2, sj.I, x)))).toBe('Factors({2: 1, I: 1, x: 1})');
    expect(String(new sj.Factors(new Map([[sj.S.NegOne, 1]])))).toBe('Factors({-1: 1})');
    expect(String(a.mul(new sj.Factors(sj.mul(x, sj.pow(y, -2)))))).toBe('Factors({x: 2})');
    expect(new sj.Factors().isOne).toBe(true);
    expect(new sj.Factors(0).isZero).toBe(true);
    expect([...a.gens].map(s)).toEqual(['x', 'y']);
    expect(() => a.div(0)).toThrow(RangeError);
  });
});

describe('matrices: mutable and immutable', () => {
  it('changes a mutable matrix in place and sympifies to an immutable copy', () => {
    const m = sj.MutableDenseMatrix.zeros(2);
    m.set(0, 1, x);
    m.set(-1, -1, 3);
    expect(String(m)).toBe('Matrix([[0, x], [0, 3]])');
    m.rowSwap(0, 1);
    m.colSwap(0, 1);
    expect(String(m)).toBe('Matrix([[3, 0], [x, 0]])');
    m.rowOp(0, (v) => sj.add(v, 1));
    m.colOp(1, (v, i) => sj.add(v, i));
    m.zipRowOp(1, 0, (v, u) => sj.add(v, u));
    expect(String(m)).toBe('Matrix([[4, 1], [x + 4, 2]])');
    m.copyinMatrix(0, 0, sj.Matrix.eye(1));
    expect(String(m.get(0, 0))).toBe('1');
    const frozen = sj.sympify(m) as sj.Matrix;
    expect(frozen).not.toBeInstanceOf(sj.MutableDenseMatrix);
    expect(sj.isSame(m, frozen)).toBe(false);
    expect(sj.isSame(frozen, sj.sympify(frozen))).toBe(true);
    m.fill(0);
    expect(String(frozen)).toBe('Matrix([[1, 1], [x + 4, 2]])');
    expect(() => m.set(5, 0, 1)).toThrow(RangeError);
    expect(String(sj.MutableMatrix.of([[1, 2]]))).toBe('Matrix([[1, 2]])');
  });
});

describe('isSame and equalValued', () => {
  it('compares structure, numbers with the given function', () => {
    expect(sj.isSame(sj.mul(half, x), sj.mul(half, x))).toBe(true);
    expect(sj.isSame(sj.mul(new sj.Float(0.5), x), sj.mul(half, x))).toBe(false);
    expect(sj.isSame(sj.mul(new sj.Float(0.5), x), sj.mul(half, x), sj.equalValued)).toBe(true);
    expect(sj.equalValued(new sj.Float(2), 2)).toBe(true);
    expect(sj.equalValued(new sj.Float(0.1), sj.Rational.of(1n, 10n))).toBe(false);
    expect(sj.isSame(1, 1)).toBe(true);
  });
});

describe('Basic, Monomial and Poly helpers', () => {
  it('matches inside generic Basic nodes', () => {
    const [a, b, c] = sj.symbols('a b c') as [sj.Sym, sj.Sym, sj.Sym];
    const w = new sj.Wild('x');
    const m = sj.match(sj.Basic(sj.add(a, b, c), sj.add(b, c)), sj.Basic(sj.add(a, w), w));
    expect(m instanceof Map && s(m.get(w))).toBe('b + c');
    expect(s(sj.Basic(x, 1))).toBe('Basic(x, 1)');
  });
  it('Monomial', () => {
    const m = new sj.Monomial([2, 0], [x, y]);
    expect(String(m)).toBe('x**2*y**0');
    expect(s(m.asExpr())).toBe('x**2');
    expect(String(m.mul([1, 1]))).toBe('x**3*y**1');
    expect(String(new sj.Monomial([1, 2]).gcd([0, 3]))).toBe('Monomial((0, 2))');
    expect(String(new sj.Monomial([1]).lcm([3]))).toBe('Monomial((3,))');
    expect(() => new sj.Monomial([1]).asExpr()).toThrow();
  });
  it('termwise and per', () => {
    const p = sj.Poly.from(sj.add(sj.pow(x, 2), sj.mul(20, x), 400));
    expect(String(p.termwise((k, c) => sj.floor(sj.mul(c, sj.pow(10, k[0]! - 2)))))).toBe("Poly(x**2 + 2*x + 4, x, domain='ZZ')");
    expect(String(p.termwise((k, c) => [[k[0]! + 1], c] as const))).toBe("Poly(x**3 + 20*x**2 + 400*x, x, domain='ZZ')");
    expect(() => p.termwise(() => [[0], 1] as const)).toThrow();
    expect(String(p.per([1, 1], { gens: [y] }))).toBe("Poly(y + 1, y, domain='ZZ')");
    expect(String(sj.Poly.from(sj.mul(x, y), [x, y]).per([[1, 0], [2]]))).toBe("Poly(x*y + 2, x, y, domain='ZZ')");
    expect(s(p.per([5], { remove: 0 }))).toBe('5');
  });
});

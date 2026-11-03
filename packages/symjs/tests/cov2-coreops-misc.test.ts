// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Coverage of the small core modules: AccumBounds (core and functions), relations and
// Piecewise (core/logic), And/Or/Not/Xor (core/boolalg), assumption queries, numeric helpers
// and the node classes. Expected values are SymPy 1.14's (sympy.core.tests.test_relational,
// test_assumptions, test_numbers, sympy.calculus.tests.test_accumulationbounds), obtained by
// running SymPy; deviations are explained where they occur.
import { inspect } from 'node:util';
import { describe, expect, it } from 'vitest';
import * as sj from '../src';
import { InvariantError } from '../src/core/errors';
import {
  Add,
  BoolAtom,
  Expr,
  ExtensionExpr,
  Float,
  Mul,
  Pow,
  Rational,
  S,
  WildFunction,
  asRational,
  compareExpr,
} from '../src/core/nodes';
import { add, mul, pow } from '../src/core/ops';
import { isNegative, isPositive, isReal } from '../src/core/assumptions';
import { numAdd, numCmp, numInv, numMul, numPowInt } from '../src/core/num';
import { factorInt, iroot, ipow, lcm } from '../src/core/numbers';
import { Eq, Ge, Gt, Le, Lt, Ne, piecewise, rel } from '../src/core/logic';
import { BoolOp, and, not, or, xor } from '../src/core/boolalg';

const { I, oo, zoo, nan, pi } = sj;
const [x, y, z, a] = sj.symbols('x y z a');
const s = (e: Expr): string => e.toString();
const R = (p: number, q = 1) => Rational.of(p, q);
const A = sj.AccumBounds;
const negOo = mul(-1, oo);

describe('AccumBounds (SymPy test_accumulationbounds)', () => {
  it('has delta, mid, LaTeX and membership', () => {
    const ab = A(1, 3);
    expect(s((ab as sj.AccumBoundsNode).delta)).toBe('2');
    expect(s((ab as sj.AccumBoundsNode).mid)).toBe('2');
    expect(sj.latex(ab)).toBe('\\left\\langle 1, 3\\right\\rangle');
    expect((ab as sj.AccumBoundsNode).contains(2)).toBe(true);
    expect((ab as sj.AccumBoundsNode).contains(4)).toBe(false);
  });
  it('rebuilds with new bounds by substitution', () => {
    // SymPy: AccumBounds(1, 2).subs(2, 3) = AccumBounds(1, 3)
    expect(s(A(1, 2).subs(R(2), 3))).toBe('AccumBounds(1, 3)');
  });
  it('intersects and unites intervals', () => {
    const ab = (lo: number, hi: number) => A(lo, hi) as sj.AccumBoundsNode;
    // SymPy: AccumBounds(1, 3).intersection(AccumBounds(2, 5)) = AccumBounds(2, 3), either way round
    expect(s(ab(1, 3).intersection(ab(2, 5)))).toBe('AccumBounds(2, 3)');
    expect(s(ab(2, 5).intersection(ab(1, 3)))).toBe('AccumBounds(2, 3)');
    expect(ab(1, 2).intersection(ab(3, 4))).toBe(sj.EmptySet);
    // SymPy: AccumBounds(1, 3).intersection(FiniteSet(2, 7)) = {2}
    expect(s(ab(1, 3).intersection(new sj.FiniteSet([R(2), R(7)])))).toBe('{2}');
    expect(s(ab(1, 3).union(ab(2, 5)))).toBe('AccumBounds(1, 5)');
    expect(() => ab(1, 2).union(ab(3, 4))).toThrow(RangeError);
  });
  it('multiplies intervals with an unbounded end (0*oo = 0 for the bounds)', () => {
    // SymPy: AccumBounds(0, oo)*AccumBounds(-1, 1) = AccumBounds(-oo, oo)
    expect(s(mul(A(0, oo), A(-1, 1)))).toBe('AccumBounds(-oo, oo)');
    // SymPy gives AccumBounds(-oo, 1)*0 = AccumBounds(-oo, 0); every point of the interval times 0 is 0
    expect(mul(A(negOo, 1), 0)).toBe(S.Zero);
  });
  it('keeps a non-real number beside the interval', () => {
    // SymPy: AccumBounds(1, 2) + I, I*AccumBounds(1, 2), (1 + I)*AccumBounds(1, 2)
    expect(s(add(A(1, 2), I))).toBe('AccumBounds(1, 2) + I');
    expect(s(mul(I, A(1, 2)))).toBe('I*AccumBounds(1, 2)');
    expect(s(mul(A(1, 2), add(1, I)))).toBe('(1 + I)*AccumBounds(1, 2)');
  });
  it('is its own conjugate, adjoint and transpose', () => {
    // SymPy: conjugate(AccumBounds(1, 2)) = adjoint(...) = transpose(...) = AccumBounds(1, 2)
    expect(s(sj.conjugate(A(1, 2)))).toBe('AccumBounds(1, 2)');
    expect(s(sj.adjoint(A(1, 2)))).toBe('AccumBounds(1, 2)');
    expect(s(sj.transpose(A(1, 2)))).toBe('AccumBounds(1, 2)');
  });
  it('raises intervals to integer powers', () => {
    // SymPy: AccumBounds(1, 3)**0 = 1, AccumBounds(-3, -1)**2 = AccumBounds(1, 9), AccumBounds(-3, 1)**2 = AccumBounds(0, 9)
    expect(pow(A(1, 3), 0)).toBe(S.One);
    expect(s(pow(A(-3, -1), 2))).toBe('AccumBounds(1, 9)');
    expect(s(pow(A(-3, 1), 2))).toBe('AccumBounds(0, 9)');
    expect(s(pow(A(-3, -1), 3))).toBe('AccumBounds(-27, -1)');
    // SymPy: AccumBounds(2, 3)**-2 = AccumBounds(1/9, 1/4), AccumBounds(-1, 2)**-2 = AccumBounds(0, oo)
    expect(s(pow(A(2, 3), -2))).toBe('AccumBounds(1/9, 1/4)');
    expect(s(pow(A(-1, 2), -2))).toBe('AccumBounds(0, oo)');
    expect(s(pow(A(-1, 2), -1))).toBe('AccumBounds(-oo, oo)');
  });
  it('raises nonnegative intervals to fractional powers', () => {
    // SymPy: AccumBounds(1, 4)**(1/2) = AccumBounds(1, 2), AccumBounds(1, 4)**(-1/2) = AccumBounds(1/2, 1)
    expect(s(pow(A(1, 4), R(1, 2)))).toBe('AccumBounds(1, 2)');
    expect(s(pow(A(1, 4), R(-1, 2)))).toBe('AccumBounds(1/2, 1)');
    // SymPy: AccumBounds(0, 4)**(1/2) = AccumBounds(0, 2), AccumBounds(0, 4)**(-1/2) = AccumBounds(1/2, oo)
    expect(s(pow(A(0, 4), R(1, 2)))).toBe('AccumBounds(0, 2)');
    expect(s(pow(A(0, 4), R(-1, 2)))).toBe('AccumBounds(1/2, oo)');
  });
  it('leaves a fractional power of an interval with negative numbers unevaluated', () => {
    // SymPy: AccumBounds(-1, 4)**(1/2) = sqrt(AccumBounds(-1, 4)); AccumBounds(-1, 4)**(1/3) likewise
    const e = pow(A(-1, 4), R(1, 2));
    expect(e).toBeInstanceOf(Pow);
    expect(s(e)).toBe('sqrt(AccumBounds(-1, 4))');
    expect(s(pow(A(-1, 4), R(1, 3)))).toBe('AccumBounds(-1, 4)**(1/3)');
  });
  it('rejects bounds that are not ordered real numbers', () => {
    expect(() => A(2, 1)).toThrow(RangeError);
    expect(() => A(x, 1)).toThrow(TypeError);
    expect(s(A(1, 1))).toBe('1');
  });
});

describe('functions of an AccumBounds argument', () => {
  it('maps monotone and periodic functions', () => {
    // SymPy: tan(AccumBounds(0, 1)) = AccumBounds(0, tan(1)), tan(AccumBounds(1, 2)) = AccumBounds(-oo, oo)
    expect(s(sj.tan(A(0, 1)))).toBe('AccumBounds(0, tan(1))');
    expect(s(sj.tan(A(1, 2)))).toBe('AccumBounds(-oo, oo)');
    // SymPy: sin(AccumBounds(0, 3)) = AccumBounds(0, 1), cos(AccumBounds(1, 2)) = AccumBounds(cos(2), cos(1))
    expect(s(sj.sin(A(0, 3)))).toBe('AccumBounds(0, 1)');
    expect(s(sj.cos(A(1, 2)))).toBe('AccumBounds(cos(2), cos(1))');
    expect(s(sj.sin(A(negOo, 1)))).toBe('AccumBounds(-1, 1)');
  });
  it('evaluates sec, csc and cot through cos, sin and tan', () => {
    // SymPy: sec(AccumBounds(1, 2)) = AccumBounds(-oo, oo), csc(...) = AccumBounds(1, 1/sin(1)),
    // cot(...) = AccumBounds(cot(2), cot(1))
    expect(s(sj.sec(A(1, 2)))).toBe('AccumBounds(-oo, oo)');
    expect(s(sj.csc(A(1, 2)))).toBe('AccumBounds(1, 1/sin(1))');
    expect(s(sj.cot(A(1, 2)))).toBe('AccumBounds(cot(2), cot(1))');
  });
  it('maps decreasing functions', () => {
    // SymPy leaves acos(AccumBounds(0, 1)) and acot(AccumBounds(1, 2)) unevaluated; both functions are
    // decreasing, so the images AccumBounds(acos(1), acos(0)) and AccumBounds(acot(2), acot(1)) are given here
    expect(s(sj.acos(A(0, 1)))).toBe('AccumBounds(0, pi/2)');
    expect(s(sj.acot(A(1, 2)))).toBe('AccumBounds(acot(2), pi/4)');
  });
  it('leaves other functions unevaluated', () => {
    // SymPy: cosh(AccumBounds(1, 2)) stays
    expect(s(sj.cosh(A(1, 2)))).toBe('cosh(AccumBounds(1, 2))');
  });
});

describe('relations (SymPy test_relational)', () => {
  it('compares with nan', () => {
    // SymPy: Eq(nan, nan) = False, Ne(nan, 1) = True, Lt(nan, 1) raises TypeError
    expect(Eq(nan, nan)).toBe(S.false);
    expect(Ne(nan, 1)).toBe(S.true);
    expect(Eq(nan, x)).toBe(S.false);
    expect(() => Lt(nan, 1)).toThrow('Invalid NaN comparison');
    expect(() => Lt(x, nan)).toThrow(TypeError);
  });
  it('compares infinities', () => {
    // SymPy: Eq(oo, oo) = True, Ne(oo, oo) = False, Le(oo, oo) = True, Lt(oo, oo) = False
    expect(Eq(oo, oo)).toBe(S.true);
    expect(Ne(oo, oo)).toBe(S.false);
    expect(Le(oo, oo)).toBe(S.true);
    expect(Lt(oo, oo)).toBe(S.false);
    // SymPy: Lt(-oo, oo) = True, Gt(oo, 1) = True, Eq(oo, 1) = False, Ne(-oo, 2) = True
    expect(Lt(negOo, oo)).toBe(S.true);
    expect(Gt(oo, 1)).toBe(S.true);
    expect(Ge(negOo, 1)).toBe(S.false);
    expect(Eq(oo, 1)).toBe(S.false);
    expect(Ne(negOo, 2)).toBe(S.true);
  });
  it('compares with zoo', () => {
    // SymPy: Eq(zoo, 1) = False, Ne(zoo, 1) = True, Eq(zoo, zoo) = True, Eq(zoo, oo) = False
    expect(Eq(zoo, 1)).toBe(S.false);
    expect(Ne(zoo, 1)).toBe(S.true);
    expect(Eq(zoo, zoo)).toBe(S.true);
    expect(Eq(zoo, oo)).toBe(S.false);
    // SymPy: Lt(zoo, 1) and Le(zoo, zoo) raise TypeError
    expect(() => Lt(zoo, 1)).toThrow('Invalid comparison of non-real zoo');
    expect(() => Le(zoo, zoo)).toThrow(TypeError);
  });
  it('compares numbers', () => {
    // SymPy: Lt(Float(1.5), 2) = True, Ne(pi, 3) = True
    expect(Lt(1.5, 2)).toBe(S.true);
    expect(Ne(pi, 3)).toBe(S.true);
    expect(Eq(pi, 3)).toBe(S.false);
    // SymPy: Eq(sin(pi/7)**2 + cos(pi/7)**2, 1) stays (the difference is 0 only numerically)
    const t = mul(pi, R(1, 7));
    expect(s(Eq(add(pow(sj.sin(t), 2), pow(sj.cos(t), 2)), 1))).toBe('Eq(sin(pi/7)**2 + cos(pi/7)**2, 1)');
    expect(s(rel('Le', x, y))).toBe('x <= y');
  });
});

describe('Piecewise (SymPy Piecewise.eval)', () => {
  it('drops False conditions and gives nan when none is left', () => {
    // SymPy: Piecewise((x, False), (1, True)) = 1; Piecewise((x, False)) = nan
    expect(s(piecewise([x, false], [1, true]))).toBe('1');
    expect(piecewise([x, false])).toBe(nan);
    expect(piecewise([x, S.false], [y, false])).toBe(nan);
  });
  it('turns a boolean Piecewise condition into ITE', () => {
    // SymPy: Piecewise((1, Piecewise((True, x > 0), (And(y > 0, z > 0), True))), (0, True))
    //   = Piecewise((1, ITE(x > 0, True, (y > 0) & (z > 0))), (0, True))
    const inner = piecewise([S.true, Gt(x, 0)], [and(Gt(y, 0), Gt(z, 0)), true]);
    expect(s(piecewise([1, inner], [0, true]))).toBe('Piecewise((1, ITE(x > 0, True, (y > 0) & (z > 0))), (0, True))');
    // SymPy: Piecewise((1, Piecewise((Lt(2, y), x > 0), (Lt(3, z), True))), (0, True))
    //   = Piecewise((1, ITE(x > 0, y > 2, z > 3)), (0, True))
    const inner2 = piecewise([Lt(2, y), Gt(x, 0)], [Lt(3, z), true]);
    expect(s(piecewise([1, inner2], [0, true]))).toBe('Piecewise((1, ITE(x > 0, y > 2, z > 3)), (0, True))');
  });
});

describe('And, Or, Not, Xor (SymPy logic.boolalg)', () => {
  it('rebuilds with new arguments', () => {
    // SymPy: Not(x).subs(x, y) = ~y; ITE(x > 0, y > 0, z > 0).subs(x, a) = ITE(a > 0, y > 0, z > 0)
    expect(s(not(x).subs(x, y))).toBe('~y');
    const ite = new BoolOp('ITE', [Gt(x, 0), Gt(y, 0), Gt(z, 0)]);
    expect(s(ite.subs(x, a))).toBe('ITE(a > 0, y > 0, z > 0)');
    expect(s(xor(x, y).subs(x, z))).toBe('y ^ z');
  });
  it('prints ITE and Xor in LaTeX', () => {
    // SymPy: latex(ITE(x > 0, y > 0, z > 0)) = \operatorname{ITE}\left(x > 0, y > 0, z > 0\right)
    const ite = new BoolOp('ITE', [Gt(x, 0), Gt(y, 0), Gt(z, 0)]);
    expect(sj.latex(ite)).toBe('\\operatorname{ITE}\\left(x > 0, y > 0, z > 0\\right)');
    expect(sj.latex(xor(x, y))).toBe('x \\veebar y');
  });
  it('prints relations with -oo first in And', () => {
    // SymPy: str(And(Gt(x, -oo), Gt(y, 0))) = (x > -oo) & (y > 0); And(Lt(-oo, x), Gt(y, 0), z) = (-oo < x) & z & (y > 0)
    expect(s(and(Gt(x, negOo), Gt(y, 0)))).toBe('(x > -oo) & (y > 0)');
    expect(s(and(Lt(negOo, x), Gt(y, 0), z))).toBe('(-oo < x) & z & (y > 0)');
  });
  it('reads the integers 1 and 0 as true and false and rejects other numbers', () => {
    // SymPy: And(1, x) = x, Or(0, x) = x, Not(1) = False, Not(2) = False, Xor(1, x) = ~x
    expect(and(1, x)).toBe(x);
    expect(or(0, x)).toBe(x);
    expect(not(1)).toBe(S.false);
    expect(not(0)).toBe(S.true);
    expect(not(2)).toBe(S.false);
    expect(s(xor(1, x))).toBe('~x');
    // SymPy: And(2, x), And(S.Half, x) and Or(Float(1.0), x) raise TypeError
    expect(() => and(2, x)).toThrow('expecting bool or Boolean, not `2`.');
    expect(() => and(R(1, 2), x)).toThrow(TypeError);
    expect(() => or(1.5, x)).toThrow(TypeError);
  });
});

describe('assumption queries (SymPy test_assumptions)', () => {
  it('knows that 0 to a negative power is not a real number', () => {
    // 0**-1 is zoo; the raw power is not known to be real
    expect(isReal(new Pow(S.Zero, S.NegOne))).toBe(undefined);
  });
  it('knows that a positive power of a nonnegative number is real', () => {
    // SymPy: sqrt(y).is_real is True for nonnegative y
    const yn = new sj.Sym('y', { nonnegative: true });
    expect(isReal(sj.sqrt(yn))).toBe(true);
  });
  it('does not know the sign of Abs(x)', () => {
    // SymPy: Abs(x).is_positive is None
    expect(isPositive(sj.Abs(x))).toBe(undefined);
    expect(isNegative(sj.Abs(x))).toBe(undefined);
    // SymPy gives None for Abs(x).is_positive with zero=False, but the modulus of a nonzero number is positive
    expect(isPositive(sj.Abs(new sj.Sym('x', { zero: false })))).toBe(true);
  });
  it('knows a product with one imaginary factor is not real', () => {
    const p = new sj.Sym('p', { positive: true });
    expect(isReal(mul(I, p))).toBe(false);
    expect(isReal(mul(I, x))).toBe(undefined);
  });
});

describe('numeric helpers', () => {
  it('works on Floats and Rationals', () => {
    expect(s(numAdd(new Float(1.5), R(1, 2)))).toBe('2.00000000000000');
    expect(s(numMul(R(1, 2), new Float(3)))).toBe('1.50000000000000');
    expect(s(numAdd(new Float(1.5, 100), new Float(1.5)))).toBe('3.0000000000000000000000000000');
    expect(numCmp(new Float(1.5), R(3, 2))).toBe(0);
    expect(numCmp(R(1), new Float(1.5))).toBe(-1);
    expect(numCmp(new Float(2.5), new Float(1.5))).toBe(1);
    expect(() => numInv(S.Zero)).toThrow(RangeError);
    expect(() => numPowInt(S.Zero, -1n)).toThrow(RangeError);
  });
  it('computes bigint helpers', () => {
    expect(lcm(0n, 5n)).toBe(0n);
    expect(lcm(4n, -6n)).toBe(12n);
    expect(() => ipow(2n, -1n)).toThrow(RangeError);
    expect(() => iroot(-1n, 2n)).toThrow(RangeError);
    expect(iroot(1n, 3n)).toBe(1n);
    expect(iroot(10n, 1n)).toBe(10n);
    expect(iroot(3n, 64n)).toBe(1n);
    expect(iroot(26n, 3n)).toBe(2n);
    expect(iroot(27n, 3n)).toBe(3n);
    expect(() => factorInt(0n)).toThrow(RangeError);
  });
  it('takes integer roots beyond the double range', () => {
    // a floating-point first guess overflows beyond 2**1024
    const big = 2n ** 1100n;
    expect(iroot(big, 2n)).toBe(2n ** 550n);
    expect(iroot(big + 1n, 2n)).toBe(2n ** 550n);
    expect(iroot(big - 1n, 2n)).toBe(2n ** 550n - 1n);
    const c = 3n ** 700n;
    expect(iroot(c, 7n)).toBe(3n ** 100n);
    // SymPy: sqrt(2**1100) = 2**550
    expect(sj.sqrt(Rational.of(big)).equals(Rational.of(2n ** 550n))).toBe(true);
  });
});

/** A minimal extension node (the extension API defaults). */
class Box extends ExtensionExpr {
  constructor(args: readonly Expr[]) {
    super('Box', args);
  }
  withArgs(args: readonly Expr[]): Expr {
    return new Box(args);
  }
}

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

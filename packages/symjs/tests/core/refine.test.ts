// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/core/refine.ts.
// ask and refine (SymPy sympy.assumptions). Where symjs differs, the comment gives SymPy's
// answer and why symjs keeps its own.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { defined } from '../../src/core/guard';

const { Q, ask, refine } = sj;
const x = sj.symbol('x');
const y = sj.symbol('y');
const s = (e: unknown): string => String(e);

it('recognizes a product of three imaginary factors', () => {
  const [u, v, w] = sj.symbols('u v w', { imaginary: true });
  expect(ask(Q.real(sj.mul(u, v, w)))).toBe(false);
});

it('distinguishes nonreal inverse sine and cosine values from extended reals', () => {
  expect(ask(Q.extended_real(sj.asin(2)))).toBe(false);
  expect(ask(Q.extended_real(sj.acos(2)))).toBe(false);
  expect(sj.isReal(sj.asin(-2))).toBe(false);
  expect(ask(Q.extended_real(sj.asin(x)))).toBe('unknown');
});

const locals: Record<string, (...a: sj.Expr[]) => sj.Expr> = {
  ...Object.fromEntries(Object.keys(Q).map((k) => [`Q_${k}`, (...a: sj.Expr[]) => defined(Q[k], k)(...a)])),
  Xor: (...a) => sj.Xor(...a),
  ITE: (a, b, c) => sj.ITE(defined(a), defined(b), defined(c)),
  Rational: (p, q) => sj.mul(defined(p), sj.pow(defined(q), -1)),
  f: (...a) => sj.SymFunction('f')(...a),
  Implies: (...a) => sj.Implies(...a),
  Equivalent: (...a) => sj.Equivalent(...a),
  Nand: (...a) => sj.Nand(...a),
  Nor: (...a) => sj.Nor(...a),
  Xnor: (...a) => sj.Xnor(...a),
};

/** Symbols with assumptions: ni (integer), rr (real) and nc (noncommutative). */
const symbols = {
  ni: sj.symbol('ni', { integer: true }),
  rr: sj.symbol('rr', { real: true }),
  nc: sj.symbol('nc', { commutative: false }),
};

/** Parses SymPy syntax with Q.<name>(...) predicates. */
const P = (src: string): sj.Expr => sj.parse(src.replace(/Q\.(\w+)/g, 'Q_$1'), { symbols, locals: { ...locals, True: sj.S.true, False: sj.S.false } });

type Case = readonly [mode: 'ask' | 'refine', expr: string, assumptions: string, expected: string];

const run = ([mode, e, a]: Case): string => {
  const assumptions = a === 'True' ? true : P(a);
  try {
    return mode === 'ask' ? String(ask(P(e), assumptions)) : String(refine(P(e), assumptions));
  } catch (err) {
    return `ERR ${err instanceof Error ? err.name : String(err)}`;
  }
};

const CASES: readonly Case[] = [
  ["ask", "Q.real(x)", "Xor(Q.positive(x), Q.negative(x))", "true"],
  ["ask", "Q.positive(x-y)", "Q.gt(x, y)", "true"],  // SymPy 1.14: unknown (SymPy does not use relations between symbols; a > b means a - b > 0)
  ["ask", "Q.negative(x-y)", "Q.lt(x, y)", "true"],  // SymPy 1.14: unknown (SymPy does not use relations between symbols; a < b means a - b < 0)
  ["ask", "Q.nonnegative(x-y)", "Q.ge(x, y)", "true"],  // SymPy 1.14: unknown (SymPy does not use relations between symbols; a >= b means a - b >= 0)
  ["ask", "Q.nonpositive(x-y)", "Q.le(x, y)", "true"],  // SymPy 1.14: unknown (SymPy does not use relations between symbols; a <= b means a - b <= 0)
  ["ask", "Q.zero(x-y)", "Q.eq(x, y)", "true"],  // SymPy 1.14: unknown (SymPy does not use relations between symbols; a = b means a - b = 0)
  ["ask", "Q.zero(x-y)", "Q.ne(x, y)", "false"],  // SymPy 1.14: unknown (SymPy does not use relations between symbols; a != b means a - b != 0)
  ["ask", "Q.lt(x, y)", "Q.lt(x, y)", "true"],
  ["ask", "Q.ge(x, y)", "Q.gt(x, y)", "true"],  // SymPy 1.14: unknown (SymPy does not use relations between symbols; a > b means a - b > 0)
  ["ask", "Q.le(x, y)", "Q.lt(x, y)", "true"],  // SymPy 1.14: unknown (SymPy does not use relations between symbols; a < b means a - b < 0)
  ["ask", "Q.eq(x, y)", "Q.gt(x, y)", "false"],  // SymPy 1.14: unknown (SymPy does not use relations between symbols; a > b means a - b > 0)
  ["ask", "Q.ne(x, y)", "Q.gt(x, y)", "true"],  // SymPy 1.14: unknown (SymPy does not use relations between symbols; a > b means a - b > 0)
  ["ask", "x < y", "Q.lt(x, y)", "true"],
  ["ask", "x >= y", "Q.gt(x, y)", "true"],  // SymPy 1.14: unknown (SymPy does not use relations between symbols; a > b means a - b > 0)
  ["ask", "x <= y", "Q.lt(x, y)", "true"],  // SymPy 1.14: unknown (SymPy does not use relations between symbols; a < b means a - b < 0)
  ["ask", "Q.real(x)", "Q.infinite(x)", "false"],
  ["ask", "Q.prime(0)", "True", "false"],
  ["ask", "Q.prime(1)", "True", "false"],
  ["ask", "Q.prime(2305843009213693951)", "True", "true"],
  ["ask", "Q.prime(1373653)", "True", "false"],
  ["ask", "Q.prime(3215031751)", "True", "false"],
  ["ask", "Q.prime(1000000007)", "True", "true"],
  ["ask", "Q.prime(25326001)", "True", "false"],
  ["ask", "Q.prime(43*47)", "True", "false"],
  ["ask", "Q.composite(2305843009213693953)", "True", "true"],
  ["ask", "Q.real(oo)", "True", "false"],
  ["ask", "Q.real(I)", "True", "false"],
  ["ask", "Q.real(2*I)", "True", "false"],
  ["ask", "Q.real(x*y)", "Q.rational(x) & Q.rational(y)", "true"],
  ["ask", "Q.extended_real(oo)", "True", "true"],
  ["ask", "Q.extended_real(zoo)", "True", "false"],
  ["ask", "Q.extended_real(x+1)", "Q.real(x)", "true"],
  ["ask", "Q.extended_real(x)", "True", "unknown"],
  ["ask", "Q.positive(oo)", "True", "false"],
  ["ask", "Q.negative(oo)", "True", "false"],
  ["ask", "Q.nonnegative(oo)", "True", "false"],
  ["ask", "Q.nonpositive(oo)", "True", "false"],
  ["ask", "Q.zero(oo)", "True", "false"],
  ["ask", "Q.nonzero(oo)", "True", "false"],
  ["ask", "Q.nonpositive(x+1)", "Q.positive(x)", "false"],
  // SymPy ask gives None; x <= 0 implies x - 1 < 0, as Symbol('x', nonpositive=True) - 1 is_nonpositive True says
  ["ask", "Q.nonpositive(x-1)", "Q.nonpositive(x)", "true"],
  ["ask", "Q.nonpositive(I)", "True", "false"],
  ["ask", "Q.nonpositive(x)", "True", "unknown"],
  ["ask", "Q.zero(x+1)", "Q.positive(x)", "false"],
  ["ask", "Q.zero(I*x)", "Q.real(x)", "unknown"],  // SymPy 1.14: false (wrong in SymPy: x = 0 is real and I*x = 0)
  ["ask", "Q.zero(x*y)", "Q.nonzero(x) & Q.nonzero(y)", "false"],
  ["ask", "Q.zero(sin(1))", "True", "false"],
  ["ask", "Q.zero(I*f(x))", "Q.positive(f(x))", "false"],
  ["ask", "Q.nonzero(I)", "True", "false"],
  ["ask", "Q.nonzero(x+1)", "Q.positive(x)", "true"],
  ["ask", "Q.nonzero(x*y)", "Q.nonzero(x) & Q.nonzero(y)", "true"],
  ["ask", "Q.nonzero(2*x+1)", "Q.integer(x)", "true"],  // SymPy 1.14: unknown (an odd integer is nonzero)
  ["ask", "Q.nonzero(x+y)", "Q.positive(x) & Q.positive(y)", "true"],
  ["ask", "Q.nonzero(x)", "Q.complex(x)", "unknown"],
  ["ask", "Q.nonzero(x+1)", "Q.odd(x+1)", "true"],
  ["ask", "Q.extended_positive(oo)", "True", "true"],
  ["ask", "Q.extended_positive(-oo)", "True", "false"],
  ["ask", "Q.extended_positive(x+1)", "Q.positive(x)", "true"],
  // SymPy ask gives None; x <= 0 implies x - 1 < 0 (SymPy's is_positive of x - 1 for a nonpositive x is False)
  ["ask", "Q.extended_positive(x-1)", "Q.nonpositive(x)", "false"],
  ["ask", "Q.extended_positive(x)", "True", "unknown"],
  ["ask", "Q.extended_positive(pi)", "True", "true"],
  ["ask", "Q.extended_negative(-oo)", "True", "true"],
  ["ask", "Q.extended_negative(oo)", "True", "false"],
  ["ask", "Q.extended_negative(x-1)", "Q.negative(x)", "true"],
  ["ask", "Q.extended_negative(x)", "True", "unknown"],
  ["ask", "Q.extended_nonnegative(oo)", "True", "true"],
  ["ask", "Q.extended_nonnegative(x+1)", "Q.positive(x)", "true"],
  ["ask", "Q.extended_nonnegative(x)", "True", "unknown"],
  ["ask", "Q.extended_nonpositive(-oo)", "True", "true"],
  ["ask", "Q.extended_nonpositive(x-1)", "Q.negative(x)", "true"],
  ["ask", "Q.extended_nonpositive(x)", "True", "unknown"],
  ["ask", "Q.extended_nonzero(oo)", "True", "true"],
  ["ask", "Q.extended_nonzero(x+1)", "Q.positive(x)", "true"],
  ["ask", "Q.extended_nonzero(x)", "True", "unknown"],
  ["ask", "Q.positive_infinite(oo)", "True", "true"],
  ["ask", "Q.positive_infinite(-oo)", "True", "false"],
  ["ask", "Q.positive_infinite(x+1)", "Q.real(x)", "false"],
  ["ask", "Q.positive_infinite(x)", "True", "unknown"],
  ["ask", "Q.negative_infinite(-oo)", "True", "true"],
  ["ask", "Q.negative_infinite(oo)", "True", "false"],
  ["ask", "Q.negative_infinite(x+1)", "Q.real(x)", "false"],
  ["ask", "Q.negative_infinite(x)", "True", "unknown"],
  ["ask", "Q.integer(oo)", "True", "false"],
  ["ask", "Q.integer(pi)", "True", "false"],
  ["ask", "Q.integer(GoldenRatio)", "True", "false"],
  ["ask", "Q.integer(Rational(1,2))", "True", "false"],
  ["ask", "Q.integer(x+1)", "Q.irrational(x)", "false"],
  ["ask", "Q.noninteger(Rational(1,2))", "True", "true"],  // SymPy 1.14: unknown (1/2 is a real non-integer)
  ["ask", "Q.noninteger(2)", "True", "false"],  // SymPy 1.14: unknown (2 is an integer)
  ["ask", "Q.noninteger(x)", "True", "unknown"],
  ["ask", "Q.irrational(Rational(1,2))", "True", "false"],
  ["ask", "Q.irrational(I)", "True", "false"],
  ["ask", "Q.irrational(x)", "True", "unknown"],
  ["ask", "Q.irrational(x+1)", "Q.irrational(x)", "true"],
  ["ask", "Q.transcendental(pi)", "True", "true"],  // SymPy 1.14: unknown (pi is transcendental (Lindemann))
  ["ask", "Q.transcendental(2)", "True", "false"],
  ["ask", "Q.transcendental(x)", "True", "unknown"],
  ["ask", "Q.transcendental(x+pi)", "Q.algebraic(x)", "true"],  // SymPy 1.14: unknown (algebraic plus transcendental is transcendental)
  ["ask", "Q.even(Rational(1,2))", "True", "false"],
  ["ask", "Q.even(x*y)", "Q.odd(x) & Q.odd(y)", "false"],
  ["ask", "Q.odd(x*y)", "Q.odd(x) & Q.odd(y)", "true"],
  ["ask", "Q.odd(x*y)", "Q.odd(x) & Q.integer(y)", "unknown"],
  ["ask", "Q.even(x*y)", "Q.integer(x)", "unknown"],
  ["ask", "Q.even(x+y)", "Q.odd(x) & Q.odd(y)", "true"],
  ["ask", "Q.odd(x+y)", "Q.odd(x) & Q.even(y)", "true"],
  ["ask", "Q.even(x+y)", "Q.integer(x) & Q.integer(y)", "unknown"],
  ["ask", "Q.even(x+y)", "Q.integer(x)", "unknown"],
  ["ask", "Q.even(x**2)", "Q.even(x)", "true"],
  ["ask", "Q.odd(x**y)", "Q.odd(x) & Q.positive(y) & Q.integer(y)", "true"],
  ["ask", "Q.even(x**y)", "Q.integer(x) & Q.positive(y) & Q.integer(y)", "unknown"],
  ["ask", "Q.even(x**(-1))", "Q.even(x)", "unknown"],
  ["ask", "Q.even(Abs(x))", "Q.even(x)", "true"],
  ["ask", "Q.odd(Abs(x))", "Q.integer(x)", "unknown"],
  ["ask", "Q.even(sin(x))", "Q.integer(sin(x)) & ~Q.odd(sin(x))", "true"],
  ["ask", "Q.even(x)", "Q.integer(x) & ~Q.odd(x)", "true"],
  ["ask", "Q.odd(x)", "Q.integer(x) & ~Q.even(x)", "true"],
  ["ask", "Q.even(x)", "Q.irrational(x)", "false"],
  ["ask", "Q.prime(x*y)", "Q.integer(x) & Q.integer(y)", "unknown"],
  ["ask", "Q.prime(x*y)", "True", "unknown"],
  ["ask", "Q.prime(x**2)", "Q.integer(x)", "false"],
  ["ask", "Q.prime(x**y)", "True", "unknown"],
  ["ask", "Q.prime(x+2)", "Q.zero(x)", "true"],  // SymPy 1.14: unknown (x = 0 gives 2)
  // SymPy ask gives None; x = 0 makes x + 4 = 4, which is not prime
  ["ask", "Q.prime(x+4)", "Q.zero(x)", "false"],
  ["ask", "Q.prime(x)", "Q.even(x)", "unknown"],
  ["ask", "Q.prime(x)", "Q.negative(x)", "false"],
  ["ask", "Q.prime(x+1)", "Q.odd(x)", "unknown"],
  ["ask", "Q.composite(4)", "True", "true"],
  ["ask", "Q.composite(1)", "True", "false"],
  ["ask", "Q.composite(Rational(1,2))", "True", "false"],
  ["ask", "Q.composite(x+1)", "Q.negative(x)", "unknown"],
  ["ask", "Q.composite(x+2)", "Q.zero(x)", "false"],  // SymPy 1.14: unknown (x = 0 gives 2)
  ["ask", "Q.composite(x)", "True", "unknown"],
  ["ask", "Q.complex(oo)", "True", "false"],
  ["ask", "Q.complex(x+y)", "Q.complex(x) & Q.complex(y)", "true"],
  ["ask", "Q.complex(x+oo)", "Q.real(x)", "false"],
  ["ask", "Q.complex(x*y)", "True", "unknown"],
  ["ask", "Q.complex(x**y)", "Q.complex(x) & Q.complex(y) & Q.positive(x)", "true"],
  ["ask", "Q.complex(x**y)", "True", "unknown"],
  ["ask", "Q.complex(sin(x))", "Q.complex(x)", "true"],
  ["ask", "Q.complex(sin(x))", "True", "unknown"],  // SymPy 1.14: true (SymPy answers True for any argument; x may be infinite)
  ["ask", "Q.complex(gamma(x))", "Q.complex(x)", "unknown"],
  ["ask", "Q.complex(exp(x))", "Q.complex(x)", "true"],
  ["ask", "Q.imaginary(2)", "True", "false"],
  ["ask", "Q.imaginary(pi)", "True", "false"],
  ["ask", "Q.imaginary(oo)", "True", "false"],
  ["ask", "Q.imaginary(x+1)", "Q.real(x)", "false"],
  ["ask", "Q.imaginary(x*y)", "Q.imaginary(x) & Q.real(y) & Q.nonzero(y)", "true"],
  ["ask", "Q.imaginary(x*y)", "Q.imaginary(x) & Q.imaginary(y)", "false"],
  ["ask", "Q.imaginary(x*y)", "Q.imaginary(x)", "unknown"],
  ["ask", "Q.imaginary(x+y)", "Q.imaginary(x) & Q.imaginary(y)", "unknown"],  // SymPy 1.14: true (wrong in SymPy: x = I, y = -I gives 0, which is not imaginary)
  ["ask", "Q.imaginary(x+I)", "Q.imaginary(x)", "unknown"],  // SymPy 1.14: true (wrong in SymPy: x = -I gives 0, which is not imaginary)
  ["ask", "Q.imaginary(exp(I*pi*x))", "Q.rational(x)", "unknown"],
  ["ask", "Q.imaginary(sqrt(x))", "Q.negative(x)", "true"],
  ["ask", "Q.imaginary(x**y)", "True", "unknown"],
  ["ask", "Q.imaginary(sin(x))", "True", "unknown"],
  ["ask", "Q.hermitian(x+1)", "Q.real(x)", "true"],
  ["ask", "Q.hermitian(I)", "True", "false"],
  ["ask", "Q.hermitian(x)", "True", "unknown"],
  ["ask", "Q.antihermitian(I)", "True", "true"],
  ["ask", "Q.antihermitian(0)", "True", "true"],
  ["ask", "Q.antihermitian(2)", "True", "false"],
  ["ask", "Q.antihermitian(x)", "True", "unknown"],
  ["ask", "Q.finite(x+1)", "Q.real(x)", "true"],
  ["ask", "Q.finite(x*y)", "Q.real(x) & Q.real(y)", "true"],
  ["ask", "Q.finite(x*y)", "True", "unknown"],
  ["ask", "Q.finite(x**y)", "Q.real(x) & Q.real(y) & Q.positive(x)", "true"],
  ["ask", "Q.finite(exp(x))", "Q.real(x)", "true"],
  ["ask", "Q.finite(x**y)", "True", "unknown"],
  ["ask", "Q.finite(sin(x))", "Q.real(x)", "true"],
  ["ask", "Q.finite(Abs(x))", "Q.finite(x)", "true"],
  ["ask", "Q.finite(gamma(x))", "True", "unknown"],
  ["ask", "Q.finite(sin(x))", "True", "unknown"],  // SymPy 1.14: true (SymPy answers True for any argument; x may be infinite)
  ["ask", "Q.finite(oo)", "True", "false"],
  ["ask", "Q.finite(pi)", "True", "true"],
  ["ask", "Q.finite(x)", "Q.algebraic(x)", "true"],
  ["ask", "Q.infinite(oo)", "True", "true"],
  ["ask", "Q.infinite(x+1)", "Q.real(x)", "false"],
  ["ask", "Q.commutative(x)", "True", "true"],
  ["ask", "Q.commutative(x+1)", "True", "true"],
  ["ask", "Q.is_true(x)", "True", "unknown"],
  ["ask", "Q.is_true(True)", "True", "true"],
  ["ask", "Q.rational(1.5)", "True", "unknown"],
  ["ask", "Q.rational(oo)", "True", "false"],
  ["ask", "Q.rational(EulerGamma)", "True", "unknown"],
  ["ask", "Q.rational(pi)", "True", "false"],
  ["ask", "Q.rational(x)", "Q.complex(x)", "unknown"],
  ["ask", "Q.rational(x+pi)", "Q.rational(x)", "false"],
  ["ask", "Q.rational(x*pi)", "Q.rational(x) & Q.nonzero(x)", "false"],
  ["ask", "Q.rational(x*pi)", "Q.rational(x)", "unknown"],  // SymPy 1.14: false (wrong in SymPy: x = 0 gives 0)
  ["ask", "Q.rational(x+y)", "True", "unknown"],
  ["ask", "Q.rational(x+I)", "Q.rational(x)", "false"],
  ["ask", "Q.rational(x+y)", "Q.imaginary(x) & Q.real(y)", "false"],
  ["ask", "Q.rational(exp(2))", "True", "false"],
  ["ask", "Q.rational(exp(x))", "Q.rational(x) & Q.nonzero(x)", "false"],
  ["ask", "Q.rational(x**2)", "Q.rational(x)", "true"],  // SymPy 1.14: unknown (the square of a rational number is rational)
  ["ask", "Q.rational(x**(-1))", "Q.rational(x)", "unknown"],
  ["ask", "Q.rational(x**(-1))", "Q.rational(x) & Q.nonzero(x)", "true"],
  ["ask", "Q.rational(sqrt(2))", "True", "false"],
  ["ask", "Q.rational(sqrt(x))", "Q.rational(x) & Q.positive(x)", "unknown"],
  ["ask", "Q.rational(x**y)", "True", "unknown"],
  ["ask", "Q.rational(sin(x))", "Q.rational(x) & Q.nonzero(x)", "false"],
  ["ask", "Q.rational(log(x))", "Q.rational(x) & Q.positive(x)", "unknown"],
  ["ask", "Q.rational(acos(x))", "Q.rational(x)", "unknown"],
  ["ask", "Q.rational(sin(x))", "True", "unknown"],
  ["ask", "Q.rational(gamma(x))", "True", "unknown"],
  ["ask", "Q.algebraic(1.5)", "True", "true"],
  ["ask", "Q.algebraic(oo)", "True", "false"],
  ["ask", "Q.algebraic(I)", "True", "true"],
  ["ask", "Q.algebraic(GoldenRatio)", "True", "true"],
  ["ask", "Q.algebraic(pi)", "True", "false"],
  ["ask", "Q.algebraic(E)", "True", "false"],
  ["ask", "Q.algebraic(EulerGamma)", "True", "unknown"],
  ["ask", "Q.algebraic(x)", "Q.integer(x)", "true"],
  ["ask", "Q.algebraic(x)", "True", "unknown"],
  ["ask", "Q.algebraic(x+pi)", "Q.algebraic(x)", "false"],
  ["ask", "Q.algebraic(x*pi)", "Q.algebraic(x) & Q.nonzero(x)", "false"],
  ["ask", "Q.algebraic(x*pi)", "Q.algebraic(x)", "unknown"],  // SymPy 1.14: false (wrong in SymPy: x = 0 gives 0)
  ["ask", "Q.algebraic(x+y)", "True", "unknown"],
  ["ask", "Q.algebraic(exp(x))", "Q.algebraic(x) & Q.nonzero(x)", "false"],
  ["ask", "Q.algebraic(exp(x))", "True", "unknown"],
  ["ask", "Q.algebraic(x**Rational(1,2))", "Q.algebraic(x)", "true"],
  ["ask", "Q.algebraic(x**y)", "True", "unknown"],
  ["ask", "Q.algebraic(sin(x))", "Q.algebraic(x) & Q.nonzero(x)", "false"],
  ["ask", "Q.algebraic(log(x))", "Q.algebraic(x) & Q.nonzero(x-1)", "false"],
  ["ask", "Q.algebraic(sin(x))", "True", "unknown"],
  ["ask", "Q.algebraic(gamma(x))", "True", "unknown"],
  ["ask", "Xor(Q.positive(x), Q.negative(x))", "Q.positive(x)", "true"],
  ["ask", "Xor(Q.positive(x), Q.negative(x))", "True", "unknown"],
  ["ask", "ITE(Q.positive(x), Q.real(x), Q.negative(x))", "Q.positive(x)", "true"],
  ["ask", "ITE(Q.positive(x), Q.real(x), Q.negative(x))", "Q.negative(x)", "true"],
  ["ask", "ITE(Q.positive(x), Q.real(x), Q.negative(x))", "True", "unknown"],
  ["ask", "~Q.positive(x)", "Q.negative(x)", "true"],
  ["ask", "Q.positive(x) | Q.real(y)", "Q.positive(x)", "true"],
  ["ask", "Q.positive(x) | Q.real(y)", "Q.negative(x) & Q.imaginary(y)", "false"],
  ["ask", "Q.positive(x) | Q.real(y)", "Q.negative(x)", "unknown"],
  ["ask", "Q.positive(x) & Q.real(y)", "Q.negative(x)", "false"],
  ["ask", "Q.positive(x)", "False", "ERR RangeError"],  // SymPy 1.14: ERR ValueError (SymPy raises ValueError; symjs throws RangeError for inconsistent assumptions)
  ["ask", "True", "True", "true"],
  ["ask", "False", "True", "false"],
  ["refine", "sqrt(x**2)", "Q.positive(x) | Q.negative(x)", "Abs(x)"],
  ["refine", "Q.positive(x) & Q.real(y)", "Q.positive(x)", "Q.real(y)"],
  ["refine", "Q.positive(x) | Q.real(y)", "Q.negative(x)", "Q.real(y)"],
  ["refine", "~Q.real(y)", "Q.positive(x)", "~Q.real(y)"],
  ["refine", "x > 0", "Q.positive(x)", "True"],
  ["refine", "x > 0", "True", "x > 0"],
  ["refine", "Abs(x)", "Q.negative(x)", "-x"],
  ["refine", "(-1)**(x+y+1)", "Q.odd(x) & Q.odd(y)", "-1"],
  ["ask", "Q.real(x)", "Implies(Q.positive(y), Q.positive(x)) & Q.positive(y)", "true"],
  ["ask", "Q.real(x)", "Equivalent(Q.positive(x), Q.positive(y)) & Q.positive(y)", "true"],
  ["ask", "Q.real(x)", "Nand(Q.positive(x), Q.negative(y)) & Q.negative(y)", "unknown"],
  ["ask", "Q.real(x)", "Nor(Q.imaginary(x), Q.negative(y))", "unknown"],
  ["ask", "Q.real(x)", "Xnor(Q.positive(x), Q.negative(y)) & Q.negative(y)", "true"],
  ["ask", "Implies(Q.positive(x), Q.real(x))", "True", "true"],
  ["ask", "Equivalent(Q.positive(x), Q.real(x))", "Q.positive(x)", "true"],
  ["ask", "Nand(Q.positive(x), Q.real(x))", "Q.negative(x)", "true"],
  ["ask", "Nor(Q.positive(x), Q.real(x))", "Q.negative(x)", "false"],
  ["ask", "Xnor(Q.positive(x), Q.real(x))", "Q.negative(x)", "false"],
  ["ask", "Xor(Q.positive(x), Q.real(x), Q.negative(x))", "Q.negative(x)", "false"],
  ["ask", "Q.real(x)", "(Q.positive(x)|Q.negative(x)) & (Q.positive(y)|Q.negative(y)) & (Q.positive(z)|Q.negative(z)) & (Q.positive(n)|Q.negative(n)) & (Q.positive(m)|Q.negative(m)) & (Q.positive(x+1)|Q.negative(x+1)) & (Q.positive(y+1)|Q.negative(y+1)) & (Q.positive(z+1)|Q.negative(z+1)) & (Q.positive(n+1)|Q.negative(n+1))", "unknown"],  // SymPy 1.14: true (assumptions with more than 256 branches in disjunctive normal form are not used)
  ["ask", "Q.negative(x)", "Q.positive(x) | Q.negative(x)", "unknown"],
  ["ask", "Q.nonzero(exp(x))", "True", "unknown"],
  ["ask", "Q.nonzero(0)", "True", "false"],
  ["ask", "Q.nonzero(x+I*y)", "Q.positive(x)", "unknown"],
  ["ask", "Q.extended_nonzero(-oo)", "True", "true"],
  ["ask", "Q.extended_positive(x) ", "Q.extended_nonpositive(x)", "false"],
  ["ask", "Q.positive(I*x)", "Q.positive(x)", "false"],
  ["ask", "Q.negative(I*x)", "Q.positive(x)", "false"],
  ["ask", "Q.nonnegative(I*x)", "Q.positive(x)", "false"],
  ["ask", "Q.rational(ni)", "True", "true"],
  ["ask", "Q.rational(I*x)", "Q.positive(x)", "false"],
  ["ask", "Q.rational(f(x))", "True", "unknown"],
  ["ask", "Q.rational(Derivative(f(x), x))", "True", "unknown"],
  ["ask", "Q.algebraic(ni)", "True", "true"],  // SymPy 1.14: unknown (an integer is algebraic)
  ["ask", "Q.algebraic(f(x))", "True", "unknown"],
  ["ask", "Q.algebraic(Derivative(f(x), x))", "True", "unknown"],
  ["ask", "Q.algebraic(acos(x))", "Q.algebraic(x) & Q.nonzero(x-1)", "false"],
  ["ask", "Q.rational(acos(x))", "Q.rational(x) & Q.nonzero(x-1)", "false"],
  ["ask", "Q.rational(log(x))", "Q.rational(x) & Q.positive(x) & Q.nonzero(x-1)", "false"],
  ["ask", "Q.rational(Pow(-2, Rational(1,3)))", "True", "unknown"],
  ["ask", "Q.rational(2**Rational(1,3))", "True", "false"],
  ["ask", "Q.even(x+1)", "Q.irrational(x)", "false"],
  ["ask", "Q.prime(x+1)", "Q.irrational(x)", "false"],
  ["ask", "Q.prime(x-1)", "Q.negative(x) & Q.integer(x)", "false"],
  ["ask", "Q.prime(x+2)", "Q.even(x) & Q.positive(x)", "false"],  // SymPy 1.14: unknown (an even x >= 2 gives an even number >= 4)
  ["ask", "Q.complex(x**2)", "Q.complex(x)", "true"],
  ["ask", "Q.complex(exp(x))", "Q.complex(x)", "true"],
  ["ask", "Q.complex(E**x)", "Q.complex(x)", "true"],
  ["ask", "Q.complex(x**y)", "Q.complex(x) & Q.complex(y)", "unknown"],  // SymPy 1.14: true (wrong in SymPy: x = 0, y = -1 gives zoo)
  ["ask", "Q.finite(rr)", "True", "true"],
  ["ask", "Q.finite(x)", "True", "unknown"],
  ["ask", "Q.finite(x*oo)", "Q.positive(x)", "false"],
  ["ask", "Q.finite(x*oo)", "Q.real(x)", "unknown"],
  ["ask", "Q.finite(x+oo+y)", "Q.real(x)", "unknown"],
  ["ask", "Q.finite(x**2)", "Q.real(x)", "true"],
  ["ask", "Q.finite(E**x)", "Q.real(x)", "true"],
  ["ask", "Q.finite(log(x))", "Q.positive(x)", "true"],
  ["ask", "Q.finite(Derivative(f(x), x))", "True", "unknown"],
  ["ask", "Q.commutative(nc)", "True", "false"],
  ["ask", "Q.imaginary(sqrt(x))", "Q.positive(x)", "false"],
  ["ask", "Q.real(x)", "True", "unknown"],
  ["ask", "Q.positive(x)", "Q.real(x)", "unknown"],
  ["refine", "(-1)**(x+y)", "True", "(-1)**(x + y)"],
  ["refine", "x > 0", "Q.negative(x)", "False"],
  ["refine", "sqrt(x**2)", "(Q.positive(x) & Q.positive(y)) | Q.negative(x)", "Abs(x)"],
  ["refine", "sqrt(x**2)", "Q.positive(y) | Q.negative(y)", "sqrt(x**2)"],
  ["refine", "2", "Q.positive(x)", "2"],
  ["ask", "Implies(Q.positive(x), Q.negative(x))", "Q.positive(x)", "false"],
  ["ask", "Implies(Q.positive(x), Q.negative(x))", "Q.negative(x)", "true"],
  ["ask", "Implies(Q.positive(x), Q.integer(x))", "True", "unknown"],
  ["ask", "Q.extended_positive(x-1)", "Q.negative(x)", "false"],
];

describe('assumptions (SymPy sympy.assumptions)', () => {
  it('asks the number-theoretic and algebraic predicates', () => {
    expect(ask(Q.rational(sj.pi))).toBe(false);
    expect(ask(Q.even(sj.mul(x, y)), Q.even(x).and(Q.integer(y)))).toBe(true);
    expect(ask(Q.prime(sj.mul(4, x)), Q.integer(x))).toBe(false);
    expect(ask(Q.prime(7))).toBe(true);
    expect(ask(Q.composite(9))).toBe(true);
    expect(ask(Q.irrational(sj.sqrt(2)))).toBe(true);
    expect(ask(Q.odd(sj.add(x, 1)), Q.even(x))).toBe(true);
    expect(ask(Q.algebraic(sj.add(sj.sqrt(2), 1)))).toBe(true);
    expect(ask(Q.transcendental(sj.mul(2, sj.pi)))).toBe(true);
    expect(ask(Q.imaginary(sj.mul(2, sj.I)))).toBe(true);
  });

  it('combines assumptions with And, Or and Not', () => {
    expect(ask(Q.positive(sj.add(x, y)), sj.and(Q.positive(x), Q.positive(y)))).toBe(true);
    expect(ask(Q.real(x), sj.or(Q.positive(x), Q.negative(x)))).toBe(true);
    expect(ask(Q.positive(x), sj.or(Q.positive(x), Q.negative(x)))).toBe('unknown');
    expect(ask(Q.negative(x), sj.and(sj.not(Q.positive(x)), Q.nonzero(x)))).toBe(true);
    expect(ask(Q.gt(x, 0), Q.positive(x))).toBe(true);
    expect(ask(sj.Gt(x, y), Q.gt(x, y))).toBe(true);
    expect(ask(Q.positive(x), sj.Gt(x, 0))).toBe('unknown');
    expect(() => ask(Q.positive(x), sj.and(Q.positive(x), Q.negative(x)))).toThrow(RangeError);
    expect(s(sj.not(Q.positive(x)))).toBe('~Q.positive(x)');
  });

  it('refines expressions and predicates', () => {
    expect(s(refine(sj.sqrt(sj.pow(x, 2)), Q.real(x)))).toBe('Abs(x)');
    expect(s(refine(sj.sqrt(sj.pow(x, 2)), Q.positive(x)))).toBe('x');
    expect(s(refine(Q.real(x), Q.positive(x)))).toBe('True');
    expect(s(refine(Q.positive(x), Q.real(x)))).toBe('Q.positive(x)');
    expect(s(refine(sj.pow(-1, sj.add(x, y)), Q.even(x)))).toBe('(-1)**y');
    expect(s(refine(sj.pow(-1, sj.add(x, y, 2)), Q.odd(x)))).toBe('(-1)**(y + 1)');
  });

  it('keeps global assumptions and user predicates', () => {
    expect(sj.assuming([Q.integer(x)], () => ask(Q.integer(sj.mul(2, x))))).toBe(true);
    expect(ask(Q.integer(sj.mul(2, x)))).toBe('unknown');
    sj.globalAssumptions.add(Q.real(x));
    expect(ask(Q.real(x))).toBe(true);
    sj.globalAssumptions.clear();
    expect(ask(Q.real(x))).toBe('unknown');
    const handler: sj.PredicateHandler = (e) => (e instanceof sj.Rational ? e.p % 3n === 0n : 'unknown');
    const div3 = sj.Predicate('div3', handler);
    expect(ask(div3(9))).toBe(true);
    expect(s(div3(x))).toBe('Q.div3(x)');
    sj.removeHandler('div3', handler);
    expect(ask(div3(9))).toBe('unknown');
  });
});

describe('ask and refine (SymPy sympy.assumptions)', () => {
  it.each(CASES)('%s %s under %s', (...c) => {
    expect(run(c)).toBe(c[3]);
  });
});

describe('predicates, handlers and assumption contexts', () => {
  const x = sj.symbol('x');
  const y = sj.symbol('y');
  const z = sj.symbol('z');

  it('prints and combines applied predicates', () => {
    expect(sj.latex(Q.positive(x))).toBe('\\operatorname{Q}_{\\text{positive}}(x)');
    expect(sj.latex(Q.extended_real(x))).toBe('\\operatorname{Q}_{\\text{extended\\_real}}(x)');
    expect(sj.latex(Q.gt(x, y))).toBe('\\operatorname{Q}_{\\text{gt}}(x, y)');
    expect(String(Q.positive)).toBe('Q.positive');
    expect(String(Q.positive(x).subs(x, y))).toBe('Q.positive(y)');
    expect(String(Q.positive(x).or(Q.real(y)))).toBe('Q.positive(x) | Q.real(y)');
    expect(String(Q.positive(x).not())).toBe('~Q.positive(x)');
    expect(String(Q.positive(x).and([Q.real(y)]))).toBe('Q.positive(x) & Q.real(y)');
  });

  it('keeps assumption contexts', () => {
    const ctx = new sj.AssumptionsContext();
    ctx.add(Q.real(x), Q.positive(y));
    expect(ctx.size).toBe(2);
    // SymPy prints a set: AssumptionsContext({Q.positive(y), Q.real(x)}) in some order
    expect(String(ctx)).toMatch(/^AssumptionsContext\(\{(Q\.real\(x\), Q\.positive\(y\)|Q\.positive\(y\), Q\.real\(x\))\}\)$/);
    expect(String(ctx.toExpr())).toBe('Q.positive(y) & Q.real(x)');
    expect([...ctx].length).toBe(2);
    ctx.remove(Q.real(x));
    expect(ctx.has(Q.real(x))).toBe(false);
  });

  it('takes a list of assumptions, true and false', () => {
    expect(ask(Q.real(x), [Q.positive(x)])).toBe(true);
    expect(ask(true)).toBe(true);
    expect(ask(false)).toBe(false);
    // SymPy: ValueError (inconsistent assumptions)
    expect(() => ask(Q.real(x), false)).toThrow(RangeError);
    // SymPy: TypeError proposition must be a valid logical expression
    expect(() => ask(x)).toThrow(TypeError);
    // a negated constant inside the assumptions (Not(True) as built by Piecewise conditions)
    expect(ask(Q.real(x), sj.or(Q.positive(x), new sj.BoolOp('Not', [sj.S.true])))).toBe(true);
  });

  it('uses user handlers, also for predicates of several arguments', () => {
    const f = sj.SymFunction('f');
    const fx = f(x);
    const unknown: sj.PredicateHandler = () => 'unknown';
    const rational: sj.PredicateHandler = (e) => (e.key === fx.key ? true : 'unknown');
    const positive: sj.PredicateHandler = (e) => (e.key === fx.key ? true : 'unknown');
    sj.registerHandler(Q.rational, unknown);
    sj.registerHandler(Q.rational, rational);
    sj.registerHandler('positive', positive);
    try {
      // real from the rational handler, not negative from the positive one
      expect(ask(Q.real(fx))).toBe(true);
      expect(ask(Q.negative(fx))).toBe(false);
    } finally {
      sj.removeHandler(Q.rational, unknown);
      sj.removeHandler(Q.rational, rational);
      sj.removeHandler('positive', positive);
    }
    expect(ask(Q.real(fx))).toBe('unknown');
    // and not positive from a negative one. Deliberate difference: with a Q.negative handler that says
    // f(x) is negative, SymPy 1.14 gives ask(Q.positive(f(x))) = None (its positive handlers do not
    // consult the negative ones), but a negative value is not positive
    const negative: sj.PredicateHandler = (e) => (e.key === fx.key ? true : 'unknown');
    sj.registerHandler('negative', negative);
    try {
      expect(ask(Q.positive(fx))).toBe(false);
    } finally {
      sj.removeHandler('negative', negative);
    }
    sj.removeHandler('no_such_predicate', unknown);
    // a symbol that a handler says is not real is not rational
    const notReal: sj.PredicateHandler = (e) => (e.key === x.key ? false : 'unknown');
    sj.registerHandler('real', notReal);
    expect(ask(Q.rational(x))).toBe(false);
    sj.removeHandler('real', notReal);

    const divides: sj.PredicateHandler = (_e, _a, args) => {
      const [a, b] = args;
      return a instanceof sj.Rational && b instanceof sj.Rational ? b.p % a.p === 0n : 'unknown';
    };
    const skip: sj.PredicateHandler = () => 'unknown';
    sj.registerHandler('divides', skip);
    sj.registerHandler('divides', divides);
    const dividesQ = defined(Q.divides);
    expect(ask(dividesQ(3, 12))).toBe(true);
    expect(ask(dividesQ(5, 12))).toBe(false);
    expect(ask(dividesQ(x, 12))).toBe('unknown');
    expect(ask(sj.Predicate('no_handler')(x, y))).toBe('unknown');
    // a predicate of several arguments in the assumptions is not used
    expect(ask(Q.positive(x), dividesQ(x, y))).toBe('unknown');
    sj.removeHandler('divides', divides);
    sj.removeHandler('divides', skip);
  });

  it('decides unevaluated Nand, Nor and Xnor gates', () => {
    const [p, r] = [Q.positive(x), Q.real(x)];
    expect(ask(sj.Nand(p, r, { evaluate: false }), Q.negative(x))).toBe(true);
    expect(ask(sj.Nor(p, r, { evaluate: false }), Q.negative(x))).toBe(false);
    expect(ask(sj.Xnor(p, r, { evaluate: false }), Q.negative(x))).toBe(false);
    expect(ask(Q.real(x), sj.and(sj.Nand(Q.imaginary(x), r, { evaluate: false }), sj.not(Q.imaginary(x))))).toBe('unknown');
  });

  it('decides an imaginary sum when it is known to be nonzero', () => {
    // SymPy 1.14: True
    const nz = Q.nonzero(sj.mul(-1, sj.I, sj.add(x, y)));
    expect(ask(Q.imaginary(sj.add(x, y)), sj.and(Q.imaginary(x), Q.imaginary(y), nz))).toBe(true);
  });

  it('refines matrices, numbers and branches without common facts', () => {
    const M = sj.Matrix.of([[sj.sqrt(sj.pow(x, 2)), 1]]);
    expect(String(refine(M, Q.positive(x)))).toBe('Matrix([[x, 1]])');
    expect(String(refine(2, Q.positive(x)))).toBe('2');
    expect(() => refine('x' as unknown as number)).toThrow(sj.SympifyError);
    const assumptions = sj.or(sj.and(Q.positive(x), Q.positive(y)), sj.and(Q.negative(x), Q.real(z)));
    expect(String(refine(sj.sqrt(sj.pow(x, 2)), assumptions))).toBe('Abs(x)');
  });
});

describe('extended predicates, imaginary sums, zero products and Q.is_true (SymPy 1.14)', () => {
  const { Q, ask, I } = sj;
  const [x, y] = sj.symbols('x y');
  it('a number that is not an extended real', () => {
    expect(ask(Q.extended_negative(sj.mul(-1, I)))).toBe(false);
    expect(ask(Q.extended_nonnegative(-1))).toBe(false);
    expect(ask(Q.extended_nonnegative(I))).toBe(false);
    expect(ask(Q.extended_nonpositive(I))).toBe(false);
    expect(ask(Q.extended_nonzero(I))).toBe(false);
    expect(ask(Q.extended_positive(I))).toBe(false);
    expect(ask(Q.extended_real(I))).toBe(false);
    expect(ask(Q.extended_nonzero(0))).toBe(false);
    expect(ask(Q.extended_nonpositive(2))).toBe(false);
    expect(ask(Q.extended_negative(2))).toBe(false);
    expect(ask(Q.extended_nonzero(x!))).toBe('unknown');
  });
  it('imaginary sums and zero products', () => {
    expect(ask(Q.imaginary(sj.add(2, sj.mul(3, I))))).toBe(false);
    expect(ask(Q.imaginary(sj.add(x!, I)))).toBe('unknown');
    expect(ask(Q.zero(sj.mul(x!, y!)), sj.Or(Q.zero(x!), Q.zero(y!)))).toBe(true);
    expect(ask(Q.zero(sj.mul(x!, y!)), Q.zero(x!))).toBe(true);
  });
  it('Q.is_true', () => {
    expect(ask(Q.is_true(true))).toBe(true);
    expect(ask(Q.is_true(false))).toBe(false);
    expect(String(Q.is_true(Q.even(x!)))).toBe('Q.even(x)');
    expect(String(Q.is_true(sj.Eq(x!, y!)))).toBe('Q.eq(x, y)');
    expect(String(Q.is_true(sj.Gt(x!, y!)))).toBe('Q.gt(x, y)');
    expect(String(Q.is_true(x!))).toBe('Q.is_true(x)');
  });
});

describe('predicates on nan', () => {
  it('leaves every predicate but commutative undecided (SymPy: ask(Q.finite(nan)) is None)', () => {
    expect(ask(Q.finite(sj.S.NaN))).toBe('unknown');
    expect(ask(Q.zero(sj.mul(0, sj.oo)))).toBe('unknown');
    expect(ask(Q.positive(sj.S.NaN))).toBe('unknown');
    expect(ask(Q.commutative(sj.S.NaN))).toBe(true);
  });
});

it('retains the function of applied predicates', async () => {
  const a = await import('../../src');
  expect(a.Q.integer(1).function).toBe(a.Q.integer);
  expect(String(a.Predicate('custom_property')(1).function)).toBe('Q.custom_property');
});

it('recognizes rational roots of unity as algebraic', async () => {
  const a = await import('../../src');
  const exponent = a.mul(a.Rational.of(2,3),a.pi,a.I);
  expect(a.isAlgebraic(a.exp(exponent))).toBe(true);
});

it('exposes the arguments of an applied predicate', () => {
  expect(sj.Q.integer(1).arguments).toEqual([sj.S.One]);
});

it('queries complete symbol facts including explicit false and parity', () => {
  const odd = sj.symbol('n', { odd: true });
  expect(sj.ask(sj.Q.odd(odd))).toBe(true);
  expect(sj.ask(sj.Q.even(odd))).toBe(false);
  expect(sj.ask(sj.Q.rational(sj.symbol('q', { rational: true })))).toBe(true);
  expect(sj.ask(sj.Q.finite(sj.symbol('z', { finite: false })))).toBe(false);
  expect(sj.ask(sj.Q.real(sj.symbol('z', { real: false })))).toBe(false);
});

it('derives number-domain consequences from registered symbol predicate handlers', () => {
  const value = sj.symbol('custom');
  const handler: sj.PredicateHandler = (e) => e.equals(value) ? true : 'unknown';
  for (const [predicate, consequence] of [[Q.integer, Q.rational], [Q.rational, Q.algebraic], [Q.complex, Q.finite]] as const) {
    sj.registerHandler(predicate, handler);
    try {
      expect(ask(consequence(value))).toBe(true);
    } finally {
      sj.removeHandler(predicate, handler);
    }
    expect(ask(consequence(value))).toBe('unknown');
  }
});

describe('ask on functions (SymPy test_miscellaneous, test_complexes, test_exponential, test_hyperbolic)', () => {
  const { ask, Q, symbol, Max, Min } = sj;
  const raw = (name: string, ...args: sj.ExprLike[]): sj.Expr => new sj.AppliedFunction(name as never, args.map((a) => sj.sympify(a)));
  const o = symbol('o', { odd: true });
  const e = symbol('e', { even: true });
  const q = symbol('q', { rational: true });
  const t = symbol('t', { real: true, transcendental: true });
  const a = symbol('a', { algebraic: true });
  const na = symbol('na', { algebraic: true, nonzero: true });
  const r = symbol('r', { real: true });
  const x = symbol('x');
  const i = symbol('i', { imaginary: true });

  it('gives Max and Min the properties all their arguments share', () => {
    expect(ask(Q.odd(Max(o, symbol('o2', { odd: true }))))).toBe(true);
    expect(ask(Q.even(Min(o, symbol('o2', { odd: true }))))).toBe(false);
    expect(ask(Q.odd(Max(o, e)))).toBe('unknown');
    expect(ask(Q.rational(Max(q, o)))).toBe(true);
    expect(ask(Q.algebraic(Max(t, symbol('t2', { real: true, transcendental: true }))))).toBe(false);
    expect(ask(Q.real(Max(r, t)))).toBe(true);
  });

  it('gives a Piecewise the properties all its expressions share', () => {
    const pw = sj.piecewise([0, sj.Lt(x, 1)], [1, true]);
    expect(ask(Q.finite(pw))).toBe(true);
    expect(ask(Q.imaginary(sj.piecewise([sj.I, sj.Lt(x, 1)], [mul2(sj.I), true])))).toBe(true);
    expect(ask(Q.positive(pw))).toBe('unknown');
  });

  it('knows the functions that are extended real on the extended real line', () => {
    expect(ask(Q.extended_real(raw('cot', r)))).toBe(true);
    expect(ask(Q.extended_real(raw('acsch', symbol('y', { extendedReal: true }))))).toBe(true);
    expect(ask(Q.extended_real(raw('cot', x)))).toBe('unknown');
  });

  it('decides Abs from a real argument', () => {
    expect(ask(Q.rational(raw('abs', q)))).toBe(true);
    expect(ask(Q.integer(raw('abs', symbol('k', { integer: true }))))).toBe(true);
    expect(ask(Q.even(raw('abs', symbol('ne', { integer: true, even: false }))))).toBe(false);
    expect(ask(Q.odd(raw('abs', symbol('no', { integer: true, odd: false }))))).toBe(false);
    expect(ask(Q.odd(raw('abs', x)))).toBe('unknown');
    expect(ask(Q.rational(raw('abs', x)))).toBe('unknown');
  });

  it('knows algebraic and transcendental values of functions', () => {
    expect(ask(Q.algebraic(raw('sin', mul2(sj.S.Pi, q))))).toBe(true);
    expect(ask(Q.algebraic(raw('tan', mul2(sj.S.Pi, q))))).toBe('unknown');
    expect(ask(Q.algebraic(raw('re', a)))).toBe(true);
    expect(ask(Q.algebraic(raw('LambertW', na)))).toBe(false);
    expect(ask(Q.algebraic(sj.exp(mul2(sj.S.Pi, symbol('rn', { rational: true, nonzero: true })))))).toBe(false);
    // pi + sqrt(3) is transcendental
    expect(ask(Q.rational(sj.add(sj.S.Pi, sj.sqrt(3))))).toBe(false);
    expect(ask(Q.rational(raw('log', 1)))).toBe(true);
  });

  it('knows where the inverse hyperbolic functions are finite', () => {
    expect(ask(Q.finite(raw('asinh', 2)))).toBe(true);
    expect(ask(Q.finite(raw('acosh', x)))).toBe('unknown');
    expect(ask(Q.finite(raw('acoth', 2)))).toBe(true);
    expect(ask(Q.finite(raw('asech', sj.Rational.of(2n, 3n))))).toBe(true);
    expect(ask(Q.finite(raw('floor', r)))).toBe(true);
    expect(ask(Q.finite(raw('frac', x)))).toBe(true);
  });

  it('decides sign(x) through its argument', () => {
    expect(ask(Q.finite(raw('sign', x)))).toBe(true);
    expect(ask(Q.imaginary(raw('sign', i)))).toBe(true);
    expect(ask(Q.imaginary(raw('sign', r)))).toBe(false);
  });
});

const mul2 = (...xs: sj.ExprLike[]): sj.Expr => sj.mul(...xs);

it('uses SymPy scalar Hermitian and antihermitian predicate handlers with local facts', async () => {
  const { Sym, Q, ask } = await import('../../src');
  const x = new Sym('local');
  expect(ask(Q.hermitian(x), Q.imaginary(x))).toBe(false);
  expect(ask(Q.antihermitian(x), Q.even(x))).toBe('unknown');
  expect(ask(Q.antihermitian(x), Q.rational(x))).toBe('unknown');
  expect(ask(Q.antihermitian(x), Q.zero(x))).toBe(true);
});

it('does not reject an unconstrained noncommutative Hermitian operator', () => {
  const operator = sj.symbol('operator', { commutative: false });
  expect(sj.ask(sj.Q.hermitian(operator))).toBe('unknown');
  expect(sj.ask(sj.Q.hermitian(operator), sj.Q.hermitian(operator))).toBe(true);
});

it('tracks zero, sign and cancellation in finite scalar expressions', () => {
  const cases: readonly Case[] = [
    ['ask', 'Q.finite(x**y)', '~Q.finite(x) & Q.extended_negative(y)', 'true'],
    ['ask', 'Q.finite(x**y)', '~Q.finite(x)', 'unknown'],
    ['ask', 'Q.finite((-2)**y)', 'Q.extended_negative(y)', 'true'],
    ['ask', 'Q.finite(2**y)', '~Q.finite(y) & Q.extended_positive(y)', 'false'],
    ['ask', 'Q.finite(x+y)', 'Q.negative_infinite(x) & Q.extended_negative(y)', 'false'],
    ['ask', 'Q.finite(x+y)', '~Q.finite(x) & ~Q.finite(y) & ~Q.extended_positive(x) & ~Q.extended_positive(y)', 'unknown'],
    ['ask', 'Q.hermitian(I*x)', 'Q.real(x) & Q.nonzero(x)', 'false'],
    ['ask', 'Q.hermitian(I*x)', 'Q.real(x)', 'unknown'],
    ['ask', 'Q.antihermitian(x+y)', 'Q.imaginary(x) & Q.imaginary(y)', 'true'],
    ['ask', 'Q.imaginary(x+y)', 'Q.imaginary(x) & Q.imaginary(y)', 'unknown'],
    ['ask', 'Q.rational(x**y)', '~Q.algebraic(x) & Q.rational(y)', 'unknown'],
    ['ask', 'Q.rational(x**2)', '~Q.algebraic(x)', 'false'],
  ];
  for (const c of cases) expect(run(c), `${c[1]} under ${c[2]}`).toBe(c[3]);
});

it('distinguishes integral floats from fractional floats and evaluates zero powers', () => {
  expect(ask(Q.integer(new sj.Float(1)))).toBe('unknown');
  expect(ask(Q.integer(new sj.Float(1.25)))).toBe(false);
  expect(ask(Q.algebraic(new sj.Pow(x, y)), Q.zero(y))).toBe(true);
});

it('keeps real powers of a real base sound when the base may be zero or negative', () => {
  const cases: readonly Case[] = [
    ['ask', 'Q.real(x**y)', 'Q.real(x) & Q.positive(y)', 'unknown'],  // SymPy 1.14: true (wrong in SymPy: (-1)**(1/2) = I)
    ['ask', 'Q.real(x**(1/2))', 'Q.real(x)', 'unknown'],  // SymPy 1.14: true (wrong in SymPy: sqrt(-4) = 2*I)
    ['ask', 'Q.real(x**(1/2))', 'Q.nonnegative(x)', 'true'],
    ['ask', 'Q.real(x**(1/2))', 'Q.negative(x)', 'false'],
    ['ask', 'Q.real(x**(3/2))', 'Q.real(x)', 'unknown'],
    ['ask', 'Q.real(x**2)', 'Q.real(x)', 'true'],
    ['ask', 'Q.real(x**(-1))', 'Q.real(x)', 'unknown'],
    ['ask', 'Q.real(x**(-1))', 'Q.real(x) & Q.nonzero(x)', 'true'],
    ['ask', 'Q.real(x**y)', 'Q.zero(x) & Q.positive(y)', 'true'],
    ['ask', 'Q.real(x**y)', 'Q.zero(x) & Q.real(y)', 'unknown'],
    ['ask', 'Q.real(x**y)', 'Q.nonnegative(x) & Q.positive(y)', 'true'],
    ['ask', 'Q.real(x**y)', 'Q.nonnegative(x) & Q.real(y)', 'unknown'],
  ];
  for (const c of cases) expect(run(c), `${c[1]} under ${c[2]}`).toBe(c[3]);
});

it('decides rational, prime and finite facts of powers', () => {
  const { ask, Q, And } = sj;
  // fresh symbol names: ask caches its answers by expression
  const u = new sj.Sym('u_pow'), v = new sj.Sym('v_pow'), w = new sj.Sym('w_pow'), k = new sj.Sym('k_pow');
  // the reciprocal of a finite irrational number is irrational
  expect(ask(Q.rational(sj.pow(u, -1)), Q.irrational(u))).toBe(false);
  // a power of a composite number with an integer exponent is not prime
  expect(ask(Q.prime(sj.pow(v, k)), And(Q.composite(v), Q.integer(k)))).toBe(false);
  // a finite power: a nonzero finite base with a finite exponent is finite, 0**negative is not
  expect(ask(Q.finite(sj.pow(w, k)), And(Q.nonzero(w), Q.finite(w), Q.finite(k)))).toBe(true);
  expect(ask(Q.finite(sj.pow(u, v)), And(Q.zero(u), Q.negative(v), Q.finite(v)))).toBe(false);
  expect(ask(Q.finite(sj.pow(v, w)), And(Q.finite(v), Q.finite(w)))).toBe('unknown');
});

it('an infinite base gives a finite power for a negative exponent and an infinite one for a positive exponent', () => {
  // symbols with their own assumptions and names no other test uses (ask caches by expression)
  const base = new sj.Sym('infinite_power_base', { infinite: true });
  const exponent = new sj.Sym('negative_power_exponent', { negative: true });
  expect(sj.ask(sj.Q.finite(sj.pow(base, exponent)))).toBe(true);
  // and with a positive exponent an infinite power
  const positive = new sj.Sym('positive_power_exponent', { positive: true });
  expect(sj.ask(sj.Q.finite(sj.pow(base, positive)))).toBe(false);
});

it('queries exponential phases and their integer powers', () => {
  const { Fn, Pow, S, mul } = sj;
  const phase = mul(S.I, S.Pi, x);
  const forms = [new Pow(S.E, phase)];
  for (const base of forms) {
    expect(ask(Q.real(new Pow(base, y)), sj.And(Q.integer(x), Q.integer(y)))).toBe(true);
    expect(ask(Q.imaginary(new Pow(base, y)), sj.And(Q.integer(x), Q.integer(y)))).toBe(false);
    expect(ask(Q.real(new Pow(base, y)), Q.imaginary(y))).toBe('unknown');
    expect(ask(Q.imaginary(new Pow(base, y)), Q.imaginary(y))).toBe('unknown');
    expect(ask(Q.real(new Pow(base, y)), sj.And(Q.imaginary(phase), Q.imaginary(y)))).toBe(true);
    expect(ask(Q.imaginary(new Pow(base, y)), sj.And(Q.imaginary(phase), Q.imaginary(y)))).toBe(false);
  }
  expect(ask(Q.algebraic(new Pow(S.E, phase)), Q.rational(x))).toBe(true);
  expect(ask(Q.odd(new Fn('re', [x])), Q.odd(x))).toBe(true);
  expect(ask(Q.odd(new Fn('im', [x])), Q.real(x))).toBe(false);
  expect(ask(Q.finite(new Pow(x, y)), sj.And(sj.Not(Q.finite(x)), Q.extended_positive(y)))).toBe(false);
  expect(ask(Q.hermitian(sj.add(x, y)), sj.And(sj.Not(Q.hermitian(x)), Q.hermitian(y)))).toBe(false);
  expect(ask(Q.extended_real(new sj.Add([S.NegativeInfinity, x])), Q.real(x))).toBe(true);
  expect(refine(new Pow(new Pow(x, S.NegOne), S.Half), Q.positive(x)).toString()).toBe('1/sqrt(x)');
  const reciprocalRoot = new Pow(new Pow(x, S.NegOne), S.Half);
  expect(refine(reciprocalRoot)).toBe(reciprocalRoot);
});

it('keeps unknown numerical coordinates undecided', () => {
  const e = new sj.Pow(new sj.Fn('erf2inv', [sj.S.One]), sj.S.Half);
  expect(ask(Q.imaginary(e))).toBe('unknown');
});

it('handles core boolean atoms and relation normalization without optional proposition handlers', async () => {
  const { vi } = await import('vitest');
  vi.resetModules();
  const core = await import('../../src/core/refine');
  await import('../../src/core');
  const nodes = await import('../../src/core/nodes');
  const bool = await import('../../src/core/boolalg');
  expect(core.ask(true)).toBe(true);
  expect(core.ask(false)).toBe(false);
  expect(() => core.ask(bool.or(core.Q.real(new nodes.Sym('u')), core.Q.real(new nodes.Sym('v'))), false)).toThrow(RangeError);
  const a = new nodes.Sym('a'), b = new nodes.Sym('b');
  const relation = new nodes.Rel('Gt', a, b);
  expect(core.ask(relation, core.Q.real(a))).toBe('unknown');
  expect(core.ask(relation, relation)).toBe(true);
  expect(core.ask(bool.or(core.Q.real(nodes.S.I), core.Q.positive(nodes.S.NegOne)))).toBe(false);
  expect(core.ask(core.Q.eq(a, b), core.Q.eq(b, a))).toBe(true);
  expect(core.ask(bool.or(core.Q.real(a), core.Q.real(b)), bool.and(core.Q.positive(a), core.Q.positive(b)))).toBe(true);
});

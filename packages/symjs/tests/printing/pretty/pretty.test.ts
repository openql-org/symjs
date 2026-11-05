// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/printing/pretty/pretty.ts.

import { describe, expect, it } from 'vitest';
import * as sj from '../../../src';
import { Add, ExtensionExpr, Fn, Integral, Mul, Pow, Rational, S } from '../../../src/core/nodes';
import type { Expr } from '../../../src/core/nodes';
import { Implies, ITE } from '../../../src/logic';
import { pagerPrint, pprint, pprintTryUseUnicode, pprintUseUnicode, pretty, PrettyForm, prettyHooks, prettyPrint, PrettyPrinter, PrettyTuple, prettyUseUnicode } from '../../../src/printing/pretty';
import type { PrettyOptions, Printable } from '../../../src/printing/pretty';
import { Contains, FiniteSet, Interval, Range, SetExpr, SetOp, UniversalSet } from '../../../src/sets/sets';

const sym = (name: string, assumptions: sj.Assumptions = {}): sj.Sym => sj.symbol(name, assumptions);
const def = (name: string): sj.DefinedFunction => sj.defineFunction(name, {});
const R = (p: bigint, q = 1n): sj.Rational => sj.Rational.of(p, q);

/** [SymPy source, symjs builder, ASCII output, unicode output, options]. */
type Case = readonly [string, () => Printable, string, string, PrettyOptions];

/** Expressions of SymPy 1.14 sympy/printing/pretty/tests/test_pretty.py that symjs can build. */
const TEST_PRETTY: readonly Case[] = [
  ["oo", () => sj.oo, "oo", "∞", {}],
  ["(x**2)", () => sj.pow(sym("x"), R(2n)), " 2\nx ", " 2\nx ", {}],
  ["1/x", () => sj.pow(sym("x"), R(-1n)), "1\n-\nx", "1\n─\nx", {}],
  ["x**-1.0", () => sj.pow(sym("x"), new sj.Float(-1.0)), " -1.0\nx    ", " -1.0\nx    ", {}],
  ["Pow(S(2), -1.0, evaluate=False)", () => new sj.Pow(R(2n), new sj.Float(-1.0)), " -1.0\n2    ", " -1.0\n2    ", {}],
  ["y*x**-2", () => sj.mul(sym("y"), sj.pow(sym("x"), R(-2n))), "y \n--\n 2\nx ", "y \n──\n 2\nx ", {}],
  ["x**Rational(1, 3)", () => sj.pow(sym("x"), R(1n, 3n)), "3 ___\n\\/ x ", "3 ___\n╲╱ x ", {}],
  ["x**Rational(-5, 2)", () => sj.pow(sym("x"), R(-5n, 2n)), " 1  \n----\n 5/2\nx   ", " 1  \n────\n 5/2\nx   ", {}],
  ["(-2)**x", () => sj.pow(R(-2n), sym("x")), "    x\n(-2) ", "    x\n(-2) ", {}],
  ["Pow(3, 1, evaluate=False)", () => new sj.Pow(R(3n), R(1n)), " 1\n3 ", " 1\n3 ", {}],
  ["(x**2 + x + 1)", () => sj.add(R(1n), sym("x"), sj.pow(sym("x"), R(2n))), " 2        \nx  + x + 1", " 2        \nx  + x + 1", {}],
  ["1 - x", () => sj.add(R(1n), sj.mul(R(-1n), sym("x"))), "1 - x", "1 - x", {}],
  ["1 - 2*x", () => sj.add(R(1n), sj.mul(R(-2n), sym("x"))), "1 - 2*x", "1 - 2⋅x", {}],
  ["x/y", () => sj.mul(sym("x"), sj.pow(sym("y"), R(-1n))), "x\n-\ny", "x\n─\ny", {}],
  ["-x/y", () => sj.mul(R(-1n), sym("x"), sj.pow(sym("y"), R(-1n))), "-x \n---\n y ", "-x \n───\n y ", {}],
  ["(x + 2)/y", () => sj.mul(sj.pow(sym("y"), R(-1n)), sj.add(R(2n), sym("x"))), "x + 2\n-----\n  y  ", "x + 2\n─────\n  y  ", {}],
  ["(1 + x)*y", () => sj.mul(sym("y"), sj.add(R(1n), sym("x"))), "y*(x + 1)", "y⋅(x + 1)", {}],
  ["-5*x/(x + 10)", () => sj.mul(R(-5n), sym("x"), sj.pow(sj.add(R(10n), sym("x")), R(-1n))), "-5*x  \n------\nx + 10", "-5⋅x  \n──────\nx + 10", {}],
  ["-S.Half - 3*x", () => sj.add(R(-1n, 2n), sj.mul(R(-3n), sym("x"))), "-3*x - 1/2", "-3⋅x - 1/2", {}],
  ["S.Half - 3*x", () => sj.add(R(1n, 2n), sj.mul(R(-3n), sym("x"))), "1/2 - 3*x", "1/2 - 3⋅x", {}],
  ["-S.Half - 3*x/2", () => sj.add(R(-1n, 2n), sj.mul(R(-3n, 2n), sym("x"))), "  3*x   1\n- --- - -\n   2    2", "  3⋅x   1\n- ─── - ─\n   2    2", {}],
  ["S.Half - 3*x/2", () => sj.add(R(1n, 2n), sj.mul(R(-3n, 2n), sym("x"))), "1   3*x\n- - ---\n2    2 ", "1   3⋅x\n─ - ───\n2    2 ", {}],
  ["-x*z/y", () => sj.mul(R(-1n), sym("x"), sym("z"), sj.pow(sym("y"), R(-1n))), "-x*z \n-----\n  y  ", "-x⋅z \n─────\n  y  ", {}],
  ["x**2/y", () => sj.mul(sj.pow(sym("x"), R(2n)), sj.pow(sym("y"), R(-1n))), " 2\nx \n--\ny ", " 2\nx \n──\ny ", {}],
  ["-x**2/y", () => sj.mul(R(-1n), sj.pow(sym("x"), R(2n)), sj.pow(sym("y"), R(-1n))), "  2 \n-x  \n----\n y  ", "  2 \n-x  \n────\n y  ", {}],
  ["-x/(y*z)", () => sj.mul(R(-1n), sym("x"), sj.pow(sym("y"), R(-1n)), sj.pow(sym("z"), R(-1n))), "-x \n---\ny*z", "-x \n───\ny⋅z", {}],
  ["-a/y**2", () => sj.mul(R(-1n), sym("a"), sj.pow(sym("y"), R(-2n))), "-a \n---\n 2 \ny  ", "-a \n───\n 2 \ny  ", {}],
  ["y**(-a/b)", () => sj.pow(sym("y"), sj.mul(R(-1n), sym("a"), sj.pow(sym("b"), R(-1n)))), " -a \n ---\n  b \ny   ", " -a \n ───\n  b \ny   ", {}],
  ["-1/y**2", () => sj.mul(R(-1n), sj.pow(sym("y"), R(-2n))), "-1 \n---\n 2 \ny  ", "-1 \n───\n 2 \ny  ", {}],
  ["-10/b**2", () => sj.mul(R(-10n), sj.pow(sym("b"), R(-2n))), "-10 \n----\n  2 \n b  ", "-10 \n────\n  2 \n b  ", {}],
  ["Rational(-200, 37)", () => R(-200n, 37n), "-200 \n-----\n 37  ", "-200 \n─────\n 37  ", {}],
  ["Mul(0, 1, evaluate=False)", () => new sj.Mul([R(0n), R(1n)]), "0*1", "0⋅1", {}],
  ["Mul(1, 0, evaluate=False)", () => new sj.Mul([R(1n), R(0n)]), "1*0", "1⋅0", {}],
  ["Mul(1, 1, evaluate=False)", () => new sj.Mul([R(1n), R(1n)]), "1*1", "1⋅1", {}],
  ["Mul(1, 1, 1, evaluate=False)", () => new sj.Mul([R(1n), R(1n), R(1n)]), "1*1*1", "1⋅1⋅1", {}],
  ["Mul(1, 2, evaluate=False)", () => new sj.Mul([R(1n), R(2n)]), "1*2", "1⋅2", {}],
  ["Add(0, 1, evaluate=False)", () => new sj.Add([R(0n), R(1n)]), "0 + 1", "0 + 1", {}],
  ["Mul(1, 1, 2, evaluate=False)", () => new sj.Mul([R(1n), R(1n), R(2n)]), "1*1*2", "1⋅1⋅2", {}],
  ["Add(0, 0, 1, evaluate=False)", () => new sj.Add([R(0n), R(0n), R(1n)]), "0 + 0 + 1", "0 + 0 + 1", {}],
  ["Mul(1, -1, evaluate=False)", () => new sj.Mul([R(1n), R(-1n)]), "1*-1", "1⋅-1", {}],
  ["Mul(1.0, x, evaluate=False)", () => sj.mul(new sj.Float(1.0), sym("x")), "1.0*x", "1.0⋅x", {}],
  ["Mul(1, 1, 2, 3, x, evaluate=False)", () => new sj.Mul([R(1n), R(1n), R(2n), R(3n), sym("x")]), "1*1*2*3*x", "1⋅1⋅2⋅3⋅x", {}],
  ["Mul(-1, 1, evaluate=False)", () => new sj.Mul([R(-1n), R(1n)]), "-1*1", "-1⋅1", {}],
  ["Mul(4, 3, 2, 1, 0, y, x, evaluate=False)", () => new sj.Mul([R(4n), R(3n), R(2n), R(1n), R(0n), sym("y"), sym("x")]), "4*3*2*1*0*y*x", "4⋅3⋅2⋅1⋅0⋅y⋅x", {}],
  ["Mul(4, 3, 2, 1+z, 0, y, x, evaluate=False)", () => new sj.Mul([R(4n), R(3n), R(2n), sj.add(R(1n), sym("z")), R(0n), sym("y"), sym("x")]), "4*3*2*(z + 1)*0*y*x", "4⋅3⋅2⋅(z + 1)⋅0⋅y⋅x", {}],
  ["Mul(Rational(2, 3), Rational(5, 7), evaluate=False)", () => new sj.Mul([R(2n, 3n), R(5n, 7n)]), "2/3*5/7", "2/3⋅5/7", {}],
  ["Mul(x + y, Rational(1, 2), evaluate=False)", () => new sj.Mul([sj.add(sym("x"), sym("y")), R(1n, 2n)]), "(x + y)*1/2", "(x + y)⋅1/2", {}],
  ["Mul(Rational(1, 2), x + y, evaluate=False)", () => new sj.Mul([R(1n, 2n), sj.add(sym("x"), sym("y"))]), "x + y\n-----\n  2  ", "x + y\n─────\n  2  ", {}],
  ["Mul(S.One, x + y, evaluate=False)", () => new sj.Mul([R(1n), sj.add(sym("x"), sym("y"))]), "1*(x + y)", "1⋅(x + y)", {}],
  ["Mul(x - y, S.One, evaluate=False)", () => new sj.Mul([sj.add(sym("x"), sj.mul(R(-1n), sym("y"))), R(1n)]), "(x - y)*1", "(x - y)⋅1", {}],
  ["Mul(Rational(1, 2), x - y, S.One, x + y, evaluate=False)", () => new sj.Mul([R(1n, 2n), sj.add(sym("x"), sj.mul(R(-1n), sym("y"))), R(1n), sj.add(sym("x"), sym("y"))]), "1/2*(x - y)*1*(x + y)", "1/2⋅(x - y)⋅1⋅(x + y)", {}],
  ["Mul(x + y, Rational(3, 4), S.One, y - z, evaluate=False)", () => new sj.Mul([sj.add(sym("x"), sym("y")), R(3n, 4n), R(1n), sj.add(sym("y"), sj.mul(R(-1n), sym("z")))]), "(x + y)*3/4*1*(y - z)", "(x + y)⋅3/4⋅1⋅(y - z)", {}],
  ["Mul(x + y, Rational(1, 1), Rational(3, 4), Rational(5, 6),evaluate=False)", () => new sj.Mul([sj.add(sym("x"), sym("y")), R(1n), R(3n, 4n), R(5n, 6n)]), "(x + y)*1*3/4*5/6", "(x + y)⋅1⋅3/4⋅5/6", {}],
  ["Mul(Rational(3, 4), x + y, S.One, y - z, evaluate=False)", () => new sj.Mul([R(3n, 4n), sj.add(sym("x"), sym("y")), R(1n), sj.add(sym("y"), sj.mul(R(-1n), sym("z")))]), "3/4*(x + y)*1*(y - z)", "3/4⋅(x + y)⋅1⋅(y - z)", {}],
  ["x - x**3/6 + x**5/120 + O(x**6)", () => sj.add(sym("x"), sj.mul(R(-1n, 6n), sj.pow(sym("x"), R(3n))), sj.mul(R(1n, 120n), sj.pow(sym("x"), R(5n))), sj.O(sj.pow(sym("x"), R(6n)), sym("x"), R(0n))), "     3    5         \n    x    x      / 6\\\nx - -- + --- + O\\x /\n    6    120        ", "     3    5         \n    x    x      ⎛ 6⎞\nx - ── + ─── + O⎝x ⎠\n    6    120        ", {}],
  ["Eq(x, y)", () => sj.Eq(sym("x"), sym("y")), "x = y", "x = y", {}],
  ["Lt(x, y)", () => sj.Lt(sym("x"), sym("y")), "x < y", "x < y", {}],
  ["Gt(x, y)", () => sj.Gt(sym("x"), sym("y")), "x > y", "x > y", {}],
  ["Le(x, y)", () => sj.Le(sym("x"), sym("y")), "x <= y", "x ≤ y", {}],
  ["Ge(x, y)", () => sj.Ge(sym("x"), sym("y")), "x >= y", "x ≥ y", {}],
  ["Ne(x/(y + 1), y**2)", () => sj.Ne(sj.mul(sym("x"), sj.pow(sj.add(R(1n), sym("y")), R(-1n))), sj.pow(sym("y"), R(2n))), "  x       2\n----- != y \ny + 1      ", "  x      2\n───── ≠ y \ny + 1     ", {}],
  ["y**Rational(3, 2) * x**Rational(-5, 2)", () => sj.mul(sj.pow(sym("x"), R(-5n, 2n)), sj.pow(sym("y"), R(3n, 2n))), " 3/2\ny   \n----\n 5/2\nx   ", " 3/2\ny   \n────\n 5/2\nx   ", {}],
  ["sin(x)**3/tan(x)**2", () => sj.mul(sj.pow(sj.fn("sin", [sym("x")], { evaluate: false }), R(3n)), sj.pow(sj.fn("tan", [sym("x")], { evaluate: false }), R(-2n))), "   3   \nsin (x)\n-------\n   2   \ntan (x)", "   3   \nsin (x)\n───────\n   2   \ntan (x)", {}],
  ["(2*x + exp(x))", () => sj.add(sj.mul(R(2n), sym("x")), sj.exp(sym("x"))), "       x\n2*x + e ", "       x\n2⋅x + ℯ ", {}],
  ["Abs(x)", () => sj.fn("abs", [sym("x")], { evaluate: false }), "|x|", "│x│", {}],
  ["Abs(x/(x**2 + 1))", () => sj.fn("abs", [sj.mul(sym("x"), sj.pow(sj.add(R(1n), sj.pow(sym("x"), R(2n))), R(-1n)))], { evaluate: false }), "|  x   |\n|------|\n| 2    |\n|x  + 1|", "│  x   │\n│──────│\n│ 2    │\n│x  + 1│", {}],
  ["Abs(1 / (y - Abs(x)))", () => sj.pow(sj.fn("abs", [sj.add(sym("y"), sj.mul(R(-1n), sj.fn("abs", [sym("x")], { evaluate: false })))], { evaluate: false }), R(-1n)), "    1    \n---------\n|y - |x||", "    1    \n─────────\n│y - │x││", {}],
  ["factorial(n)", () => sj.fn("factorial", [sym("n")], { evaluate: false }), "n!", "n!", {}],
  ["factorial(2*n)", () => sj.fn("factorial", [sj.mul(R(2n), sym("n"))], { evaluate: false }), "(2*n)!", "(2⋅n)!", {}],
  ["factorial(factorial(factorial(n)))", () => sj.fn("factorial", [sj.fn("factorial", [sj.fn("factorial", [sym("n")], { evaluate: false })], { evaluate: false })], { evaluate: false }), "((n!)!)!", "((n!)!)!", {}],
  ["factorial(n + 1)", () => sj.fn("factorial", [sj.add(R(1n), sym("n"))], { evaluate: false }), "(n + 1)!", "(n + 1)!", {}],
  ["subfactorial(n)", () => sj.fn("subfactorial", [sym("n")], { evaluate: false }), "!n", "!n", {}],
  ["subfactorial(2*n)", () => sj.fn("subfactorial", [sj.mul(R(2n), sym("n"))], { evaluate: false }), "!(2*n)", "!(2⋅n)", {}],
  ["factorial2(n)", () => sj.fn("factorial2", [sym("n")], { evaluate: false }), "n!!", "n!!", {}],
  ["factorial2(2*n)", () => sj.fn("factorial2", [sj.mul(R(2n), sym("n"))], { evaluate: false }), "(2*n)!!", "(2⋅n)!!", {}],
  ["factorial2(factorial2(factorial2(n)))", () => sj.fn("factorial2", [sj.fn("factorial2", [sj.fn("factorial2", [sym("n")], { evaluate: false })], { evaluate: false })], { evaluate: false }), "((n!!)!!)!!", "((n!!)!!)!!", {}],
  ["factorial2(n + 1)", () => sj.fn("factorial2", [sj.add(R(1n), sym("n"))], { evaluate: false }), "(n + 1)!!", "(n + 1)!!", {}],
  ["2*binomial(n, k)", () => sj.mul(R(2n), sj.fn("binomial", [sym("n"), sym("k")], { evaluate: false })), "  /n\\\n2*| |\n  \\k/", "  ⎛n⎞\n2⋅⎜ ⎟\n  ⎝k⎠", {}],
  ["2*binomial(2*n, k)", () => sj.mul(R(2n), sj.fn("binomial", [sj.mul(R(2n), sym("n")), sym("k")], { evaluate: false })), "  /2*n\\\n2*|   |\n  \\ k /", "  ⎛2⋅n⎞\n2⋅⎜   ⎟\n  ⎝ k ⎠", {}],
  ["2*binomial(n**2, k)", () => sj.mul(R(2n), sj.fn("binomial", [sj.pow(sym("n"), R(2n)), sym("k")], { evaluate: false })), "  / 2\\\n  |n |\n2*|  |\n  \\k /", "  ⎛ 2⎞\n  ⎜n ⎟\n2⋅⎜  ⎟\n  ⎝k ⎠", {}],
  ["catalan(n)", () => sj.fn("catalan", [sym("n")], { evaluate: false }), "C \n n", "C \n n", {}],
  ["bell(n)", () => sj.fn("bell", [sym("n")], { evaluate: false }), "B \n n", "B \n n", {}],
  ["bernoulli(n)", () => sj.fn("bernoulli", [sym("n")], { evaluate: false }), "B \n n", "B \n n", {}],
  ["bernoulli(n, x)", () => sj.fn("bernoulli", [sym("n"), sym("x")], { evaluate: false }), "B (x)\n n   ", "B (x)\n n   ", {}],
  ["fibonacci(n)", () => sj.fn("fibonacci", [sym("n")], { evaluate: false }), "F \n n", "F \n n", {}],
  ["lucas(n)", () => sj.fn("lucas", [sym("n")], { evaluate: false }), "L \n n", "L \n n", {}],
  ["tribonacci(n)", () => sj.fn("tribonacci", [sym("n")], { evaluate: false }), "T \n n", "T \n n", {}],
  ["stieltjes(n)", () => def("stieltjes")(sym("n")), "stieltjes \n         n", "γ \n n", {}],
  ["stieltjes(n, x)", () => def("stieltjes")(sym("n"), sym("x")), "stieltjes (x)\n         n   ", "γ (x)\n n   ", {}],
  ["mathieuc(x, y, z)", () => def("mathieuc")(sym("x"), sym("y"), sym("z")), "C(x, y, z)", "C(x, y, z)", {}],
  ["mathieus(x, y, z)", () => def("mathieus")(sym("x"), sym("y"), sym("z")), "S(x, y, z)", "S(x, y, z)", {}],
  ["mathieucprime(x, y, z)", () => def("mathieucprime")(sym("x"), sym("y"), sym("z")), "C'(x, y, z)", "C'(x, y, z)", {}],
  ["mathieusprime(x, y, z)", () => def("mathieusprime")(sym("x"), sym("y"), sym("z")), "S'(x, y, z)", "S'(x, y, z)", {}],
  ["conjugate(x)", () => sj.fn("conjugate", [sym("x")], { evaluate: false }), "_\nx", "_\nx", {}],
  ["conjugate(f(x + 1))", () => sj.fn("conjugate", [sj.SymFunction("f")(sj.add(R(1n), sym("x")))], { evaluate: false }), "________\nf(x + 1)", "________\nf(x + 1)", {}],
  ["f(x)", () => sj.SymFunction("f")(sym("x")), "f(x)", "f(x)", {}],
  ["f(x, y)", () => sj.SymFunction("f")(sym("x"), sym("y")), "f(x, y)", "f(x, y)", {}],
  ["f(x/(y + 1), y)", () => sj.SymFunction("f")(sj.mul(sym("x"), sj.pow(sj.add(R(1n), sym("y")), R(-1n))), sym("y")), " /  x     \\\nf|-----, y|\n \\y + 1   /", " ⎛  x     ⎞\nf⎜─────, y⎟\n ⎝y + 1   ⎠", {}],
  ["f(x**x**x**x**x**x)", () => sj.SymFunction("f")(sj.pow(sym("x"), sj.pow(sym("x"), sj.pow(sym("x"), sj.pow(sym("x"), sj.pow(sym("x"), sym("x"))))))), " / / / / / x\\\\\\\\\\\n | | | | \\x /||||\n | | | \\x    /|||\n | | \\x       /||\n | \\x          /|\nf\\x             /", " ⎛ ⎛ ⎛ ⎛ ⎛ x⎞⎞⎞⎞⎞\n ⎜ ⎜ ⎜ ⎜ ⎝x ⎠⎟⎟⎟⎟\n ⎜ ⎜ ⎜ ⎝x    ⎠⎟⎟⎟\n ⎜ ⎜ ⎝x       ⎠⎟⎟\n ⎜ ⎝x          ⎠⎟\nf⎝x             ⎠", {}],
  ["sin(x)**2", () => sj.pow(sj.fn("sin", [sym("x")], { evaluate: false }), R(2n)), "   2   \nsin (x)", "   2   \nsin (x)", {}],
  ["conjugate(a + b*I)", () => sj.add(sj.mul(R(-1n), sj.I, sj.fn("conjugate", [sym("b")], { evaluate: false })), sj.fn("conjugate", [sym("a")], { evaluate: false })), "_     _\na - I*b", "_     _\na - ⅈ⋅b", {}],
  ["conjugate(exp(a + b*I))", () => sj.exp(sj.add(sj.mul(R(-1n), sj.I, sj.fn("conjugate", [sym("b")], { evaluate: false })), sj.fn("conjugate", [sym("a")], { evaluate: false }))), " _     _\n a - I*b\ne       ", " _     _\n a - ⅈ⋅b\nℯ       ", {}],
  ["conjugate( f(1 + conjugate(f(x))) )", () => sj.fn("conjugate", [sj.SymFunction("f")(sj.add(R(1n), sj.fn("conjugate", [sj.SymFunction("f")(sym("x"))], { evaluate: false })))], { evaluate: false }), "___________\n /____    \\\nf\\f(x) + 1/", "___________\n ⎛____    ⎞\nf⎝f(x) + 1⎠", {}],
  ["floor(1 / (y - floor(x)))", () => sj.fn("floor", [sj.pow(sj.add(sym("y"), sj.mul(R(-1n), sj.fn("floor", [sym("x")], { evaluate: false }))), R(-1n))], { evaluate: false }), "     /     1      \\\nfloor|------------|\n     \\y - floor(x)/", "⎢   1   ⎥\n⎢───────⎥\n⎣y - ⌊x⌋⎦", {}],
  ["ceiling(1 / (y - ceiling(x)))", () => sj.fn("ceiling", [sj.pow(sj.add(sym("y"), sj.mul(R(-1n), sj.fn("ceiling", [sym("x")], { evaluate: false }))), R(-1n))], { evaluate: false }), "       /      1       \\\nceiling|--------------|\n       \\y - ceiling(x)/", "⎡   1   ⎤\n⎢───────⎥\n⎢y - ⌈x⌉⎥", {}],
  ["euler(n)", () => sj.fn("euler", [sym("n")], { evaluate: false }), "E \n n", "E \n n", {}],
  ["euler(1/(1 + 1/(1 + 1/n)))", () => sj.fn("euler", [sj.pow(sj.add(R(1n), sj.pow(sj.add(R(1n), sj.pow(sym("n"), R(-1n))), R(-1n))), R(-1n))], { evaluate: false }), "E         \n     1    \n ---------\n       1  \n 1 + -----\n         1\n     1 + -\n         n", "E         \n     1    \n ─────────\n       1  \n 1 + ─────\n         1\n     1 + ─\n         n", {}],
  ["euler(n, x)", () => sj.fn("euler", [sym("n"), sym("x")], { evaluate: false }), "E (x)\n n   ", "E (x)\n n   ", {}],
  ["euler(n, x/2)", () => sj.fn("euler", [sym("n"), sj.mul(R(1n, 2n), sym("x"))], { evaluate: false }), "  /x\\\nE |-|\n n\\2/", "  ⎛x⎞\nE ⎜─⎟\n n⎝2⎠", {}],
  ["sqrt(2)", () => sj.pow(R(2n), R(1n, 2n)), "  ___\n\\/ 2 ", "√2", {}],
  ["2**Rational(1, 3)", () => sj.pow(R(2n), R(1n, 3n)), "3 ___\n\\/ 2 ", "3 ___\n╲╱ 2 ", {}],
  ["2**Rational(1, 1000)", () => sj.pow(R(2n), R(1n, 1000n)), "1000___\n  \\/ 2 ", "1000___\n  ╲╱ 2 ", {}],
  ["sqrt(x**2 + 1)", () => sj.pow(sj.add(R(1n), sj.pow(sym("x"), R(2n))), R(1n, 2n)), "   ________\n  /  2     \n\\/  x  + 1 ", "   ________\n  ╱  2     \n╲╱  x  + 1 ", {}],
  ["(1 + sqrt(5))**Rational(1, 3)", () => sj.pow(sj.add(R(1n), sj.pow(R(5n), R(1n, 2n))), R(1n, 3n)), "   ___________\n3 /       ___ \n\\/  1 + \\/ 5  ", "3 ________\n╲╱ 1 + √5 ", {}],
  ["2**(1/x)", () => sj.pow(R(2n), sj.pow(sym("x"), R(-1n))), "x ___\n\\/ 2 ", "x ___\n╲╱ 2 ", {}],
  ["sqrt(2 + pi)", () => sj.pow(sj.add(R(2n), sj.pi), R(1n, 2n)), "  ________\n\\/ 2 + pi ", "  _______\n╲╱ 2 + π ", {}],
  ["sqrt(Symbol('C1'))", () => sj.pow(sym("C1"), R(1n, 2n)), "  ____\n\\/ C1 ", "  ____\n╲╱ C₁ ", {}],
  ["KroneckerDelta(x, y)", () => sj.fn("KroneckerDelta", [sym("x"), sym("y")], { evaluate: false }), "d   \n x,y", "δ   \n x,y", {}],
  ["Product(f((n/3)**2), (n, k**2, l))", () => sj.Product(sj.SymFunction("f")(sj.mul(R(1n, 9n), sj.pow(sym("n"), R(2n)))), [sym("n"), sj.pow(sym("k"), R(2n)), sym("l")]), "    l           \n__________      \n |      |   / 2\\\n |      |   |n |\n |      |  f|--|\n |      |   \\9 /\n |      |       \n       2        \n  n = k         ", "    l           \n─┬──────┬─      \n │      │   ⎛ 2⎞\n │      │   ⎜n ⎟\n │      │  f⎜──⎟\n │      │   ⎝9 ⎠\n │      │       \n       2        \n  n = k         ", {}],
  ["Product(f((n/3)**2), (n, k**2, l), (l, 1, m))", () => sj.Product(sj.SymFunction("f")(sj.mul(R(1n, 9n), sj.pow(sym("n"), R(2n)))), [sym("n"), sj.pow(sym("k"), R(2n)), sym("l")], [sym("l"), R(1n), sym("m")]), "    m          l           \n__________ __________      \n |      |   |      |   / 2\\\n |      |   |      |   |n |\n |      |   |      |  f|--|\n |      |   |      |   \\9 /\n |      |   |      |       \n  l = 1           2        \n             n = k         ", "    m          l           \n─┬──────┬─ ─┬──────┬─      \n │      │   │      │   ⎛ 2⎞\n │      │   │      │   ⎜n ⎟\n │      │   │      │  f⎜──⎟\n │      │   │      │   ⎝9 ⎠\n │      │   │      │       \n  l = 1           2        \n             n = k         ", {}],
  ["Lambda(x, x+1)", () => sj.Lambda(sym("x"), sj.add(R(1n), sym("x"))), "x -> x + 1", "x ↦ x + 1", {}],
  ["Lambda(x, x**2)", () => sj.Lambda(sym("x"), sj.pow(sym("x"), R(2n))), "      2\nx -> x ", "     2\nx ↦ x ", {}],
  ["Lambda(x, x**2)**2", () => sj.pow(sj.Lambda(sym("x"), sj.pow(sym("x"), R(2n))), R(2n)), "         2\n/      2\\ \n\\x -> x / ", "        2\n⎛     2⎞ \n⎝x ↦ x ⎠ ", {}],
  ["Lambda((x, y), x)", () => sj.Lambda([sym("x"), sym("y")], sym("x")), "(x, y) -> x", "(x, y) ↦ x", {}],
  ["Lambda((x, y), x**2)", () => sj.Lambda([sym("x"), sym("y")], sj.pow(sym("x"), R(2n))), "           2\n(x, y) -> x ", "          2\n(x, y) ↦ x ", {}],
  ["O(1)", () => sj.O(R(1n)), "O(1)", "O(1)", {}],
  ["O(1/x)", () => sj.O(sj.pow(sym("x"), R(-1n)), sym("x"), R(0n)), " /1\\\nO|-|\n \\x/", " ⎛1⎞\nO⎜─⎟\n ⎝x⎠", {}],
  ["O(x**2 + y**2)", () => sj.O(sj.add(sj.pow(sym("x"), R(2n)), sj.pow(sym("y"), R(2n))), [sym("x"), sym("y")], R(0n)), " / 2    2                  \\\nO\\x  + y ; (x, y) -> (0, 0)/", " ⎛ 2    2                 ⎞\nO⎝x  + y ; (x, y) → (0, 0)⎠", {}],
  ["O(1, (x, oo))", () => sj.O(R(1n), sym("x"), sj.oo), "O(1; x -> oo)", "O(1; x → ∞)", {}],
  ["O(1/x, (x, oo))", () => sj.O(sj.pow(sym("x"), R(-1n)), sym("x"), sj.oo), " /1         \\\nO|-; x -> oo|\n \\x         /", " ⎛1       ⎞\nO⎜─; x → ∞⎟\n ⎝x       ⎠", {}],
  ["O(x**2 + y**2, (x, oo), (y, oo))", () => sj.O(sj.add(sj.pow(sym("x"), R(2n)), sj.pow(sym("y"), R(2n))), [sym("x"), sym("y")], sj.oo), " / 2    2                    \\\nO\\x  + y ; (x, y) -> (oo, oo)/", " ⎛ 2    2                 ⎞\nO⎝x  + y ; (x, y) → (∞, ∞)⎠", {}],
  ["Derivative(log(x), x, evaluate=False)", () => sj.Derivative(sj.fn("log", [sym("x")], { evaluate: false }), [sym("x"), 1]), "d         \n--(log(x))\ndx        ", "d         \n──(log(x))\ndx        ", {}],
  ["Derivative(log(x), x, evaluate=False) + x", () => sj.add(sym("x"), sj.Derivative(sj.fn("log", [sym("x")], { evaluate: false }), [sym("x"), 1])), "    d         \nx + --(log(x))\n    dx        ", "    d         \nx + ──(log(x))\n    dx        ", {}],
  ["Derivative(log(x + y) + x, x)", () => sj.Derivative(sj.add(sym("x"), sj.fn("log", [sj.add(sym("x"), sym("y"))], { evaluate: false })), [sym("x"), 1]), "d                 \n--(x + log(x + y))\ndx                ", "∂                 \n──(x + log(x + y))\n∂x                ", {}],
  ["Derivative(log(x) + x**2, x, y)", () => sj.Derivative(sj.add(sj.pow(sym("x"), R(2n)), sj.fn("log", [sym("x")], { evaluate: false })), [sym("x"), 1], [sym("y"), 1]), "  2               \n d   / 2         \\\n-----\\x  + log(x)/\ndy dx             ", "  2               \n d   ⎛ 2         ⎞\n─────⎝x  + log(x)⎠\ndy dx             ", {}],
  ["Derivative(2*x*y, y, x) + x**2", () => sj.add(sj.pow(sym("x"), R(2n)), sj.Derivative(sj.mul(R(2n), sym("x"), sym("y")), [sym("y"), 1], [sym("x"), 1])), "       2         \n 2    d          \nx  + -----(2*x*y)\n     dx dy       ", "       2         \n 2    ∂          \nx  + ─────(2⋅x⋅y)\n     ∂x ∂y       ", {}],
  ["Derivative(2*x*y, x, x)", () => sj.Derivative(sj.mul(R(2n), sym("x"), sym("y")), [sym("x"), 2]), " 2        \nd         \n---(2*x*y)\n  2       \ndx        ", " 2        \n∂         \n───(2⋅x⋅y)\n  2       \n∂x        ", {}],
  ["Derivative(2*x*y, x, 17)", () => sj.Derivative(sj.mul(R(2n), sym("x"), sym("y")), [sym("x"), 17]), " 17        \nd          \n----(2*x*y)\n  17       \ndx         ", " 17        \n∂          \n────(2⋅x⋅y)\n  17       \n∂x         ", {}],
  ["Derivative(2*x*y, x, x, y)", () => sj.Derivative(sj.mul(R(2n), sym("x"), sym("y")), [sym("x"), 2], [sym("y"), 1]), "   3         \n  d          \n------(2*x*y)\n     2       \ndy dx        ", "   3         \n  ∂          \n──────(2⋅x⋅y)\n     2       \n∂y ∂x        ", {}],
  ["Integral(log(x), x)", () => new sj.Integral([sj.fn("log", [sym("x")], { evaluate: false }), sym("x")]), "  /         \n |          \n | log(x) dx\n |          \n/           ", "⌠          \n⎮ log(x) dx\n⌡          ", {}],
  ["Integral(x**2, x)", () => new sj.Integral([sj.pow(sym("x"), R(2n)), sym("x")]), "  /     \n |      \n |  2   \n | x  dx\n |      \n/       ", "⌠      \n⎮  2   \n⎮ x  dx\n⌡      ", {}],
  ["Integral((sin(x))**2 / (tan(x))**2)", () => new sj.Integral([sj.mul(sj.pow(sj.fn("sin", [sym("x")], { evaluate: false }), R(2n)), sj.pow(sj.fn("tan", [sym("x")], { evaluate: false }), R(-2n))), sym("x")]), "  /          \n |           \n |    2      \n | sin (x)   \n | ------- dx\n |    2      \n | tan (x)   \n |           \n/            ", "⌠           \n⎮    2      \n⎮ sin (x)   \n⎮ ─────── dx\n⎮    2      \n⎮ tan (x)   \n⌡           ", {}],
  ["Integral(x**(2**x), x)", () => new sj.Integral([sj.pow(sym("x"), sj.pow(R(2n), sym("x"))), sym("x")]), "  /        \n |         \n |  / x\\   \n |  \\2 /   \n | x     dx\n |         \n/          ", "⌠         \n⎮  ⎛ x⎞   \n⎮  ⎝2 ⎠   \n⎮ x     dx\n⌡         ", {}],
  ["Integral(x**2, (x, 1, 2))", () => new sj.Integral([sj.pow(sym("x"), R(2n)), sym("x"), R(1n), R(2n)]), "  2      \n  /      \n |       \n |   2   \n |  x  dx\n |       \n/        \n1        ", "2      \n⌠      \n⎮  2   \n⎮ x  dx\n⌡      \n1      ", {}],
  ["Integral(x**2, (x, Rational(1, 2), 10))", () => new sj.Integral([sj.pow(sym("x"), R(2n)), sym("x"), R(1n, 2n), R(10n)]), " 10      \n  /      \n |       \n |   2   \n |  x  dx\n |       \n/        \n1/2      ", "10       \n⌠        \n⎮    2   \n⎮   x  dx\n⌡        \n1/2      ", {}],
  ["Integral(x**2*y**2, x, y)", () => new sj.Integral([new sj.Integral([sj.mul(sj.pow(sym("x"), R(2n)), sj.pow(sym("y"), R(2n))), sym("x")]), sym("y")]), "  /  /           \n |  |            \n |  |  2  2      \n |  | x *y  dx dy\n |  |            \n/  /             ", "⌠ ⌠            \n⎮ ⎮  2  2      \n⎮ ⎮ x ⋅y  dx dy\n⌡ ⌡            ", {}],
  ["Integral(sin(th)/cos(ph), (th, 0, pi), (ph, 0, 2*pi))", () => new sj.Integral([new sj.Integral([sj.mul(sj.pow(sj.fn("cos", [sym("phi")], { evaluate: false }), R(-1n)), sj.fn("sin", [sym("theta")], { evaluate: false })), sym("theta"), R(0n), sj.pi]), sym("phi"), R(0n), sj.mul(R(2n), sj.pi)]), " 2*pi pi                           \n   /   /                           \n  |   |                            \n  |   |  sin(theta)                \n  |   |  ---------- d(theta) d(phi)\n  |   |   cos(phi)                 \n  |   |                            \n /   /                             \n0    0                             ", "2⋅π π             \n ⌠  ⌠             \n ⎮  ⎮ sin(θ)      \n ⎮  ⎮ ────── dθ dφ\n ⎮  ⎮ cos(φ)      \n ⌡  ⌡             \n 0  0             ", {}],
  ["Matrix()", () => sj.Matrix.of([]), "[]", "[]", {}],
  ["Matrix(2, 0, lambda i, j: 0)", () => sj.Matrix.of([[], []]), "[]", "[]", {}],
  ["Matrix(0, 2, lambda i, j: 0)", () => sj.Matrix.of([]), "[]", "[]", {}],
  ["Matrix([[x**2 + 1, 1], [y, x + y]])", () => sj.Matrix.of([[sj.add(R(1n), sj.pow(sym("x"), R(2n))), R(1n)], [sym("y"), sj.add(sym("x"), sym("y"))]]), "[ 2           ]\n[x  + 1    1  ]\n[             ]\n[  y     x + y]", "⎡ 2           ⎤\n⎢x  + 1    1  ⎥\n⎢             ⎥\n⎣  y     x + y⎦", {}],
  ["Matrix([[x/y, y, th], [0, exp(I*k*ph), 1]])", () => sj.Matrix.of([[sj.mul(sym("x"), sj.pow(sym("y"), R(-1n))), sym("y"), sym("theta")], [R(0n), sj.exp(sj.mul(sj.I, sym("k"), sym("phi"))), R(1n)]]), "[x                 ]\n[-     y      theta]\n[y                 ]\n[                  ]\n[    I*k*phi       ]\n[0  e           1  ]", "⎡x           ⎤\n⎢─    y     θ⎥\n⎢y           ⎥\n⎢            ⎥\n⎢    ⅈ⋅k⋅φ   ⎥\n⎣0  ℯ       1⎦", {}],
  ["Piecewise((x, x < 1), (x**2, True))", () => sj.Piecewise([sym("x"), sj.Lt(sym("x"), R(1n))], [sj.pow(sym("x"), R(2n)), true]), "/x   for x < 1\n|             \n< 2           \n|x   otherwise\n\\             ", "⎧x   for x < 1\n⎪             \n⎨ 2           \n⎪x   otherwise\n⎩             ", {}],
  ["-Piecewise((x, x < 1), (x**2, True))", () => sj.mul(R(-1n), sj.Piecewise([sym("x"), sj.Lt(sym("x"), R(1n))], [sj.pow(sym("x"), R(2n)), true])), " //x   for x < 1\\\n ||             |\n-|< 2           |\n ||x   otherwise|\n \\\\             /", " ⎛⎧x   for x < 1⎞\n ⎜⎪             ⎟\n-⎜⎨ 2           ⎟\n ⎜⎪x   otherwise⎟\n ⎝⎩             ⎠", {}],
  ["x*Piecewise((x, x > 0), (y, True))", () => sj.mul(sym("x"), sj.Piecewise([sym("x"), sj.Gt(sym("x"), R(0n))], [sym("y"), true])), "  //x  for x > 0\\\nx*|<            |\n  \\\\y  otherwise/", "  ⎛⎧x  for x > 0⎞\nx⋅⎜⎨            ⎟\n  ⎝⎩y  otherwise⎠", {}],
  ["Pow(Piecewise((x, x > 0), (y, True)), 2, evaluate=False)", () => new sj.Pow(sj.Piecewise([sym("x"), sj.Gt(sym("x"), R(0n))], [sym("y"), true]), R(2n)), "               2\n//x  for x > 0\\ \n|<            | \n\\\\y  otherwise/ ", "               2\n⎛⎧x  for x > 0⎞ \n⎜⎨            ⎟ \n⎝⎩y  otherwise⎠ ", {}],
  ["()", () => new PrettyTuple(), "()", "()", {}],
  ["[]", () => [], "[]", "[]", {}],
  ["{}", () => new Map<sj.Expr, sj.Expr>([]), "{}", "{}", {}],
  ["(1/x,)", () => new PrettyTuple(sj.pow(sym("x"), R(-1n))), " 1  \n(-,)\n x  ", "⎛1 ⎞\n⎜─,⎟\n⎝x ⎠", {}],
  ["[x**2, 1/x, x, y, sin(th)**2/cos(ph)**2]", () => [sj.pow(sym("x"), R(2n)), sj.pow(sym("x"), R(-1n)), sym("x"), sym("y"), sj.mul(sj.pow(sj.fn("cos", [sym("phi")], { evaluate: false }), R(-2n)), sj.pow(sj.fn("sin", [sym("theta")], { evaluate: false }), R(2n)))], "                 2        \n  2  1        sin (theta) \n[x , -, x, y, -----------]\n     x            2       \n               cos (phi)  ", "⎡                2   ⎤\n⎢ 2  1        sin (θ)⎥\n⎢x , ─, x, y, ───────⎥\n⎢    x           2   ⎥\n⎣             cos (φ)⎦", {}],
  ["(x**2, 1/x, x, y, sin(th)**2/cos(ph)**2)", () => new PrettyTuple(sj.pow(sym("x"), R(2n)), sj.pow(sym("x"), R(-1n)), sym("x"), sym("y"), sj.mul(sj.pow(sj.fn("cos", [sym("phi")], { evaluate: false }), R(-2n)), sj.pow(sj.fn("sin", [sym("theta")], { evaluate: false }), R(2n)))), "                 2        \n  2  1        sin (theta) \n(x , -, x, y, -----------)\n     x            2       \n               cos (phi)  ", "⎛                2   ⎞\n⎜ 2  1        sin (θ)⎟\n⎜x , ─, x, y, ───────⎟\n⎜    x           2   ⎟\n⎝             cos (φ)⎠", {}],
  ["Tuple(x**2, 1/x, x, y, sin(th)**2/cos(ph)**2)", () => new PrettyTuple(sj.pow(sym("x"), R(2n)), sj.pow(sym("x"), R(-1n)), sym("x"), sym("y"), sj.mul(sj.pow(sj.fn("cos", [sym("phi")], { evaluate: false }), R(-2n)), sj.pow(sj.fn("sin", [sym("theta")], { evaluate: false }), R(2n)))), "                 2        \n  2  1        sin (theta) \n(x , -, x, y, -----------)\n     x            2       \n               cos (phi)  ", "⎛                2   ⎞\n⎜ 2  1        sin (θ)⎟\n⎜x , ─, x, y, ───────⎟\n⎜    x           2   ⎟\n⎝             cos (φ)⎠", {}],
  ["{x: sin(x)}", () => new Map<sj.Expr, sj.Expr>([[sym("x"), sj.fn("sin", [sym("x")], { evaluate: false })]]), "{x: sin(x)}", "{x: sin(x)}", {}],
  ["{1/x: 1/y, x: sin(x)**2}", () => new Map<sj.Expr, sj.Expr>([[sj.pow(sym("x"), R(-1n)), sj.pow(sym("y"), R(-1n))], [sym("x"), sj.pow(sj.fn("sin", [sym("x")], { evaluate: false }), R(2n))]]), " 1  1        2    \n{-: -, x: sin (x)}\n x  y             ", "⎧1  1        2   ⎫\n⎨─: ─, x: sin (x)⎬\n⎩x  y            ⎭", {}],
  ["[x**2]", () => [sj.pow(sym("x"), R(2n))], "  2 \n[x ]", "⎡ 2⎤\n⎣x ⎦", {}],
  ["(x**2,)", () => new PrettyTuple(sj.pow(sym("x"), R(2n))), "  2  \n(x ,)", "⎛ 2 ⎞\n⎝x ,⎠", {}],
  ["Tuple(x**2)", () => new PrettyTuple(sj.pow(sym("x"), R(2n))), "  2  \n(x ,)", "⎛ 2 ⎞\n⎝x ,⎠", {}],
  ["Limit(x, x, oo)", () => new sj.Limit([sym("x"), sym("x"), sj.oo], "-"), " lim x\nx->oo ", "lim x\nx─→∞ ", {}],
  ["Limit(x**2, x, 0)", () => new sj.Limit([sj.pow(sym("x"), R(2n)), sym("x"), R(0n)], "+"), "      2\n lim x \nx->0+  ", "      2\n lim x \nx─→0⁺  ", {}],
  ["Limit(1/x, x, 0)", () => new sj.Limit([sj.pow(sym("x"), R(-1n)), sym("x"), R(0n)], "+"), "     1\n lim -\nx->0+x", "     1\n lim ─\nx─→0⁺x", {}],
  ["Limit(sin(x)/x, x, 0)", () => new sj.Limit([sj.mul(sj.pow(sym("x"), R(-1n)), sj.fn("sin", [sym("x")], { evaluate: false })), sym("x"), R(0n)], "+"), "     /sin(x)\\\n lim |------|\nx->0+\\  x   /", "     ⎛sin(x)⎞\n lim ⎜──────⎟\nx─→0⁺⎝  x   ⎠", {}],
  ["Limit(sin(x)/x, x, 0, \"-\")", () => new sj.Limit([sj.mul(sj.pow(sym("x"), R(-1n)), sj.fn("sin", [sym("x")], { evaluate: false })), sym("x"), R(0n)], "-"), "     /sin(x)\\\n lim |------|\nx->0-\\  x   /", "     ⎛sin(x)⎞\n lim ⎜──────⎟\nx─→0⁻⎝  x   ⎠", {}],
  ["Limit(x + sin(x), x, 0)", () => new sj.Limit([sj.add(sym("x"), sj.fn("sin", [sym("x")], { evaluate: false })), sym("x"), R(0n)], "+"), " lim (x + sin(x))\nx->0+            ", " lim (x + sin(x))\nx─→0⁺            ", {}],
  ["Limit(x, x, 0)**2", () => sj.pow(new sj.Limit([sym("x"), sym("x"), R(0n)], "+"), R(2n)), "        2\n/ lim x\\ \n\\x->0+ / ", "        2\n⎛ lim x⎞ \n⎝x─→0⁺ ⎠ ", {}],
  ["Limit(x*Limit(y/2,y,0), x, 0)", () => new sj.Limit([sj.mul(sym("x"), new sj.Limit([sj.mul(R(1n, 2n), sym("y")), sym("y"), R(0n)], "+")), sym("x"), R(0n)], "+"), "     /       /y\\\\\n lim |x* lim |-||\nx->0+\\  y->0+\\2//", "     ⎛       ⎛y⎞⎞\n lim ⎜x⋅ lim ⎜─⎟⎟\nx─→0⁺⎝  y─→0⁺⎝2⎠⎠", {}],
  ["2*Limit(x*Limit(y/2,y,0), x, 0)", () => sj.mul(R(2n), new sj.Limit([sj.mul(sym("x"), new sj.Limit([sj.mul(R(1n, 2n), sym("y")), sym("y"), R(0n)], "+")), sym("x"), R(0n)], "+")), "       /       /y\\\\\n2* lim |x* lim |-||\n  x->0+\\  y->0+\\2//", "       ⎛       ⎛y⎞⎞\n2⋅ lim ⎜x⋅ lim ⎜─⎟⎟\n  x─→0⁺⎝  y─→0⁺⎝2⎠⎠", {}],
  ["Limit(sin(x), x, 0, dir='+-')", () => new sj.Limit([sj.fn("sin", [sym("x")], { evaluate: false }), sym("x"), R(0n)], "+-"), "lim sin(x)\nx->0      ", "lim sin(x)\nx─→0      ", {}],
  ["Not(x, evaluate=False)", () => sj.Not(sym("x")), "Not(x)", "¬x", {}],
  ["And(x, y)", () => sj.And(sym("x"), sym("y")), "And(x, y)", "x ∧ y", {}],
  ["Or(x, y)", () => sj.Or(sym("x"), sym("y")), "Or(x, y)", "x ∨ y", {}],
  ["Xor(x, y, evaluate=False)", () => sj.Xor(sym("x"), sym("y")), "Xor(x, y)", "x ⊻ y", {}],
  ["Nand(x, y, evaluate=False)", () => sj.Nand(sym("x"), sym("y"), { evaluate: false }), "Nand(x, y)", "x ⊼ y", {}],
  ["Nor(x, y, evaluate=False)", () => sj.Nor(sym("x"), sym("y"), { evaluate: false }), "Nor(x, y)", "x ⊽ y", {}],
  ["Implies(x, y, evaluate=False)", () => sj.Implies(sym("x"), sym("y")), "Implies(x, y)", "x → y", {}],
  ["Implies(y, x, evaluate=False)", () => sj.Implies(sym("y"), sym("x")), "Implies(y, x)", "y → x", {}],
  ["Equivalent(x, y, evaluate=False)", () => sj.Equivalent(sym("x"), sym("y")), "Equivalent(x, y)", "x ⇔ y", {}],
  ["Equivalent(y, x, evaluate=False)", () => sj.Equivalent(sym("x"), sym("y")), "Equivalent(x, y)", "x ⇔ y", {}],
  ["Sum(k**k, (k, 0, n))", () => sj.Sum(sj.pow(sym("k"), sym("k")), [sym("k"), R(0n), sym("n")]), " n      \n___     \n\\  `    \n \\     k\n /    k \n/__,    \nk = 0   ", "  n     \n ___    \n ╲      \n  ╲    k\n  ╱   k \n ╱      \n ‾‾‾    \nk = 0   ", {}],
  ["Sum(k**k, (k, oo, n))", () => sj.Sum(sj.pow(sym("k"), sym("k")), [sym("k"), sj.oo, sym("n")]), "  n      \n ___     \n \\  `    \n  \\     k\n  /    k \n /__,    \nk = oo   ", "  n     \n ___    \n ╲      \n  ╲    k\n  ╱   k \n ╱      \n ‾‾‾    \nk = ∞   ", {}],
  ["Sum(k**(Integral(x**n, (x, -oo, oo))), (k, 0, n**n))", () => sj.Sum(sj.pow(sym("k"), new sj.Integral([sj.pow(sym("x"), sym("n")), sym("x"), sj.S.NegativeInfinity, sj.oo])), [sym("k"), R(0n), sj.pow(sym("n"), sym("n"))]), "   n              \n  n               \n______            \n\\     `           \n \\        oo      \n  \\        /      \n   \\      |       \n    \\     |   n   \n     )    |  x  dx\n    /     |       \n   /     /        \n  /      -oo      \n /      k         \n/_____,           \n k = 0            ", "   n            \n  n             \n______          \n╲               \n ╲              \n  ╲     ∞       \n   ╲    ⌠       \n    ╲   ⎮   n   \n    ╱   ⎮  x  dx\n   ╱    ⌡       \n  ╱     -∞      \n ╱     k        \n╱               \n‾‾‾‾‾‾          \nk = 0           ", {}],
  ["Sum(x, (x, 0, oo))", () => sj.Sum(sym("x"), [sym("x"), R(0n), sj.oo]), " oo    \n __    \n \\ `   \n  )   x\n /_,   \nx = 0  ", "  ∞    \n ___   \n ╲     \n  ╲    \n  ╱   x\n ╱     \n ‾‾‾   \nx = 0  ", {}],
  ["Sum(x**2, (x, 0, oo))", () => sj.Sum(sj.pow(sym("x"), R(2n)), [sym("x"), R(0n), sj.oo]), " oo     \n___     \n\\  `    \n \\     2\n /    x \n/__,    \nx = 0   ", "  ∞     \n ___    \n ╲      \n  ╲    2\n  ╱   x \n ╱      \n ‾‾‾    \nx = 0   ", {}],
  ["Sum(x/2, (x, 0, oo))", () => sj.Sum(sj.mul(R(1n, 2n), sym("x")), [sym("x"), R(0n), sj.oo]), " oo    \n___    \n\\  `   \n \\    x\n  )   -\n /    2\n/__,   \nx = 0  ", " ∞     \n____   \n╲      \n ╲     \n  ╲   x\n  ╱   ─\n ╱    2\n╱      \n‾‾‾‾   \nx = 0  ", {}],
  ["Sum(x**3/2, (x, 0, oo))", () => sj.Sum(sj.mul(R(1n, 2n), sj.pow(sym("x"), R(3n))), [sym("x"), R(0n), sj.oo]), " oo     \n____    \n\\   `   \n \\     3\n  \\   x \n  /   --\n /    2 \n/___,   \nx = 0   ", " ∞      \n____    \n╲       \n ╲     3\n  ╲   x \n  ╱   ──\n ╱    2 \n╱       \n‾‾‾‾    \nx = 0   ", {}],
  ["Sum((x**3*y**(x/2))**n, (x, 0, oo))", () => sj.Sum(sj.pow(sj.mul(sj.pow(sym("x"), R(3n)), sj.pow(sym("y"), sj.mul(R(1n, 2n), sym("x")))), sym("n")), [sym("x"), R(0n), sj.oo]), " oo           \n____          \n\\   `         \n \\           n\n  \\   /    x\\ \n   )  |    -| \n  /   | 3  2| \n /    \\x *y / \n/___,         \nx = 0         ", "  ∞           \n_____         \n╲             \n ╲            \n  ╲          n\n   ╲  ⎛    x⎞ \n   ╱  ⎜    ─⎟ \n  ╱   ⎜ 3  2⎟ \n ╱    ⎝x ⋅y ⎠ \n╱             \n‾‾‾‾‾         \nx = 0         ", {}],
  ["Sum(1/x**2, (x, 0, oo))", () => sj.Sum(sj.pow(sym("x"), R(-2n)), [sym("x"), R(0n), sj.oo]), " oo     \n____    \n\\   `   \n \\    1 \n  \\   --\n  /    2\n /    x \n/___,   \nx = 0   ", " ∞      \n____    \n╲       \n ╲    1 \n  ╲   ──\n  ╱    2\n ╱    x \n╱       \n‾‾‾‾    \nx = 0   ", {}],
  ["Sum(1/y**(a/b), (x, 0, oo))", () => sj.Sum(sj.pow(sym("y"), sj.mul(R(-1n), sym("a"), sj.pow(sym("b"), R(-1n)))), [sym("x"), R(0n), sj.oo]), " oo       \n____      \n\\   `     \n \\     -a \n  \\    ---\n  /     b \n /    y   \n/___,     \nx = 0     ", " ∞        \n____      \n╲         \n ╲     -a \n  ╲    ───\n  ╱     b \n ╱    y   \n╱         \n‾‾‾‾      \nx = 0     ", {}],
  ["Sum(1/y**(a/b), (x, 0, oo), (y, 1, 2))", () => sj.Sum(sj.pow(sym("y"), sj.mul(R(-1n), sym("a"), sj.pow(sym("b"), R(-1n)))), [sym("x"), R(0n), sj.oo], [sym("y"), R(1n), R(2n)]), "  2    oo       \n____  ____      \n\\   ` \\   `     \n \\     \\     -a \n  \\     \\    ---\n  /     /     b \n /     /    y   \n/___, /___,     \ny = 1 x = 0     ", " 2     ∞        \n____  ____      \n╲     ╲         \n ╲     ╲     -a \n  ╲     ╲    ───\n  ╱     ╱     b \n ╱     ╱    y   \n╱     ╱         \n‾‾‾‾  ‾‾‾‾      \ny = 1 x = 0     ", {}],
  ["Subs(f(x), x, ph**2)", () => sj.Subs(sj.SymFunction("f")(sym("x")), [sym("x")], [sj.pow(sym("phi"), R(2n))]), "(f(x))|     2\n      |x=phi ", "(f(x))│   2\n      │x=φ ", {}],
  ["Subs(f(x).diff(x), x, 0)", () => sj.Subs(sj.Derivative(sj.SymFunction("f")(sym("x")), [sym("x"), 1]), [sym("x")], [R(0n)]), "/d       \\|   \n|--(f(x))||   \n\\dx      /|x=0", "⎛d       ⎞│   \n⎜──(f(x))⎟│   \n⎝dx      ⎠│x=0", {}],
  ["Subs(f(x).diff(x)/y, (x, y), (0, Rational(1, 2)))", () => sj.Subs(sj.mul(sj.pow(sym("y"), R(-1n)), sj.Derivative(sj.SymFunction("f")(sym("x")), [sym("x"), 1])), [sym("x"), sym("y")], [R(0n), R(1n, 2n)]), "/d       \\|          \n|--(f(x))||          \n|dx      ||          \n|--------||          \n\\   y    /|x=0, y=1/2", "⎛d       ⎞│          \n⎜──(f(x))⎟│          \n⎜dx      ⎟│          \n⎜────────⎟│          \n⎝   y    ⎠│x=0, y=1/2", {}],
  ["atan2(y/sqrt(200), sqrt(x))", () => sj.fn("atan2", [sj.mul(R(1n, 20n), sym("y"), sj.pow(R(2n), R(1n, 2n))), sj.pow(sym("x"), R(1n, 2n))], { evaluate: false }), "     /  ___         \\\n     |\\/ 2 *y    ___|\natan2|-------, \\/ x |\n     \\  20          /", "     ⎛√2⋅y    ⎞\natan2⎜────, √x⎟\n     ⎝ 20     ⎠", {}],
  ["Ei(x)", () => sj.fn("Ei", [sym("x")], { evaluate: false }), "Ei(x)", "Ei(x)", {}],
  ["expint(1, z)", () => sj.fn("expint", [R(1n), sym("z")], { evaluate: false }), "expint(1, z)", "E₁(z)", {}],
  ["elliptic_k(1/(z + 1))", () => def("elliptic_k")(sj.pow(sj.add(R(1n), sym("z")), R(-1n))), " /  1  \\\nK|-----|\n \\z + 1/", " ⎛  1  ⎞\nK⎜─────⎟\n ⎝z + 1⎠", {}],
  ["elliptic_f(1, 1/(1 + z))", () => def("elliptic_f")(R(1n), sj.pow(sj.add(R(1n), sym("z")), R(-1n))), " / |  1  \\\nF|1|-----|\n \\ |z + 1/", " ⎛ │  1  ⎞\nF⎜1│─────⎟\n ⎝ │z + 1⎠", {}],
  ["elliptic_e(1/(z + 1))", () => def("elliptic_e")(sj.pow(sj.add(R(1n), sym("z")), R(-1n))), " /  1  \\\nE|-----|\n \\z + 1/", " ⎛  1  ⎞\nE⎜─────⎟\n ⎝z + 1⎠", {}],
  ["elliptic_e(1, 1/(1 + z))", () => def("elliptic_e")(R(1n), sj.pow(sj.add(R(1n), sym("z")), R(-1n))), " / |  1  \\\nE|1|-----|\n \\ |z + 1/", " ⎛ │  1  ⎞\nE⎜1│─────⎟\n ⎝ │z + 1⎠", {}],
  ["elliptic_pi(3, 4/x)", () => def("elliptic_pi")(R(3n), sj.mul(R(4n), sj.pow(sym("x"), R(-1n)))), "  / |4\\\nPi|3|-|\n  \\ |x/", " ⎛ │4⎞\nΠ⎜3│─⎟\n ⎝ │x⎠", {}],
  ["elliptic_pi(3, 4/x, 6)", () => def("elliptic_pi")(R(3n), sj.mul(R(4n), sj.pow(sym("x"), R(-1n))), R(6n)), "  /   4| \\\nPi|3; -|6|\n  \\   x| /", " ⎛   4│ ⎞\nΠ⎜3; ─│6⎟\n ⎝   x│ ⎠", {}],
  ["'xxx'", () => "xxx", "xxx", "xxx", {}],
  ["\"xxx\"", () => "xxx", "xxx", "xxx", {}],
  ["'xxx\\'xxx'", () => "xxx'xxx", "xxx'xxx", "xxx'xxx", {}],
  ["'xxx\"xxx'", () => "xxx\"xxx", "xxx\"xxx", "xxx\"xxx", {}],
  ["'xxx\\\"xxx'", () => "xxx\"xxx", "xxx\"xxx", "xxx\"xxx", {}],
  ["\"xxx'xxx\"", () => "xxx'xxx", "xxx'xxx", "xxx'xxx", {}],
  ["\"xxx\\'xxx\"", () => "xxx'xxx", "xxx'xxx", "xxx'xxx", {}],
  ["\"xxx\\\"xxx\"", () => "xxx\"xxx", "xxx\"xxx", "xxx\"xxx", {}],
  ["\"xxx\\\"xxx\\'xxx\"", () => "xxx\"xxx'xxx", "xxx\"xxx'xxx", "xxx\"xxx'xxx", {}],
  ["\"xxx\\nxxx\"", () => "xxx\nxxx", "xxx\nxxx", "xxx\nxxx", {}],
  ["Symbol('alpha^+_1')", () => sym("alpha^+_1"), "alpha^+_1", "α⁺₁", {}],
  ["Symbol('beta')", () => sym("beta"), "beta", "β", {}],
  ["Symbol('lambda')", () => sym("lambda"), "lambda", "λ", {}],
  ["Symbol('beta12')", () => sym("beta12"), "beta12", "β₁₂", {}],
  ["Symbol('Y00')", () => sym("Y00"), "Y00", "Y₀₀", {}],
  ["Symbol('Y_00')", () => sym("Y_00"), "Y_00", "Y₀₀", {}],
  ["Symbol('F^+-')", () => sym("F^+-"), "F^+-", "F⁺⁻", {}],
  ["Symbol('beta_1_2')", () => sym("beta_1_2"), "beta_1_2", "β₁ ₂", {}],
  ["Symbol('beta^1^2')", () => sym("beta^1^2"), "beta^1^2", "β¹ ²", {}],
  ["Symbol('beta_1^2')", () => sym("beta_1^2"), "beta_1^2", "β²₁", {}],
  ["Symbol('beta_10_20')", () => sym("beta_10_20"), "beta_10_20", "β₁₀ ₂₀", {}],
  ["Symbol('beta_ax_gamma^i')", () => sym("beta_ax_gamma^i"), "beta_ax_gamma^i", "βⁱₐₓ ᵧ", {}],
  ["Symbol(\"F^1^2_3_4\")", () => sym("F^1^2_3_4"), "F^1^2_3_4", "F¹ ²₃ ₄", {}],
  ["Symbol(\"F_1_2^3^4\")", () => sym("F_1_2^3^4"), "F_1_2^3^4", "F³ ⁴₁ ₂", {}],
  ["Symbol(\"F_1_2_3_4\")", () => sym("F_1_2_3_4"), "F_1_2_3_4", "F₁ ₂ ₃ ₄", {}],
  ["Symbol(\"F^1^2^3^4\")", () => sym("F^1^2^3^4"), "F^1^2^3^4", "F¹ ² ³ ⁴", {}],
  ["Symbol('F_beta')", () => sym("F_beta"), "F_beta", "Fᵦ", {}],
  ["Symbol('F_gamma')", () => sym("F_gamma"), "F_gamma", "Fᵧ", {}],
  ["Symbol('F_rho')", () => sym("F_rho"), "F_rho", "Fᵨ", {}],
  ["Symbol('F_phi')", () => sym("F_phi"), "F_phi", "Fᵩ", {}],
  ["Symbol('F_chi')", () => sym("F_chi"), "F_chi", "Fᵪ", {}],
  ["Symbol('F_a')", () => sym("F_a"), "F_a", "Fₐ", {}],
  ["Symbol('F_e')", () => sym("F_e"), "F_e", "Fₑ", {}],
  ["Symbol('F_i')", () => sym("F_i"), "F_i", "Fᵢ", {}],
  ["Symbol('F_o')", () => sym("F_o"), "F_o", "Fₒ", {}],
  ["Symbol('F_u')", () => sym("F_u"), "F_u", "Fᵤ", {}],
  ["Symbol('F_r')", () => sym("F_r"), "F_r", "Fᵣ", {}],
  ["Symbol('F_v')", () => sym("F_v"), "F_v", "Fᵥ", {}],
  ["Symbol('F_x')", () => sym("F_x"), "F_x", "Fₓ", {}],
  ["Symbol('F_h')", () => sym("F_h"), "F_h", "Fₕ", {}],
  ["Symbol('F_k')", () => sym("F_k"), "F_k", "Fₖ", {}],
  ["Symbol('F_l')", () => sym("F_l"), "F_l", "Fₗ", {}],
  ["Symbol('F_m')", () => sym("F_m"), "F_m", "Fₘ", {}],
  ["Symbol('F_n')", () => sym("F_n"), "F_n", "Fₙ", {}],
  ["Symbol('F_p')", () => sym("F_p"), "F_p", "Fₚ", {}],
  ["Symbol('F_s')", () => sym("F_s"), "F_s", "Fₛ", {}],
  ["Symbol('F_t')", () => sym("F_t"), "F_t", "Fₜ", {}],
  ["Symbol('Fmathring')", () => sym("Fmathring"), "Fmathring", "F̊", {}],
  ["Symbol('Fddddot')", () => sym("Fddddot"), "Fddddot", "F⃜", {}],
  ["Symbol('Fdddot')", () => sym("Fdddot"), "Fdddot", "F⃛", {}],
  ["Symbol('Fddot')", () => sym("Fddot"), "Fddot", "F̈", {}],
  ["Symbol('Fdot')", () => sym("Fdot"), "Fdot", "Ḟ", {}],
  ["Symbol('Fcheck')", () => sym("Fcheck"), "Fcheck", "F̌", {}],
  ["Symbol('Fbreve')", () => sym("Fbreve"), "Fbreve", "F̆", {}],
  ["Symbol('Facute')", () => sym("Facute"), "Facute", "F́", {}],
  ["Symbol('Fgrave')", () => sym("Fgrave"), "Fgrave", "F̀", {}],
  ["Symbol('Ftilde')", () => sym("Ftilde"), "Ftilde", "F̃", {}],
  ["Symbol('Fhat')", () => sym("Fhat"), "Fhat", "F̂", {}],
  ["Symbol('Fbar')", () => sym("Fbar"), "Fbar", "F̅", {}],
  ["Symbol('Fvec')", () => sym("Fvec"), "Fvec", "F⃗", {}],
  ["Symbol('Fprime')", () => sym("Fprime"), "Fprime", "F′", {}],
  ["Symbol('Fprm')", () => sym("Fprm"), "Fprm", "F′", {}],
  ["Symbol('Fbold')", () => sym("Fbold"), "Fbold", "Fbold", {}],
  ["Symbol('Fbm')", () => sym("Fbm"), "Fbm", "Fbm", {}],
  ["Symbol('Fcal')", () => sym("Fcal"), "Fcal", "Fcal", {}],
  ["Symbol('Fscr')", () => sym("Fscr"), "Fscr", "Fscr", {}],
  ["Symbol('Ffrak')", () => sym("Ffrak"), "Ffrak", "Ffrak", {}],
  ["Symbol('Fnorm')", () => sym("Fnorm"), "Fnorm", "‖F‖", {}],
  ["Symbol('Favg')", () => sym("Favg"), "Favg", "⟨F⟩", {}],
  ["Symbol('Fabs')", () => sym("Fabs"), "Fabs", "|F|", {}],
  ["Symbol('Fmag')", () => sym("Fmag"), "Fmag", "|F|", {}],
  ["Symbol('xvecdot')", () => sym("xvecdot"), "xvecdot", "x⃗̇", {}],
  ["Symbol('xDotVec')", () => sym("xDotVec"), "xDotVec", "ẋ⃗", {}],
  ["Symbol('xHATNorm')", () => sym("xHATNorm"), "xHATNorm", "‖x̂‖", {}],
  ["Symbol('xMathring_yCheckPRM__zbreveAbs')", () => sym("xMathring_yCheckPRM__zbreveAbs"), "xMathring_yCheckPRM__zbreveAbs", "x̊_y̌′__|z̆|", {}],
  ["Symbol('alphadothat_nVECDOT__tTildePrime')", () => sym("alphadothat_nVECDOT__tTildePrime"), "alphadothat_nVECDOT__tTildePrime", "α̇̂_n⃗̇__t̃′", {}],
  ["Symbol('x_dot')", () => sym("x_dot"), "x_dot", "x_dot", {}],
  ["Symbol('x__dot')", () => sym("x__dot"), "x__dot", "x__dot", {}],
  ["-Rational(1)/2", () => R(-1n, 2n), "-1/2", "-1/2", {}],
  ["-Rational(13)/22", () => R(-13n, 22n), "-13 \n----\n 22 ", "-13 \n────\n 22 ", {}],
  ["-(-x + 5)*(-x - 2*sqrt(2) + 5) - (-y + 5)*(-y + 5)", () => sj.add(sj.mul(R(-1n), sj.pow(sj.add(R(5n), sj.mul(R(-1n), sym("y"))), R(2n))), sj.mul(sj.add(R(-5n), sym("x")), sj.add(R(5n), sj.mul(R(-1n), sym("x")), sj.mul(R(-2n), sj.pow(R(2n), R(1n, 2n)))))), "         2           /         ___    \\\n- (5 - y)  + (x - 5)*\\-x - 2*\\/ 2  + 5/", "         2                          \n- (5 - y)  + (x - 5)⋅(-x - 2⋅√2 + 5)", {}],
  ["EulerGamma", () => sj.S.EulerGamma, "EulerGamma", "γ", {}],
  ["GoldenRatio", () => sj.S.GoldenRatio, "GoldenRatio", "φ", {}],
  ["Catalan", () => sj.S.Catalan, "G", "G", {}],
  ["[Symbol(\"ihat\") / (Symbol(\"i\") + 1)]", () => [sj.mul(sym("ihat"), sj.pow(sj.add(R(1n), sym("i")), R(-1n)))], " ihat  \n[-----]\n i + 1 ", "⎡  î  ⎤\n⎢─────⎥\n⎣i + 1⎦", {}],
  ["Matrix([Symbol(\"ihat\"), Symbol(\"i\") + 1])", () => sj.Matrix.of([[sym("ihat")], [sj.add(R(1n), sym("i"))]]), "[ihat ]\n[     ]\n[i + 1]", "⎡  î  ⎤\n⎢     ⎥\n⎣i + 1⎦", {}],
  ["ConditionSet(x, Eq(sin(x), 0), S.Reals)", () => new sj.ConditionSet(sym("x"), sj.Eq(sj.fn("sin", [sym("x")], { evaluate: false }), R(0n)), sj.Interval.of(sj.S.NegativeInfinity, sj.oo, true, true)), "{x | x in (-oo, oo) and sin(x) = 0}", "{x │ x ∊ ℝ ∧ (sin(x) = 0)}", {}],
  ["ConditionSet(x, Contains(x, S.Reals, evaluate=False), FiniteSet(1))", () => sj.FiniteSet.of(R(1n)), "{1}", "{1}", {}],
  ["ConditionSet(x, And(x > 1, x < -1), FiniteSet(1, 2, 3))", () => sj.EmptySet, "EmptySet", "∅", {}],
  ["ConditionSet(x, Or(x > 1, x < -1), FiniteSet(1, 2))", () => sj.FiniteSet.of(R(2n)), "{2}", "{2}", {}],
  ["a*b", () => sj.mul(sym("a"), sym("b")), "a*b", "a⋅b", {}],
  ["S.UniversalSet", () => UniversalSet, "UniversalSet", "𝕌", {}],
  ["lowergamma(x, y)", () => sj.fn("lowergamma", [sym("x"), sym("y")], { evaluate: false }), "lowergamma(x, y)", "γ(x, y)", {}],
  ["uppergamma(x, y)", () => sj.fn("uppergamma", [sym("x"), sym("y")], { evaluate: false }), "Gamma(x, y)", "Γ(x, y)", {}],
  ["Shi(x)", () => sj.fn("Shi", [sym("x")], { evaluate: false }), "Shi(x)", "Shi(x)", {}],
  ["Si(x)", () => sj.fn("Si", [sym("x")], { evaluate: false }), "Si(x)", "Si(x)", {}],
  ["Ci(x)", () => sj.fn("Ci", [sym("x")], { evaluate: false }), "Ci(x)", "Ci(x)", {}],
  ["Chi(x)", () => sj.fn("Chi", [sym("x")], { evaluate: false }), "Chi(x)", "Chi(x)", {}],
  ["Pow(2, -5, evaluate=False)", () => new sj.Pow(R(2n), R(-5n)), "1 \n--\n 5\n2 ", "1 \n──\n 5\n2 ", {}],
  ["Pow(x, (1/pi))", () => sj.pow(sym("x"), sj.pow(sj.pi, R(-1n))), " 1 \n --\n pi\nx  ", " 1\n ─\n π\nx ", {}],
  ["Integral(x**2, x)**2", () => sj.pow(new sj.Integral([sj.pow(sym("x"), R(2n)), sym("x")]), R(2n)), "          2\n/  /     \\ \n| |      | \n| |  2   | \n| | x  dx| \n| |      | \n\\/       / ", "         2\n⎛⌠      ⎞ \n⎜⎮  2   ⎟ \n⎜⎮ x  dx⎟ \n⎝⌡      ⎠ ", {}],
  ["Sum(x**2, (x, 0, 1))**2", () => sj.pow(sj.Sum(sj.pow(sym("x"), R(2n)), [sym("x"), R(0n), R(1n)]), R(2n)), "          2\n/ 1      \\ \n|___     | \n|\\  `    | \n| \\     2| \n| /    x | \n|/__,    | \n\\x = 0   / ", "          2\n⎛  1     ⎞ \n⎜ ___    ⎟ \n⎜ ╲      ⎟ \n⎜  ╲    2⎟ \n⎜  ╱   x ⎟ \n⎜ ╱      ⎟ \n⎜ ‾‾‾    ⎟ \n⎝x = 0   ⎠ ", {}],
  ["Product(x**2, (x, 1, 2))**2", () => sj.pow(sj.Product(sj.pow(sym("x"), R(2n)), [sym("x"), R(1n), R(2n)]), R(2n)), "           2\n/  2      \\ \n|______   | \n| |  |   2| \n| |  |  x | \n| |  |    | \n\\x = 1    / ", "           2\n⎛  2      ⎞ \n⎜─┬──┬─   ⎟ \n⎜ │  │   2⎟ \n⎜ │  │  x ⎟ \n⎜ │  │    ⎟ \n⎝x = 1    ⎠ ", {}],
  ["Derivative(f(x), x)**2", () => sj.pow(sj.Derivative(sj.SymFunction("f")(sym("x")), [sym("x"), 1]), R(2n)), "          2\n/d       \\ \n|--(f(x))| \n\\dx      / ", "          2\n⎛d       ⎞ \n⎜──(f(x))⎟ \n⎝dx      ⎠ ", {}],
  ["1/sqrt(x)", () => sj.pow(sym("x"), R(-1n, 2n)), "  1  \n-----\n  ___\n\\/ x ", "1 \n──\n√x", {}],
  ["d", () => sym("d"), "d", "d", {}],
  ["I", () => sj.I, "I", "ⅈ", {}],
  ["t", () => sym("t"), "t", "t", {}],
  ["Not(Equivalent(x, y))", () => sj.Not(sj.Equivalent(sym("x"), sym("y"))), "Not(Equivalent(x, y))", "x ⇎ y", {}],
  ["Not(Implies(x, y))", () => sj.Not(sj.Implies(sym("x"), sym("y"))), "Not(Implies(x, y))", "x ↛ y", {}],
  ["Equivalent(x, y)", () => sj.Equivalent(sym("x"), sym("y")), "Equivalent(x, y)", "x ⇔ y", {}],
  ["S.Reals - S.Naturals", () => new SetOp('Complement', [sj.Interval.of(sj.S.NegativeInfinity, sj.oo, true, true), sj.Naturals]), "(-oo, oo) \\ Naturals", "ℝ \\ ℕ", {}],
  ["S.Reals - S.Naturals0", () => new SetOp('Complement', [sj.Interval.of(sj.S.NegativeInfinity, sj.oo, true, true), sj.Naturals0]), "(-oo, oo) \\ Naturals0", "ℝ \\ ℕ₀", {}],
  ["Mod(x, 7)", () => sj.Mod(sym("x"), R(7n)), "x mod 7", "x mod 7", {}],
  ["Mod(x + 1, 7)", () => sj.Mod(sj.add(R(1n), sym("x")), R(7n)), "(x + 1) mod 7", "(x + 1) mod 7", {}],
  ["Mod(2 * x, 7)", () => sj.Mod(sj.mul(R(2n), sym("x")), R(7n)), "2*x mod 7", "2⋅x mod 7", {}],
  ["Mod(x, 7) + 1", () => sj.add(R(1n), sj.Mod(sym("x"), R(7n))), "(x mod 7) + 1", "(x mod 7) + 1", {}],
  ["2 * Mod(x, 7)", () => sj.mul(R(2n), sj.Mod(sym("x"), R(7n))), "2*(x mod 7)", "2⋅(x mod 7)", {}],
  ["x + y", () => sj.add(sym("x"), sym("y")), "x + y", "x + y", {}],
  ["-a*x + -2*y*y", () => sj.add(sj.mul(R(-2n), sj.pow(sym("y"), R(2n))), sj.mul(R(-1n), sym("a"), sym("x"))), "          2\n-a*x - 2*y ", "          2\n-a⋅x - 2⋅y ", {}],
  ["polylog(2, 3)", () => def("polylog")(R(2n), R(3n)), "polylog(2, 3)", "Li₂(3)", {}],
  ["polylog(s, z)", () => def("polylog")(sym("s"), sym("z")), "polylog(s, z)", "Liₛ(z)", {}],
  ["expint(s, z)", () => sj.fn("expint", [sym("s"), sym("z")], { evaluate: false }), "expint(s, z)", "Eₛ(z)", {}],
  ["polylog(s**2, z)", () => def("polylog")(sj.pow(sym("s"), R(2n)), sym("z")), "       / 2   \\\npolylog\\s , z/", "       ⎛ 2   ⎞\npolylog⎝s , z⎠", {}],
  ["lerchphi(a, 1, 2)", () => def("lerchphi")(sym("a"), R(1n), R(2n)), "lerchphi(a, 1, 2)", "Φ(a, 1, 2)", {}],
  ["LambertW(x)", () => sj.fn("LambertW", [sym("x")], { evaluate: false }), "W(x)", "W(x)", {}],
  ["LambertW(x, y)", () => sj.fn("LambertW", [sym("x"), sym("y")], { evaluate: false }), "W(x, y)", "W(x, y)", {}],
  ["airyai(x)", () => sj.fn("airyai", [sym("x")], { evaluate: false }), "Ai(x)", "Ai(x)", {}],
  ["airybi(x)", () => sj.fn("airybi", [sym("x")], { evaluate: false }), "Bi(x)", "Bi(x)", {}],
  ["airyaiprime(x)", () => sj.fn("airyaiprime", [sym("x")], { evaluate: false }), "Ai'(x)", "Ai'(x)", {}],
  ["airybiprime(x)", () => sj.fn("airybiprime", [sym("x")], { evaluate: false }), "Bi'(x)", "Bi'(x)", {}],
  ["fresnelc(x)", () => sj.fn("fresnelc", [sym("x")], { evaluate: false }), "C(x)", "C(x)", {}],
  ["fresnels(x)", () => sj.fn("fresnels", [sym("x")], { evaluate: false }), "S(x)", "S(x)", {}],
  ["Heaviside(x)", () => def("Heaviside")(sym("x"), R(1n, 2n)), "Heaviside(x)", "θ(x)", {}],
  ["Heaviside(x, y)", () => def("Heaviside")(sym("x"), sym("y")), "Heaviside(x, y)", "θ(x, y)", {}],
  ["dirichlet_eta(x)", () => def("dirichlet_eta")(sym("x")), "dirichlet_eta(x)", "η(x)", {}],
  ["Sum(n, (n, -oo, 1))", () => sj.Sum(sym("n"), [sym("n"), sj.S.NegativeInfinity, R(1n)]), "   1     \n  __     \n  \\ `    \n   )    n\n  /_,    \nn = -oo  ", "  1     \n ___    \n ╲      \n  ╲     \n  ╱    n\n ╱      \n ‾‾‾    \nn = -∞  ", {}],
  ["pi**(1/exp(1))", () => sj.pow(sj.pi, sj.exp(R(-1n))), "  / -1\\\n  \\e  /\npi     ", " ⎛ -1⎞\n ⎝ℯ  ⎠\nπ     ", {}],
  ["pi**(1/pi)", () => sj.pow(sj.pi, sj.pow(sj.pi, R(-1n))), "  1 \n  --\n  pi\npi  ", " 1\n ─\n π\nπ ", {}],
  ["pi**(1/EulerGamma)", () => sj.pow(sj.pi, sj.pow(sj.S.EulerGamma, R(-1n))), "      1     \n  ----------\n  EulerGamma\npi          ", " 1\n ─\n γ\nπ ", {}],
  ["7**(1/z)", () => sj.pow(R(7n), sj.pow(sym("z"), R(-1n))), "z ___\n\\/ 7 ", "z ___\n╲╱ 7 ", {}],
  ["ConditionSet(x, Eq(-x + exp(x), 0), S.Complexes)", () => new sj.ConditionSet(sym("x"), sj.Eq(sj.add(sj.mul(R(-1n), sym("x")), sj.exp(sym("x"))), R(0n)), sj.Complexes), "                              x     \n{x | x in Complexes and -x + e  = 0}", "⎧  │         ⎛      x    ⎞⎫\n⎨x │ x ∊ ℂ ∧ ⎝-x + ℯ  = 0⎠⎬\n⎩  │                      ⎭", {}],
  ["m", () => sym("m"), "m", "m", {}],
  ["p", () => sym("p"), "p", "p", {}],
  ["b", () => sym("b"), "b", "b", {}],
];

/** Further expressions (all features of the printer, options). */
const EXTRA: readonly Case[] = [
  ["x", () => sym("x"), "x", "x", {}],
  ["-oo", () => sj.S.NegativeInfinity, "-oo", "-∞", {}],
  ["zoo", () => sj.zoo, "zoo", "zoo", {}],
  ["nan", () => sj.nan, "nan", "nan", {}],
  ["pi", () => sj.pi, "pi", "π", {}],
  ["E", () => sj.E, "e", "ℯ", {}],
  ["S.true", () => sj.S.true, "True", "True", {}],
  ["Rational(1, 2)", () => R(1n, 2n), "1/2", "1/2", {}],
  ["Rational(-1, 2)", () => R(-1n, 2n), "-1/2", "-1/2", {}],
  ["Rational(200, 37)", () => R(200n, 37n), "200\n---\n37 ", "200\n───\n37 ", {}],
  ["Integer(-5)", () => R(-5n), "-5", "-5", {}],
  ["Integer(12345678901234567890)", () => R(12345678901234567890n), "12345678901234567890", "12345678901234567890", {}],
  ["Float(1.5)", () => new sj.Float(1.5), "1.50000000000000", "1.50000000000000", {}],
  ["Float(-2.25)", () => new sj.Float(-2.25), "-2.25000000000000", "-2.25000000000000", {}],
  ["Float('0.1')", () => new sj.Float(0.1), "0.100000000000000", "0.100000000000000", {}],
  ["x**2", () => sj.pow(sym("x"), R(2n)), " 2\nx ", " 2\nx ", {}],
  ["x**2 + x + 1", () => sj.add(R(1n), sym("x"), sj.pow(sym("x"), R(2n))), " 2        \nx  + x + 1", " 2        \nx  + x + 1", {}],
  ["x - x**3/6 + x**5/120", () => sj.add(sym("x"), sj.mul(R(-1n, 6n), sj.pow(sym("x"), R(3n))), sj.mul(R(1n, 120n), sj.pow(sym("x"), R(5n)))), " 5     3    \nx     x     \n--- - -- + x\n120   6     ", " 5     3    \nx     x     \n─── - ── + x\n120   6     ", {}],
  ["x**2 + 2*x + 1", () => sj.add(R(1n), sj.pow(sym("x"), R(2n)), sj.mul(R(2n), sym("x"))), " 2          \nx  + 2*x + 1", " 2          \nx  + 2⋅x + 1", {}],
  ["x*y*z", () => sj.mul(sym("x"), sym("y"), sym("z")), "x*y*z", "x⋅y⋅z", {}],
  ["2*x*y", () => sj.mul(R(2n), sym("x"), sym("y")), "2*x*y", "2⋅x⋅y", {}],
  ["-x*y", () => sj.mul(R(-1n), sym("x"), sym("y")), "-x*y", "-x⋅y", {}],
  ["x - y", () => sj.add(sym("x"), sj.mul(R(-1n), sym("y"))), "x - y", "x - y", {}],
  ["-x - y", () => sj.add(sj.mul(R(-1n), sym("x")), sj.mul(R(-1n), sym("y"))), "-x - y", "-x - y", {}],
  ["x**2*y**3", () => sj.mul(sj.pow(sym("x"), R(2n)), sj.pow(sym("y"), R(3n))), " 2  3\nx *y ", " 2  3\nx ⋅y ", {}],
  ["(x + y)**2", () => sj.pow(sj.add(sym("x"), sym("y")), R(2n)), "       2\n(x + y) ", "       2\n(x + y) ", {}],
  ["(x + y)**-2", () => sj.pow(sj.add(sym("x"), sym("y")), R(-2n)), "   1    \n--------\n       2\n(x + y) ", "   1    \n────────\n       2\n(x + y) ", {}],
  ["(x*y)**z", () => sj.pow(sj.mul(sym("x"), sym("y")), sym("z")), "     z\n(x*y) ", "     z\n(x⋅y) ", {}],
  ["x**(y**z)", () => sj.pow(sym("x"), sj.pow(sym("y"), sym("z"))), " / z\\\n \\y /\nx    ", " ⎛ z⎞\n ⎝y ⎠\nx    ", {}],
  ["(x**y)**z", () => sj.pow(sj.pow(sym("x"), sym("y")), sym("z")), "    z\n/ y\\ \n\\x / ", "    z\n⎛ y⎞ \n⎝x ⎠ ", {}],
  ["x**(1/y)", () => sj.pow(sym("x"), sj.pow(sym("y"), R(-1n))), "y ___\n\\/ x ", "y ___\n╲╱ x ", {}],
  ["sqrt(x)", () => sj.pow(sym("x"), R(1n, 2n)), "  ___\n\\/ x ", "√x", {}],
  ["sqrt(x*y)", () => sj.pow(sj.mul(sym("x"), sym("y")), R(1n, 2n)), "  _____\n\\/ x*y ", "  _____\n╲╱ x⋅y ", {}],
  ["sqrt(x)/2", () => sj.mul(R(1n, 2n), sj.pow(sym("x"), R(1n, 2n))), "  ___\n\\/ x \n-----\n  2  ", "√x\n──\n2 ", {}],
  ["x**Rational(3, 2)", () => sj.pow(sym("x"), R(3n, 2n)), " 3/2\nx   ", " 3/2\nx   ", {}],
  ["2*x + exp(x)", () => sj.add(sj.mul(R(2n), sym("x")), sj.exp(sym("x"))), "       x\n2*x + e ", "       x\n2⋅x + ℯ ", {}],
  ["exp(x)", () => sj.exp(sym("x")), " x\ne ", " x\nℯ ", {}],
  ["exp(-x)", () => sj.exp(sj.mul(R(-1n), sym("x"))), " -x\ne  ", " -x\nℯ  ", {}],
  ["exp(x**2)", () => sj.exp(sj.pow(sym("x"), R(2n))), " / 2\\\n \\x /\ne    ", " ⎛ 2⎞\n ⎝x ⎠\nℯ    ", {}],
  ["x*exp(-x)", () => sj.mul(sym("x"), sj.exp(sj.mul(R(-1n), sym("x")))), "   -x\nx*e  ", "   -x\nx⋅ℯ  ", {}],
  ["exp(x)**2", () => sj.exp(sj.mul(R(2n), sym("x"))), " 2*x\ne   ", " 2⋅x\nℯ   ", {}],
  ["Abs(1/(y - Abs(x)))", () => sj.pow(sj.fn("abs", [sj.add(sym("y"), sj.mul(R(-1n), sj.fn("abs", [sym("x")], { evaluate: false })))], { evaluate: false }), R(-1n)), "    1    \n---------\n|y - |x||", "    1    \n─────────\n│y - │x││", {}],
  ["binomial(n, k)", () => sj.fn("binomial", [sym("n"), sym("k")], { evaluate: false }), "/n\\\n| |\n\\k/", "⎛n⎞\n⎜ ⎟\n⎝k⎠", {}],
  ["conjugate(f(1 + conjugate(f(x))))", () => sj.fn("conjugate", [sj.SymFunction("f")(sj.add(R(1n), sj.fn("conjugate", [sj.SymFunction("f")(sym("x"))], { evaluate: false })))], { evaluate: false }), "___________\n /____    \\\nf\\f(x) + 1/", "___________\n ⎛____    ⎞\nf⎝f(x) + 1⎠", {}],
  ["floor(1/(y - floor(x)))", () => sj.fn("floor", [sj.pow(sj.add(sym("y"), sj.mul(R(-1n), sj.fn("floor", [sym("x")], { evaluate: false }))), R(-1n))], { evaluate: false }), "     /     1      \\\nfloor|------------|\n     \\y - floor(x)/", "⎢   1   ⎥\n⎢───────⎥\n⎣y - ⌊x⌋⎦", {}],
  ["ceiling(1/(y - ceiling(x)))", () => sj.fn("ceiling", [sj.pow(sj.add(sym("y"), sj.mul(R(-1n), sj.fn("ceiling", [sym("x")], { evaluate: false }))), R(-1n))], { evaluate: false }), "       /      1       \\\nceiling|--------------|\n       \\y - ceiling(x)/", "⎡   1   ⎤\n⎢───────⎥\n⎢y - ⌈x⌉⎥", {}],
  ["floor(x)", () => sj.fn("floor", [sym("x")], { evaluate: false }), "floor(x)", "⌊x⌋", {}],
  ["ceiling(x)", () => sj.fn("ceiling", [sym("x")], { evaluate: false }), "ceiling(x)", "⌈x⌉", {}],
  ["sin(x)", () => sj.fn("sin", [sym("x")], { evaluate: false }), "sin(x)", "sin(x)", {}],
  ["cos(x/2)", () => sj.fn("cos", [sj.mul(R(1n, 2n), sym("x"))], { evaluate: false }), "   /x\\\ncos|-|\n   \\2/", "   ⎛x⎞\ncos⎜─⎟\n   ⎝2⎠", {}],
  ["tan(x)**2", () => sj.pow(sj.fn("tan", [sym("x")], { evaluate: false }), R(2n)), "   2   \ntan (x)", "   2   \ntan (x)", {}],
  ["log(x)", () => sj.fn("log", [sym("x")], { evaluate: false }), "log(x)", "log(x)", {}],
  ["log(x)**2", () => sj.pow(sj.fn("log", [sym("x")], { evaluate: false }), R(2n)), "   2   \nlog (x)", "   2   \nlog (x)", {}],
  ["log(x + 1)", () => sj.fn("log", [sj.add(R(1n), sym("x"))], { evaluate: false }), "log(x + 1)", "log(x + 1)", {}],
  ["sin(x + y)", () => sj.fn("sin", [sj.add(sym("x"), sym("y"))], { evaluate: false }), "sin(x + y)", "sin(x + y)", {}],
  ["sin(x)*cos(y)", () => sj.mul(sj.fn("cos", [sym("y")], { evaluate: false }), sj.fn("sin", [sym("x")], { evaluate: false })), "sin(x)*cos(y)", "sin(x)⋅cos(y)", {}],
  ["asin(x)", () => sj.fn("asin", [sym("x")], { evaluate: false }), "asin(x)", "asin(x)", {}],
  ["atan2(y, x)", () => sj.fn("atan2", [sym("y"), sym("x")], { evaluate: false }), "atan2(y, x)", "atan2(y, x)", {}],
  ["gamma(x)", () => sj.fn("gamma", [sym("x")], { evaluate: false }), "Gamma(x)", "Γ(x)", {}],
  ["gamma(x)**2", () => sj.pow(sj.fn("gamma", [sym("x")], { evaluate: false }), R(2n)), "     2   \nGamma (x)", " 2   \nΓ (x)", {}],
  ["beta(x, y)", () => sj.fn("beta", [sym("x"), sym("y")], { evaluate: false }), "B(x, y)", "Β(x, y)", {}],
  ["zeta(x)", () => sj.fn("zeta", [sym("x")], { evaluate: false }), "zeta(x)", "ζ(x)", {}],
  ["expint(n, z)", () => sj.fn("expint", [sym("n"), sym("z")], { evaluate: false }), "expint(n, z)", "Eₙ(z)", {}],
  ["expint(10, z)", () => sj.fn("expint", [R(10n), sym("z")], { evaluate: false }), "expint(10, z)", "expint(10, z)", {}],
  ["erf(x)", () => sj.fn("erf", [sym("x")], { evaluate: false }), "erf(x)", "erf(x)", {}],
  ["re(x)", () => sj.fn("re", [sym("x")], { evaluate: false }), "re(x)", "re(x)", {}],
  ["im(x)", () => sj.fn("im", [sym("x")], { evaluate: false }), "im(x)", "im(x)", {}],
  ["sign(x)", () => sj.fn("sign", [sym("x")], { evaluate: false }), "sign(x)", "sign(x)", {}],
  ["KroneckerDelta(x, y + 1)", () => sj.fn("KroneckerDelta", [sym("x"), sj.add(R(1n), sym("y"))], { evaluate: false }), "d       \n x,y + 1", "δ       \n x,y + 1", {}],
  ["primenu(n)", () => sj.fn("primenu", [sym("n")], { evaluate: false }), "nu(n)", "ν(n)", {}],
  ["primeomega(n)", () => sj.fn("primeomega", [sym("n")], { evaluate: false }), "Omega(n)", "Ω(n)", {}],
  ["harmonic(n)", () => sj.fn("harmonic", [sym("n")], { evaluate: false }), "harmonic(n)", "harmonic(n)", {}],
  ["Eq(x**2 + 1, 0)", () => sj.Eq(sj.add(R(1n), sj.pow(sym("x"), R(2n))), R(0n)), " 2        \nx  + 1 = 0", " 2        \nx  + 1 = 0", {}],
  ["Le(x/2, 1)", () => sj.Le(sj.mul(R(1n, 2n), sym("x")), R(1n)), "x     \n- <= 1\n2     ", "x    \n─ ≤ 1\n2    ", {}],
  ["Not(x)", () => sj.Not(sym("x")), "Not(x)", "¬x", {}],
  ["And(x < 1, y > 2)", () => sj.And(sj.Gt(sym("y"), R(2n)), sj.Lt(sym("x"), R(1n))), "And(y > 2, x < 1)", "y > 2 ∧ x < 1", {}],
  ["Or(x < 1, x > 2)", () => sj.Or(sj.Gt(sym("x"), R(2n)), sj.Lt(sym("x"), R(1n))), "Or(x > 2, x < 1)", "x > 2 ∨ x < 1", {}],
  ["And(x, Or(y, z))", () => sj.And(sym("x"), sj.Or(sym("y"), sym("z"))), "And(x, Or(y, z))", "x ∧ (y ∨ z)", {}],
  ["Not(And(x, y))", () => sj.Not(sj.And(sym("x"), sym("y"))), "Not(And(x, y))", "¬(x ∧ y)", {}],
  ["And(*symbols('a b c d e f'))", () => sj.And(sym("a"), sym("b"), sym("c"), sym("d"), sym("e"), sym("f")), "And(a, b, c, d, e, f)", "a ∧ b ∧ c ∧ d ∧ e ∧ f", {}],
  ["Or(*symbols('a b c d e f'))", () => sj.Or(sym("a"), sym("b"), sym("c"), sym("d"), sym("e"), sym("f")), "Or(a, b, c, d, e, f)", "a ∨ b ∨ c ∨ d ∨ e ∨ f", {}],
  ["Not(Equivalent(x, y, evaluate=False))", () => sj.Not(sj.Equivalent(sym("x"), sym("y"))), "Not(Equivalent(x, y))", "x ⇎ y", {}],
  ["Not(Implies(x, y, evaluate=False))", () => sj.Not(sj.Implies(sym("x"), sym("y"))), "Not(Implies(x, y))", "x ↛ y", {}],
  ["Integral(sin(x)**2/tan(x)**2, x)", () => new sj.Integral([sj.mul(sj.pow(sj.fn("sin", [sym("x")], { evaluate: false }), R(2n)), sj.pow(sj.fn("tan", [sym("x")], { evaluate: false }), R(-2n))), sym("x")]), "  /          \n |           \n |    2      \n | sin (x)   \n | ------- dx\n |    2      \n | tan (x)   \n |           \n/            ", "⌠           \n⎮    2      \n⎮ sin (x)   \n⎮ ─────── dx\n⎮    2      \n⎮ tan (x)   \n⌡           ", {}],
  ["Integral(x + 1, x)", () => new sj.Integral([sj.add(R(1n), sym("x")), sym("x")]), "  /          \n |           \n | (x + 1) dx\n |           \n/            ", "⌠           \n⎮ (x + 1) dx\n⌡           ", {}],
  ["Integral(exp(-x**2), (x, -oo, oo))", () => new sj.Integral([sj.exp(sj.mul(R(-1n), sj.pow(sym("x"), R(2n)))), sym("x"), sj.S.NegativeInfinity, sj.oo]), " oo        \n  /        \n |         \n |     2   \n |   -x    \n |  e    dx\n |         \n/          \n-oo        ", "∞         \n⌠         \n⎮     2   \n⎮   -x    \n⎮  ℯ    dx\n⌡         \n-∞        ", {}],
  ["Integral(1/x, (x, 1, oo))", () => new sj.Integral([sj.pow(sym("x"), R(-1n)), sym("x"), R(1n), sj.oo]), " oo     \n  /     \n |      \n |  1   \n |  - dx\n |  x   \n |      \n/       \n1       ", "∞     \n⌠     \n⎮ 1   \n⎮ ─ dx\n⎮ x   \n⌡     \n1     ", {}],
  ["Sum(1/(1 + 1/(1 + 1/k)) + 1, (k, 111, 1 + 1/n), (k, 1/(1 + m), oo)) + 1/(1 + 1/k)", () => sj.add(sj.pow(sj.add(R(1n), sj.pow(sym("k"), R(-1n))), R(-1n)), sj.Sum(sj.add(R(1n), sj.pow(sj.add(R(1n), sj.pow(sj.add(R(1n), sj.pow(sym("k"), R(-1n))), R(-1n))), R(-1n))), [sym("k"), R(111n), sj.add(R(1n), sj.pow(sym("n"), R(-1n)))], [sym("k"), sj.pow(sj.add(R(1n), sym("m")), R(-1n)), sj.oo])), "              1                          \n          1 + -                          \n   oo         n                          \n _____    _____                          \n \\    `   \\    `                         \n  \\        \\      /        1    \\        \n   \\        \\     |1 + ---------|        \n    \\        \\    |          1  |     1  \n     )        )   |    1 + -----| + -----\n    /        /    |            1|       1\n   /        /     |        1 + -|   1 + -\n  /        /      \\            k/       k\n /____,   /____,                         \n      1   k = 111                        \nk = -----                                \n    m + 1                                ", "              1                          \n          1 + ─                          \n   ∞          n                          \n ______   ______                         \n ╲        ╲                              \n  ╲        ╲                             \n   ╲        ╲     ⎛        1    ⎞        \n    ╲        ╲    ⎜1 + ─────────⎟        \n     ╲        ╲   ⎜          1  ⎟     1  \n     ╱        ╱   ⎜    1 + ─────⎟ + ─────\n    ╱        ╱    ⎜            1⎟       1\n   ╱        ╱     ⎜        1 + ─⎟   1 + ─\n  ╱        ╱      ⎝            k⎠       k\n ╱        ╱                              \n ‾‾‾‾‾‾   ‾‾‾‾‾‾                         \n      1   k = 111                        \nk = ─────                                \n    m + 1                                ", {}],
  ["Sum(1/k**2, (k, 1, n))", () => sj.Sum(sj.pow(sym("k"), R(-2n)), [sym("k"), R(1n), sym("n")]), "  n     \n____    \n\\   `   \n \\    1 \n  \\   --\n  /    2\n /    k \n/___,   \nk = 1   ", " n      \n____    \n╲       \n ╲    1 \n  ╲   ──\n  ╱    2\n ╱    k \n╱       \n‾‾‾‾    \nk = 1   ", {}],
  ["Sum(k + 1, (k, 1, n))", () => sj.Sum(sj.add(R(1n), sym("k")), [sym("k"), R(1n), sym("n")]), "  n          \n __          \n \\ `         \n  )   (k + 1)\n /_,         \nk = 1        ", "  n          \n ___         \n ╲           \n  ╲          \n  ╱   (k + 1)\n ╱           \n ‾‾‾         \nk = 1        ", {}],
  ["Product(k, (k, 1, n))", () => sj.Product(sym("k"), [sym("k"), R(1n), sym("n")]), "  n    \n_____  \n | |  k\n | |   \nk = 1  ", "  n    \n─┬─┬─  \n │ │  k\n │ │   \nk = 1  ", {}],
  ["Product(1/k, (k, 1, n))", () => sj.Product(sj.pow(sym("k"), R(-1n)), [sym("k"), R(1n), sym("n")]), "   n      \n________  \n |    |  1\n |    |  -\n |    |  k\n |    |   \n k = 1    ", "   n      \n─┬────┬─  \n │    │  1\n │    │  ─\n │    │  k\n │    │   \n k = 1    ", {}],
  ["Derivative(f(x), x)", () => sj.Derivative(sj.SymFunction("f")(sym("x")), [sym("x"), 1]), "d       \n--(f(x))\ndx      ", "d       \n──(f(x))\ndx      ", {}],
  ["Derivative(f(x), x, 2)", () => sj.Derivative(sj.SymFunction("f")(sym("x")), [sym("x"), 2]), " 2       \nd        \n---(f(x))\n  2      \ndx       ", " 2       \nd        \n───(f(x))\n  2      \ndx       ", {}],
  ["Derivative(sin(x)*y, x)", () => sj.Derivative(sj.mul(sym("y"), sj.fn("sin", [sym("x")], { evaluate: false })), [sym("x"), 1]), "d           \n--(y*sin(x))\ndx          ", "∂           \n──(y⋅sin(x))\n∂x          ", {}],
  ["Derivative(f(x, y), x, y)", () => sj.Derivative(sj.SymFunction("f")(sym("x"), sym("y")), [sym("x"), 1], [sym("y"), 1]), "  2           \n d            \n-----(f(x, y))\ndy dx         ", "  2           \n ∂            \n─────(f(x, y))\n∂y ∂x         ", {}],
  ["Limit(sin(x)/x, x, 0, '-')", () => new sj.Limit([sj.mul(sj.pow(sym("x"), R(-1n)), sj.fn("sin", [sym("x")], { evaluate: false })), sym("x"), R(0n)], "-"), "     /sin(x)\\\n lim |------|\nx->0-\\  x   /", "     ⎛sin(x)⎞\n lim ⎜──────⎟\nx─→0⁻⎝  x   ⎠", {}],
  ["Limit(x*Limit(y/2, y, 0), x, 0)", () => new sj.Limit([sj.mul(sym("x"), new sj.Limit([sj.mul(R(1n, 2n), sym("y")), sym("y"), R(0n)], "+")), sym("x"), R(0n)], "+"), "     /       /y\\\\\n lim |x* lim |-||\nx->0+\\  y->0+\\2//", "     ⎛       ⎛y⎞⎞\n lim ⎜x⋅ lim ⎜─⎟⎟\nx─→0⁺⎝  y─→0⁺⎝2⎠⎠", {}],
  ["2*Limit(x*Limit(y/2, y, 0), x, 0)", () => sj.mul(R(2n), new sj.Limit([sj.mul(sym("x"), new sj.Limit([sj.mul(R(1n, 2n), sym("y")), sym("y"), R(0n)], "+")), sym("x"), R(0n)], "+")), "       /       /y\\\\\n2* lim |x* lim |-||\n  x->0+\\  y->0+\\2//", "       ⎛       ⎛y⎞⎞\n2⋅ lim ⎜x⋅ lim ⎜─⎟⎟\n  x─→0⁺⎝  y─→0⁺⎝2⎠⎠", {}],
  ["Limit(1/x, x, -oo)", () => new sj.Limit([sj.pow(sym("x"), R(-1n)), sym("x"), sj.S.NegativeInfinity], "+"), "      1\n lim  -\nx->-oox", "     1\n lim ─\nx─→-∞x", {}],
  ["x + Piecewise((x, x > 0), (y, True)) + Piecewise((x/y, x < 2), (y**2, x > 2), (1, True)) + 1", () => sj.add(R(1n), sym("x"), sj.Piecewise([sym("x"), sj.Gt(sym("x"), R(0n))], [sym("y"), true]), sj.Piecewise([sj.mul(sym("x"), sj.pow(sym("y"), R(-1n))), sj.Lt(sym("x"), R(2n))], [sj.pow(sym("y"), R(2n)), sj.Gt(sym("x"), R(2n))], [R(1n), true])), "                      //x            \\    \n                      ||-   for x < 2|    \n                      ||y            |    \n    //x  for x > 0\\   ||             |    \nx + |<            | + |< 2           | + 1\n    \\\\y  otherwise/   ||y   for x > 2|    \n                      ||             |    \n                      ||1   otherwise|    \n                      \\\\             /    ", "                      ⎛⎧x            ⎞    \n                      ⎜⎪─   for x < 2⎟    \n                      ⎜⎪y            ⎟    \n    ⎛⎧x  for x > 0⎞   ⎜⎪             ⎟    \nx + ⎜⎨            ⎟ + ⎜⎨ 2           ⎟ + 1\n    ⎝⎩y  otherwise⎠   ⎜⎪y   for x > 2⎟    \n                      ⎜⎪             ⎟    \n                      ⎜⎪1   otherwise⎟    \n                      ⎝⎩             ⎠    ", {}],
  ["x - Piecewise((x, x > 0), (y, True)) + Piecewise((x/y, x < 2), (y**2, x > 2), (1, True)) + 1", () => sj.add(R(1n), sym("x"), sj.mul(R(-1n), sj.Piecewise([sym("x"), sj.Gt(sym("x"), R(0n))], [sym("y"), true])), sj.Piecewise([sj.mul(sym("x"), sj.pow(sym("y"), R(-1n))), sj.Lt(sym("x"), R(2n))], [sj.pow(sym("y"), R(2n)), sj.Gt(sym("x"), R(2n))], [R(1n), true])), "                      //x            \\    \n                      ||-   for x < 2|    \n                      ||y            |    \n    //x  for x > 0\\   ||             |    \nx - |<            | + |< 2           | + 1\n    \\\\y  otherwise/   ||y   for x > 2|    \n                      ||             |    \n                      ||1   otherwise|    \n                      \\\\             /    ", "                      ⎛⎧x            ⎞    \n                      ⎜⎪─   for x < 2⎟    \n                      ⎜⎪y            ⎟    \n    ⎛⎧x  for x > 0⎞   ⎜⎪             ⎟    \nx - ⎜⎨            ⎟ + ⎜⎨ 2           ⎟ + 1\n    ⎝⎩y  otherwise⎠   ⎜⎪y   for x > 2⎟    \n                      ⎜⎪             ⎟    \n                      ⎜⎪1   otherwise⎟    \n                      ⎝⎩             ⎠    ", {}],
  ["Piecewise((x, x > 0), (y, True))*Piecewise((x/y, x < 2), (y**2, x > 2), (1, True))", () => sj.mul(sj.Piecewise([sym("x"), sj.Gt(sym("x"), R(0n))], [sym("y"), true]), sj.Piecewise([sj.mul(sym("x"), sj.pow(sym("y"), R(-1n))), sj.Lt(sym("x"), R(2n))], [sj.pow(sym("y"), R(2n)), sj.Gt(sym("x"), R(2n))], [R(1n), true])), "                //x            \\\n                ||-   for x < 2|\n                ||y            |\n//x  for x > 0\\ ||             |\n|<            |*|< 2           |\n\\\\y  otherwise/ ||y   for x > 2|\n                ||             |\n                ||1   otherwise|\n                \\\\             /", "                ⎛⎧x            ⎞\n                ⎜⎪─   for x < 2⎟\n                ⎜⎪y            ⎟\n⎛⎧x  for x > 0⎞ ⎜⎪             ⎟\n⎜⎨            ⎟⋅⎜⎨ 2           ⎟\n⎝⎩y  otherwise⎠ ⎜⎪y   for x > 2⎟\n                ⎜⎪             ⎟\n                ⎜⎪1   otherwise⎟\n                ⎝⎩             ⎠", {}],
  ["-Piecewise((x, x > 0), (y, True))*Piecewise((x/y, x < 2), (y**2, x > 2), (1, True))", () => sj.mul(R(-1n), sj.Piecewise([sym("x"), sj.Gt(sym("x"), R(0n))], [sym("y"), true]), sj.Piecewise([sj.mul(sym("x"), sj.pow(sym("y"), R(-1n))), sj.Lt(sym("x"), R(2n))], [sj.pow(sym("y"), R(2n)), sj.Gt(sym("x"), R(2n))], [R(1n), true])), "                 //x            \\\n                 ||-   for x < 2|\n                 ||y            |\n //x  for x > 0\\ ||             |\n-|<            |*|< 2           |\n \\\\y  otherwise/ ||y   for x > 2|\n                 ||             |\n                 ||1   otherwise|\n                 \\\\             /", "                 ⎛⎧x            ⎞\n                 ⎜⎪─   for x < 2⎟\n                 ⎜⎪y            ⎟\n ⎛⎧x  for x > 0⎞ ⎜⎪             ⎟\n-⎜⎨            ⎟⋅⎜⎨ 2           ⎟\n ⎝⎩y  otherwise⎠ ⎜⎪y   for x > 2⎟\n                 ⎜⎪             ⎟\n                 ⎜⎪1   otherwise⎟\n                 ⎝⎩             ⎠", {}],
  ["Piecewise((0, x < 0), (x**2, x < 1), (1, True))", () => sj.Piecewise([R(0n), sj.Lt(sym("x"), R(0n))], [sj.pow(sym("x"), R(2n)), sj.Lt(sym("x"), R(1n))], [R(1n), true]), "/0   for x < 0\n|             \n| 2           \n<x   for x < 1\n|             \n|1   otherwise\n\\             ", "⎧0   for x < 0\n⎪             \n⎪ 2           \n⎨x   for x < 1\n⎪             \n⎪1   otherwise\n⎩             ", {}],
  ["Piecewise((x, x > 0), (y, True))**2", () => sj.Piecewise([sj.pow(sym("x"), R(2n)), sj.Gt(sym("x"), R(0n))], [sj.pow(sym("y"), R(2n)), true]), "/ 2           \n|x   for x > 0\n<             \n| 2           \n\\y   otherwise", "⎧ 2           \n⎪x   for x > 0\n⎨             \n⎪ 2           \n⎩y   otherwise", {}],
  ["Interval(0, 1)", () => sj.Interval.of(R(0n), R(1n), false, false), "[0, 1]", "[0, 1]", {}],
  ["Interval(0, 1, True, False)", () => sj.Interval.of(R(0n), R(1n), true, false), "(0, 1]", "(0, 1]", {}],
  ["Interval(0, 1, False, True)", () => sj.Interval.of(R(0n), R(1n), false, true), "[0, 1)", "[0, 1)", {}],
  ["Interval(0, 1, True, True)", () => sj.Interval.of(R(0n), R(1n), true, true), "(0, 1)", "(0, 1)", {}],
  ["Interval(0, oo)", () => sj.Interval.of(R(0n), sj.oo, false, true), "[0, oo)", "[0, ∞)", {}],
  ["Interval(-oo, 0, True, False)", () => sj.Interval.of(sj.S.NegativeInfinity, R(0n), true, false), "(-oo, 0]", "(-∞, 0]", {}],
  ["Interval(x, y)", () => sj.Interval.of(sym("x"), sym("y"), false, false), "[x, y]", "[x, y]", {}],
  ["Interval(1, Rational(5, 2))", () => sj.Interval.of(R(1n), R(5n, 2n), false, false), "[1, 5/2]", "[1, 5/2]", {}],
  ["FiniteSet(1, 2, 3)", () => sj.FiniteSet.of(R(1n), R(2n), R(3n)), "{1, 2, 3}", "{1, 2, 3}", {}],
  ["FiniteSet(x, y, z)", () => sj.FiniteSet.of(sym("x"), sym("y"), sym("z")), "{x, y, z}", "{x, y, z}", {}],
  ["FiniteSet(x**2, Rational(1, 2))", () => sj.FiniteSet.of(R(1n, 2n), sj.pow(sym("x"), R(2n))), "       2 \n{1/2, x }", "⎧      2⎫\n⎨1/2, x ⎬\n⎩       ⎭", {}],
  ["Union(Interval(0, 1), Interval(2, 3))", () => sj.Union(sj.Interval.of(R(0n), R(1n), false, false), sj.Interval.of(R(2n), R(3n), false, false)), "[0, 1] U [2, 3]", "[0, 1] ∪ [2, 3]", {}],
  ["Union(Interval(0, 1), FiniteSet(5))", () => sj.Union(sj.Interval.of(R(0n), R(1n), false, false), sj.FiniteSet.of(R(5n))), "[0, 1] U {5}", "[0, 1] ∪ {5}", {}],
  ["Intersection(Interval(0, x), Interval(y, 3))", () => sj.Intersection(sj.Interval.of(R(0n), sym("x"), false, false), sj.Interval.of(sym("y"), R(3n), false, false)), "[0, x] n [y, 3]", "[0, x] ∩ [y, 3]", {}],
  ["Complement(Interval(0, 2), FiniteSet(1), evaluate=False)", () => new SetOp('Complement', [sj.Interval.of(R(0n), R(2n), false, false), sj.FiniteSet.of(R(1n))]), "[0, 2] \\ {1}", "[0, 2] \\ {1}", {}],
  ["Union(Intersection(Interval(0, x), Interval(y, 3)), Interval(5, 6))", () => sj.Union(sj.Interval.of(R(5n), R(6n), false, false), sj.Intersection(sj.Interval.of(R(0n), sym("x"), false, false), sj.Interval.of(sym("y"), R(3n), false, false))), "[5, 6] U ([0, x] n [y, 3])", "[5, 6] ∪ ([0, x] ∩ [y, 3])", {}],
  ["S.EmptySet", () => sj.EmptySet, "EmptySet", "∅", {}],
  ["S.Reals", () => sj.Interval.of(sj.S.NegativeInfinity, sj.oo, true, true), "(-oo, oo)", "ℝ", {}],
  ["S.Integers", () => sj.Integers, "Integers", "ℤ", {}],
  ["S.Naturals", () => sj.Naturals, "Naturals", "ℕ", {}],
  ["S.Naturals0", () => sj.Naturals0, "Naturals0", "ℕ₀", {}],
  ["S.Complexes", () => sj.Complexes, "Complexes", "ℂ", {}],
  ["ImageSet(Lambda(x, x**2), S.Naturals)", () => sj.imageset(sym("x"), sj.pow(sym("x"), R(2n)), sj.Naturals), "  2                 \n{x  | x in Naturals}", "⎧ 2 │      ⎫\n⎨x  │ x ∊ ℕ⎬\n⎩   │      ⎭", {}],
  ["ImageSet(Lambda(x, 1/x**2), S.Naturals)", () => sj.imageset(sym("x"), sj.pow(sym("x"), R(-2n)), sj.Naturals), " 1                  \n{-- | x in Naturals}\n  2                 \n x                  ", "⎧1  │      ⎫\n⎪── │ x ∊ ℕ⎪\n⎨ 2 │      ⎬\n⎪x  │      ⎪\n⎩   │      ⎭", {}],
  ["ConditionSet(x, x < 1, S.Reals)", () => new sj.ConditionSet(sym("x"), sj.Lt(sym("x"), R(1n)), sj.Interval.of(sj.S.NegativeInfinity, sj.oo, true, true)), "{x | x in (-oo, oo) and x < 1}", "{x │ x ∊ ℝ ∧ (x < 1)}", {}],
  ["ConditionSet(x, Eq(x**2, 1), S.Reals)", () => new sj.ConditionSet(sym("x"), sj.Eq(sj.pow(sym("x"), R(2n)), R(1n)), sj.Interval.of(sj.S.NegativeInfinity, sj.oo, true, true)), "                         2     \n{x | x in (-oo, oo) and x  = 1}", "⎧  │         ⎛ 2    ⎞⎫\n⎨x │ x ∊ ℝ ∧ ⎝x  = 1⎠⎬\n⎩  │                 ⎭", {}],
  ["Lambda(x, x + 1)", () => sj.Lambda(sym("x"), sj.add(R(1n), sym("x"))), "x -> x + 1", "x ↦ x + 1", {}],
  ["Mod(2*x, 7)", () => sj.Mod(sj.mul(R(2n), sym("x")), R(7n)), "2*x mod 7", "2⋅x mod 7", {}],
  ["Mod(x, 7)*2", () => sj.mul(R(2n), sj.Mod(sym("x"), R(7n))), "2*(x mod 7)", "2⋅(x mod 7)", {}],
  ["O(x**2)", () => sj.O(sj.pow(sym("x"), R(2n)), sym("x"), R(0n)), " / 2\\\nO\\x /", " ⎛ 2⎞\nO⎝x ⎠", {}],
  ["O(x)", () => sj.O(sym("x"), sym("x"), R(0n)), "O(x)", "O(x)", {}],
  ["alpha", () => sym("alpha"), "alpha", "α", {}],
  ["Symbol('alpha_1')", () => sym("alpha_1"), "alpha_1", "α₁", {}],
  ["Symbol('x_1')", () => sym("x_1"), "x_1", "x₁", {}],
  ["Symbol('x_12')", () => sym("x_12"), "x_12", "x₁₂", {}],
  ["Symbol('x1')", () => sym("x1"), "x1", "x₁", {}],
  ["Symbol('y_beta')", () => sym("y_beta"), "y_beta", "yᵦ", {}],
  ["Symbol('x^2')", () => sym("x^2"), "x^2", "x²", {}],
  ["Symbol('x__2')", () => sym("x__2"), "x__2", "x²", {}],
  ["Symbol('x_a')", () => sym("x_a"), "x_a", "xₐ", {}],
  ["Symbol('x_b')", () => sym("x_b"), "x_b", "x_b", {}],
  ["Symbol('x_ab')", () => sym("x_ab"), "x_ab", "x_ab", {}],
  ["Symbol('F_1_2')", () => sym("F_1_2"), "F_1_2", "F₁ ₂", {}],
  ["Symbol('F^1^2_3_4')", () => sym("F^1^2_3_4"), "F^1^2_3_4", "F¹ ²₃ ₄", {}],
  ["Symbol('Gamma')", () => sym("Gamma"), "Gamma", "Γ", {}],
  ["Symbol('xdot')", () => sym("xdot"), "xdot", "ẋ", {}],
  ["Symbol('xhat')", () => sym("xhat"), "xhat", "x̂", {}],
  ["Symbol('xbar')", () => sym("xbar"), "xbar", "x̅", {}],
  ["Symbol('xvec')", () => sym("xvec"), "xvec", "x⃗", {}],
  ["Symbol('xprime')", () => sym("xprime"), "xprime", "x′", {}],
  ["Symbol('xddot')", () => sym("xddot"), "xddot", "ẍ", {}],
  ["Symbol('xmathring')", () => sym("xmathring"), "xmathring", "x̊", {}],
  ["Symbol('xnorm')", () => sym("xnorm"), "xnorm", "‖x‖", {}],
  ["Symbol('xabs')", () => sym("xabs"), "xabs", "|x|", {}],
  ["Symbol('xavg')", () => sym("xavg"), "xavg", "⟨x⟩", {}],
  ["Symbol('alphahat')", () => sym("alphahat"), "alphahat", "α̂", {}],
  ["Symbol('Upsilon_2')", () => sym("Upsilon_2"), "Upsilon_2", "Υ₂", {}],
  ["Symbol('omega_i')", () => sym("omega_i"), "omega_i", "ωᵢ", {}],
  ["Symbol('hbar')", () => sym("hbar"), "hbar", "h̅", {}],
  ["Symbol('varsigma')", () => sym("varsigma"), "varsigma", "ς", {}],
  ["alpha**2 + beta_s", () => sj.add(sym("beta"), sj.pow(sym("alpha"), R(2n))), "     2       \nalpha  + beta", " 2    \nα  + β", {}],
  ["th*ph", () => sj.mul(sym("phi"), sym("theta")), "phi*theta", "φ⋅θ", {}],
  ["x + y + z", () => sj.add(sym("x"), sym("y"), sym("z")), "x + y + z", "x + y + z", {}],
  ["x**3 + x**2*y + x*y**2 + y**3", () => sj.add(sj.pow(sym("x"), R(3n)), sj.pow(sym("y"), R(3n)), sj.mul(sym("x"), sj.pow(sym("y"), R(2n))), sj.mul(sym("y"), sj.pow(sym("x"), R(2n)))), " 3    2        2    3\nx  + x *y + x*y  + y ", " 3    2        2    3\nx  + x ⋅y + x⋅y  + y ", {}],
  ["x**2*y + x*y**2", () => sj.add(sj.mul(sym("x"), sj.pow(sym("y"), R(2n))), sj.mul(sym("y"), sj.pow(sym("x"), R(2n)))), " 2        2\nx *y + x*y ", " 2        2\nx ⋅y + x⋅y ", {}],
  ["(x + 1)**10", () => sj.pow(sj.add(R(1n), sym("x")), R(10n)), "       10\n(x + 1)  ", "       10\n(x + 1)  ", {}],
  ["1/(1 + 1/(1 + 1/x))", () => sj.pow(sj.add(R(1n), sj.pow(sj.add(R(1n), sj.pow(sym("x"), R(-1n))), R(-1n))), R(-1n)), "    1    \n---------\n      1  \n1 + -----\n        1\n    1 + -\n        x", "    1    \n─────────\n      1  \n1 + ─────\n        1\n    1 + ─\n        x", {}],
  ["x/(y/z)", () => sj.mul(sym("x"), sym("z"), sj.pow(sym("y"), R(-1n))), "x*z\n---\n y ", "x⋅z\n───\n y ", {}],
  ["(x + y)/(x - y)", () => sj.mul(sj.pow(sj.add(sym("x"), sj.mul(R(-1n), sym("y"))), R(-1n)), sj.add(sym("x"), sym("y"))), "x + y\n-----\nx - y", "x + y\n─────\nx - y", {}],
  ["1/(x*y*z)", () => sj.mul(sj.pow(sym("x"), R(-1n)), sj.pow(sym("y"), R(-1n)), sj.pow(sym("z"), R(-1n))), "  1  \n-----\nx*y*z", "  1  \n─────\nx⋅y⋅z", {}],
  ["2/x", () => sj.mul(R(2n), sj.pow(sym("x"), R(-1n))), "2\n-\nx", "2\n─\nx", {}],
  ["2*x/3", () => sj.mul(R(2n, 3n), sym("x")), "2*x\n---\n 3 ", "2⋅x\n───\n 3 ", {}],
  ["-2*x/3", () => sj.mul(R(-2n, 3n), sym("x")), "-2*x \n-----\n  3  ", "-2⋅x \n─────\n  3  ", {}],
  ["x/2 + y/3", () => sj.add(sj.mul(R(1n, 2n), sym("x")), sj.mul(R(1n, 3n), sym("y"))), "x   y\n- + -\n2   3", "x   y\n─ + ─\n2   3", {}],
  ["3*I", () => sj.mul(R(3n), sj.I), "3*I", "3⋅ⅈ", {}],
  ["-I", () => sj.mul(R(-1n), sj.I), "-I", "-ⅈ", {}],
  ["x*I", () => sj.mul(sj.I, sym("x")), "I*x", "ⅈ⋅x", {}],
  ["2 + 3*I", () => sj.add(R(2n), sj.mul(R(3n), sj.I)), "2 + 3*I", "2 + 3⋅ⅈ", {}],
  ["I*pi", () => sj.mul(sj.pi, sj.I), "I*pi", "ⅈ⋅π", {}],
  ["pi*x", () => sj.mul(sj.pi, sym("x")), "pi*x", "π⋅x", {}],
  ["E*x", () => sj.mul(sj.E, sym("x")), "e*x", "ℯ⋅x", {}],
  ["x*oo", () => sj.mul(sj.oo, sym("x")), "oo*x", "∞⋅x", {}],
  ["x - oo", () => sj.add(sj.S.NegativeInfinity, sym("x")), "x - oo", "x - ∞", {}],
  ["x + oo", () => sj.add(sj.oo, sym("x")), "x + oo", "x + ∞", {}],
  ["2*pi", () => sj.mul(R(2n), sj.pi), "2*pi", "2⋅π", {}],
  ["pi**2", () => sj.pow(sj.pi, R(2n)), "  2\npi ", " 2\nπ ", {}],
  ["sqrt(pi)", () => sj.pow(sj.pi, R(1n, 2n)), "  ____\n\\/ pi ", "√π", {}],
  ["sqrt(2)*x", () => sj.mul(sym("x"), sj.pow(R(2n), R(1n, 2n))), "  ___  \n\\/ 2 *x", "√2⋅x", {}],
  ["sqrt(2)/2", () => sj.mul(R(1n, 2n), sj.pow(R(2n), R(1n, 2n))), "  ___\n\\/ 2 \n-----\n  2  ", "√2\n──\n2 ", {}],
  ["-sqrt(2)/2 + sqrt(6)/4", () => sj.add(sj.mul(R(-1n, 2n), sj.pow(R(2n), R(1n, 2n))), sj.mul(R(1n, 4n), sj.pow(R(6n), R(1n, 2n)))), "    ___     ___\n  \\/ 2    \\/ 6 \n- ----- + -----\n    2       4  ", "  √2   √6\n- ── + ──\n  2    4 ", {}],
  ["x**(-2)", () => sj.pow(sym("x"), R(-2n)), "1 \n--\n 2\nx ", "1 \n──\n 2\nx ", {}],
  ["x**Rational(2, 3)", () => sj.pow(sym("x"), R(2n, 3n)), " 2/3\nx   ", " 2/3\nx   ", {}],
  ["x**(S(1)/x)", () => sj.pow(sym("x"), sj.pow(sym("x"), R(-1n))), "x ___\n\\/ x ", "x ___\n╲╱ x ", {}],
  ["exp(1/x)", () => sj.exp(sj.pow(sym("x"), R(-1n))), " 1\n -\n x\ne ", " 1\n ─\n x\nℯ ", {}],
  ["exp(-1)", () => sj.exp(R(-1n)), " -1\ne  ", " -1\nℯ  ", {}],
  ["exp(Rational(1, 2))", () => sj.exp(R(1n, 2n)), " 1/2\ne   ", " 1/2\nℯ   ", {}],
  ["log(x)/log(10)", () => sj.mul(sj.pow(sj.fn("log", [R(10n)], { evaluate: false }), R(-1n)), sj.fn("log", [sym("x")], { evaluate: false })), "log(x) \n-------\nlog(10)", "log(x) \n───────\nlog(10)", {}],
  ["1 + 1/x", () => sj.add(R(1n), sj.pow(sym("x"), R(-1n))), "    1\n1 + -\n    x", "    1\n1 + ─\n    x", {}],
  ["1 - 1/x**2", () => sj.add(R(1n), sj.mul(R(-1n), sj.pow(sym("x"), R(-2n)))), "    1 \n1 - --\n     2\n    x ", "    1 \n1 - ──\n     2\n    x ", {}],
  ["x**2/(x**2 + 1)", () => sj.mul(sj.pow(sym("x"), R(2n)), sj.pow(sj.add(R(1n), sj.pow(sym("x"), R(2n))), R(-1n))), "   2  \n  x   \n------\n 2    \nx  + 1", "   2  \n  x   \n──────\n 2    \nx  + 1", {}],
  ["(x**2 + 1)/(x - 1)**2", () => sj.mul(sj.pow(sj.add(R(-1n), sym("x")), R(-2n)), sj.add(R(1n), sj.pow(sym("x"), R(2n)))), "  2     \n x  + 1 \n--------\n       2\n(x - 1) ", "  2     \n x  + 1 \n────────\n       2\n(x - 1) ", {}],
  ["x*(y + z)", () => sj.mul(sym("x"), sj.add(sym("y"), sym("z"))), "x*(y + z)", "x⋅(y + z)", {}],
  ["-x*(y + z)", () => sj.mul(R(-1n), sym("x"), sj.add(sym("y"), sym("z"))), "-x*(y + z)", "-x⋅(y + z)", {}],
  ["(x - y)*(y - z)", () => sj.mul(sj.add(sym("x"), sj.mul(R(-1n), sym("y"))), sj.add(sym("y"), sj.mul(R(-1n), sym("z")))), "(x - y)*(y - z)", "(x - y)⋅(y - z)", {}],
  ["x**(x + y)", () => sj.pow(sym("x"), sj.add(sym("x"), sym("y"))), " x + y\nx     ", " x + y\nx     ", {}],
  ["x**(y/2)", () => sj.pow(sym("x"), sj.mul(R(1n, 2n), sym("y"))), " y\n -\n 2\nx ", " y\n ─\n 2\nx ", {}],
  ["(x/y)**2", () => sj.mul(sj.pow(sym("x"), R(2n)), sj.pow(sym("y"), R(-2n))), " 2\nx \n--\n 2\ny ", " 2\nx \n──\n 2\ny ", {}],
  ["(1 + x)**Rational(1, 2)", () => sj.pow(sj.add(R(1n), sym("x")), R(1n, 2n)), "  _______\n\\/ x + 1 ", "  _______\n╲╱ x + 1 ", {}],
  ["(1 + x)**Rational(-1, 2)", () => sj.pow(sj.add(R(1n), sym("x")), R(-1n, 2n)), "    1    \n---------\n  _______\n\\/ x + 1 ", "    1    \n─────────\n  _______\n╲╱ x + 1 ", {}],
  ["f(x)**2", () => sj.pow(sj.SymFunction("f")(sym("x")), R(2n)), " 2   \nf (x)", " 2   \nf (x)", {}],
  ["f(x, y)**2", () => sj.pow(sj.SymFunction("f")(sym("x"), sym("y")), R(2n)), " 2      \nf (x, y)", " 2      \nf (x, y)", {}],
  ["sin(x)**Rational(1, 2)", () => sj.pow(sj.fn("sin", [sym("x")], { evaluate: false }), R(1n, 2n)), "  ________\n\\/ sin(x) ", "  ________\n╲╱ sin(x) ", {}],
  ["sin(x)**(-1)", () => sj.pow(sj.fn("sin", [sym("x")], { evaluate: false }), R(-1n)), "  1   \n------\nsin(x)", "  1   \n──────\nsin(x)", {}],
  ["sin(x)**x", () => sj.pow(sj.fn("sin", [sym("x")], { evaluate: false }), sym("x")), "   x   \nsin (x)", "   x   \nsin (x)", {}],
  ["sin(1/x)", () => sj.fn("sin", [sj.pow(sym("x"), R(-1n))], { evaluate: false }), "   /1\\\nsin|-|\n   \\x/", "   ⎛1⎞\nsin⎜─⎟\n   ⎝x⎠", {}],
  ["sin(x/(y + 1))**2", () => sj.pow(sj.fn("sin", [sj.mul(sym("x"), sj.pow(sj.add(R(1n), sym("y")), R(-1n)))], { evaluate: false }), R(2n)), "   2/  x  \\\nsin |-----|\n    \\y + 1/", "   2⎛  x  ⎞\nsin ⎜─────⎟\n    ⎝y + 1⎠", {}],
  ["1.5*x + 2.5", () => sj.add(new sj.Float(2.5), sj.mul(new sj.Float(1.5), sym("x"))), "1.5*x + 2.5", "1.5⋅x + 2.5", {}],
  ["x**1.5", () => sj.pow(sym("x"), new sj.Float(1.5)), " 1.5\nx   ", " 1.5\nx   ", {}],
  ["Float('3.14159265358979')", () => new sj.Float(3.14159265358979), "3.14159265358979", "3.14159265358979", {}],
  ["-2.0*x", () => sj.mul(new sj.Float(-2.0), sym("x")), "-2.0*x", "-2.0⋅x", {}],
  ["Mul(x + y, Rational(1, 1), Rational(3, 4), Rational(5, 6), evaluate=False)", () => new sj.Mul([sj.add(sym("x"), sym("y")), R(1n), R(3n, 4n), R(5n, 6n)]), "(x + y)*1*3/4*5/6", "(x + y)⋅1⋅3/4⋅5/6", {}],
  ["Matrix([[1, 2], [3, 4]])", () => sj.Matrix.of([[R(1n), R(2n)], [R(3n), R(4n)]]), "[1  2]\n[    ]\n[3  4]", "⎡1  2⎤\n⎢    ⎥\n⎣3  4⎦", {}],
  ["Matrix([[1], [2], [3]])", () => sj.Matrix.of([[R(1n)], [R(2n)], [R(3n)]]), "[1]\n[ ]\n[2]\n[ ]\n[3]", "⎡1⎤\n⎢ ⎥\n⎢2⎥\n⎢ ⎥\n⎣3⎦", {}],
  ["Matrix([[x, y]])", () => sj.Matrix.of([[sym("x"), sym("y")]]), "[x  y]", "[x  y]", {}],
  ["Matrix([[Rational(1, 2), sqrt(x)], [Integral(x, x), -1]])", () => sj.Matrix.of([[R(1n, 2n), sj.pow(sym("x"), R(1n, 2n))], [new sj.Integral([sym("x"), sym("x")]), R(-1n)]]), "[           ___]\n[  1/2    \\/ x ]\n[              ]\n[  /           ]\n[ |            ]\n[ | x dx   -1  ]\n[ |            ]\n[/             ]", "⎡ 1/2    √x⎤\n⎢          ⎥\n⎢⌠         ⎥\n⎢⎮ x dx  -1⎥\n⎣⌡         ⎦", {}],
  ["Matrix([[x]])", () => sj.Matrix.of([[sym("x")]]), "[x]", "[x]", {}],
  ["(1 + x)**20 ;; {\"num_columns\": 80}", () => sj.pow(sj.add(R(1n), sym("x")), R(20n)), "       20\n(x + 1)  ", "       20\n(x + 1)  ", {"numColumns": 80}],
  ["expand((1 + x)**20) ;; {\"num_columns\": 80}", () => sj.add(R(1n), sj.pow(sym("x"), R(20n)), sj.mul(R(20n), sym("x")), sj.mul(R(20n), sj.pow(sym("x"), R(19n))), sj.mul(R(190n), sj.pow(sym("x"), R(2n))), sj.mul(R(190n), sj.pow(sym("x"), R(18n))), sj.mul(R(1140n), sj.pow(sym("x"), R(3n))), sj.mul(R(1140n), sj.pow(sym("x"), R(17n))), sj.mul(R(4845n), sj.pow(sym("x"), R(4n))), sj.mul(R(4845n), sj.pow(sym("x"), R(16n))), sj.mul(R(15504n), sj.pow(sym("x"), R(5n))), sj.mul(R(15504n), sj.pow(sym("x"), R(15n))), sj.mul(R(38760n), sj.pow(sym("x"), R(6n))), sj.mul(R(38760n), sj.pow(sym("x"), R(14n))), sj.mul(R(77520n), sj.pow(sym("x"), R(7n))), sj.mul(R(77520n), sj.pow(sym("x"), R(13n))), sj.mul(R(125970n), sj.pow(sym("x"), R(8n))), sj.mul(R(125970n), sj.pow(sym("x"), R(12n))), sj.mul(R(167960n), sj.pow(sym("x"), R(9n))), sj.mul(R(167960n), sj.pow(sym("x"), R(11n))), sj.mul(R(184756n), sj.pow(sym("x"), R(10n)))), " 20       19        18         17         16          15          14           >\nx   + 20*x   + 190*x   + 1140*x   + 4845*x   + 15504*x   + 38760*x   + 77520*x >\n\n> 13           12           11           10           9           8          7 >\n>    + 125970*x   + 167960*x   + 184756*x   + 167960*x  + 125970*x  + 77520*x  >\n\n>           6          5         4         3        2           \n>  + 38760*x  + 15504*x  + 4845*x  + 1140*x  + 190*x  + 20*x + 1", " 20       19        18         17         16          15          14           ↪\nx   + 20⋅x   + 190⋅x   + 1140⋅x   + 4845⋅x   + 15504⋅x   + 38760⋅x   + 77520⋅x ↪\n\n↪ 13           12           11           10           9           8          7 ↪\n↪    + 125970⋅x   + 167960⋅x   + 184756⋅x   + 167960⋅x  + 125970⋅x  + 77520⋅x  ↪\n\n↪           6          5         4         3        2           \n↪  + 38760⋅x  + 15504⋅x  + 4845⋅x  + 1140⋅x  + 190⋅x  + 20⋅x + 1", {"numColumns": 80}],
  ["expand((1 + x)**20) ;; {\"num_columns\": 40}", () => sj.add(R(1n), sj.pow(sym("x"), R(20n)), sj.mul(R(20n), sym("x")), sj.mul(R(20n), sj.pow(sym("x"), R(19n))), sj.mul(R(190n), sj.pow(sym("x"), R(2n))), sj.mul(R(190n), sj.pow(sym("x"), R(18n))), sj.mul(R(1140n), sj.pow(sym("x"), R(3n))), sj.mul(R(1140n), sj.pow(sym("x"), R(17n))), sj.mul(R(4845n), sj.pow(sym("x"), R(4n))), sj.mul(R(4845n), sj.pow(sym("x"), R(16n))), sj.mul(R(15504n), sj.pow(sym("x"), R(5n))), sj.mul(R(15504n), sj.pow(sym("x"), R(15n))), sj.mul(R(38760n), sj.pow(sym("x"), R(6n))), sj.mul(R(38760n), sj.pow(sym("x"), R(14n))), sj.mul(R(77520n), sj.pow(sym("x"), R(7n))), sj.mul(R(77520n), sj.pow(sym("x"), R(13n))), sj.mul(R(125970n), sj.pow(sym("x"), R(8n))), sj.mul(R(125970n), sj.pow(sym("x"), R(12n))), sj.mul(R(167960n), sj.pow(sym("x"), R(9n))), sj.mul(R(167960n), sj.pow(sym("x"), R(11n))), sj.mul(R(184756n), sj.pow(sym("x"), R(10n)))), " 20       19        18         17      >\nx   + 20*x   + 190*x   + 1140*x   + 48 >\n\n>     16          15          14       >\n> 45*x   + 15504*x   + 38760*x   + 775 >\n\n>     13           12           11     >\n> 20*x   + 125970*x   + 167960*x   + 1 >\n\n>        10           9           8    >\n> 84756*x   + 167960*x  + 125970*x  +  >\n\n>        7          6          5       >\n> 77520*x  + 38760*x  + 15504*x  + 484 >\n\n>    4         3        2           \n> 5*x  + 1140*x  + 190*x  + 20*x + 1", " 20       19        18         17      ↪\nx   + 20⋅x   + 190⋅x   + 1140⋅x   + 48 ↪\n\n↪     16          15          14       ↪\n↪ 45⋅x   + 15504⋅x   + 38760⋅x   + 775 ↪\n\n↪     13           12           11     ↪\n↪ 20⋅x   + 125970⋅x   + 167960⋅x   + 1 ↪\n\n↪        10           9           8    ↪\n↪ 84756⋅x   + 167960⋅x  + 125970⋅x  +  ↪\n\n↪        7          6          5       ↪\n↪ 77520⋅x  + 38760⋅x  + 15504⋅x  + 484 ↪\n\n↪    4         3        2           \n↪ 5⋅x  + 1140⋅x  + 190⋅x  + 20⋅x + 1", {"numColumns": 40}],
  ["expand((1 + x)**20) ;; {\"wrap_line\": false}", () => sj.add(R(1n), sj.pow(sym("x"), R(20n)), sj.mul(R(20n), sym("x")), sj.mul(R(20n), sj.pow(sym("x"), R(19n))), sj.mul(R(190n), sj.pow(sym("x"), R(2n))), sj.mul(R(190n), sj.pow(sym("x"), R(18n))), sj.mul(R(1140n), sj.pow(sym("x"), R(3n))), sj.mul(R(1140n), sj.pow(sym("x"), R(17n))), sj.mul(R(4845n), sj.pow(sym("x"), R(4n))), sj.mul(R(4845n), sj.pow(sym("x"), R(16n))), sj.mul(R(15504n), sj.pow(sym("x"), R(5n))), sj.mul(R(15504n), sj.pow(sym("x"), R(15n))), sj.mul(R(38760n), sj.pow(sym("x"), R(6n))), sj.mul(R(38760n), sj.pow(sym("x"), R(14n))), sj.mul(R(77520n), sj.pow(sym("x"), R(7n))), sj.mul(R(77520n), sj.pow(sym("x"), R(13n))), sj.mul(R(125970n), sj.pow(sym("x"), R(8n))), sj.mul(R(125970n), sj.pow(sym("x"), R(12n))), sj.mul(R(167960n), sj.pow(sym("x"), R(9n))), sj.mul(R(167960n), sj.pow(sym("x"), R(11n))), sj.mul(R(184756n), sj.pow(sym("x"), R(10n)))), " 20       19        18         17         16          15          14          13           12           11           10           9           8          7          6          5         4         3        2           \nx   + 20*x   + 190*x   + 1140*x   + 4845*x   + 15504*x   + 38760*x   + 77520*x   + 125970*x   + 167960*x   + 184756*x   + 167960*x  + 125970*x  + 77520*x  + 38760*x  + 15504*x  + 4845*x  + 1140*x  + 190*x  + 20*x + 1", " 20       19        18         17         16          15          14          13           12           11           10           9           8          7          6          5         4         3        2           \nx   + 20⋅x   + 190⋅x   + 1140⋅x   + 4845⋅x   + 15504⋅x   + 38760⋅x   + 77520⋅x   + 125970⋅x   + 167960⋅x   + 184756⋅x   + 167960⋅x  + 125970⋅x  + 77520⋅x  + 38760⋅x  + 15504⋅x  + 4845⋅x  + 1140⋅x  + 190⋅x  + 20⋅x + 1", {"wrapLine": false}],
  ["expand((a + b + c)**4) ;; {\"num_columns\": 50}", () => sj.add(sj.pow(sym("a"), R(4n)), sj.pow(sym("b"), R(4n)), sj.pow(sym("c"), R(4n)), sj.mul(R(4n), sym("a"), sj.pow(sym("b"), R(3n))), sj.mul(R(4n), sym("a"), sj.pow(sym("c"), R(3n))), sj.mul(R(4n), sym("b"), sj.pow(sym("a"), R(3n))), sj.mul(R(4n), sym("b"), sj.pow(sym("c"), R(3n))), sj.mul(R(4n), sym("c"), sj.pow(sym("a"), R(3n))), sj.mul(R(4n), sym("c"), sj.pow(sym("b"), R(3n))), sj.mul(R(6n), sj.pow(sym("a"), R(2n)), sj.pow(sym("b"), R(2n))), sj.mul(R(6n), sj.pow(sym("a"), R(2n)), sj.pow(sym("c"), R(2n))), sj.mul(R(6n), sj.pow(sym("b"), R(2n)), sj.pow(sym("c"), R(2n))), sj.mul(R(12n), sym("a"), sym("b"), sj.pow(sym("c"), R(2n))), sj.mul(R(12n), sym("a"), sym("c"), sj.pow(sym("b"), R(2n))), sj.mul(R(12n), sym("b"), sym("c"), sj.pow(sym("a"), R(2n)))), " 4      3        3        2  2       2           >\na  + 4*a *b + 4*a *c + 6*a *b  + 12*a *b*c + 6*a >\n\n> 2  2        3         2             2        3 >\n>  *c  + 4*a*b  + 12*a*b *c + 12*a*b*c  + 4*a*c  >\n\n>     4      3        2  2        3    4\n>  + b  + 4*b *c + 6*b *c  + 4*b*c  + c ", " 4      3        3        2  2       2           ↪\na  + 4⋅a ⋅b + 4⋅a ⋅c + 6⋅a ⋅b  + 12⋅a ⋅b⋅c + 6⋅a ↪\n\n↪ 2  2        3         2             2        3 ↪\n↪  ⋅c  + 4⋅a⋅b  + 12⋅a⋅b ⋅c + 12⋅a⋅b⋅c  + 4⋅a⋅c  ↪\n\n↪     4      3        2  2        3    4\n↪  + b  + 4⋅b ⋅c + 6⋅b ⋅c  + 4⋅b⋅c  + c ", {"numColumns": 50}],
  ["sqrt(2) ;; {\"use_unicode_sqrt_char\": false}", () => sj.pow(R(2n), R(1n, 2n)), "  ___\n\\/ 2 ", "  ___\n╲╱ 2 ", {"useUnicodeSqrtChar": false}],
  ["sqrt(Symbol('C1')) ;; {\"use_unicode_sqrt_char\": false}", () => sj.pow(sym("C1"), R(1n, 2n)), "  ____\n\\/ C1 ", "  ____\n╲╱ C₁ ", {"useUnicodeSqrtChar": false}],
  ["x**Rational(1, 3) ;; {\"root_notation\": false}", () => sj.pow(sym("x"), R(1n, 3n)), " 1/3\nx   ", " 1/3\nx   ", {"rootNotation": false}],
  ["sqrt(x) ;; {\"root_notation\": false}", () => sj.pow(sym("x"), R(1n, 2n)), " 1/2\nx   ", " 1/2\nx   ", {"rootNotation": false}],
  ["x**(1/y) ;; {\"root_notation\": false}", () => sj.pow(sym("x"), sj.pow(sym("y"), R(-1n))), " 1\n -\n y\nx ", " 1\n ─\n y\nx ", {"rootNotation": false}],
  ["2 + 3*I ;; {\"imaginary_unit\": \"j\"}", () => sj.add(R(2n), sj.mul(R(3n), sj.I)), "2 + 3*I", "2 + 3⋅ⅉ", {"imaginaryUnit": "j"}],
  ["I ;; {\"imaginary_unit\": \"j\"}", () => sj.I, "I", "ⅉ", {"imaginaryUnit": "j"}],
  ["Float(1.5) + x ;; {\"full_prec\": true}", () => sj.add(new sj.Float(1.5), sym("x")), "x + 1.50000000000000", "x + 1.50000000000000", {"fullPrec": true}],
  ["Float(1.5)*x ;; {\"full_prec\": false}", () => sj.mul(new sj.Float(1.5), sym("x")), "1.5*x", "1.5⋅x", {"fullPrec": false}],
  ["Float(1.5) ;; {\"full_prec\": false}", () => new sj.Float(1.5), "1.5", "1.5", {"fullPrec": false}],
  ["x**2 + y + 1 ;; {\"order\": \"none\"}", () => sj.add(R(1n), sym("y"), sj.pow(sym("x"), R(2n))), "         2\n1 + y + x ", "         2\n1 + y + x ", {"orderTerms": "none"}],
];

const check = ([, build, ascii, unicode, opts]: Case): void => {
  const e = build();
  expect(pretty(e, { ...opts, useUnicode: false })).toBe(ascii);
  expect(pretty(e, { ...opts, useUnicode: true })).toBe(unicode);
};

const [x, y, z] = sj.symbols('x y z');
const Rn = (p: number, q = 1): Rational => Rational.of(BigInt(p), BigInt(q));

/** [SymPy source, symjs builder, ASCII output, unicode output]. */
const CASES: [string, () => Printable, string, string][] = [
  ["Union(Interval(sqrt(2), 3), FiniteSet(x), evaluate=False)", () => new SetOp('Union', [sj.Interval.of(sj.sqrt(2), 3), sj.FiniteSet.of(x)]), "   ___          \n[\\/ 2 , 3] U {x}", "[√2, 3] ∪ {x}"],
  ["Union(S.Integers, Interval(0, 1), evaluate=False)", () => new SetOp('Union', [sj.Integers, sj.Interval.of(0, 1)]), "Integers U [0, 1]", "ℤ ∪ [0, 1]"],
  ["Union(S.Naturals, FiniteSet(-1), evaluate=False)", () => new SetOp('Union', [sj.Naturals, sj.FiniteSet.of(-1)]), "{-1} U Naturals", "{-1} ∪ ℕ"],
  ["Union(S.Naturals0, FiniteSet(-1), evaluate=False)", () => new SetOp('Union', [sj.Naturals0, sj.FiniteSet.of(-1)]), "{-1} U Naturals0", "{-1} ∪ ℕ₀"],
  ["Union(S.Naturals0, S.Naturals, evaluate=False)", () => new SetOp('Union', [sj.Naturals, sj.Naturals0]), "Naturals0 U Naturals", "ℕ₀ ∪ ℕ"],
  ["Union(FiniteSet(1, x), Interval(0, 1), evaluate=False)", () => new SetOp('Union', [sj.FiniteSet.of(1, x), sj.Interval.of(0, 1)]), "[0, 1] U {1, x}", "[0, 1] ∪ {1, x}"],
  ["Union(FiniteSet(1, 2), Interval(-1, 0), evaluate=False)", () => new SetOp('Union', [sj.FiniteSet.of(1, 2), sj.Interval.of(-1, 0)]), "[-1, 0] U {1, 2}", "[-1, 0] ∪ {1, 2}"],
  ["Intersection(Union(Interval(0, 1), Interval(2, 3), evaluate=False), Interval(-5, -4), evaluate=False)", () => new SetOp('Intersection', [new SetOp('Union', [sj.Interval.of(0, 1), sj.Interval.of(2, 3)]), sj.Interval.of(-5, -4)]), "[-5, -4] n ([0, 1] U [2, 3])", "[-5, -4] ∩ ([0, 1] ∪ [2, 3])"],
  ["Union(S.Reals, FiniteSet(-1), evaluate=False)", () => new SetOp('Union', [sj.Reals, sj.FiniteSet.of(-1)]), "(-oo, oo) U {-1}", "ℝ ∪ {-1}"],
  ["Union(S.Complexes, FiniteSet(-1), evaluate=False)", () => new SetOp('Union', [sj.Complexes, sj.FiniteSet.of(-1)]), "{-1} U Complexes", "{-1} ∪ ℂ"],
  ["S.TribonacciConstant", () => S.TribonacciConstant, "TribonacciConstant", "TribonacciConstant"],
  ["factorial(x + 1)", () => new Fn('factorial', [sj.add(x, 1)]), "(x + 1)!", "(x + 1)!"],
  ["factorial2(x + 1)", () => new Fn('factorial2', [sj.add(x, 1)]), "(x + 1)!!", "(x + 1)!!"],
  ["subfactorial(x + 1)", () => new Fn('subfactorial', [sj.add(x, 1)]), "!(x + 1)", "!(x + 1)"],
  ["factorial(Rational(1, 2), evaluate=False)", () => new Fn('factorial', [Rn(1, 2)]), "(1/2)!", "(1/2)!"],
  ["exp_polar(x)", () => new Fn('exp_polar', [x]), " x\ne ", " x\nℯ "],
  ["gamma(x)", () => new Fn('gamma', [x]), "Gamma(x)", "Γ(x)"],
  ["uppergamma(x, y)", () => new Fn('uppergamma', [x, y]), "Gamma(x, y)", "Γ(x, y)"],
  ["lowergamma(x, y)", () => new Fn('lowergamma', [x, y]), "lowergamma(x, y)", "γ(x, y)"],
  ["beta(x, y)", () => new Fn('beta', [x, y]), "B(x, y)", "Β(x, y)"],
  ["fresnels(x)", () => new Fn('fresnels', [x]), "S(x)", "S(x)"],
  ["fresnelc(x)", () => new Fn('fresnelc', [x]), "C(x)", "C(x)"],
  ["airyai(x)", () => new Fn('airyai', [x]), "Ai(x)", "Ai(x)"],
  ["airybiprime(x)", () => new Fn('airybiprime', [x]), "Bi'(x)", "Bi'(x)"],
  ["LambertW(x)", () => new Fn('LambertW', [x]), "W(x)", "W(x)"],
  ["DiracDelta(x)", () => sj.DiracDelta(x), "DiracDelta(x)", "δ(x)"],
  ["DiracDelta(x, 1)", () => sj.DiracDelta(x, 1), "DiracDelta(x, 1)", " (1)    \nδ    (x)"],
  ["Add(x, -oo, evaluate=False)", () => new Add([x, S.NegativeInfinity]), "x - oo", "x - ∞"],
  ["Add(-oo, x, evaluate=False)", () => new Add([S.NegativeInfinity, x]), "x - oo", "x - ∞"],
  ["Add(y, Mul(x, -1, evaluate=False), evaluate=False)", () => new Add([y, new Mul([x, Rn(-1)])]), "x*-1 + y", "x⋅-1 + y"],
  ["Pow(S.Half, x, evaluate=False)", () => new Pow(Rn(1, 2), x), " -x\n2  ", " -x\n2  "],
  ["Integral(x, (x, 1))", () => new Integral([x, x, Rn(1)]), "  1     \n  /     \n |      \n |  x dx\n |      \n/       \n        ", "1     \n⌠     \n⎮ x dx\n⌡     \n      "],
  // a degenerate Interval node prints as the point set, which is what SymPy's Interval(x, x) evaluates to
  ["FiniteSet(x)", () => new Interval(x, x, false, false), "{x}", "{x}"],
  ["ConditionSet(x, x > 0, S.UniversalSet)", () => new sj.ConditionSet(x, sj.Gt(x, 0), UniversalSet), "{x | x > 0}", "{x │ (x > 0)}"],
  ["AccumBounds(1, 2)", () => sj.AccumBounds(1, 2), "<1, 2>", "<1, 2>"],
  ["x**(1/y)", () => sj.pow(x, sj.pow(y, -1)), "y ___\n\\/ x ", "y ___\n╲╱ x "],
  ["(x**2)**(1/y)", () => new Pow(sj.pow(x, 2), sj.pow(y, -1)), "   ____\ny /  2 \n\\/  x  ", "   ____\ny ╱  2 \n╲╱  x  "],
  ["Mod(x, y)", () => sj.Mod(x, y), "x mod y", "x mod y"],
  ["Mod(x + 1, y)", () => sj.Mod(sj.add(x, 1), y), "(x + 1) mod y", "(x + 1) mod y"],
  ["floor(x)", () => new Fn('floor', [x]), "floor(x)", "⌊x⌋"],
  ["atan2(y, x)", () => new Fn('atan2', [y, x]), "atan2(y, x)", "atan2(y, x)"],
  ["KroneckerDelta(x, y)", () => new Fn('KroneckerDelta', [x, y]), "d   \n x,y", "δ   \n x,y"],
  ["primenu(x)", () => new Fn('primenu', [x]), "nu(x)", "ν(x)"],
  ["primeomega(x)", () => new Fn('primeomega', [x]), "Omega(x)", "Ω(x)"],
  ["expint(2, x)", () => new Fn('expint', [Rn(2), x]), "expint(2, x)", "E₂(x)"],
  ["expint(y, x)", () => new Fn('expint', [y, x]), "expint(y, x)", "expint(y, x)"],
  ["Chi(x)", () => new Fn('Chi', [x]), "Chi(x)", "Chi(x)"],
  ["binomial(x, y)", () => new Fn('binomial', [x, y]), "/x\\\n| |\n\\y/", "⎛x⎞\n⎜ ⎟\n⎝y⎠"],
  ["Union(Interval(0, 1), FiniteSet(0, 5), evaluate=False)", () => new SetOp('Union', [sj.Interval.of(0, 1), sj.FiniteSet.of(0, 5)]), "{0, 5} U [0, 1]", "{0, 5} ∪ [0, 1]"],
  ["Union(FiniteSet(f(1)), Interval(0, 1), evaluate=False)", () => new SetOp('Union', [sj.FiniteSet.of(sj.SymFunction('f')(1)), sj.Interval.of(0, 1)]), "[0, 1] U {f(1)}", "[0, 1] ∪ {f(1)}"],
  ["Union(FiniteSet(5), Interval(0, 1), evaluate=False)", () => new SetOp('Union', [sj.FiniteSet.of(5), sj.Interval.of(0, 1)]), "[0, 1] U {5}", "[0, 1] ∪ {5}"],
  ["Union(FiniteSet(pi), FiniteSet(3), evaluate=False)", () => new SetOp('Union', [sj.FiniteSet.of(S.Pi), sj.FiniteSet.of(3)]), "{3} U {pi}", "{3} ∪ {π}"],
  ["Derivative(f(x, n), x) with n integer", () => sj.Derivative(sj.SymFunction('f')(x, sj.symbol('n', { integer: true })), x), "d          \n--(f(x, n))\ndx         ", "d          \n──(f(x, n))\ndx         "],
  ["Derivative(f(x, y), x)", () => sj.Derivative(sj.SymFunction('f')(x, y), x), "d          \n--(f(x, y))\ndx         ", "∂          \n──(f(x, y))\n∂x         "],
];

const uni = (e: unknown): string => sj.pretty(e as Expr, { useUnicode: true });
const asc = (e: unknown): string => sj.pretty(e as Expr, { useUnicode: false });

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

describe('pretty: SymPy test_pretty.py', () => {
  it.each(TEST_PRETTY.map((c) => [c[0], c] as const))('%s', (_src, c) => check(c));
});

describe('pretty: further expressions and settings', () => {
  it.each(EXTRA.map((c) => [c[0], c] as const))('%s', (_src, c) => check(c));
});

describe('pprint / prettyPrint / pagerPrint', () => {
  const x = sym('x');
  const e = sj.add(sj.pow(x, 2), sj.mul(2, x), 1);
  it('pretty of x**2 + 2*x + 1', () => {
    expect(pretty(e)).toBe(' 2          \nx  + 2⋅x + 1');
    expect(pretty(e, { useUnicode: false })).toBe(' 2          \nx  + 2*x + 1');
  });
  it('pprint returns the printed text', () => {
    expect(pprint(e)).toBe(' 2          \nx  + 2⋅x + 1\n');
    expect(prettyPrint(e, { useUnicode: false })).toBe(' 2          \nx  + 2*x + 1\n');
  });
  it('pagerPrint does not wrap', () => {
    const long = sj.expand(sj.pow(sj.add(x, 1), 30));
    expect(pagerPrint(long).includes('\n\n')).toBe(false);
    expect(pretty(long).includes('\n\n')).toBe(true);
  });
  it('without useUnicode, the module-wide flag of pprintUseUnicode decides (SymPy use_unicode=None)', () => {
    const prev = pprintUseUnicode(false);
    try {
      expect(pprintUseUnicode()).toBe(false);
      // SymPy doctests print in ASCII: pprint(x**2) is ' 2\nx'
      expect(pretty(sj.pow(x, 2))).toBe(' 2\nx ');
      expect(pretty(sj.mul(2, x))).toBe('2*x');
      expect(pretty(sj.mul(2, x), { useUnicode: true })).toBe('2⋅x');
      pprintTryUseUnicode();
      expect(pprintUseUnicode()).toBe(true);
      expect(pretty(sj.mul(2, x))).toBe('2⋅x');
    } finally {
      pprintUseUnicode(prev);
    }
  });
  it('restores the unicode flag', () => {
    const prev = prettyUseUnicode();
    pretty(e, { useUnicode: !prev });
    expect(prettyUseUnicode()).toBe(prev);
  });
  it('mulSymbol (symjs extension)', () => {
    expect(pretty(sj.mul(2, x), { mulSymbol: '·' })).toBe('2·x');
    expect(pretty(sj.mul(2, x))).toBe('2⋅x');
  });
  it('rejects an invalid imaginary unit', () => {
    expect(() => new PrettyPrinter({ imaginaryUnit: 'k' as unknown as 'i' })).toThrow(RangeError);
  });
  it('strings, numbers and booleans', () => {
    expect(pretty('xxx')).toBe('xxx');
    expect(pretty(3)).toBe('3');
    expect(pretty(true)).toBe('True');
    expect(pretty(new PrettyTuple(x))).toBe('(x,)');
  });
});

describe('prettyHooks', () => {
  it('a registered printer for an extension node', () => {
    const x = sym('x');
    const e = sj.Lambda(x, sj.pow(x, 2));
    prettyHooks.extension.set('Lambda', () => new PrettyForm('LAMBDA'));
    try {
      expect(pretty(e)).toBe('LAMBDA');
    } finally {
      prettyHooks.extension.delete('Lambda');
    }
    expect(pretty(e, { useUnicode: false })).toBe('      2\nx -> x ');
  });
  it('a matrix printer', () => {
    const m = sj.Matrix.of([[1, 2]]);
    prettyHooks.matrix = (mm, p) => p.printMatrixContents(mm);
    try {
      expect(pretty(m)).toBe('1  2');
    } finally {
      prettyHooks.matrix = undefined;
    }
    expect(pretty(m)).toBe('[1  2]');
  });
});

/**
 * Coverage of the 2D pretty printer: every expected string was
 * produced by `sympy.pretty(expr, use_unicode=False|True)` with SymPy 1.14.
 */

describe('pretty: SymPy 1.14 output', () => {
  for (const [src, build, ascii, unicode] of CASES) {
    it(src, () => {
      const e = build();
      expect(pretty(e, { useUnicode: false })).toBe(ascii);
      expect(pretty(e, { useUnicode: true })).toBe(unicode);
    });
  }
});

describe('pretty: values it cannot print', () => {
  it('a value that is not printable throws a TypeError', () => {
    expect(() => pretty({} as unknown as Printable)).toThrow(TypeError);
  });
  it('an expression or set class the printer does not know prints as its str form', () => {
    // an Expr subclass outside the library's node classes
    class MyExpr extends sj.Expr {
      readonly kind = 'Extension' as const;
      readonly args: readonly sj.Expr[] = [];
      protected computeKey(): string {
        return 'MyExpr()';
      }
    }
    class MySet extends SetExpr {
      readonly args: readonly sj.Expr[] = [];
      get className(): string {
        return 'MySet';
      }
      protected computeKey(): string {
        return 'MySet()';
      }
    }
    expect(pretty(new MyExpr(), { useUnicode: false })).toBe('MyExpr()');
    expect(pretty(new MySet(), { useUnicode: false })).toBe('MySet()');
  });
});

/**
 * Coverage of printing/sets.ts, sortkey.ts, str.ts and the pretty printer
 * (pretty.ts, stringpict.ts, symbology.ts). Expected strings from SymPy 1.14
 * (str, pretty with and without unicode, latex, default_sort_key).
 */

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

describe('pretty of sequences, Range, products of sets, regions and special functions (SymPy 1.14 pretty())', () => {
  const v = { a: sj.symbol('a'), b: sj.symbol('b'), n: sj.symbol('n'), x: sj.symbol('x'), y: sj.symbol('y'), z: sj.symbol('z') };
  /** [SymPy source, builder, ASCII output, unicode output]. */
  const cases: [string, () => Printable, string, string][] = [
    ["SingularityFunction(x, a, n)", () => sj.SingularityFunction(v.x, v.a, v.n), "        n\n<-a + x> ", "        n\n<-a + x> "],
    ["SingularityFunction(x, 4, 5) + SingularityFunction(x, -3, 4)", () => sj.add(sj.SingularityFunction(v.x, 4, 5), sj.SingularityFunction(v.x, -3, 4)), "       4          5\n<x + 3>  + <x - 4> ", "       4          5\n<x + 3>  + <x - 4> "],
    ["SingularityFunction(x, a, n)**3", () => sj.pow(sj.SingularityFunction(v.x, v.a, v.n), 3), "           3\n/        n\\ \n\\<-a + x> / ", "           3\n⎛        n⎞ \n⎝<-a + x> ⎠ "],
    ["SingularityFunction(x, 0, -1)", () => sj.SingularityFunction(v.x, 0, -1), "   -1\n<x>  ", "   -1\n<x>  "],
    ["SingularityFunction(x, a, 2)*x", () => sj.mul(sj.SingularityFunction(v.x, v.a, 2), v.x), "          2\nx*<-a + x> ", "          2\nx⋅<-a + x> "],
    ["Range(1, 10)", () => Range.of(1, 10), "{1, 2, ..., 9}", "{1, 2, …, 9}"],
    ["Range(1, 10, 2)", () => Range.of(1, 10, 2), "{1, 3, ..., 9}", "{1, 3, …, 9}"],
    ["Range(0, oo, 2)", () => Range.of(0, S.Infinity, 2), "{0, 2, ...}", "{0, 2, …}"],
    ["Range(-oo, 0)", () => Range.of(S.NegativeInfinity, 0), "{..., -2, -1}", "{…, -2, -1}"],
    ["Range(-oo, oo)", () => Range.of(S.NegativeInfinity, S.Infinity), "{..., -1, 0, 1, ...}", "{…, -1, 0, 1, …}"],
    ["Range(10, 1, -1)", () => Range.of(10, 1, -1), "{10, 9, ..., 2}", "{10, 9, …, 2}"],
    ["Range(5, 6)", () => Range.of(5, 6), "{5}", "{5}"],
    ["Range(0, 0)", () => Range.of(0, 0), "{}", "{}"],
    ["Range(0, -10, -3)", () => Range.of(0, -10, -3), "{0, -3, -6, -9}", "{0, -3, -6, -9}"],
    ["SeqFormula(n**2, (n, 0, oo))", () => sj.SeqFormula(sj.pow(v.n, 2), [v.n, 0, S.Infinity]), "[0, 1, 4, 9, ...]", "[0, 1, 4, 9, …]"],
    ["SeqFormula(n**2, (n, 0, 5))", () => sj.SeqFormula(sj.pow(v.n, 2), [v.n, 0, 5]), "[0, 1, 4, 9, ...]", "[0, 1, 4, 9, …]"],
    ["SeqFormula(n**2, (n, 0, 3))", () => sj.SeqFormula(sj.pow(v.n, 2), [v.n, 0, 3]), "[0, 1, 4, 9]", "[0, 1, 4, 9]"],
    ["SeqFormula(n**2, (n, -oo, 0))", () => sj.SeqFormula(sj.pow(v.n, 2), [v.n, S.NegativeInfinity, 0]), "[..., 9, 4, 1, 0]", "[…, 9, 4, 1, 0]"],
    ["SeqPer((1, 2, 3), (n, 0, oo))", () => sj.SeqPer([1, 2, 3], [v.n, 0, S.Infinity]), "[1, 2, 3, 1, ...]", "[1, 2, 3, 1, …]"],
    ["SeqPer((1, 2), (n, 0, 3))", () => sj.SeqPer([1, 2], [v.n, 0, 3]), "[1, 2, 1, 2]", "[1, 2, 1, 2]"],
    ["SeqAdd(SeqFormula(n**2, (n, 0, oo)), SeqPer((1, 2), (n, 0, oo)))", () => sj.SeqAdd(sj.SeqFormula(sj.pow(v.n, 2), [v.n, 0, S.Infinity]), sj.SeqPer([1, 2], [v.n, 0, S.Infinity])), "[1, 3, 5, 11, ...]", "[1, 3, 5, 11, …]"],
    ["SeqMul(SeqFormula(n**2, (n, 0, oo)), SeqPer((1, 2), (n, 0, oo)))", () => sj.SeqMul(sj.SeqFormula(sj.pow(v.n, 2), [v.n, 0, S.Infinity]), sj.SeqPer([1, 2], [v.n, 0, S.Infinity])), "[0, 2, 4, 18, ...]", "[0, 2, 4, 18, …]"],
    ["S.EmptySequence", () => sj.EmptySequence, "EmptySequence", "EmptySequence"],
    ["polylog(x, y)", () => sj.polylog(v.x, v.y), "polylog(x, y)", "Liₓ(y)"],
    ["polylog(2, x)**3", () => sj.pow(sj.polylog(2, v.x), 3), "       3      \npolylog (2, x)", "   3   \nLi₂ (x)"],
    ["lerchphi(x, y, n)", () => sj.lerchphi(v.x, v.y, v.n), "lerchphi(x, y, n)", "Φ(x, y, n)"],
    ["lerchphi(x, y, n)**2", () => sj.pow(sj.lerchphi(v.x, v.y, v.n), 2), "        2         \nlerchphi (x, y, n)", " 2         \nΦ (x, y, n)"],
    ["elliptic_k(x)**2", () => sj.pow(sj.ellipticK(v.x), 2), "    2\nK(x) ", "    2\nK(x) "],
    ["elliptic_f(x, y)", () => sj.ellipticF(v.x, v.y), "F(x|y)", "F(x│y)"],
    ["elliptic_e(x)", () => sj.ellipticE(v.x), "E(x)", "E(x)"],
    ["elliptic_e(x, y)", () => sj.ellipticE(v.x, v.y), "E(x|y)", "E(x│y)"],
    ["elliptic_e(x)**2", () => sj.pow(sj.ellipticE(v.x), 2), "    2\nE(x) ", "    2\nE(x) "],
    ["elliptic_pi(x, y)", () => sj.ellipticPi(v.x, v.y), "Pi(x|y)", "Π(x│y)"],
    ["elliptic_pi(x, y, z)**2", () => sj.pow(sj.ellipticPi(v.x, v.y, v.z), 2), "          2\nPi(x; y|z) ", "         2\nΠ(x; y│z) "],
    ["betainc(a, b, x, y)", () => sj.betainc(v.a, v.b, v.x, v.y), "B'(a, b, x, y)", "B'(a, b, x, y)"],
    ["betainc_regularized(a, b, x, y)**2", () => sj.pow(sj.betaincRegularized(v.a, v.b, v.x, v.y), 2), " 2            \nI (a, b, x, y)", " 2            \nI (a, b, x, y)"],
    ["dirichlet_eta(x)**2", () => sj.pow(sj.dirichletEta(v.x), 2), "             2   \ndirichlet_eta (x)", " 2   \nη (x)"],
    ["stieltjes(n)", () => sj.stieltjes(v.n), "stieltjes \n         n", "γ \n n"],
    ["stieltjes(n)**2", () => sj.pow(sj.stieltjes(v.n), 2), "          2\nstieltjes  \n         n ", "  2\nγ  \n n "],
    ["stieltjes(n, x)**2", () => sj.pow(sj.stieltjes(v.n, v.x), 2), "          2   \nstieltjes  (x)\n         n    ", "  2   \nγ  (x)\n n    "],
    ["meijerg(((a,), ()), ((), (b,)), z)", () => sj.meijerg([v.a], [], [], [v.b], v.z), " __0, 1 /a    |  \\\n/__     |     | z|\n\\_|1, 1 \\   b |  /", "╭─╮0, 1 ⎛a    │  ⎞\n│╶┐     ⎜     │ z⎟\n╰─╯1, 1 ⎝   b │  ⎠"],
    ["meijerg(((a,), ()), ((), (b,)), z)**2", () => sj.pow(sj.meijerg([v.a], [], [], [v.b], v.z), 2), "                  2\n __0, 1 /a    |  \\ \n/__     |     | z| \n\\_|1, 1 \\   b |  / ", "                  2\n╭─╮0, 1 ⎛a    │  ⎞ \n│╶┐     ⎜     │ z⎟ \n╰─╯1, 1 ⎝   b │  ⎠ "],
    ["hyper((a, b), (x,), z)", () => sj.hyper([v.a, v.b], [v.x], v.z), "  _            \n |_  /a, b |  \\\n |   |     | z|\n2  1 \\ x   |  /", " ┌─  ⎛a, b │  ⎞\n ├─  ⎜     │ z⎟\n2╵ 1 ⎝ x   │  ⎠"],
    ["hyper((a, b), (x,), z)**2", () => sj.pow(sj.hyper([v.a, v.b], [v.x], v.z), 2), "               2\n  _             \n |_  /a, b |  \\ \n |   |     | z| \n2  1 \\ x   |  / ", "               2\n ┌─  ⎛a, b │  ⎞ \n ├─  ⎜     │ z⎟ \n2╵ 1 ⎝ x   │  ⎠ "],
    ["Heaviside(x, 0)", () => sj.Heaviside(v.x, 0), "Heaviside(x, 0)", "θ(x, 0)"],
    ["Heaviside(x, S.Half)", () => sj.Heaviside(v.x, S.Half), "Heaviside(x)", "θ(x)"],
    ["Heaviside(x)**2", () => sj.pow(sj.Heaviside(v.x), 2), "            2\nHeaviside(x) ", "    2\nθ(x) "],
    ["DiracDelta(x)**2", () => sj.pow(sj.DiracDelta(v.x), 2), "          2   \nDiracDelta (x)", "    2\nδ(x) "],
    ["DiracDelta(x, 2)**2", () => sj.pow(sj.DiracDelta(v.x, 2), 2), "          2      \nDiracDelta (x, 2)", "        2\n (2)     \nδ    (x) "],
    ["ProductSet(Interval(0, 1), FiniteSet(1, 2))", () => sj.ProductSet(Interval.of(0, 1), FiniteSet.of(1, 2)), "[0, 1] x {1, 2}", "[0, 1] × {1, 2}"],
    ["ProductSet(Interval(0, 1), Interval(0, 1), Interval(0, 1))", () => sj.ProductSet(Interval.of(0, 1), Interval.of(0, 1), Interval.of(0, 1)), "      3\n[0, 1] ", "      3\n[0, 1] "],
    ["ProductSet(Union(Interval(0, 1), Interval(2, 3)), FiniteSet(1))", () => sj.ProductSet(sj.union(Interval.of(0, 1), Interval.of(2, 3)), FiniteSet.of(1)), "([0, 1] U [2, 3]) x {1}", "([0, 1] ∪ [2, 3]) × {1}"],
    ["ComplexRegion(Interval(0, 1)*Interval(0, 2))", () => sj.ComplexRegion(sj.ProductSet(Interval.of(0, 1), Interval.of(0, 2))), "{x + y*I | x, y in [0, 1] x [0, 2]}", "{x + y⋅ⅈ │ x, y ∊ [0, 1] × [0, 2]}"],
    ["ComplexRegion(Interval(0, 1)*Interval(0, 2*pi), polar=True)", () => sj.ComplexRegion(sj.ProductSet(Interval.of(0, 1), Interval.of(0, sj.mul(2, S.Pi))), true), "{r*(I*sin(theta) + cos(theta)) | r, theta in [0, 1] x [0, 2*pi)}", "{r⋅(ⅈ⋅sin(θ) + cos(θ)) │ r, θ ∊ [0, 1] × [0, 2⋅π)}"],
    ["Contains(x, Interval(0, 1))", () => new Contains(v.x, Interval.of(0, 1)), "Contains(x, Interval(0, 1))", "x ∈ [0, 1]"],
    ["Permutation([1, 0, 2])", () => new sj.Permutation([1, 0, 2]), "(0 1)", "(0 1)"],
  ];
  it.each(cases)('%s', (_src, build, ascii, unicode) => {
    expect(pretty(build(), { useUnicode: false })).toBe(ascii);
    expect(pretty(build(), { useUnicode: true })).toBe(unicode);
  });
  it('a sequence with a symbolic bound prints as its str form', () => {
    // SymPy raises NotImplementedError("Pretty printing of sequences with symbolic bound not implemented")
    expect(pretty(sj.SeqFormula(sj.pow(v.n, 2), [v.n, v.a, S.Infinity]))).toBe('SeqFormula(n**2, (n, a, oo))');
  });
  it('meijerg with parameter counts of different widths', () => {
    // SymPy pretty(meijerg([list(range(1, 11)), []], [[], [0]], z))
    const g = sj.meijerg([1, 2, 3, 4, 5, 6, 7, 8, 9, 10], [], [], [0], v.z);
    expect(pretty(g, { useUnicode: false })).toBe(" __ 0, 10 /1, 2, 3, 4, 5, 6, 7, 8, 9, 10    |  \\\n/__       |                                 | z|\n\\_|10,  1 \\                               0 |  /");
    expect(pretty(g, { useUnicode: true })).toBe("╭─╮ 0, 10 ⎛1, 2, 3, 4, 5, 6, 7, 8, 9, 10    │  ⎞\n│╶┐       ⎜                                 │ z⎟\n╰─╯10,  1 ⎝                               0 │  ⎠");
  });
  it('a Range over all the integers downwards', () => {
    // SymPy pretty(Range(oo, -oo, -1))
    expect(pretty(Range.of(S.Infinity, S.NegativeInfinity, -1), { useUnicode: true })).toBe('{…, 1, 0, -1, …}');
  });
  it('the identity permutation', () => {
    // SymPy pretty(Permutation(3)) and pretty(Permutation([]))
    expect(pretty(new sj.Permutation(3))).toBe('()');
    expect(pretty(new sj.Permutation([[0, 1], [2, 3]]))).toBe('(0 1)(2 3)');
  });
});

describe('pretty of a SymPy Dict', () => {
  it('prints like a dict (SymPy _print_Dict)', () => {
    const x = sj.symbol('x');
    expect(sj.pretty(sj.Dict([[x, 1], [2, sj.Rational.of(1n, 2n)]]), { useUnicode: false })).toBe('{2: 1/2, x: 1}');
  });
});

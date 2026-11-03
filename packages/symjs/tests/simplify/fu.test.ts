// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/simplify/fu.ts.

// Expected values are the str() forms printed by SymPy 1.14 (the calls of
// sympy/simplify/tests/test_fu.py, recorded with their results).

import { describe, expect, it } from 'vitest';
import { Dummy, countOps, fn, parse, pi, sstr, symbol, xreplace } from '../../src';
import type { Expr } from '../../src';
import * as FU from '../../src/simplify/fu';

type Assume = NonNullable<Parameters<typeof symbol>[1]>;
type Kw = { half?: boolean; two?: boolean; max?: number; pow?: boolean; base?: string };
type Row = [string, string[], Kw, Record<string, Assume>, string];

const show = (x: unknown): string => {
  if (x === undefined) return 'None';
  if (typeof x === 'boolean') return x ? 'True' : 'False';
  if (typeof x === 'number') return String(x);
  if (Array.isArray(x)) return `(${x.map(show).join(', ')})`;
  return sstr(x as Expr);
};

function run(fn: string, args: Expr[], kw: Kw): unknown {
  const [a, b] = args as [Expr, Expr | undefined];
  switch (fn) {
    case 'trig_split':
      return FU.trigSplit(a, b as Expr, kw.two ?? false);
    case 'as_f_sign_1':
      return FU.asFSign1(a);
    case 'TR2i':
      return FU.TR2i(a, kw.half ?? false);
    case 'TR11':
      return FU.TR11(a, b ?? (kw.base === undefined ? undefined : parse(kw.base)));
    case 'TR5':
      return FU.TR5(a, kw);
    case 'sincos_to_sum':
      return FU.sincosToSum(a);
    case '_TR11':
      return FU.TR11Half(a);
    default:
      return (FU as unknown as Record<string, (e: Expr) => unknown>)[fn]?.(a);
  }
}

// [function, arguments, options, symbols with assumptions, SymPy result]
const ROWS: Row[] = [
  ["L", ["sin(x) + cos(x)"], {}, {}, "2"],
  ["TR1", ["2*csc(x) + sec(x)"], {}, {}, "1/cos(x) + 2/sin(x)"],
  ["TR10", ["cos(a + b)"], {}, {}, "-sin(a)*sin(b) + cos(a)*cos(b)"],
  ["TR10", ["sin(a + b)"], {}, {}, "sin(a)*cos(b) + sin(b)*cos(a)"],
  ["TR10", ["sin(a + b + c)"], {}, {}, "(-sin(a)*sin(b) + cos(a)*cos(b))*sin(c) + (sin(a)*cos(b) + sin(b)*cos(a))*cos(c)"],
  ["TR10", ["cos(a + b + c)"], {}, {}, "(-sin(a)*sin(b) + cos(a)*cos(b))*cos(c) - (sin(a)*cos(b) + sin(b)*cos(a))*sin(c)"],
  ["TR10i", ["cos(1)*cos(3) + sin(1)*sin(3)"], {}, {}, "cos(2)"],
  ["TR10i", ["cos(1)*cos(3) - sin(1)*sin(3)"], {}, {}, "cos(4)"],
  ["TR10i", ["sin(3)*cos(1) - sin(1)*cos(3)"], {}, {}, "sin(2)"],
  ["TR10i", ["sin(1)*cos(3) + sin(3)*cos(1)"], {}, {}, "sin(4)"],
  ["TR10i", ["sin(1)*cos(3) + sin(3)*cos(1) + 7"], {}, {}, "sin(4) + 7"],
  ["TR10i", ["cos(3) + sin(1)*cos(3) + sin(3)*cos(1)"], {}, {}, "cos(3) + sin(4)"],
  ["TR10i", ["2*sin(1)*cos(3) + cos(3) + 2*sin(3)*cos(1)"], {}, {}, "2*sin(4) + cos(3)"],
  ["TR10i", ["(sin(1)*cos(2) + sin(2)*cos(1))*sin(2) + cos(2)*cos(3)"], {}, {}, "cos(1)"],
  ["TR10i", ["sin(1)*sin(5) + ((sin(1)*cos(2) + sin(2)*cos(1))*sin(2) + cos(2)*cos(3))*cos(5)"], {}, {}, "cos(4)"],
  ["TR10i", ["sin(1)*sin(5) + sin(1)*sin(2)*cos(2)*cos(5) + cos(2)*cos(3)*cos(5) + sin(2)**2*cos(1)*cos(5)"], {}, {}, "cos(4)"],
  ["TR10i", ["sqrt(6)*x*sin(x) + sqrt(2)*x*cos(x)"], {}, {}, "2*sqrt(2)*x*sin(x + pi/6)"],
  ["TR10i", ["2*sqrt(2)*sin(x)/3 + 2*sqrt(6)*cos(x)/9"], {}, {}, "4*sqrt(6)*sin(x + pi/6)/9"],
  ["TR10i", ["sqrt(2)*sin(x)/2 + sqrt(2)*sin(y)/6 + sqrt(6)*cos(x)/6 + sqrt(6)*cos(y)/18"], {}, {}, "sqrt(6)*sin(x + pi/6)/3 + sqrt(6)*sin(y + pi/6)/9"],
  ["TR10i", ["sqrt(3)*sin(x) + cos(x) + 2*sqrt(3)*cos(x + pi/6)"], {}, {}, "4*cos(x)"],
  ["TR10i", ["sqrt(3)*sin(x) + 4*sin(x) + cos(x) + 2*sqrt(3)*cos(x + pi/6)"], {}, {}, "4*sqrt(2)*sin(x + pi/4)"],
  ["TR10i", ["sin(2)*cos(4) + sin(3)*cos(2)"], {}, {}, "sin(2)*cos(4) + sin(3)*cos(2)"],
  ["TR10i", ["sqrt(6)*sin(x)*A + sqrt(2)*cos(x)*A"], {}, { A: { commutative: false } }, "2*sqrt(2)*sin(x + pi/6)*A"],
  ["TR10i", ["sin(x)*sin(y) + cos(x)*cos(y)"], {}, {}, "cos(x - y)"],
  ["TR10i", ["sin(x)*cos(y) + sin(y)*cos(x)"], {}, {}, "sin(x + y)"],
  ["TR10i", ["-sin(x)*sin(y) + cos(x)*cos(y)"], {}, {}, "cos(x + y)"],
  ["TR10i", ["-sin(x)*cos(y) + sin(y)*cos(x)"], {}, {}, "-sin(x - y)"],
  ["TR10i", ["sin(x)*sin(y) - cos(x)*cos(y)"], {}, {}, "-cos(x + y)"],
  ["TR10i", ["sin(x)*cos(y) - sin(y)*cos(x)"], {}, {}, "sin(x - y)"],
  ["TR10i", ["-sin(x)*sin(y) - cos(x)*cos(y)"], {}, {}, "-cos(x - y)"],
  ["TR10i", ["-sin(x)*cos(y) - sin(y)*cos(x)"], {}, {}, "-sin(x + y)"],
  ["TR10i", ["sin(x)/2 + sqrt(3)*cos(x)/2"], {}, {}, "sin(x + pi/3)"],
  ["TR10i", ["sqrt(3)*sin(x)/2 + cos(x)/2"], {}, {}, "sin(x + pi/6)"],
  ["TR10i", ["-sin(x)/2 + sqrt(3)*cos(x)/2"], {}, {}, "cos(x + pi/6)"],
  ["TR10i", ["-sqrt(3)*sin(x)/2 + cos(x)/2"], {}, {}, "cos(x + pi/3)"],
  ["TR10i", ["sin(x)/2 - sqrt(3)*cos(x)/2"], {}, {}, "-cos(x + pi/6)"],
  ["TR10i", ["sqrt(3)*sin(x)/2 - cos(x)/2"], {}, {}, "-cos(x + pi/3)"],
  ["TR10i", ["-sin(x)/2 - sqrt(3)*cos(x)/2"], {}, {}, "-sin(x + pi/3)"],
  ["TR10i", ["-sqrt(3)*sin(x)/2 - cos(x)/2"], {}, {}, "-sin(x + pi/6)"],
  ["TR11", ["sin(2*x)"], {}, {}, "2*sin(x)*cos(x)"],
  ["TR11", ["sin(4*x)"], {}, {}, "4*(-sin(x)**2 + cos(x)**2)*sin(x)*cos(x)"],
  ["TR11", ["sin(4*x/3)"], {}, {}, "4*(-sin(x/3)**2 + cos(x/3)**2)*sin(x/3)*cos(x/3)"],
  ["TR11", ["cos(2*x)"], {}, {}, "-sin(x)**2 + cos(x)**2"],
  ["TR11", ["cos(4*x)"], {}, {}, "(-sin(x)**2 + cos(x)**2)**2 - 4*sin(x)**2*cos(x)**2"],
  ["TR11", ["cos(2)"], {}, {}, "cos(2)"],
  ["TR11", ["cos(3*pi/7)", "2*pi/7"], {}, {}, "-cos(2*pi/7)**2 + sin(2*pi/7)**2"],
  ["TR11", ["cos(4)", "2"], {}, {}, "-sin(2)**2 + cos(2)**2"],
  ["TR11", ["cos(6)", "2"], {}, {}, "cos(6)"],
  ["TR11", ["sin(x)/cos(x/2)", "x/2"], {}, {}, "2*sin(x/2)"],
  ["TR12", ["tan(x + y)"], {}, {}, "(tan(x) + tan(y))/(-tan(x)*tan(y) + 1)"],
  ["TR12", ["tan(x + y + z)"], {}, {}, "(tan(z) + (tan(x) + tan(y))/(-tan(x)*tan(y) + 1))/(1 - (tan(x) + tan(y))*tan(z)/(-tan(x)*tan(y) + 1))"],
  ["TR12", ["tan(x*y)"], {}, {}, "tan(x*y)"],
  ["TR12i", ["(tan(a) + tan(b))/(-tan(a)*tan(b) + 1)"], {}, {}, "tan(a + b)"],
  ["TR12i", ["(tan(a) + tan(b))/(tan(a)*tan(b) - 1)"], {}, {}, "-tan(a + b)"],
  ["TR12i", ["(-tan(a) - tan(b))/(tan(a)*tan(b) - 1)"], {}, {}, "tan(a + b)"],
  // SymPy: -3*tan(a + b)*tan(a + c)/(2*(tan(a) + tan(b) - 1)), which is wrong (TR12i puts the rest of
  // the denominator back as tan(a) + tan(b) - 1 instead of tan(a)*tan(b) - 1; a, b, c = 0.3, 0.7, 0.2
  // differ by 10.1); the value here equals the input
  ["TR12i", ["-3*tan(a)**2/(2*tan(a)**3*tan(b)**2*tan(c) - 2*tan(a)**2*tan(b)**2 - 4*tan(a)**2*tan(b)*tan(c) + 4*tan(a)*tan(b) + 2*tan(a)*tan(c) - 2) - 3*tan(a)*tan(b)/(2*tan(a)**3*tan(b)**2*tan(c) - 2*tan(a)**2*tan(b)**2 - 4*tan(a)**2*tan(b)*tan(c) + 4*tan(a)*tan(b) + 2*tan(a)*tan(c) - 2) - 3*tan(a)*tan(c)/(2*tan(a)**3*tan(b)**2*tan(c) - 2*tan(a)**2*tan(b)**2 - 4*tan(a)**2*tan(b)*tan(c) + 4*tan(a)*tan(b) + 2*tan(a)*tan(c) - 2) - 3*tan(b)*tan(c)/(2*tan(a)**3*tan(b)**2*tan(c) - 2*tan(a)**2*tan(b)**2 - 4*tan(a)**2*tan(b)*tan(c) + 4*tan(a)*tan(b) + 2*tan(a)*tan(c) - 2)"], {}, {}, "-3*tan(a + b)*tan(a + c)/(2*(tan(a)*tan(b) - 1))"],
  ["TR12i", ["tan(x)/sin(x)"], {}, {}, "tan(x)/sin(x)"],
  ["TR12i", ["(tan(a) + cos(2))/(-tan(a)*tan(b) + 1)"], {}, {}, "(tan(a) + cos(2))/(-tan(a)*tan(b) + 1)"],
  ["TR12i", ["(tan(a) + tan(b) + 2)**2/(-tan(a)*tan(b) + 1)"], {}, {}, "(tan(a) + tan(b) + 2)**2/(-tan(a)*tan(b) + 1)"],
  ["TR12i", ["tan(a)/(-tan(a)*tan(b) + 1)"], {}, {}, "tan(a)/(-tan(a)*tan(b) + 1)"],
  // SymPy: -(a + 1)**2*tan(a + b), which drops a factor tan(a) + tan(b) (TR12i takes one power of
  // tan(a) + tan(b) out of the square); the value here equals the input
  ["TR12i", ["(a*tan(a) + a*tan(b) + tan(a) + tan(b))**2/(tan(a)*tan(b) - 1)"], {}, {}, "-(a + 1)**2*(tan(a) + tan(b))*tan(a + b)"],
  ["TR13", ["tan(2)*tan(3)"], {}, {}, "-tan(2)/tan(5) - tan(3)/tan(5) + 1"],
  ["TR13", ["cot(2)*cot(3)"], {}, {}, "cot(2)*cot(5) + 1 + cot(3)*cot(5)"],
  ["TR13", ["tan(1)*tan(2)*tan(3)"], {}, {}, "(-tan(2)/tan(5) - tan(3)/tan(5) + 1)*tan(1)"],
  ["TR13", ["tan(1)*tan(2)*cot(3)"], {}, {}, "(-tan(2)/tan(3) + 1 - tan(1)/tan(3))*cot(3)"],
  ["TR14", ["(cos(x) - 1)*(cos(x) + 1)"], {}, {}, "-sin(x)**2"],
  ["TR14", ["1/((cos(x) - 1)*(cos(x) + 1))"], {}, {}, "-1/sin(x)**2"],
  ["TR14", ["(cos(x) - 1)**2*(cos(x) + 1)**2"], {}, {}, "sin(x)**4"],
  ["TR14", ["(cos(x) - 1)**2*(cos(x) + 1)**3"], {}, {}, "(cos(x) + 1)*sin(x)**4"],
  ["TR14", ["(cos(x) - 1)**3*(cos(x) + 1)**2"], {}, {}, "(cos(x) - 1)*sin(x)**4"],
  ["TR14", ["(cos(x) - 1)**y*(cos(x) + 1)**y"], {}, {}, "(cos(x) - 1)**y*(cos(x) + 1)**y"],
  ["TR14", ["(cos(x) - 2)**y*(cos(x) + 1)"], {}, {}, "(cos(x) - 2)**y*(cos(x) + 1)"],
  ["TR14", ["(cos(x) + 1)*(tan(x) - 2)**2"], {}, {}, "(cos(x) + 1)*(tan(x) - 2)**2"],
  ["TR14", ["(cos(x) - 1)**i*(cos(x) + 1)**i"], {}, { i: { integer: true } }, "(-sin(x)**2)**i"],
  ["TR14", ["(sin(x) - 1)**i*(sin(x) + 1)**i"], {}, { i: { integer: true } }, "(-cos(x)**2)**i"],
  ["TR14", ["(cos(x) - 1)**(i + 1)*(cos(x) + 1)**i"], {}, { i: { integer: true } }, "(cos(x) - 1)**(i + 1)*(cos(x) + 1)**i"],
  ["TR14", ["(sin(x) - 1)*(sin(x) + 1)"], {}, {}, "-cos(x)**2"],
  ["TR14", ["(x - 1)*(cos(x) - 1)*(cos(x) + 1)*(cos(y) + 1)*(2*cos(y) - 2)*(3*cos(y) - 3)*(3*cos(y) + 3)"], {}, {}, "-18*(x - 1)*sin(x)**2*sin(y)**4"],
  ["TR15", ["1 - 1/sin(x)**2"], {}, {}, "-cot(x)**2"],
  ["TR16", ["1 - 1/cos(x)**2"], {}, {}, "-tan(x)**2"],
  ["TR111", ["1 - 1/tan(x)**2"], {}, {}, "1 - cot(x)**2"],
  ["TR2", ["tan(x)"], {}, {}, "sin(x)/cos(x)"],
  ["TR2", ["cot(x)"], {}, {}, "cos(x)/sin(x)"],
  ["TR2", ["-tan(sin(x)/cos(x) - tan(x))"], {}, {}, "0"],
  ["TR2i", ["sin(x)/cos(x)"], {}, {}, "tan(x)"],
  ["TR2i", ["sin(x)*sin(y)/cos(x)"], {}, {}, "sin(y)*tan(x)"],
  ["TR2i", ["cos(x)/sin(x)"], {}, {}, "1/tan(x)"],
  ["TR2i", ["cos(x)/(sin(x)*sin(y))"], {}, {}, "1/(sin(y)*tan(x))"],
  // (SymPy's test builds the unevaluated 2*(cos(x) + 1); parsed, it is 2*cos(x) + 2 in SymPy too)
  ["TR2i", ["sin(x)/(2*cos(x) + 2)"], {}, {}, "sin(x)/(2*cos(x) + 2)"],
  ["TR2i", ["sin(x)/(2*(cos(x) + 1))"], { half: true }, {}, "tan(x/2)/2"],
  ["TR2i", ["sin(1)/(cos(1) + 1)"], { half: true }, {}, "tan(1/2)"],
  ["TR2i", ["sin(2)/(cos(2) + 1)"], { half: true }, {}, "tan(1)"],
  ["TR2i", ["sin(4)/(cos(4) + 1)"], { half: true }, {}, "tan(2)"],
  ["TR2i", ["sin(5)/(cos(5) + 1)"], { half: true }, {}, "tan(5/2)"],
  ["TR2i", ["(cos(1) + 1)/sin(1)"], { half: true }, {}, "1/tan(1/2)"],
  ["TR2i", ["(cos(2) + 1)/sin(2)"], { half: true }, {}, "1/tan(1)"],
  ["TR2i", ["(cos(4) + 1)/sin(4)"], { half: true }, {}, "1/tan(2)"],
  ["TR2i", ["(cos(5) + 1)/sin(5)"], { half: true }, {}, "1/tan(5/2)"],
  ["TR2i", ["sin(1)**a/(cos(1) + 1)**a"], { half: true }, {}, "tan(1/2)**a"],
  ["TR2i", ["sin(2)**a/(cos(2) + 1)**a"], { half: true }, {}, "tan(1)**a"],
  ["TR2i", ["sin(4)**a/(cos(4) + 1)**a"], { half: true }, {}, "sin(4)**a/(cos(4) + 1)**a"],
  ["TR2i", ["sin(5)**a/(cos(5) + 1)**a"], { half: true }, {}, "sin(5)**a/(cos(5) + 1)**a"],
  ["TR2i", ["(cos(1) + 1)**a/sin(1)**a"], { half: true }, {}, "tan(1/2)**(-a)"],
  ["TR2i", ["(cos(2) + 1)**a/sin(2)**a"], { half: true }, {}, "tan(1)**(-a)"],
  ["TR2i", ["(cos(4) + 1)**a/sin(4)**a"], { half: true }, {}, "(cos(4) + 1)**a/sin(4)**a"],
  ["TR2i", ["(cos(5) + 1)**a/sin(5)**a"], { half: true }, {}, "(cos(5) + 1)**a/sin(5)**a"],
  ["TR2i", ["(cos(5) + 1)**i/sin(5)**i"], { half: true }, { i: { integer: true } }, "tan(5/2)**(-i)"],
  ["TR2i", ["sin(5)**i/(cos(5) + 1)**i"], { half: true }, { i: { integer: true } }, "tan(5/2)**i"],
  ["TR3", ["cos(x*(-x + y) - y)"], {}, {}, "cos(x*(x - y) + y)"],
  ["TR3", ["cos(3*pi/7)"], {}, {}, "sin(pi/14)"],
  ["TR3", ["sin(3*pi/7)"], {}, {}, "cos(pi/14)"],
  ["TR3", ["tan(3*pi/7)"], {}, {}, "cot(pi/14)"],
  ["TR3", ["cot(3*pi/7)"], {}, {}, "tan(pi/14)"],
  ["TR3", ["csc(3*pi/7)"], {}, {}, "sec(pi/14)"],
  ["TR3", ["sec(3*pi/7)"], {}, {}, "csc(pi/14)"],
  ["TR3", ["cos((9*pi)/22)"], {}, {}, "sin(pi/11)"],
  ["TR4", ["cos(0)"], {}, {}, "1"],
  ["TR4", ["cos(pi/6)"], {}, {}, "sqrt(3)/2"],
  ["TR4", ["cos(pi/4)"], {}, {}, "sqrt(2)/2"],
  ["TR4", ["cos(pi/3)"], {}, {}, "1/2"],
  ["TR4", ["cos(pi/2)"], {}, {}, "0"],
  ["TR5", ["sin(x)**2"], {}, {}, "1 - cos(x)**2"],
  ["TR5", ["sin(x)**(-2)"], {}, {}, "sin(x)**(-2)"],
  ["TR5", ["sin(x)**4"], {}, {}, "(1 - cos(x)**2)**2"],
  ["TR6", ["cos(x)**2"], {}, {}, "1 - sin(x)**2"],
  ["TR6", ["cos(x)**(-2)"], {}, {}, "cos(x)**(-2)"],
  ["TR6", ["cos(x)**4"], {}, {}, "(1 - sin(x)**2)**2"],
  ["TR7", ["cos(x)**2"], {}, {}, "cos(2*x)/2 + 1/2"],
  ["TR7", ["cos(x)**2 + 1"], {}, {}, "cos(2*x)/2 + 3/2"],
  ["TR8", ["cos(2)*cos(3)"], {}, {}, "cos(5)/2 + cos(1)/2"],
  ["TR8", ["sin(3)*cos(2)"], {}, {}, "sin(5)/2 + sin(1)/2"],
  ["TR8", ["sin(2)*sin(3)"], {}, {}, "-cos(5)/2 + cos(1)/2"],
  ["TR8", ["sin(1)*sin(2)*sin(3)"], {}, {}, "sin(4)/4 - sin(6)/4 + sin(2)/4"],
  ["TR8", ["cos(2)*cos(3)*cos(4)*cos(5)"], {}, {}, "cos(4)/4 + cos(10)/8 + cos(2)/8 + cos(8)/8 + cos(14)/8 + cos(6)/8 + 1/8"],
  ["TR8", ["cos(2)*cos(3)*cos(4)*cos(5)*cos(6)"], {}, {}, "cos(10)/8 + cos(4)/8 + 3*cos(2)/16 + cos(16)/16 + cos(8)/8 + cos(14)/16 + cos(20)/16 + cos(12)/16 + 1/16 + cos(6)/8"],
  ["TR8", ["sin(3*pi/7)**2*cos(3*pi/7)**2/(16*sin(pi/7)**2)"], {}, {}, "1/64"],
  ["TR9", ["1/2"], {}, {}, "1/2"],
  ["TR9", ["cos(2) + cos(1)"], {}, {}, "2*cos(1/2)*cos(3/2)"],
  ["TR9", ["-cos(2) + cos(1)"], {}, {}, "2*sin(1/2)*sin(3/2)"],
  ["TR9", ["-sin(2) + sin(1)"], {}, {}, "-2*sin(1/2)*cos(3/2)"],
  ["TR9", ["sin(1) + sin(2)"], {}, {}, "2*sin(3/2)*cos(1/2)"],
  ["TR9", ["cos(1) + 2*sin(1) + 2*sin(2)"], {}, {}, "cos(1) + 4*sin(3/2)*cos(1/2)"],
  ["TR9", ["2*cos(1)*cos(3) + cos(4) + cos(2)"], {}, {}, "4*cos(1)*cos(3)"],
  ["TR9", ["cos(3) + (cos(4) + cos(2))/(2*cos(3))"], {}, {}, "2*cos(1)*cos(2)"],
  ["TR9", ["cos(3) + cos(4) + cos(5) + cos(6)"], {}, {}, "4*cos(1/2)*cos(1)*cos(9/2)"],
  ["TR9", ["cos(3) + cos(2)*cos(3)"], {}, {}, "cos(3) + cos(2)*cos(3)"],
  ["TR9", ["-cos(y) + cos(x*y)"], {}, {}, "-2*sin(x*y/2 - y/2)*sin(x*y/2 + y/2)"],
  ["TR9", ["-sin(y) + sin(x*y)"], {}, {}, "2*sin(x*y/2 - y/2)*cos(x*y/2 + y/2)"],
  ["TR9", ["sin(x) + cos(x)"], {}, {}, "sin(x) + cos(x)"],
  ["TR9", ["cos(x) + cos(x*y)"], {}, {}, "2*cos(x*y/2 - x/2)*cos(x*y/2 + x/2)"],
  ["TR9", ["sin(x) + sin(x*y)"], {}, {}, "2*sin(x*y/2 + x/2)*cos(x*y/2 - x/2)"],
  ["TR9", ["-sin(x) + cos(x)"], {}, {}, "-sin(x) + cos(x)"],
  ["TR9", ["sin(x) - cos(x)"], {}, {}, "sin(x) - cos(x)"],
  ["TR9", ["cos(x) - cos(x*y)"], {}, {}, "2*sin(x*y/2 - x/2)*sin(x*y/2 + x/2)"],
  ["TR9", ["sin(x) - sin(x*y)"], {}, {}, "-2*sin(x*y/2 - x/2)*cos(x*y/2 + x/2)"],
  ["TR9", ["-cos(x) + cos(x*y)"], {}, {}, "-2*sin(x*y/2 - x/2)*sin(x*y/2 + x/2)"],
  ["TR9", ["-sin(x) + sin(x*y)"], {}, {}, "2*sin(x*y/2 - x/2)*cos(x*y/2 + x/2)"],
  ["TR9", ["-sin(x) - cos(x)"], {}, {}, "-sin(x) - cos(x)"],
  ["TR9", ["-cos(x) - cos(x*y)"], {}, {}, "-2*cos(x*y/2 - x/2)*cos(x*y/2 + x/2)"],
  ["TR9", ["-sin(x) - sin(x*y)"], {}, {}, "-2*sin(x*y/2 + x/2)*cos(x*y/2 - x/2)"],
  ["TRmorrie", ["7*cos(1)*cos(2)*cos(3)*cos(4)*cos(5)*cos(6)*cos(7)*cos(8)*cos(9)"], {}, {}, "7*sin(12)*sin(16)*cos(5)*cos(7)*cos(9)/(64*sin(1)*sin(3))"],
  ["TRmorrie", ["x"], {}, {}, "x"],
  ["TRmorrie", ["2*x"], {}, {}, "2*x"],
  ["TRmorrie", ["-cos(pi/7)*cos(2*pi/7)*cos(3*pi/7)"], {}, {}, "-sin(3*pi/7)*cos(3*pi/7)/(4*sin(pi/7))"],
  ["TR8", ["-sin(3*pi/7)*cos(3*pi/7)/(4*sin(pi/7))"], {}, {}, "-1/8"],
  ["TRmorrie", ["cos(pi/17)**4*cos(2*pi/17)**3*cos(4*pi/17)**3*cos(8*pi/17)**3*cos(512*pi/17)*cos(1024*pi/17)*cos(2048*pi/17)"], {}, {}, "sin(pi/17)*cos(pi/17)/(32768*sin(2*pi/17))"],
  ["TR3", ["sin(pi/17)*cos(pi/17)/(32768*sin(2*pi/17))"], {}, {}, "sin(pi/17)*cos(pi/17)/(32768*sin(2*pi/17))"],
  ["TR8", ["sin(pi/17)*cos(pi/17)/(32768*sin(2*pi/17))"], {}, {}, "1/65536"],
  ["TRmorrie", ["cos(x)/cos(x/2)"], {}, {}, "cos(x)/cos(x/2)"],
  ["TRmorrie", ["sin(x/2)*cos(x/2)*cos(x)**3"], {}, {}, "sin(2*x)*cos(x)**2/4"],
  ["TRpower", ["sin(x)**(-2)"], {}, {}, "sin(x)**(-2)"],
  ["TRpower", ["sin(x/2)**4*cos(x)**3"], {}, {}, "(3*cos(x)/4 + cos(3*x)/4)*(-cos(x)/2 + cos(2*x)/8 + 3/8)"],
  ["TRpower", ["sin(x)**2"], {}, {}, "1/2 - cos(2*x)/2"],
  ["TRpower", ["cos(x)**2"], {}, {}, "cos(2*x)/2 + 1/2"],
  ["TRpower", ["sin(x)**3"], {}, {}, "3*sin(x)/4 - sin(3*x)/4"],
  ["TRpower", ["cos(x)**3"], {}, {}, "3*cos(x)/4 + cos(3*x)/4"],
  ["TRpower", ["sin(x)**4"], {}, {}, "-cos(2*x)/2 + cos(4*x)/8 + 3/8"],
  ["TRpower", ["cos(x)**4"], {}, {}, "cos(2*x)/2 + cos(4*x)/8 + 3/8"],
  ["TRpower", ["sin(x)**5"], {}, {}, "5*sin(x)/8 - 5*sin(3*x)/16 + sin(5*x)/16"],
  ["TRpower", ["cos(x)**5"], {}, {}, "5*cos(x)/8 + 5*cos(3*x)/16 + cos(5*x)/16"],
  ["TRpower", ["sin(x)**6"], {}, {}, "-15*cos(2*x)/32 + 3*cos(4*x)/16 - cos(6*x)/32 + 5/16"],
  ["TRpower", ["cos(x)**6"], {}, {}, "15*cos(2*x)/32 + 3*cos(4*x)/16 + cos(6*x)/32 + 5/16"],
  ["TRpower", ["sin(x)**7"], {}, {}, "35*sin(x)/64 - 21*sin(3*x)/64 + 7*sin(5*x)/64 - sin(7*x)/64"],
  ["TRpower", ["cos(x)**7"], {}, {}, "35*cos(x)/64 + 21*cos(3*x)/64 + 7*cos(5*x)/64 + cos(7*x)/64"],
  ["_TR11", ["sin(x/4)*sin(x/3)*sin(2*x)/(cos(x/8)*cos(x/6))"], {}, {}, "4*sin(x/8)*sin(x/6)*sin(2*x)"],
  ["_TR11", ["sin(x/3)/cos(x/6)"], {}, {}, "2*sin(x/6)"],
  ["_TR11", ["cos(x/6)/sin(x/3)"], {}, {}, "1/(2*sin(x/6))"],
  ["_TR11", ["sin(2*x)*cos(x/8)/sin(x/4)"], {}, {}, "sin(2*x)/(2*sin(x/8))"],
  ["_TR11", ["sin(x)/sin(x/2)"], {}, {}, "2*cos(x/2)"],
  ["as_f_sign_1", ["x + 1"], {}, {}, "(1, x, 1)"],
  ["as_f_sign_1", ["x - 1"], {}, {}, "(1, x, -1)"],
  ["as_f_sign_1", ["1 - x"], {}, {}, "(-1, x, -1)"],
  ["as_f_sign_1", ["-x - 1"], {}, {}, "(-1, x, 1)"],
  ["as_f_sign_1", ["2*x + 2"], {}, {}, "(2, x, 1)"],
  ["as_f_sign_1", ["x*y - y"], {}, {}, "(y, x, -1)"],
  ["as_f_sign_1", ["-x*y + y"], {}, {}, "(-y, x, -1)"],
  ["fu", ["sin(50)**2 + 1/2 + cos(50)**2"], {}, {}, "3/2"],
  ["fu", ["sqrt(2)*sin(x) + sqrt(6)*cos(x)"], {}, {}, "2*sqrt(2)*sin(x + pi/3)"],
  ["fu", ["sin(x)**4 + sin(y)**2 + 2*cos(x)**2 - cos(y)**2"], {}, {}, "cos(x)**4 - 2*cos(y)**2 + 2"],
  ["fu", ["1/2 - cos(2*x)/2"], {}, {}, "sin(x)**2"],
  ["fu", ["(-sin(b) + cos(b))*sin(a) + (sin(b) + cos(b))*cos(a)"], {}, {}, "sqrt(2)*sin(a + b + pi/4)"],
  ["fu", ["sin(x)/2 + sqrt(3)*cos(x)/2"], {}, {}, "sin(x + pi/3)"],
  ["fu", ["-sin(2*x)**2/4 - sin(y)**2 - cos(x)**4 + 1"], {}, {}, "-cos(x)**2 + cos(y)**2"],
  ["fu", ["cos(4*pi/9)"], {}, {}, "sin(pi/18)"],
  ["fu", ["cos(pi/9)*cos(2*pi/9)*cos(4*pi/9)/2"], {}, {}, "1/16"],
  ["fu", ["-sqrt(3)*tan(5*pi/18)*tan(7*pi/18) + tan(5*pi/18) + tan(7*pi/18)"], {}, {}, "-sqrt(3)"],
  ["fu", ["tan(1)*tan(2)"], {}, {}, "tan(1)*tan(2)"],
  ["fu", ["cos(1)*cos(2)*cos(4)*cos(8)*cos(16)*cos(32)*cos(64)*cos(128)*cos(256)*cos(512)"], {}, {}, "sin(1024)/(1024*sin(1))"],
  ["fu", ["sqrt(sin(x)**2) + cos(x)"], {}, {}, "sqrt(sin(x)**2) + cos(x)"],
  ["fu", ["(-14*sin(x)**3 + 35*sin(x) + 6*sqrt(3)*cos(x)**3 + 9*sqrt(3)*cos(x))/(cos(2*x) + 4)"], {}, {}, "7*sin(x) + 3*sqrt(3)*cos(x)"],
  ["fu", ["-sin(_Dummy_34*x)**2 + cos(_Dummy_34*x)**2"], {}, {}, "cos(2*_Dummy_34*x)"],
  ["TR12", ["I*tan(_Dummy_36*x + _Dummy_36*y)"], {}, {}, "I*(tan(_Dummy_36*x) + tan(_Dummy_36*y))/(-tan(_Dummy_36*x)*tan(_Dummy_36*y) + 1)"],
  ["TR8", ["2*sin(x)*cos(x)*B*A"], {}, { A: { commutative: false }, B: { commutative: false } }, "sin(2*x)*B*A"],
  ["TR13", ["tan(2)*tan(3)*B*A"], {}, { B: { commutative: false }, A: { commutative: false } }, "(-tan(2)/tan(5) - tan(3)/tan(5) + 1)*B*A"],
  ["TR3", ["cos(x)"], {}, {}, "cos(x)"],
  ["TR1", ["cos(x)"], {}, {}, "cos(x)"],
  ["TR12", ["cos(x)"], {}, {}, "cos(x)"],
  ["TR2", ["cos(x)"], {}, {}, "cos(x)"],
  ["L", ["cos(x)"], {}, {}, "1"],
  ["TR2i", ["cos(x)"], {}, {}, "cos(x)"],
  ["TR14", ["cos(x)"], {}, {}, "cos(x)"],
  ["TR5", ["cos(x)"], {}, {}, "cos(x)"],
  ["TR10", ["cos(x)"], {}, {}, "cos(x)"],
  ["TR11", ["cos(x)"], {}, {}, "cos(x)"],
  ["_TR11", ["cos(x)"], {}, {}, "cos(x)"],
  ["TR6", ["cos(x)"], {}, {}, "cos(x)"],
  ["TR10i", ["cos(x)"], {}, {}, "cos(x)"],
  ["TRmorrie", ["cos(x)"], {}, {}, "cos(x)"],
  ["TR8", ["cos(x)"], {}, {}, "cos(x)"],
  ["TR15", ["cos(x)"], {}, {}, "cos(x)"],
  ["TR16", ["cos(x)"], {}, {}, "cos(x)"],
  ["TR111", ["cos(x)"], {}, {}, "cos(x)"],
  ["TR22", ["cos(x)"], {}, {}, "cos(x)"],
  ["TR3", ["sin(x)"], {}, {}, "sin(x)"],
  ["TR1", ["sin(x)"], {}, {}, "sin(x)"],
  ["TR12", ["sin(x)"], {}, {}, "sin(x)"],
  ["TR2", ["sin(x)"], {}, {}, "sin(x)"],
  ["L", ["sin(x)"], {}, {}, "1"],
  ["TR2i", ["sin(x)"], {}, {}, "sin(x)"],
  ["TR14", ["sin(x)"], {}, {}, "sin(x)"],
  ["TR5", ["sin(x)"], {}, {}, "sin(x)"],
  ["TR10", ["sin(x)"], {}, {}, "sin(x)"],
  ["TR11", ["sin(x)"], {}, {}, "sin(x)"],
  ["_TR11", ["sin(x)"], {}, {}, "sin(x)"],
  ["TR6", ["sin(x)"], {}, {}, "sin(x)"],
  ["TR10i", ["sin(x)"], {}, {}, "sin(x)"],
  ["TRmorrie", ["sin(x)"], {}, {}, "sin(x)"],
  ["TR8", ["sin(x)"], {}, {}, "sin(x)"],
  ["TR15", ["sin(x)"], {}, {}, "sin(x)"],
  ["TR16", ["sin(x)"], {}, {}, "sin(x)"],
  ["TR111", ["sin(x)"], {}, {}, "sin(x)"],
  ["TR22", ["sin(x)"], {}, {}, "sin(x)"],
  ["TR3", ["2*sin(x)*B*A + cos(x)"], {}, { A: { commutative: false }, B: { commutative: false } }, "2*sin(x)*B*A + cos(x)"],
  ["TR1", ["2*sin(x)*B*A + cos(x)"], {}, { A: { commutative: false }, B: { commutative: false } }, "2*sin(x)*B*A + cos(x)"],
  ["TR12", ["2*sin(x)*B*A + cos(x)"], {}, { A: { commutative: false }, B: { commutative: false } }, "2*sin(x)*B*A + cos(x)"],
  ["TR2", ["2*sin(x)*B*A + cos(x)"], {}, { A: { commutative: false }, B: { commutative: false } }, "2*sin(x)*B*A + cos(x)"],
  ["L", ["2*sin(x)*B*A + cos(x)"], {}, { A: { commutative: false }, B: { commutative: false } }, "2"],
  ["TR2i", ["2*sin(x)*B*A + cos(x)"], {}, { A: { commutative: false }, B: { commutative: false } }, "2*sin(x)*B*A + cos(x)"],
  ["TR14", ["2*sin(x)*B*A + cos(x)"], {}, { A: { commutative: false }, B: { commutative: false } }, "2*sin(x)*B*A + cos(x)"],
  ["TR5", ["2*sin(x)*B*A + cos(x)"], {}, { A: { commutative: false }, B: { commutative: false } }, "2*sin(x)*B*A + cos(x)"],
  ["TR10", ["2*sin(x)*B*A + cos(x)"], {}, { A: { commutative: false }, B: { commutative: false } }, "2*sin(x)*B*A + cos(x)"],
  ["TR11", ["2*sin(x)*B*A + cos(x)"], {}, { A: { commutative: false }, B: { commutative: false } }, "2*sin(x)*B*A + cos(x)"],
  ["_TR11", ["2*sin(x)*B*A + cos(x)"], {}, { A: { commutative: false }, B: { commutative: false } }, "2*sin(x)*B*A + cos(x)"],
  ["TR6", ["2*sin(x)*B*A + cos(x)"], {}, { A: { commutative: false }, B: { commutative: false } }, "2*sin(x)*B*A + cos(x)"],
  ["TR10i", ["2*sin(x)*B*A + cos(x)"], {}, { A: { commutative: false }, B: { commutative: false } }, "2*sin(x)*B*A + cos(x)"],
  ["TRmorrie", ["2*sin(x)*B*A + cos(x)"], {}, { A: { commutative: false }, B: { commutative: false } }, "2*sin(x)*B*A + cos(x)"],
  ["TR8", ["2*sin(x)*B*A + cos(x)"], {}, { A: { commutative: false }, B: { commutative: false } }, "2*sin(x)*B*A + cos(x)"],
  ["TR15", ["2*sin(x)*B*A + cos(x)"], {}, { A: { commutative: false }, B: { commutative: false } }, "2*sin(x)*B*A + cos(x)"],
  ["TR16", ["2*sin(x)*B*A + cos(x)"], {}, { A: { commutative: false }, B: { commutative: false } }, "2*sin(x)*B*A + cos(x)"],
  ["TR111", ["2*sin(x)*B*A + cos(x)"], {}, { A: { commutative: false }, B: { commutative: false } }, "2*sin(x)*B*A + cos(x)"],
  ["TR22", ["2*sin(x)*B*A + cos(x)"], {}, { A: { commutative: false }, B: { commutative: false } }, "2*sin(x)*B*A + cos(x)"],
  ["TR3", ["cos(x)*(2*sin(x)*B*A + cos(x))"], {}, { A: { commutative: false }, B: { commutative: false } }, "cos(x)*(2*sin(x)*B*A + cos(x))"],
  ["TR1", ["cos(x)*(2*sin(x)*B*A + cos(x))"], {}, { A: { commutative: false }, B: { commutative: false } }, "cos(x)*(2*sin(x)*B*A + cos(x))"],
  ["TR12", ["cos(x)*(2*sin(x)*B*A + cos(x))"], {}, { A: { commutative: false }, B: { commutative: false } }, "cos(x)*(2*sin(x)*B*A + cos(x))"],
  ["TR2", ["cos(x)*(2*sin(x)*B*A + cos(x))"], {}, { A: { commutative: false }, B: { commutative: false } }, "cos(x)*(2*sin(x)*B*A + cos(x))"],
  ["L", ["cos(x)*(2*sin(x)*B*A + cos(x))"], {}, { A: { commutative: false }, B: { commutative: false } }, "3"],
  ["L", ["2*sin(x)*cos(x)*B*A + cos(x)**2"], {}, { A: { commutative: false }, B: { commutative: false } }, "3"],
  ["TR2i", ["cos(x)*(2*sin(x)*B*A + cos(x))"], {}, { A: { commutative: false }, B: { commutative: false } }, "cos(x)*(2*sin(x)*B*A + cos(x))"],
  ["TR14", ["cos(x)*(2*sin(x)*B*A + cos(x))"], {}, { A: { commutative: false }, B: { commutative: false } }, "cos(x)*(2*sin(x)*B*A + cos(x))"],
  ["TR5", ["cos(x)*(2*sin(x)*B*A + cos(x))"], {}, { A: { commutative: false }, B: { commutative: false } }, "cos(x)*(2*sin(x)*B*A + cos(x))"],
  ["TR10", ["cos(x)*(2*sin(x)*B*A + cos(x))"], {}, { A: { commutative: false }, B: { commutative: false } }, "cos(x)*(2*sin(x)*B*A + cos(x))"],
  ["TR11", ["cos(x)*(2*sin(x)*B*A + cos(x))"], {}, { A: { commutative: false }, B: { commutative: false } }, "cos(x)*(2*sin(x)*B*A + cos(x))"],
  ["_TR11", ["cos(x)*(2*sin(x)*B*A + cos(x))"], {}, { A: { commutative: false }, B: { commutative: false } }, "cos(x)*(2*sin(x)*B*A + cos(x))"],
  ["TR6", ["cos(x)*(2*sin(x)*B*A + cos(x))"], {}, { A: { commutative: false }, B: { commutative: false } }, "cos(x)*(2*sin(x)*B*A + cos(x))"],
  ["TR10i", ["cos(x)*(2*sin(x)*B*A + cos(x))"], {}, { A: { commutative: false }, B: { commutative: false } }, "cos(x)*(2*sin(x)*B*A + cos(x))"],
  ["TRmorrie", ["cos(x)*(2*sin(x)*B*A + cos(x))"], {}, { A: { commutative: false }, B: { commutative: false } }, "cos(x)*(2*sin(x)*B*A + cos(x))"],
  // (SymPy keeps 1/2 outside a non-commutative sum; the symjs core distributes it)
  ["TR8", ["cos(x)*(2*sin(x)*B*A + cos(x))"], {}, { A: { commutative: false }, B: { commutative: false } }, "sin(2*x)*B*A + cos(2*x)/2 + 1/2"],
  ["L", ["(2*sin(2*x)*B*A + cos(2*x) + 1)/2"], {}, { A: { commutative: false }, B: { commutative: false } }, "2"],
  // (SymPy keeps 1/2 outside a non-commutative sum; the symjs core distributes it)
  ["TR2", ["(2*sin(2*x)*B*A + cos(2*x) + 1)/2"], {}, { A: { commutative: false }, B: { commutative: false } }, "sin(2*x)*B*A + cos(2*x)/2 + 1/2"],
  // (SymPy keeps 1/2 outside a non-commutative sum; the symjs core distributes it)
  ["TR2i", ["(2*sin(2*x)*B*A + cos(2*x) + 1)/2"], {}, { A: { commutative: false }, B: { commutative: false } }, "sin(2*x)*B*A + cos(2*x)/2 + 1/2"],
  // (SymPy keeps 1/2 outside a non-commutative sum; the symjs core distributes it)
  ["TR5", ["(2*sin(2*x)*B*A + cos(2*x) + 1)/2"], {}, { A: { commutative: false }, B: { commutative: false } }, "sin(2*x)*B*A + cos(2*x)/2 + 1/2"],
  // (SymPy keeps 1/2 outside a non-commutative sum; the symjs core distributes it)
  ["TR15", ["(2*sin(2*x)*B*A + cos(2*x) + 1)/2"], {}, { A: { commutative: false }, B: { commutative: false } }, "sin(2*x)*B*A + cos(2*x)/2 + 1/2"],
  ["L", ["sin(2*x)*B*A + cos(2*x)/2 + 1/2"], {}, { A: { commutative: false }, B: { commutative: false } }, "2"],
  ["TR6", ["sin(2*x)*B*A + cos(2*x)/2 + 1/2"], {}, { A: { commutative: false }, B: { commutative: false } }, "sin(2*x)*B*A + cos(2*x)/2 + 1/2"],
  ["TR16", ["sin(2*x)*B*A + cos(2*x)/2 + 1/2"], {}, { A: { commutative: false }, B: { commutative: false } }, "sin(2*x)*B*A + cos(2*x)/2 + 1/2"],
  ["TR111", ["sin(2*x)*B*A + cos(2*x)/2 + 1/2"], {}, { A: { commutative: false }, B: { commutative: false } }, "sin(2*x)*B*A + cos(2*x)/2 + 1/2"],
  ["TR2i", ["sin(2*x)*B*A + cos(2*x)/2 + 1/2"], {}, { A: { commutative: false }, B: { commutative: false } }, "sin(2*x)*B*A + cos(2*x)/2 + 1/2"],
  ["TR22", ["sin(2*x)*B*A + cos(2*x)/2 + 1/2"], {}, { A: { commutative: false }, B: { commutative: false } }, "sin(2*x)*B*A + cos(2*x)/2 + 1/2"],
  ["TR1", ["sin(2*x)*B*A + cos(2*x)/2 + 1/2"], {}, { A: { commutative: false }, B: { commutative: false } }, "sin(2*x)*B*A + cos(2*x)/2 + 1/2"],
  ["TR2", ["sin(2*x)*B*A + cos(2*x)/2 + 1/2"], {}, { A: { commutative: false }, B: { commutative: false } }, "sin(2*x)*B*A + cos(2*x)/2 + 1/2"],
  ["TR12", ["sin(2*x)*B*A + cos(2*x)/2 + 1/2"], {}, { A: { commutative: false }, B: { commutative: false } }, "sin(2*x)*B*A + cos(2*x)/2 + 1/2"],
  ["trig_split", ["cos(x)", "cos(y)"], {}, {}, "(1, 1, 1, x, y, True)"],
  ["trig_split", ["2*cos(x)", "-2*cos(y)"], {}, {}, "(2, 1, -1, x, y, True)"],
  ["trig_split", ["sin(y)*cos(x)", "sin(y)*cos(y)"], {}, {}, "(sin(y), 1, 1, x, y, True)"],
  ["trig_split", ["cos(x)", "-sqrt(3)*sin(x)"], { two: true }, {}, "(2, 1, -1, x, pi/6, False)"],
  ["trig_split", ["cos(x)", "sin(x)"], { two: true }, {}, "(sqrt(2), 1, 1, x, pi/4, False)"],
  ["trig_split", ["cos(x)", "-sin(x)"], { two: true }, {}, "(sqrt(2), 1, -1, x, pi/4, False)"],
  ["trig_split", ["sqrt(2)*cos(x)", "-sqrt(6)*sin(x)"], { two: true }, {}, "(2*sqrt(2), 1, -1, x, pi/6, False)"],
  ["trig_split", ["-sqrt(6)*cos(x)", "-sqrt(2)*sin(x)"], { two: true }, {}, "(-2*sqrt(2), 1, 1, x, pi/3, False)"],
  ["trig_split", ["sqrt(6)*cos(x)/6", "sqrt(2)*sin(x)/2"], { two: true }, {}, "(sqrt(6)/3, 1, 1, x, pi/6, False)"],
  ["trig_split", ["-sqrt(6)*sin(y)*cos(x)", "-sqrt(2)*sin(x)*sin(y)"], { two: true }, {}, "(-2*sqrt(2)*sin(y), 1, 1, x, pi/3, False)"],
  ["trig_split", ["cos(x)", "sin(x)"], {}, {}, "None"],
  ["trig_split", ["cos(x)", "sin(z)"], {}, {}, "None"],
  ["trig_split", ["2*cos(x)", "-sin(x)"], {}, {}, "None"],
  ["trig_split", ["cos(x)", "-sqrt(3)*sin(x)"], {}, {}, "None"],
  ["trig_split", ["cos(x)*cos(y)", "sin(x)*sin(z)"], {}, {}, "None"],
  ["trig_split", ["cos(x)*cos(y)", "sin(x)*sin(y)"], {}, {}, "None"],
  ["trig_split", ["-sqrt(6)*cos(x)", "sqrt(2)*sin(x)*sin(y)"], { two: true }, {}, "None"],
  ["trig_split", ["sqrt(3)*sqrt(x)", "cos(3)"], { two: true }, {}, "None"],
  ["trig_split", ["sqrt(3)*x**(1/3)", "sin(3)*cos(2)"], { two: true }, {}, "None"],
  ["trig_split", ["cos(5)*cos(6)", "sin(5)*cos(7)"], { two: true }, {}, "None"],
];

// More calls (inputs chosen to reach the remaining branches), with SymPy 1.14's results
const MORE: Row[] = [
  ["trig_split", ["x**(2*a)*cos(x)", "x**a*cos(y)"], {}, {}, "None"],
  ["TR14", ["(1 - cos(x))**3*(1 + cos(x))"], {}, {}, "(1 - cos(x))**2*sin(x)**2"],
  ["TR14", ["(1 + cos(x))**3*(1 - cos(x))"], {}, {}, "(cos(x) + 1)**2*sin(x)**2"],
  ["trig_split", ["x**2*cos(x)", "x**a*cos(y)"], {}, {}, "None"],
  ["TR2i", ["(cos(x) + 2)/sin(x)"], { half: true }, {}, "(cos(x) + 2)/sin(x)"],
  ["TR9", ["z + cos(a) + x*y + cos(b + c)"], {}, {}, "x*y + z + 2*cos(-a/2 + b/2 + c/2)*cos(a/2 + b/2 + c/2)"],
  ["TR10i", ["cos(x)*cos(y) - sin(x)*sin(y) - cos(x + y) + z"], {}, {}, "z"],
  ["TR14", ["(cos(x) - 1)**3*(cos(x) + 1)"], {}, {}, "-(cos(x) - 1)**2*sin(x)**2"],
  ["TR14", ["(cos(x) - 1)*(cos(x) + 1)**3"], {}, {}, "-(cos(x) + 1)**2*sin(x)**2"],
  ["TR14", ["(1 + cos(x))**2*(1 + sin(y))**m"], {}, { m: { integer: true } }, "(sin(y) + 1)**m*(cos(x) + 1)**2"],
  ["TR12i", ["(tan(a) + tan(b))/(1 - tan(a)*tan(b))**(m + 1)"], {}, { m: { integer: true } }, "(-tan(a)*tan(b) + 1)**(-m - 1)*(tan(a) + tan(b))"],
  // SymPy: -tan(a + b)/((-1)**m*(tan(a) + tan(b) - 1)**m), wrong for m = 2, a = b = pi/8 (see above)
  ["TR12i", ["(tan(a) + tan(b))/(1 - tan(a)*tan(b))**m"], {}, { m: { integer: true } }, "(tan(a) + tan(b))/(-tan(a)*tan(b) + 1)**m"],
  // SymPy raises KeyError (a + b): the numerator has no matching denominator
  ["TR12i", ["(tan(a) + tan(b))/(1 - tan(c)*tan(d))"], {}, {}, "(tan(a) + tan(b))/(-tan(c)*tan(d) + 1)"],
  ["TR2i", ["sin(x)/(cos(y) + 1)"], { half: true }, {}, "sin(x)/(cos(y) + 1)"],
  ["TR2i", ["(cos(x) + 1)/sin(y)"], { half: true }, {}, "(cos(x) + 1)/sin(y)"],
  ["TR2i", ["sin(x)**2/(cos(x)**2*(x + 1))"], {}, {}, "tan(x)**2/(x + 1)"],
  ["TR2i", ["sin(x)/((x*y + x)*cos(x))"], {}, {}, "tan(x)/(x*y + x)"],
  ["TR2i", ["sin(x)**y/cos(x)"], {}, {}, "sin(x)**y/cos(x)"],
  ["TR5", ["sin(x)**(3/2)"], {}, {}, "sin(x)**(3/2)"],
  ["TR5", ["sin(x)**6"], { max: 6 }, {}, "(1 - cos(x)**2)**3"],
  ["TR5", ["sin(x)**6"], { max: 6, pow: true }, {}, "sin(x)**6"],
  ["TR5", ["sin(x)**8"], { max: 8, pow: true }, {}, "(1 - cos(x)**2)**4"],
  ["TR5", ["sin(x)**(-2)"], {}, {}, "sin(x)**(-2)"],
  ["TR11", ["cos(x)"], { base: "pi/4" }, {}, "cos(x)"],
  ["TR11", ["sin(2*x)"], { base: "-x" }, {}, "2*sin(x)*cos(x)"],
  ["TR9", ["cos(a) + sin(c) + cos(b)"], {}, {}, "sin(c) + 2*cos(a/2 - b/2)*cos(a/2 + b/2)"],
  ["TR9", ["cos(a) + sin(c) + cos(b) + sin(d)"], {}, {}, "2*sin(c/2 + d/2)*cos(c/2 - d/2) + 2*cos(a/2 - b/2)*cos(a/2 + b/2)"],
  ["TR10i", ["cos(a)*cos(b) + sin(c) - sin(a)*sin(b) + x"], {}, {}, "x + sin(c) + cos(a + b)"],
  ["TR12i", ["(tan(a) + tan(b))/(1 + tan(a)*tan(b))"], {}, {}, "(tan(a) + tan(b))/(tan(a)*tan(b) + 1)"],
  ["TR12i", ["(tan(a) + tan(b))/(x**2 - 1)"], {}, {}, "(tan(a) + tan(b))/(x**2 - 1)"],
  ["TR12i", ["(tan(a) + tan(b))/((x**2 - 1)**2*(1 - tan(a)*tan(b)))"], {}, {}, "tan(a + b)/((x - 1)**2*(x + 1)**2)"],
  // SymPy: -tan(a + b)/(tan(a) + tan(b) - 1), which is wrong (a = b = pi/8: the input is 1)
  ["TR12i", ["(tan(a) + tan(b))**2/(1 - tan(a)*tan(b))**2"], {}, {}, "tan(a + b)**2"],
  // SymPy: tan(a + b), which drops a factor tan(a) + tan(b) (a = b = pi/8: the input is 2*tan(pi/8))
  ["TR12i", ["(tan(a) + tan(b))**2/(1 - tan(a)*tan(b))"], {}, {}, "(tan(a) + tan(b))*tan(a + b)"],
  ["TR12i", ["(tan(a) + tan(b))*(x**2 - 1)/(1 - tan(a)*tan(b))"], {}, {}, "(x - 1)*(x + 1)*tan(a + b)"],
  ["TR12i", ["(tan(a) + tan(b))*(x**2 - 1)**2/(1 - tan(a)*tan(b))"], {}, {}, "(x - 1)**2*(x + 1)**2*tan(a + b)"],
  ["TR12i", ["(tan(a) + tan(b))*(x + 1)**y/(1 - tan(a)*tan(b))"], {}, {}, "(x + 1)**y*tan(a + b)"],
  ["TR12i", ["(tan(a) + tan(b))/(1 - tan(a)*tan(b))**y"], {}, {}, "(tan(a) + tan(b))/(-tan(a)*tan(b) + 1)**y"],
  ["TR12i", ["(tan(a) + tan(b))*x/(1 - tan(a)*tan(b))**(y + 1)"], {}, {}, "x*(-tan(a)*tan(b) + 1)**(-y - 1)*(tan(a) + tan(b))"],
  ["TR12i", ["(-tan(a) - tan(b))/(1 - tan(a)*tan(b))"], {}, {}, "-tan(a + b)"],
  ["TR14", ["(cos(x) - 1)**2*(cos(x) + 1)**3"], {}, {}, "(cos(x) + 1)*sin(x)**4"],
  ["TR14", ["(cos(x) - 1)**3*(cos(x) + 1)**2"], {}, {}, "(cos(x) - 1)*sin(x)**4"],
  ["TR14", ["(cos(x) - 1)**2*(cos(y) + 1)**3"], {}, {}, "(cos(x) - 1)**2*(cos(y) + 1)**3"],
  ["TR14", ["(cos(x) - 1)**a*(cos(x) + 1)**b"], {}, {}, "(cos(x) - 1)**a*(cos(x) + 1)**b"],
  ["TR14", ["(cos(x) - 1)**y*(x + 1)"], {}, {}, "(x + 1)*(cos(x) - 1)**y"],
  ["TR14", ["(cos(x) - 1)*(cos(x) + 1)/(x*(sin(x) - 1)*(sin(x) + 1))"], {}, {}, "sin(x)**2/(x*cos(x)**2)"],
  ["TRmorrie", ["cos(x)**2*cos(2*x)*cos(4*x)"], {}, {}, "sin(8*x)*cos(x)/(8*sin(x))"],
  ["TRmorrie", ["cos(x)*cos(2*x)**2*cos(4*x)**3"], {}, {}, "sin(8*x)**2*cos(4*x)/(32*sin(x)*sin(2*x))"],
  ["TR15", ["sin(x)**(-3)"], {}, {}, "(cot(x)**2 + 1)/sin(x)"],
  ["TR16", ["cos(x)**(-3)"], {}, {}, "cos(x)**(-3)"],
  ["TR16", ["cos(x)**(-2)"], {}, {}, "tan(x)**2 + 1"],
  ["TR111", ["x**(-2)"], {}, {}, "x**(-2)"],
  ["TR111", ["cot(x)**(-2)"], {}, {}, "cot(x)**(-2)"],
  ["TRpower", ["sin(x)**y"], {}, {}, "sin(x)**y"],
  ["TRpower", ["cos(x)**4"], {}, {}, "cos(2*x)/2 + cos(4*x)/8 + 3/8"],
  ["TRpower", ["sin(x)**4"], {}, {}, "-cos(2*x)/2 + cos(4*x)/8 + 3/8"],
  ["TRpower", ["sin(x)**5"], {}, {}, "5*sin(x)/8 - 5*sin(3*x)/16 + sin(5*x)/16"],
  ["sincos_to_sum", ["x**2"], {}, {}, "x**2"],
  ["sincos_to_sum", ["16*sin(x)**3*cos(2*x)**2"], {}, {}, "7*sin(x) - 5*sin(3*x) + 3*sin(5*x) - sin(7*x)"],
  ["fu", ["sin(x) < cos(x)**2 + sin(x)**2"], {}, {}, "sin(x) < 1"],
  ["fu", ["tan(x)**2 + 1"], {}, {}, "tan(x)**2 + 1"],
  ["fu", ["x"], {}, {}, "x"],
  ["trig_split", ["x**(a + 1)*cos(x)", "x**a*cos(y)"], {}, {}, "None"],
  ["trig_split", ["x**(a + 2)*cos(x)", "x**(b + 1)*cos(y)"], {}, {}, "None"],
  ["trig_split", ["x**(a + 1)*cos(x)", "x**(b + 2)*cos(y)"], {}, {}, "None"],
  ["trig_split", ["x**(a + 1)*cos(x)", "x**(b + 1)*cos(y)"], {}, {}, "None"],
  ["trig_split", ["x**a*cos(x)", "x**b*cos(y)"], {}, {}, "None"],
  ["trig_split", ["x**2*cos(x)", "x**3*cos(y)"], {}, {}, "None"],
  ["trig_split", ["cos(x)*cos(y)", "sin(x)*sin(z)"], { two: true }, {}, "None"],
  ["trig_split", ["cos(x)*sin(y)", "sin(x)*sin(y)"], { two: true }, {}, "(sqrt(2)*sin(y), 1, 1, x, pi/4, False)"],
  ["trig_split", ["cos(x)*sin(y)", "sin(z)*cos(w)"], { two: true }, {}, "None"],
  ["trig_split", ["sqrt(2)*cos(x)*sin(y)", "sin(x)"], { two: true }, {}, "None"],
  ["trig_split", ["sqrt(2)*cos(x)", "sqrt(5)*sin(x)"], { two: true }, {}, "None"],
  ["trig_split", ["cos(x)", "sin(y)"], { two: true }, {}, "None"],
  ["trig_split", ["cos(x)*sqrt(2)*sqrt(3)", "sin(x)"], { two: true }, {}, "None"],
  ["trig_split", ["x*cos(x)", "sin(x)"], { two: true }, {}, "None"],
  ["trig_split", ["cos(x)*x", "sin(x)*y"], { two: true }, {}, "None"],
  ["trig_split", ["x", "sin(x)"], {}, {}, "None"],
  ["trig_split", ["cos(x)", "x"], {}, {}, "None"],
  ["as_f_sign_1", ["x + 1"], {}, {}, "(1, x, 1)"],
  ["as_f_sign_1", ["x*y + 2*x"], {}, {}, "None"],
  ["as_f_sign_1", ["-x*y - x"], {}, {}, "(-x, y, 1)"],
  ["as_f_sign_1", ["x*y - x"], {}, {}, "(x, y, -1)"],
  ["as_f_sign_1", ["2*x + 2"], {}, {}, "(2, x, 1)"],
  ["as_f_sign_1", ["x + y + 1"], {}, {}, "None"],
  ["TR3", ["cos(31*pi/64 + x)"], {}, {}, "cos(x + 31*pi/64)"],
  ["TR10", ["sin(a + b + c)"], {}, {}, "(-sin(a)*sin(b) + cos(a)*cos(b))*sin(c) + (sin(a)*cos(b) + sin(b)*cos(a))*cos(c)"],
  ["TR12", ["tan(a + b + c)"], {}, {}, "(tan(c) + (tan(a) + tan(b))/(-tan(a)*tan(b) + 1))/(1 - (tan(a) + tan(b))*tan(c)/(-tan(a)*tan(b) + 1))"],
  ["TR13", ["tan(a)*tan(b)*tan(c)*cot(a)*cot(b)*cot(c)"], {}, {}, "(-tan(b)/tan(b + c) - tan(c)/tan(b + c) + 1)*(cot(b)*cot(b + c) + cot(c)*cot(b + c) + 1)*tan(a)*cot(a)"],
  ["TR22", ["tan(x)**3*cot(x)**4"], {}, {}, "(csc(x)**2 - 1)**2*(sec(x)**2 - 1)*tan(x)"],
  ["TR8", ["sin(x)**3*cos(y)"], {}, {}, "3*sin(x - y)/8 + 3*sin(x + y)/8 - sin(3*x - y)/8 - sin(3*x + y)/8"],
  ["TR8", ["cos(x)**3"], {}, {}, "3*cos(x)/4 + cos(3*x)/4"],
  ["TR8", ["sin(x)**3"], {}, {}, "3*sin(x)/4 - sin(3*x)/4"],
  ["TR7", ["cos(x)**3"], {}, {}, "cos(x)**3"],
  ["L", ["x"], {}, {}, "0"],
];

describe('test_fu.py: SymPy 1.14 cases', () => {
  it.each([...ROWS, ...MORE])('%s(%j)', (fn, args, kw, syms, want) => {
    const opts = { symbols: Object.entries(syms).map(([k, v]) => symbol(k, v)) };
    expect(show(run(fn, args.map((s) => parse(s, opts)), kw))).toBe(want);
  });
});

describe('fu.ts: helpers and options', () => {
  const P = (t: string) => parse(t);
  it('fu with a measure (SymPy test_objective)', () => {
    expect(sstr(FU.fu(P('sin(x)/cos(x)'), { measure: (e) => countOps(e) }))).toBe('tan(x)');
    expect(sstr(FU.fu(P('sin(x)/cos(x)'), { measure: (e) => -countOps(e) }))).toBe('sin(x)/cos(x)');
  });
  it('fu maps over relations', () => {
    expect(sstr(FU.fu(P('sin(x) < cos(x)**2 + sin(x)**2')))).toBe('sin(x) < 1');
  });
  it('FU holds the rules by name (SymPy FU)', () => {
    const e = P('tan(x)*sin(2*x)**2 + sec(x)*cos(x + y) + 3*csc(x)');
    const want: Record<string, string> = {
      TR0: 'sin(2*x)**2*tan(x) + cos(x + y)*sec(x) + 3*csc(x)',
      TR1: 'sin(2*x)**2*tan(x) + cos(x + y)/cos(x) + 3/sin(x)',
      TR2: 'sin(x)*sin(2*x)**2/cos(x) + cos(x + y)*sec(x) + 3*csc(x)',
      TR5: '(1 - cos(2*x)**2)*tan(x) + cos(x + y)*sec(x) + 3*csc(x)',
      TR8: '(1/2 - cos(4*x)/2)*tan(x) + cos(x + y)*sec(x) + 3*csc(x)',
      TR10: '(-sin(x)*sin(y) + cos(x)*cos(y))*sec(x) + sin(2*x)**2*tan(x) + 3*csc(x)',
      TR11: '4*sin(x)**2*cos(x)**2*tan(x) + cos(x + y)*sec(x) + 3*csc(x)',
      L: '5',
    };
    for (const [k, rule] of FU.FU) expect([k, sstr(rule(e))]).toEqual([k, want[k] ?? sstr(e)]);
  });
  it('hyper_as_trig: Osborne rule and back', () => {
    const h = P('sinh(x) + cosh(x) + tanh(x) + coth(x) + sech(x) + csch(x)');
    const [t, back] = FU.hyperAsTrig(h);
    const d = [...t.freeSymbols()].find((v) => v instanceof Dummy);
    expect(sstr(xreplace(t, [[d ?? P('x'), symbol('d')]]))).toBe('I*sin(d*x) + cos(d*x) + I*tan(d*x) - I*cot(d*x) - I*csc(d*x) + sec(d*x)');
    expect(sstr(back(t))).toBe('sinh(x) + cosh(x) + tanh(x) + coth(x) + csch(x) + sech(x)');
  });
  it('TR3 and TR4 evaluate unevaluated functions (SymPy cos(pi, evaluate=False))', () => {
    expect(sstr(FU.TR3(fn('cos', [pi], { evaluate: false })))).toBe('-1');
    expect(sstr(FU.TR4(fn('sin', [pi.div(3)], { evaluate: false })))).toBe('sqrt(3)/2');
  });
  it('positive: the sign of closed numbers', () => {
    expect(FU.positive(P('I*sin(1)'))).toBe(false);
    expect(FU.positive(P('sin(1)**2 + cos(1)**2 - 1'))).toBe(undefined);
    expect(FU.positive(P('f(1)'))).toBe(undefined);
    expect(FU.positive(P('sin(1)'))).toBe(true);
  });
  it('nodeCount of a derivative (SymPy _nodes)', () => {
    expect(FU.nodeCount(P('Derivative(f(x), x)'))).toBe(3);
  });
});

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project
// Ported from SymPy 1.14.0 (sympy/core/basic.py: Basic.compare, _cmp_name, ordering_of_classes),
// Copyright (c) 2006-2023 SymPy Development Team, BSD 3-Clause License.

/**
 * @file SymPy's view of an expression: its class name (`type(e).__name__`),
 * its arguments in SymPy's order (`expr.args`) and `Basic.compare`, the
 * order of the arguments of sums and products. The printers that show the
 * tree (srepr, print_tree, dotprint) and cse use it.
 */

import type { RelOp, SpecialName } from './nodes';
import type { Expr } from './nodes';
import { Add, Constant, Dummy, ExtensionExpr, Float, Fn, Mul, Pow, Rational, Rel, Special, Sym, UndefFn, Wild } from './nodes';
import { BoolAtom } from './nodes';
import { str } from '../printing/str';
import { at } from './guard';

const isExp = (e: Expr): boolean => e instanceof Pow && e.base instanceof Constant && e.base.name === 'E';

const FN_CLASSES: Readonly<Record<string, string>> = { abs: 'Abs', ff: 'FallingFactorial', rf: 'RisingFactorial' };

/** The class name of a node that is not an atom: exp, the function or extension name, Add, Mul, Pow, or its kind. */
function nodeClassName(e: Expr): string {
  if (isExp(e)) return 'exp';
  if (e instanceof Fn) return FN_CLASSES[e.name] ?? e.name;
  if (e instanceof UndefFn || e instanceof ExtensionExpr) return e.name;
  return e.kind;
}

const CONSTANT_CLASSES: Readonly<Record<string, string>> = { E: 'Exp1', pi: 'Pi', I: 'ImaginaryUnit' };
const SPECIAL_CLASSES: Readonly<Record<SpecialName, string>> = { oo: 'Infinity', '-oo': 'NegativeInfinity', zoo: 'ComplexInfinity', nan: 'NaN' };
const REL_CLASSES: Readonly<Record<RelOp, string>> = {
  Eq: 'Equality',
  Ne: 'Unequality',
  Lt: 'StrictLessThan',
  Gt: 'StrictGreaterThan',
  Le: 'LessThan',
  Ge: 'GreaterThan',
};

/** SymPy's class name of an expression (`type(e).__name__`). */
export function sympyClassName(e: Expr): string {
  if (e instanceof Rational) {
    if (e.isZero) return 'Zero';
    if (e.p === 1n && e.q === 1n) return 'One';
    if (e.p === -1n && e.q === 1n) return 'NegativeOne';
    if (e.p === 1n && e.q === 2n) return 'Half';
    return e.isInteger ? 'Integer' : 'Rational';
  }
  if (e instanceof Float) return 'Float';
  if (e instanceof Constant) return CONSTANT_CLASSES[e.name] ?? e.name;
  if (e instanceof Special) return SPECIAL_CLASSES[e.name];
  if (e instanceof Wild) return 'Wild';
  if (e instanceof Dummy) return 'Dummy';
  if (e instanceof Sym) return 'Symbol';
  if (e instanceof BoolAtom) return e.value ? 'BooleanTrue' : 'BooleanFalse';
  if (e instanceof Rel) return REL_CLASSES[e.op];
  return nodeClassName(e);
}

const ORDERING_OF_CLASSES = [
  'Zero', 'One', 'Half', 'Infinity', 'NaN', 'NegativeOne', 'NegativeInfinity',
  'Integer', 'Rational', 'Float',
  'Exp1', 'Pi', 'ImaginaryUnit',
  'Symbol', 'Wild',
  'Pow', 'Mul', 'Add',
  'Derivative', 'Integral',
  'Abs', 'Sign', 'Sqrt',
  'Floor', 'Ceiling',
  'Re', 'Im', 'Arg',
  'Conjugate',
  'Exp', 'Log',
  'Sin', 'Cos', 'Tan', 'Cot', 'ASin', 'ACos', 'ATan', 'ACot',
  'Sinh', 'Cosh', 'Tanh', 'Coth', 'ASinh', 'ACosh', 'ATanh', 'ACoth',
  'RisingFactorial', 'FallingFactorial',
  'factorial', 'binomial',
  'Gamma', 'LowerGamma', 'UpperGamma', 'PolyGamma',
  'Erf',
  'Chebyshev', 'Chebyshev2',
  'Function', 'WildFunction',
  'Lambda',
  'Order',
  'Equality', 'Unequality', 'StrictGreaterThan', 'StrictLessThan',
  'GreaterThan', 'LessThan',
];

const cmp = <T extends string | number | bigint>(a: T, b: T): number => (a > b ? 1 : a < b ? -1 : 0);

/** SymPy _cmp_name: by ordering_of_classes when either name is listed, else by name. */
function cmpName(n1: string, n2: string): number {
  if (n1 === n2) return 0;
  const unknown = ORDERING_OF_CLASSES.length + 1;
  const i = (n: string) => {
    const k = ORDERING_OF_CLASSES.indexOf(n);
    return k < 0 ? unknown : k;
  };
  const [i1, i2] = [i(n1), i(n2)];
  if (i1 === unknown && i2 === unknown) return cmp(n1, n2);
  return cmp(i1, i2);
}

type Content = Expr | string | number | bigint;

/** SymPy _hashable_content (symbol names, number values, otherwise the arguments in SymPy's order). */
function hashableContent(e: Expr): Content[] {
  if (e instanceof Rational) return [e.p, e.q];
  if (e instanceof Float) return [e.toNumber()];
  if (e instanceof Sym) return [e.name];
  // an atom of an extension (a matrix name Str, ...) by its printed form (SymPy Str._hashable_content is (name,))
  if (e instanceof ExtensionExpr && e.args.length === 0) return [str(e)];
  return [...sympyArgs(e)];
}

/** SymPy Basic.compare: class names, then the length and items of the hashable content. */
export function basicCompare(a: Expr, b: Expr): number {
  if (a === b) return 0;
  const c = cmpName(sympyClassName(a), sympyClassName(b));
  if (c) return c;
  const st = hashableContent(a);
  const ot = hashableContent(b);
  if (st.length !== ot.length) return cmp(st.length, ot.length);
  for (let i = 0; i < st.length; i++) {
    const l = at(st, i);
    const r = at(ot, i);
    const d = typeof l === 'object' && typeof r === 'object' ? basicCompare(l, r) : cmp(String(l), String(r));
    if (d) return d;
  }
  return 0;
}

/** SymPy's `expr.args`: exp(x) has the argument x; sums and products are in Basic.compare order. */
export function sympyArgs(e: Expr): readonly Expr[] {
  if (isExp(e)) return [at(e.args, 1)];
  if (e instanceof Add) return [...e.args].sort(basicCompare);
  if (e instanceof Mul) {
    const c = e.args.filter((a) => a.isCommutative).sort(basicCompare);
    return [...c, ...e.args.filter((a) => !a.isCommutative)];
  }
  return e.args;
}


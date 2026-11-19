// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/printing/printers.ts. Expected values are SymPy 1.14's StrPrinter, sstrrepr and multiline_latex.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { sstr } from '../../src/printing/printers';

const x = sj.symbol('x');

describe('StrPrinter, sstrrepr, printLatex and multilineLatex', () => {
  it('StrPrinter and sstrrepr', () => {
    expect(new sj.StrPrinter().doprint(sj.add(x, 1))).toBe('x + 1');
    expect(new sj.StrPrinter({ order: 'lex' }).doprint([x, 'a', null])).toBe('[x, a, None]');
    expect(sj.sstrrepr('a')).toBe("'a'");
    expect(sj.sstrrepr([x, "it's", new Map([[1, 'a']]), new Set(), true, false, 2n, 3])).toBe(`[x, "it's", {1: 'a'}, set(), True, False, 2, 3]`);
    expect(sj.sstrrepr(new Set([1, 2]))).toBe('{1, 2}');
    expect(sj.sstrrepr('a\\b\n')).toBe("'a\\\\b\\n'");
    expect(sj.sstrrepr(`x'y"z`)).toBe(`'x\\'y"z'`);
  });
  it('printLatex', () => {
    expect(sj.printLatex(sj.pow(x, 2))).toBe('x^{2}\n');
  });
  it('multilineLatex (SymPy multiline_latex)', () => {
    const e = sj.parse('sin(x) - 2*cos(x) + 3*exp(x) + log(x)');
    expect(sj.multilineLatex(x, e, { termsPerLine: 2 })).toBe(
      '\\begin{align*}\nx = & 3 e^{x} + \\log{\\left(x \\right)} \\\\\n& + \\sin{\\left(x \\right)} - 2 \\cos{\\left(x \\right)} \n\\end{align*}',
    );
    expect(sj.multilineLatex(x, e, { environment: 'eqnarray', useDots: true })).toBe(
      '\\begin{eqnarray}\nx & = & 3 e^{x} \\dots\\nonumber\\\\\n& & + \\log{\\left(x \\right)} \\dots\\nonumber\\\\\n& & + \\sin{\\left(x \\right)} \\dots\\nonumber\\\\\n& & - 2 \\cos{\\left(x \\right)} \n\\end{eqnarray}',
    );
    expect(sj.multilineLatex(x, sj.parse('-sin(x) + cos(x)'), { environment: 'IEEEeqnarray' })).toBe(
      '\\begin{IEEEeqnarray}{rCl}\nx & = &- \\sin{\\left(x \\right)} \\nonumber\\\\\n& & + \\cos{\\left(x \\right)} \n\\end{IEEEeqnarray}',
    );
    expect(sj.multilineLatex(x, sj.parse('-x - y'))).toBe('\\begin{align*}\nx = &- x \\\\\n& - y \n\\end{align*}');
    expect(sj.multilineLatex(x, x)).toBe('\\begin{align*}\nx = & x \n\\end{align*}');
    expect(sj.multilineLatex(x, sj.parse('x + y + 1'), { termsPerLine: 3 })).toBe('\\begin{align*}\nx = & x + y + 1 \n\\end{align*}');
  });
  it('sstr with the full_prec setting', () => {
    const f = sj.float('0.0175');
    expect(sstr(f)).toBe('0.0175000000000000');
    expect(sstr(f, { fullPrec: false })).toBe('0.0175');
    expect(sstr(sj.Tuple(f, 1))).toBe('(0.0175, 1)');
    expect(sstr(sj.Tuple(f, 1), { fullPrec: true })).toBe('(0.0175000000000000, 1)');
    expect(sstr(sj.mul(sj.float('1.5'), x), { fullPrec: true })).toBe('1.50000000000000*x');
    expect(sstr(sj.mul(sj.float('1.5'), x))).toBe('1.5*x');
    expect(sstr(['a', null])).toBe('[a, None]');
    // the setting applies to this call only
    expect(sj.str(sj.Tuple(f, 1))).toBe('(0.0175, 1)');
  });
});

describe('sstr with perm_cyclic', () => {
  it('prints permutations in array notation', () => {
    expect(sstr(new sj.Permutation([1, 0, 2]), { permCyclic: false })).toBe('Permutation([1, 0, 2])');
    expect(sstr(new sj.Permutation([1, 0, 2]))).toBe('(2)(0 1)');
  });
});

it('formats matrix rows with aligned columns, including empty shapes', () => {
  expect(sstr(sj.Matrix.of([[x, 1], [sj.symbol('y'), sj.add(x, sj.symbol('y'))]]))).toBe('Matrix([\n[x,     1],\n[y, x + y]])');
  expect(sstr(sj.Matrix.of([[1, 2]]))).toBe('Matrix([[1, 2]])');
  expect(sstr(sj.Matrix.zeros(0, 1))).toBe('Matrix(0, 1, [])');
  expect(sstr(sj.Matrix.zeros(1, 0))).toBe('Matrix(1, 0, [])');
});

it('provides the fallback printer and validates settings', () => {
  const printer = new sj.StrPrinter();
  expect(printer.emptyPrinter('foo')).toBe('foo');
  expect(printer.emptyPrinter(sj.mul(x, sj.symbol('y')))).toBe('x*y');
  expect(printer.emptyPrinter(32)).toBe('32');
  expect(() => sstr(x, { unknown: true } as sj.SstrOptions)).toThrow("Unknown setting 'unknown'.");
});

it('preserves scalar types, ordering and precision inside containers', () => {
  expect(sj.sstrrepr([new sj.Str('x'), 'x'])).toBe("[Str('x'), 'x']");
  expect(sstr(sj.Q.even)).toBe('Q.even');
  expect(sstr({ frozenItems: new Set([sj.pow(x, 2), x]) })).toBe('frozenset({x, x**2})');
  expect(sstr({ frozenItems: new Set() })).toBe('frozenset()');
  expect(sstr(new Set(['b', 'c']))).toBe('{b, c}');
  expect(sstr(sj.rational(7, 3), { sympyIntegers: true })).toBe('S(7)/3');
  expect(sstr(sj.rational(2), { sympyIntegers: true })).toBe('S(2)');
  expect(sstr(new sj.Float(100), { fullPrec: false, min: -2, max: 2 })).toBe('1.0e+2');
  expect(sstr(sj.SymFunction('f')(new sj.Float(1.329294)), { dps: 3 })).toBe('f(1.33)');
});

it('prints polynomials and fraction field elements over their coefficient domains', () => {
  const ring = new sj.PolyRing([x], sj.QQ_I);
  expect(sstr(ring.zero)).toBe('(0 + 0*I)');
  expect(sstr(ring.fromExpr(sj.add(sj.mul(sj.I, sj.pow(x, 2)), x)))).toBe('(0 + 1*I)*x**2 + x');
  const field = new sj.FracField([x], sj.QQ);
  expect(sstr(field.fieldNew(x))).toBe('x');
  expect(sstr(field.new(field.ring.fromExpr(sj.add(x, 1)), field.ring.fromExpr(sj.pow(x, 2))))).toBe('(x + 1)/(x**2)');
  expect(sstr(field.new(field.ring.one, field.ring.fromExpr(x)))).toBe('1/x');
  expect(sstr(sj.Poly.from(x, [x]))).toBe("Poly(x, x, domain='ZZ')");
});

it('prints Gaussian constants in a multivariate polynomial', () => {
  const ring = new sj.PolyRing([x, sj.symbol('y')], sj.QQ_I);
  expect(sstr(ring.fromExpr(sj.add(x, sj.I)))).toBe('x + (0 + 1*I)');
});

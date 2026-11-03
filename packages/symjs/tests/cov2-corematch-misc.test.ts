// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Differentiation (calculus/diff.ts), user-defined functions (core/defun.ts),
// indexed objects (core/indexed.ts), sympify of containers (core/sympify.ts),
// unevaluated derivatives (core/undef.ts) and number utilities (core/numberutils.ts).
// Expected values are SymPy 1.14 results.

import { describe, expect, it } from 'vitest';
import {
  Derivative,
  IndexedBase,
  Integral,
  Limit,
  Lt,
  Product,
  SymFunction,
  SympifyError,
  add,
  defineFunction,
  diff,
  evalf,
  expand,
  floor,
  implementedFunction,
  latex,
  mul,
  pow,
  rational,
  rewrite,
  sin,
  str,
  symbols,
  sympify,
} from '../src';
import type { Expr } from '../src';
import { NotImplementedError } from '../src/core/errors';
import { expandSymbolNames, rationalFromString } from '../src/core/numberutils';

const [x, y, k, n, i, j] = symbols('x y k n i j');
const f = SymFunction('f');
const g = SymFunction('g');
const s = (e: unknown): string => str(e as Expr);

describe('diff', () => {
  it('differentiates derivatives, integrals and unevaluated objects', () => {
    expect(s(diff(Derivative(f(y), y), x))).toBe('0');
    expect(s(diff(Derivative(f(mul(x, y)), y), x))).toBe('x*y*Subs(Derivative(f(_xi_1), (_xi_1, 2)), _xi_1, x*y) + Subs(Derivative(f(_xi_1), _xi_1), _xi_1, x*y)');
    expect(s(diff(Derivative(mul(x, f(x)), x), x))).toBe('x*Derivative(f(x), (x, 2)) + 2*Derivative(f(x), x)');
    // SymPy evaluates Derivative(floor(x*y), y) through Subs; symjs keeps it and appends x
    expect(s(diff(Derivative(floor(mul(x, y)), y), x))).toBe('Derivative(floor(x*y), y, x)');
    expect(s(diff(new Integral([f(x), x]), x))).toBe('f(x)');
    expect(s(diff(new Integral([pow(x, 2), x, rational(0), x]), x))).toBe('x**2');
    expect(s(diff(new Integral([mul(x, y), y, rational(0), rational(1)]), x))).toBe('Integral(y, (y, 0, 1))');
    expect(s(diff(Lt(x, 1), x))).toBe('Derivative(x < 1, x)');
    expect(s(diff(new Limit([mul(sin(mul(x, y)), pow(y, -1)), y, rational(0)], '+'), x))).toBe("Derivative(Limit(sin(x*y)/y, y, 0, dir='+'), x)");
    // SymPy: Sum(_h*Product(k*x, (k, 1, _h - 1))*Product(k*x, (k, _h + 1, n)), (_h, 1, n))
    expect(() => diff(Product(mul(x, k), [k, 1, n]), x)).toThrow(NotImplementedError);
    expect(() => diff(x, x, -1)).toThrow(RangeError);
    expect(() => diff(x, x, 1.5)).toThrow(RangeError);
  });
  it('merges the variables of an evaluated derivative', () => {
    expect(s(diff(diff(diff(f(x, y), x), y), x))).toBe('Derivative(f(x, y), (x, 2), y)');
    const [z] = symbols('z');
    expect(s(diff(diff(diff(f(x, y, z), z), y), x))).toBe('Derivative(f(x, y, z), x, y, z)');
    expect(s(diff(diff(diff(f(x, y, z), x), y), z))).toBe('Derivative(f(x, y, z), x, y, z)');
    // two symbols named x (one real): sorted by name, so the order is kept
    const [xr] = symbols('x', { real: true });
    expect(s(diff(diff(f(x, xr as Expr), x), xr as Expr))).toBe('Derivative(f(x, x), x, x)');
  });
});

describe('Indexed derivatives', () => {
  const A = new IndexedBase('A');
  it('differentiates with respect to indexed objects', () => {
    expect(s(diff(A.at(i), A.at(i)))).toBe('1');
    expect(s(diff(A.at(i), A.at(j)))).toBe('KroneckerDelta(i, j)');
    expect(s(diff(pow(A.at(i), 2), A.at(i)))).toBe('2*A[i]');
    expect(s(diff(pow(A.at(i), 2), A.at(j)))).toBe('2*KroneckerDelta(i, j)*A[i]');
    expect(s(diff(mul(A.at(i), A.at(j)), A.at(j)))).toBe('KroneckerDelta(i, j)*A[j] + A[i]');
    expect(s(diff(pow(A.at(i), 3), A.at(i), 2))).toBe('6*A[i]');
    expect(s(diff(x, A.at(i)))).toBe('0');
    expect(() => diff(A.at(i, j), A.at(i))).toThrow(RangeError);
  });
  it('differentiates with respect to an index or the label', () => {
    expect(s(diff(A.at(i), i))).toBe('nan');
    expect(s(diff(A.at(add(i, 1)), i))).toBe('nan');
    expect(s(diff(A.at(i), A.label))).toBe('0');
  });
});

describe('defineFunction', () => {
  const myf = defineFunction('myf', { expand: { twice: () => undefined } });
  it('differentiates without fdiff like SymPy Function.fdiff', () => {
    expect(s(diff(myf(x), x))).toBe('Derivative(myf(x), x)');
    expect(s(diff(myf(x, y), x))).toBe('Derivative(myf(x, y), x)');
    expect(s(diff(myf(pow(x, 2)), x))).toBe('2*x*Subs(Derivative(myf(_xi_1), _xi_1), _xi_1, x**2)');
    expect(s(diff(myf(x, x), x))).toBe('Subs(Derivative(myf(_xi_1, x), _xi_1), _xi_1, x) + Subs(Derivative(myf(x, _xi_2), _xi_2), _xi_2, x)');
    expect(s(diff(myf(g(x)), x))).toBe('Derivative(g(x), x)*Derivative(myf(g(x)), g(x))');
    expect(s(diff(myf(mul(2, x), y), x))).toBe('2*Subs(Derivative(myf(_xi_1, y), _xi_1), _xi_1, 2*x)');
  });
  it('uses fdiff only for the arguments containing the variable', () => {
    const h = defineFunction('h', { fdiff: (_args, idx) => (idx === 0 ? y : x) });
    expect(s(diff(h(x, y), x))).toBe('y');
  });
  it('prints LaTeX, expands and evaluates by default', () => {
    expect(latex(myf(x))).toBe('\\operatorname{myf}{\\left(x \\right)}');
    expect(latex(defineFunction('h')(x, y))).toBe('h{\\left(x,y \\right)}');
    expect(s(expand(myf(x), { twice: true }))).toBe('myf(x)');
    // myf(x).rewrite(cos) -> myf(x)
    expect(s(rewrite(myf(x), 'cos'))).toBe('myf(x)');
    // no numeric implementation: the call stays (SymPy keeps myf(1); symjs evalf also evaluates the arguments)
    expect(s(evalf(myf(1)))).toBe('myf(1.0)');
    const inv = implementedFunction('inv', (t) => 1 / t);
    expect(s(evalf(inv(x)))).toBe('inv(x)');
    // a non-finite value is not a Float: the call stays
    expect(s(evalf(inv(0)))).toBe('inv(0)');
  });
});

describe('sympify of containers', () => {
  it('converts the expressions in arrays and keeps other values', () => {
    const r = sympify([1, 2n, null, 'a', true, [3]]) as unknown[];
    expect(r.map((v) => (typeof v === 'object' && v !== null && !Array.isArray(v) ? s(v) : v))).toEqual(['1', '2', null, 'a', true, r[5]]);
    expect((r[5] as unknown[]).map(s)).toEqual(['3']);
  });
  it('rejects values that are not expressions', () => {
    expect(() => sympify(null as never)).toThrow(SympifyError);
    expect(() => sympify(undefined as never)).toThrow(SympifyError);
    expect(() => sympify('x' as never)).toThrow(SympifyError);
  });
});

describe('number utilities', () => {
  it('rejects strings without digits', () => {
    for (const t of ['', '.', '+', 'e5', '-.e3']) expect(() => rationalFromString(t)).toThrow(SyntaxError);
  });
  it('protects escaped separators from a private-use character in the name', () => {
    // symbols('a\\,b') is one symbol named 'a,b'
    expect(expandSymbolNames('a\\,b')).toEqual(['a,b']);
  });
});

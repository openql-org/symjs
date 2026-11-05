// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/solvers/solve.ts: solve, solveLinear, invertEquation, nonlinsolve, nsolve and solveUndeterminedCoeffs; expected values from SymPy 1.14.


import { describe, expect, it } from 'vitest';
import type { Assumptions } from '../../src/core/nodes';
import { detQuick, diff, type Expr, invQuick, Matrix, nonlinsolve, solveLinearSystemLU, NotImplementedError, nsolve, parse, solve, solveLinear, solveUndeterminedCoeffs, sstr, Sym, symbols, SymFunction } from '../../src';
import { xreplace } from '../../src/core/traverse';
import { invertEquation, nonlinsolve as nonlinsolveCoordinates } from '../../src/solvers/solve';
import { at } from '../../src/core/guard';

const [x, y] = symbols('x y');
const show = (r: readonly Expr[]): string => `[${r.map(String).join(', ')}]`;
it('inverts shifted exponentials and hyperbolic functions (SymPy 1.14)', () => {
  for (const [source, expected] of [
    ['exp(2*x+1)-3', '[-1/2 + log(3)/2, -1/2 + log(3)/2 + I*pi]'],
    ['log(cosh(x))-1', '[log(E - sqrt(-1 + exp(2))), log(sqrt(-1 + exp(2)) + E)]'],
    ['log(cosh(x))', '[0]'],
    ['asinh(x)-2', '[sinh(2)]'], ['acosh(x)-2', '[cosh(2)]'], ['atanh(x)-2', '[tanh(2)]'],
    ['sinh(x)-2', '[log(-2 + sqrt(5)) + I*pi, log(2 + sqrt(5))]'],
    ['asinh(x)-2*I', '[]'],
  ] as const) expect(show(solve(parse(source), x))).toBe(expected);
});
it.each([
  ['z-x-y', 'x*y-1', 'x**2+y**2-5'],
  ['z-x-y', 'x**2+y**2-1', 'x**2-y**2'],
])('back-substitutes a nonlinear eliminant into a previously eliminated coordinate: %s', (...sources) => {
  const z = new Sym('z');
  const equations = sources.map((e) => parse(e));
  const variables = [z, x, y];
  const solutions = nonlinsolveCoordinates(equations, variables);
  // Both plane systems have four real solutions, with z determined by x+y.
  expect(solutions).toHaveLength(4);
  for (const values of solutions) for (const equation of equations) {
    expect(equation.subs(variables.map((v, i): [Expr, Expr] => [v, at(values, i)])).evalf(25).toNumber()).toBeCloseTo(0, 12);
  }
});
const pair = (r: readonly [Expr, Expr]): string => `(${String(r[0])}, ${String(r[1])})`;
/** Parse a bracketed list "[a, b]" split at the top-level commas. */
const parseList = (src: string): Expr[] => {
  const parts: string[] = [];
  let depth = 0;
  let cur = '';
  for (const ch of src.trim().slice(1, -1)) {
    if (ch === '(' || ch === '[') depth++;
    if (ch === ')' || ch === ']') depth--;
    if (ch === ',' && depth === 0) {
      parts.push(cur);
      cur = '';
    } else cur += ch;
  }
  parts.push(cur);
  return parts.map((p) => parse(p));
};
const syms = (src: string): Sym[] => parseList(src).map((e) => (e instanceof Sym ? e : new Sym(String(e))));
const SOLVE: [string, Assumptions, string][] = [
  ['exp(-x) + y + 1', {}, '[log(-1/(y + 1))]'],
  ['x**5 - x + 1', {}, '[CRootOf(x**5 - x + 1, 0), CRootOf(x**5 - x + 1, 1), CRootOf(x**5 - x + 1, 2), CRootOf(x**5 - x + 1, 3), CRootOf(x**5 - x + 1, 4)]'],
  ['y*sin(x)', {}, '[0, pi]'],
  ['(x - 1)/(x + sin(y)**2 + cos(y)**2)', {}, '[1]'],
  ['Eq(x**2, 4)', {}, '[-2, 2]'],
  ['x**2 - 4', { positive: true }, '[2]'],
  ['x**2 - 1', { negative: true }, '[-1]'],
  ['x**2 - 1', { nonpositive: true }, '[-1]'],
  ['x**2 - 2', { integer: true }, '[]'],
  ['x**2 - 4', { integer: true }, '[-2, 2]'],
  ['x*(x - 1)', { zero: false }, '[1]'],
  ['x*(x + 1)', { nonpositive: true }, '[-1, 0]'],
  ['x - y', { integer: true }, '[y]'],
  ['x**2 - 4', { nonnegative: true }, '[2]'],
  ['x**2 + 1', { real: true }, '[]'],
  ['2*x - 1', { integer: true }, '[]'],
  ['(x**2 - 1)/(x - 1)', {}, '[-1]'],
  ['exp(-x) - 2', {}, '[-log(2)]'],
  ['exp(-x) - y', {}, '[log(1/y)]'],
  ['x**y - 2', {}, '[2**(1/y)]'],
  ['tan(x) - 2', {}, '[atan(2)]'],
  ['2*tan(x) - y', {}, '[atan(y/2)]'],
  ['y - 3', {}, '[]'],
  ['x*(x - 1)*sin(x)', {}, '[0, 1, pi]'],
  ['sqrt(x) + 2', {}, '[]'],
  ['sqrt(x) - 3', {}, '[9]'],
  ['x**(1/3) - 2', {}, '[8]'],
  ['x**(1/5) + x**(1/3) - 2', {}, '[1]'],
  ['x*exp(x) - 1', {}, '[LambertW(1)]'],
  ['x + exp(x)', {}, '[-LambertW(1)]'],
  ['x - exp(-x)*a', {}, '[LambertW(a)]'],
  ['(x + 1)*exp(x) + 3', {}, '[-1 + LambertW(-3*E)]'],
  ['x*exp(x) + 1/(4*E)', {}, '[LambertW(-exp(-1)/4), LambertW(-exp(-1)/4, -1)]'],
  ['sin(x) + cos(x)', {}, '[-pi/4]'],
  ['sin(2*x) - 3*cos(2*x)', {}, '[atan(3)/2]'],
  ['log(x) - 2', {}, '[exp(2)]'],
  ['cos(x) - y', {}, '[-acos(y) + 2*pi, acos(y)]'],
  ['sqrt(x + 1) - x', {}, '[1/2 + sqrt(5)/2]'],
  ['x**(-1) - 2', {}, '[1/2]'],
  ['1/x', {}, '[]'],
  ['x**2 - 2*x + 1', {}, '[1]'],
  ['(x - 1)**2', {}, '[1]'],
  ['(sin(x) - 1/2)**3', {}, '[pi/6, 5*pi/6]'],
  ['1/x + sin(y)**2 + cos(y)**2 - 1', {}, '[]'],
  ['x*exp(x) + exp(x)', {}, '[-1]'],
  ['x**(-1/2) - 2', {}, '[1/4]'],
  ['x**(1/7) - 2', {}, '[128]'],
  ['x*exp(x) + 2', {}, '[LambertW(-2)]'],
  ['x*exp(2*x) + exp(x)', {}, '[LambertW(-1)]'],
  ['sin(x) + cos(y)', {}, '[asin(cos(y)) + pi, -asin(cos(y))]'],
  ['3*sin(x) + cos(x)', {}, '[-atan(1/3)]'],
  ['x*exp(y*x) + 1', {}, '[LambertW(-y)/y]'],
];
const SOLVE_NO_SYMBOL: [string, string][] = [
  ['3', '[]'],
  ['x - 3', '[3]'],
];
const SOLVE_FOR_EXPR: [string, string][] = [
  ['x + y + 2*a | x + y', '[-2*a]'],
  ['sin(x + y) - 1 | x + y', '[pi/2]'],
  ['x - 1 | x + 1', '[2]'],
  ['x + y + 2*a + 1 | x + y', '[-2*a - 1]'],
  ['x + 3 | 2*y', '[]'],
];
const SOLVE_LINEAR: [string, { symbols?: string[]; exclude?: string[] }, string][] = [
  ['y + sin(x)**2 + cos(x)**2', {}, '(y, -sin(x)**2 - cos(x)**2)'],
  ['x*(sin(y)**2 + cos(y)**2) + z', {}, '(z, -x*sin(y)**2 - x*cos(y)**2)'],
  ['x*(sin(y)**2 + cos(y)**2)', {}, '(0, 1)'],
  ['x - 2', {}, '(x, 2)'],
  ['x + y - 2', {}, '(x, 2 - y)'],
  ['x**2 - 1', {}, '(x**2 - 1, 1)'],
  ['0', {}, '(0, 1)'],
  ['x - x', {}, '(0, 1)'],
  ['y/x - 1', {}, '(x, y)'],
  ['x*y + 1', {}, '(x, -1/y)'],
  ['x + y', { symbols: ['y'] }, '(y, -x)'],
  ['x + y', { exclude: ['x'] }, '(y, -x)'],
  ['x + y', { exclude: ['x', 'y'] }, '(0, 1)'],
  ['x**2 + y', {}, '(y, -x**2)'],
  ['1/(1/x - y)', {}, '(0, 0)'],
  ['x/(x - 1) - 1', {}, '(0, 1)'],
  ['Eq(x, 3)', {}, '(x, 3)'],
  ['x**2*y + x', {}, '(y, -1/x)'],
  ['x*exp(y) - 1', {}, '(x, exp(-y))'],
];
const INVERT: [string, string[], boolean, string][] = [
  ['x*y - 2', ['x', 'y'], false, '(2, x*y)'],
  ['2*x*y - 2', ['x', 'y'], false, '(1, x*y)'],
  ['x - 3', [], false, '(3, x)'],
  ['2*x + 3', ['x'], false, '(-3/2, x)'],
  ['y', ['x'], false, '(y, 0)'],
  ['log(x) - 3', ['x'], false, '(exp(3), x)'],
  ['exp(x) - 3', ['x'], false, '(log(3), x)'],
  ['1/x - 3', ['x'], false, '(1/3, x)'],
  ['x**2 - 4', ['x'], true, '(2, x)'],
  ['x**2 - 4', ['x'], false, '(4, x**2)'],
  ['(x + y)**(1/3) - 2', ['x', 'y'], false, '(8, x + y)'],
  ['sqrt(x) - 2', ['x'], false, '(2, sqrt(x))'],
  ['2*exp(x + 1) - 4', ['x'], false, '(-1 + log(2), x)'],
  ['sin(x) - 1', ['x'], false, '(1, sin(x))'],
];
const NONLINSOLVE: [string, string, string][] = [
  ['[x**2 - 1, y - x*z]', '[x, y]', '[[-1, -z], [1, z]]'],
  ['[x*y - 1, x - 2]', '[x, y]', '[[2, 1/2]]'],
  ['[x**2 - 1, y - x]', '[x, y]', '[[-1, -1], [1, 1]]'],
  ['[x*y, x]', '[x, y]', '[[0, y]]'],
  ['[x**2 - 2, y**2 - 3]', '[x, y]', '[[-sqrt(2), -sqrt(3)], [-sqrt(2), sqrt(3)], [sqrt(2), -sqrt(3)], [sqrt(2), sqrt(3)]]'],
  ['[x**2 + y**2 - 4, x**2 - y**2 - 1]', '[x, y]', '[[-sqrt(10)/2, -sqrt(6)/2], [-sqrt(10)/2, sqrt(6)/2], [sqrt(10)/2, -sqrt(6)/2], [sqrt(10)/2, sqrt(6)/2]]'],
  ['[x**2 - 1, x**3 - 2]', '[x]', '[]'],
  ['[x**2 - 1, x**3 + 1, y**2 - 4]', '[x, y]', '[[-1, -2], [-1, 2]]'],
  ['[x**2 + y**2 - 5, x**2 - 1]', '[x, y]', '[[-1, -2], [-1, 2], [1, -2], [1, 2]]'],
  ['[sqrt(x) - y, x - 4]', '[x, y]', '[[4, 2]]'],
  ['[sqrt(x) + sqrt(y) - 3, x - y]', '[x, y]', '[[9/4, 9/4]]'],
  ['[y - sin(sqrt(x)), x - 4]', '[x, y]', '[[4, sin(2)]]'],
  ['[x**(1/7) - y, x - 1]', '[x, y]', '[[1, 1]]'],
  ['[x + y - 1, x - y]', '[x, y]', '[[1/2, 1/2]]'],
  ['[x + y - 1, x + y]', '[x, y]', '[]'],
  ['[x*y - 1, x*y - 2]', '[x, y]', '[]'],
  ['[x/(x - 1) - y, y - 2]', '[x, y]', '[[2, 2]]'],
  ['[x**2 - x, x*y - 1]', '[x, y]', '[[1, 1]]'],
];
const UNDETERMINED: [string, string, string[], string][] = [
  ['a*exp(x)', '[a]', ['x'], '{a: 0}'],
  ['a*x + b - 2*x - 3', '[a, b]', ['x'], '{a: 2, b: 3}'],
  ['a*exp(x) + b*x - 2*exp(x) - x', '[a, b]', ['x'], '{a: 2, b: 1}'],
  ['a*x**2 + b*x*y + c - x**2 - 1', '[a, b, c]', ['x', 'y'], '{a: 1, b: 0, c: 1}'],
  ['(a - 1)*exp(x)', '[a]', ['x'], '{a: 1}'],
  ['a*x + sqrt(x) - x', '[a]', ['x'], '[]'],
];
const NSOLVE: [string, number | string | [number, number], number | undefined, string][] = [
  ['x**2 - 2', 1, undefined, '1.41421356237310'],
  ['cos(x) - x', [0, 1], undefined, '0.739085133215161'],
  ['x**2 - 2', [0, 2], undefined, '1.41421356237310'],
  ['x - 1/2', [0, 1], undefined, '0.500000000000000'],
  ['x**2 + 1', 'I', undefined, '1.0*I'],
  ['x**3', 0, undefined, '0'],
  ['x**2 - 2', 1, 30, '1.41421356237309504880168872421'],
  ['x**2', 0, 30, '0'],
];
const sol = (s: string) => show(solve(parse(s), x));

describe('solve (SymPy solve)', () => {
  it.each(SOLVE)('solve(%s) with assumptions %o', (src, assumptions, expected) => {
    const v = new Sym('x', assumptions);
    expect(show(solve(xreplace(parse(src), [[x, v]]), v))).toBe(expected);
  });
  it.each(SOLVE_NO_SYMBOL)('solve(%s) without a symbol', (src, expected) => {
    expect(show(solve(parse(src)))).toBe(expected);
  });
  it.each(SOLVE_FOR_EXPR)('solve for an expression: %s', (src, expected) => {
    const [e, target] = src.split(' | ');
    expect(show(solve(parse(e ?? ''), parse(target ?? '')))).toBe(expected);
  });
  it('cubics=False gives CRootOf', () => {
    expect(show(solve(parse('x**3 - x - 1'), x, { cubics: false }))).toBe('[CRootOf(x**3 - x - 1, 0), CRootOf(x**3 - x - 1, 1), CRootOf(x**3 - x - 1, 2)]');
    expect(show(solve(parse('x**3 + a*x + 1'), x, { cubics: false }))).toBe('[]');
  });
  it('solves for a derivative, leaving the other derivatives alone', () => {
    const f = SymFunction('f');
    expect(show(solve(parse('2*Derivative(f(x), x) - x + Derivative(f(x), x, x)'), diff(f(x), x)))).toBe('[x/2 - Derivative(f(x), (x, 2))/2]');
  });
  it('requires the symbol when there are several', () => {
    expect(() => solve(parse('x + y'))).toThrow(TypeError);
  });
  it('raises NotImplementedError like SymPy', () => {
    for (const src of ['gamma(x) - 2', 'x + exp(x) + exp(2*x)', 'x*sin(x) + cos(x)', 'sqrt(x)*sin(x) - 1', 'y*(x + sin(x)) + 1', 'gamma(sqrt(x))', 'sin(x)*exp(x) + x']) {
      expect(() => solve(parse(src), x)).toThrow(NotImplementedError);
    }
  });
});

describe('solveLinear (SymPy solve_linear)', () => {
  it.each(SOLVE_LINEAR)('solve_linear(%s, %o)', (src, opts, expected) => {
    const o = {
      ...(opts.symbols ? { symbols: opts.symbols.map((s) => new Sym(s)) } : {}),
      ...(opts.exclude ? { exclude: opts.exclude.map((s) => new Sym(s)) } : {}),
    };
    expect(pair(solveLinear(parse(src), o))).toBe(expected);
  });
});

describe('invertEquation (SymPy _invert)', () => {
  it.each(INVERT)('_invert(%s, %o, integer_power=%s)', (src, symbols, integerPower, expected) => {
    expect(pair(invertEquation(parse(src), symbols.map((s) => new Sym(s)), { integerPower }))).toBe(expected);
  });
});

describe('nonlinsolve', () => {
  it.each(NONLINSOLVE)('nonlinsolve(%s, %s)', (eqs, vars, expected) => {
    const r = nonlinsolve(parseList(eqs), syms(vars)).map(show).sort();
    expect(`[${r.join(', ')}]`).toBe(expected);
  });
});

describe('nonlinsolve with a parametric radical solution', () => {
  it('keeps x = y**2 for sqrt(x) = y', () => {
    // SymPy 1.14 returns EmptySet, which is wrong: (4, 2) is a solution. The
    // parametric solution (y**2, y) holds wherever sqrt(y**2) = y.
    expect(nonlinsolve([parse('sqrt(x) - y')], [x, new Sym('y')]).map(show)).toEqual(['[y**2, y]']);
  });
});

describe('solveUndeterminedCoeffs', () => {
  it.each(UNDETERMINED)('solve_undetermined_coeffs(%s, %s, %o)', (src, coeffs, vars, expected) => {
    const cs = syms(coeffs);
    const r = solveUndeterminedCoeffs(parse(src), cs, vars.map((s) => new Sym(s)));
    const got = r.length === 0 ? '[]' : `{${cs.map((c, i) => `${String(c)}: ${String(r[0]?.[i])}`).join(', ')}}`;
    expect(got).toBe(expected);
  });
});

describe('nsolve', () => {
  it.each(NSOLVE)('nsolve(%s, x, %o, prec=%s)', (src, x0, prec, expected) => {
    const start = Array.isArray(x0) ? x0 : typeof x0 === 'string' ? parse(x0) : x0;
    expect(String(nsolve(parse(src), x, start, prec === undefined ? {} : { prec }))).toBe(expected);
  });
  it('a bracket without a sign change is an error (SymPy ValueError)', () => {
    expect(() => nsolve(parse('x**2 - 2'), x, [2, 3])).toThrow(RangeError);
  });
});

// expected values from SymPy 1.14 solve / nonlinsolve; comments mark where symjs differs
describe('solve', () => {
  it('a power of a function of x: its base is an n-th root', () => {
    expect(sol('sin(x)**2 - 1/4')).toBe('[-pi/6, pi/6, 5*pi/6, 7*pi/6]');
    expect(sol('sin(x)**(-2) - 4')).toBe('[-pi/6, pi/6, 5*pi/6, 7*pi/6]');
  });
  it('a power of a radical or a logarithm', () => {
    expect(sol('(sqrt(x) + 1)**2 - 4')).toBe('[1]');
    expect(sol('log(x)**3 - 8')).toBe('[exp(2), exp(-1 - sqrt(3)*I), exp(-1 + sqrt(3)*I)]');
  });
  it('radicals', () => {
    // the seventh root is solved through the substitution x + 1 = t**7 (SymPy: [127])
    expect(sol('(x + 1)**(1/7) - 2')).toBe('[127]');
    expect(sol('x**(1/61) - 2')).toBe('[2305843009213693952]');
    expect(sol('1/sqrt(x) - 2')).toBe('[1/4]');
    expect(sol('sqrt(x) + x**(-1/3)')).toBe('[]');
    // the lcm 122 of the root indices is beyond the substitution limit (SymPy does not finish)
    expect(() => sol('x**(1/61) + sqrt(x) - 2')).toThrow(NotImplementedError);
  });
  it('radicals of index above 6', () => {
    // SymPy: [0]; beyond SymPy unrad's degree limit the linear radicand x + 1 = y is the variable
    expect(sol('(x + 1)**(1/7) + x - 1')).toBe('[0]');
    // SymPy: [-1/2]
    expect(sol('(2*x + 1)**(1/7) + 2*x + 1')).toBe('[-1/2]');
    // SymPy: [1/y]
    expect(show(solve(parse('(x*y)**(1/7) + x*y - 2'), x))).toBe('[1/y]');
    // a radicand that is not a polynomial (SymPy: NotImplementedError)
    expect(() => sol('(exp(x) + 1)**(1/7) + x - 1')).toThrow(NotImplementedError);
  });
  it('a seventh root of a quadratic', () => {
    // a radicand of degree 2: the polynomial (x**2 + 1) - (1 - x)**7, its roots checked numerically (SymPy: [0])
    expect(sol('(x**2 + 1)**(1/7) + x - 1')).toBe('[0]');
  });
  it('Lambert W forms', () => {
    expect(sol('x*exp(x) - 1')).toBe('[LambertW(1)]');
    // the constant term vanishes: (x + 1)*exp(x) = 0
    expect(sol('x*exp(x) + exp(x)')).toBe('[-1]');
    // the logarithm of both sides, x**2 giving 2*log(x) and 2*log(-x) (SymPy bivariate._solve_lambert)
    expect(sol('x**2*exp(x) - 1')).toBe('[2*LambertW(-1/2), 2*LambertW(1/2)]');
    // SymPy: NotImplementedError as well
    expect(() => sol('x + exp(x**2)')).toThrow(NotImplementedError);
  });
  it('equations out of reach', () => {
    // SymPy: [] (no formula for a symbolic quintic)
    expect(() => sol('x**5 + y*x + 1')).toThrow(NotImplementedError);
    // 42 nested exponentials exceed the recursion depth
    const tower = (n: number, f: string, x0: string) => Array.from({ length: n }).reduce<string>((e) => `${f}(${e})`, x0);
    expect(() => sol(`${tower(42, 'exp', 'x')} - 2`)).toThrow(NotImplementedError);
  });
  it('nested exponentials', () => {
    // 13 levels (SymPy does not finish within a minute; exp applied 13 times to the result gives 2)
    const tower = (n: number, f: string, x0: string) => Array.from({ length: n }).reduce<string>((e) => `${f}(${e})`, x0);
    expect(sol(`${tower(13, 'exp', 'x')} - 2`)).toBe(`[${String(parse(tower(13, 'log', '2')))}]`);
  });
  it('Lambert W forms through logarithms (SymPy bivariate._solve_lambert)', () => {
    // B**B = R
    expect(sol('x**x - 2')).toBe('[exp(LambertW(log(2)))]');
    expect(sol('x**x - 1/2')).toBe('[exp(LambertW(-log(2)))]');
    expect(sol('(2*x)**(2*x) - 3')).toBe('[exp(LambertW(log(3)))/2]');
    // a*log(b*x + c) + d*x + f = 0
    expect(sol('log(x) + x')).toBe('[LambertW(1)]');
    expect(sol('x - 2*log(x) - 3')).toBe('[-2*LambertW(-exp(-3/2)/2), -2*LambertW(-exp(-3/2)/2, -1)]');
    expect(sol('3*log(x) - x')).toBe('[-3*LambertW(-1/3), -3*LambertW(-1/3, -1)]');
    // the p-th roots of exp(A) give p arguments (SymPy: 3*LambertW(2**(1/3)/3),
    // 3*LambertW(2**(1/3)*(-1 - sqrt(3)*I)/6), 3*LambertW(2**(1/3)*(-1 + sqrt(3)*I)/6))
    expect(sol('x**3*exp(x) - 2')).toBe('[3*LambertW(2**(1/3)/3), 3*LambertW(-2**(1/3)/6 - 2**(1/3)*sqrt(3)*I/6), 3*LambertW(-2**(1/3)/6 + 2**(1/3)*sqrt(3)*I/6)]');
    expect(sol('x**2*2**x - 3')).toBe('[2*LambertW(-sqrt(3)*log(2)/2)/log(2), 2*LambertW(sqrt(3)*log(2)/2)/log(2)]');
    // g*p**u + R(x) = c. SymPy omits the k = -1 branch, whose argument -log(2)/8 is in (-1/e, 0):
    // that branch is the second real solution (2**x = x + 3 at x = 2.44...)
    expect(sol('2**x - x - 3')).toBe('[-3 - LambertW(-log(2)/8)/log(2), -3 - LambertW(-log(2)/8, -1)/log(2)]');
    // SymPy: [-1/2 - LambertW(-sqrt(3)*log(3)/6)/log(3)], which is 0; the k = -1 branch gives the other real solution 1
    expect(sol('3**x - 2*x - 1')).toBe('[-1/2 - LambertW(-sqrt(3)*log(3)/6)/log(3), -1/2 - LambertW(-sqrt(3)*log(3)/6, -1)/log(3)]');
    expect(sol('x**y*exp(x) - 2')).toBe('[y*LambertW(exp(log(2)/y)/y)]');
    expect(sol('sqrt(x)*exp(x) - 1')).toBe('[LambertW(2)/2]');
    // SymPy: [(-log(8) - LambertW(-log(2**(3/8))))/log(2)]; the k = -1 branch is the other real solution
    expect(sol('3*2**x - x - 3')).toBe('[(-log(8) - LambertW(-log(2**(3/8))))/log(2), (-log(8) - LambertW(-log(2**(3/8)), -1))/log(2)]');
    // SymPy: [1] for both; the LambertW forms equal 1 (W(z*exp(z)) = z for z = 1/(2*log(2)) and 1/log(2))
    expect(sol('2*log(2)*log(x) + x - 1')).toBe('[2*log(2)*LambertW(exp(1/(2*log(2)))/(2*log(2)))]');
    expect(sol('log(2)*log(x) + x - 1')).toBe('[log(2)*LambertW(exp(1/log(2))/log(2))]');
    // SymPy: [0, -1 + 2*LambertW(-exp(1/2)/2)]; -1 + 2*LambertW(exp(1/2)/2) is 0 (W(exp(1/2)/2) = 1/2)
    expect(sol('(x + 1)**2*exp(x) - 1')).toBe('[-1 + 2*LambertW(-exp(1/2)/2), -1 + 2*LambertW(exp(1/2)/2)]');
    // two even powers of different bases (SymPy: NotImplementedError)
    expect(() => sol('x**2*(x + 1)**2*exp(x) - 1')).toThrow(NotImplementedError);
    // a*x*log(x) + d*x + f = 0 through X = log(x) (SymPy: [1], [exp(LambertW(2))], [exp(-1 + LambertW(E*log(2)))])
    expect(sol('x*log(x) + x - 1')).toBe('[1]');
    expect(sol('x*log(x) - 2')).toBe('[exp(LambertW(2))]');
    expect(sol('x*log(x) + x')).toBe('[exp(-1)]');
    // after the logarithm, x*log(x) + x = 0; SymPy also gives 0, with its convention 0**0 = 1
    expect(sol('x**x*exp(x) - 1')).toBe('[exp(-1)]');
    expect(sol('x**x*exp(x) - 2')).toBe('[exp(-1 + LambertW(E*log(2)))]');
    // SymPy: NotImplementedError (x*log(x) with another log(x) term)
    expect(() => sol('x*log(x) + x - log(x)')).toThrow(NotImplementedError);
    // forms out of reach (SymPy: [] for x**x + x, NotImplementedError for the others)
    expect(() => sol('x**x + x')).toThrow(NotImplementedError);
    expect(() => sol('x**2*sin(x) - 1')).toThrow(NotImplementedError);
    expect(() => sol('2**x + 3**x - x - 3')).toThrow(NotImplementedError);
    expect(() => sol('log(x**2 + 1) + x')).toThrow(NotImplementedError);
    expect(() => sol('log(x) + log(x + 1) + x')).toThrow(NotImplementedError);
  });
});

describe('nonlinsolve', () => {
  it('an equation solved with LambertW', () => {
    // SymPy: {(x, 1)}, which leaves x free although x*exp(x) = 1 fixes it; exp(W(1))*W(1) = 1
    expect(nonlinsolve([parse('x*exp(x) - y'), parse('y - 1')], [x, y]).map(show)).toEqual(['[LambertW(1), 1]']);
  });
  it('a single radical that is the whole equation', () => {
    expect(nonlinsolve([parse('sqrt(x)'), parse('y - 1')], [x, y]).map(show)).toEqual(['[0, 1]']);
  });
  it('a solution that cannot be evaluated is kept', () => {
    // SymPy: {(ConditionSet(x, Eq(sqrt(x) - g(1), 0), {g(1)**2}),)}
    expect(nonlinsolve([parse('sqrt(x) - g(1)')], [x]).map(show)).toEqual(['[g(1)**2]']);
  });
  it('unsupported systems', () => {
    // SymPy: {(-cos(y), y)}, which does not solve sin(x) + x*y = 0
    expect(() => nonlinsolve([parse('sin(x) + x*y'), parse('cos(y) + x')], [x, y])).toThrow(NotImplementedError);
  });
});

describe('solveLinear', () => {
  it('a derivative whose free symbols are the symbols but which does not change with them', () => {
    const pr = (r: readonly [Expr, Expr]) => `(${String(r[0])}, ${String(r[1])})`;
    expect(pr(solveLinear(parse('x*(sin(x)**2 + cos(x)**2 + sin(y)**2 + cos(y)**2) - 1'), { symbols: [x, y] }))).toBe(
      '(x*(sin(x)**2 + sin(y)**2 + cos(x)**2 + cos(y)**2) - 1, 1)',
    );
    expect(pr(solveLinear(parse('x*(sin(y)**2 + cos(y)**2) - 1'), { symbols: [x] }))).toBe('(0, 1)');
  });
});

describe('LambertW (SymPy)', () => {
  it('solves equations of Lambert type', () => {
    expect(String(solve(parse('x + exp(x)'), x))).toBe('-LambertW(1)');
    expect(String(solve(parse('2*x + 3 - exp(-x)'), x))).toBe('-3/2 + LambertW(exp(3/2)/2)');
    expect(String(solve(parse('x + exp(x/2)/4'), x))).toBe('-2*LambertW(1/8)');
  });
});

describe('solve with radicals', () => {
  it('isolates one radical and checks the candidates', async () => {
    const { solve } = await import('../../src');
    const x = symbols('x')[0];
    const show = (s: string, opts = {}) => solve(parse(s), x, opts).map((e) => sstr(e));
    expect(show('sqrt(x + 1) - x + 1')).toEqual(['3']);
    expect(show('x**(2/3) - 4')).toEqual(['8']);
    expect(show('sqrt(x) + 1')).toEqual([]);
    expect(show('-x + (x**3 - 3*x**2)**(1/3) + 1')).toEqual([]);
    expect(show('-x + (x**3 - 3*x**2)**(1/3) + 1', { check: false })).toEqual(['1/3']);
  });
});

describe('nonlinsolve and undetermined coefficients', () => {
  it('handle radicals, polynomial systems and non-polynomial terms', async () => {
    const { nonlinsolve, solveUndeterminedCoeffs } = await import('../../src');
    const [x, y] = symbols('x y', { real: true });
    const P = (s: string) => parse(s, { symbols: { x, y } } as never);
    const show = (r: unknown[][]) => r.map((t) => '(' + t.map((e) => sstr(e as never)).join(', ') + ')').join(' ');
    expect(show(nonlinsolve([P('sqrt(x**2+y**2)-10'), P('sqrt(y**2+(10-x)**2)-3')], [x, y]))).toBe('(191/20, -3*sqrt(391)/20) (191/20, 3*sqrt(391)/20)');
    const [a, b, c, u, v] = symbols('a b c u v');
    const eq = parse('-v - 2*u**v + a*v + b*u**v - 3*v*u**v + c*v*u**v', { symbols: { a, b, c, u, v } } as never);
    expect(show(solveUndeterminedCoeffs(eq, [a, b, c], [u, v]))).toBe('(1, 2, 3)');
  });
});

describe('solve with several logarithms of the unknown', () => {
  it('combines c_i*log(g_i) with rational c_i (SymPy)', () => {
    // SymPy: [(-x**2 - exp(2*C1))/(x**2 - exp(2*C1))]
    expect(show(solve(parse('C1 - log(x) + log(y - 1)/2 - log(y + 1)/2'), y))).toBe('[-(x**2 + exp(2*C1))/((x - exp(C1))*(x + exp(C1)))]');
    expect(show(solve(parse('log(y) + log(y + 1) - 1'), y))).toBe('[-1/2 + sqrt(1 + 4*E)/2]');
  });
  it('counts c*y as c*log(exp(y))', () => {
    // SymPy raises NotImplementedError; exp(y) = 2 - 2*exp(-2*C1)/(2*x + 1) solves it
    expect(show(solve(parse('C1 + y/2 + log(exp(-y) - 1/2)/2 + log(2*x + 1)/2'), y))).toBe('[log(2 - 2*exp(-2*C1)/(2*x + 1))]');
  });
  it('needs rational coefficients (SymPy NotImplementedError as well)', () => {
    expect(() => solve(parse('log(y) + x*log(y + 1) - 1'), y)).toThrow(NotImplementedError);
    expect(() => solve(parse('log(y) + sin(y)'), y)).toThrow(NotImplementedError);
  });
});

describe('solve: polynomials in a single generator (SymPy _solve)', () => {
  const sv = (s: string): string => show(solve(parse(s), y));
  it('a function application', () => {
    expect(sv('cos(y)**2 + cos(y) - 1')).toBe('[2*pi - acos(-sqrt(5)/2 - 1/2), -acos(-1/2 + sqrt(5)/2) + 2*pi, acos(-1/2 + sqrt(5)/2), acos(-sqrt(5)/2 - 1/2)]');
    expect(sv('tan(y/2)**2 - 1')).toBe('[-pi/2, pi/2]');
    expect(sv('sin(y)**2 + sin(y)')).toBe('[0, -pi/2, pi, 3*pi/2]');
    expect(sv('log(y)**2 - 1')).toBe('[E, exp(-1)]');
    expect(sv('C1 + x + 1/tan((x - y)/2)')).toBe('[x + 2*atan(1/(C1 + x))]');
    // SymPy: [-acos(-(exp(2*C1) + exp(2*x))/(exp(2*C1) - exp(2*x))) + 2*pi, acos((-exp(2*C1) - exp(2*x))/(exp(2*C1) - exp(2*x)))]
    expect(sv('x + log(cos(y) - 1)/2 - log(cos(y) + 1)/2 - C1')).toBe(
      '[-acos((-exp(2*C1) - exp(2*x))/(exp(2*C1) - exp(2*x))) + 2*pi, acos((-exp(2*C1) - exp(2*x))/(exp(2*C1) - exp(2*x)))]',
    );
    // SymPy: NotImplementedError as well
    expect(() => solve(parse('gamma(y)**2 - 1'), y)).toThrow(NotImplementedError);
  });
  it('exponentials with rational multiples of one exponent', () => {
    expect(sv('exp(2*y) + exp(y) - 2')).toBe('[0, log(2) + I*pi]');
    expect(sv('exp(y) - 2*exp(-y)')).toBe('[log(2)/2 + I*pi, log(2)/2]');
    expect(sv('exp(2*y) - 2')).toBe('[log(2)/2 + I*pi, log(2)/2]');
    expect(sv('exp(3*y) - 1')).toBe('[0, -2*I*pi/3, 2*I*pi/3]');
    expect(sv('exp(-2*y) - 3')).toBe('[-log(3)/2 + I*pi, -log(3)/2]');
    // SymPy: [(log(3)/2 + I*pi)/a, log(3)/(2*a)]
    expect(sv('exp(2*a*y) - 3')).toBe('[(log(3) + 2*I*pi)/(2*a), log(3)/(2*a)]');
    expect(sv('exp(y/2) - 3')).toBe('[log(9)]');
    expect(sv('exp(2*y) - exp(x)*exp(y)')).toBe('[log(exp(x))]');
    // SymPy: [0, log(-1/2 + sqrt(5)/2) + I*pi, log(1/2 + sqrt(5)/2)] (the same values)
    expect(sv('exp(-2*y) + exp(y) - 2')).toBe('[0, log(-1/2 + sqrt(5)/2) + I*pi, log(1/2 + sqrt(5)/2)]');
    // SymPy: multiple generators
    expect(() => solve(parse('cos(y) + exp(y)'), y)).toThrow(NotImplementedError);
    expect(() => solve(parse('exp(y) + exp(x*y) - 1'), y)).toThrow(NotImplementedError);
  });
  it('sums of logarithms with a common factor', () => {
    expect(sv('2*log(y) - 2')).toBe('[E]');
    expect(sv('2*log(y) - 2*log(x + 1) - 2')).toBe('[E*(x + 1)]');
  });
});

it('checks candidates exactly and does not accept a small nonzero residual', async () => {
  const { checksol, S, SymFunction, Rational } = await import('../../src');
  expect(checksol(parse('x**2 - 1'), x, 1)).toBe(true);
  expect(checksol(parse('Eq(x, 1)'), new Map([[x, S.One]]))).toBe(true);
  expect(checksol(parse('x**2 - 1'), x, 2)).toBe(false);
  expect(checksol(parse('1/x'), x, 0)).toBe(false);
  expect(checksol(x, x, Rational.of(1n, 10n ** 30n))).toBe(false);
  expect(checksol(SymFunction('f')(x), x, 1)).toBe('unknown');
  expect(checksol(parse('exp(x)'), x, 1)).toBe(false);
});

it('retains denominator and radical checks in larger elimination systems', () => {
  const [z] = symbols('z');
  expect(nonlinsolve([parse('(x**2 - 1)/x')], [x]).map(show)).toEqual(['[-1]', '[1]']);
  expect(nonlinsolve([parse('sqrt(x)'), parse('y - 1'), parse('z - 1')], [x, y, z]).map(show)).toEqual(['[0, 1, 1]']);
  expect(nonlinsolve([parse('y - sin(sqrt(x))'), parse('x - 4'), parse('z - 1')], [x, y, z]).map(show)).toEqual(['[4, sin(2), 1]']);
  expect(nonlinsolve([parse('x**(1/7) - y'), parse('x - 1'), parse('z - 1')], [x, y, z]).map(show)).toEqual(['[1, 1, 1]']);
});

describe('detQuick, invQuick and solveLinearSystemLU (SymPy solvers.py)', () => {
  const [z, a, b] = symbols('z a b');
  const M = (rows: (number | Expr)[][]) => Matrix.of(rows);
  it('detQuick', () => {
    expect(String(detQuick(M([[1, 2], [3, 4]])))).toBe('-2');
    expect(String(detQuick(M([[x, y], [z, a]])))).toBe('a*x - y*z');
    expect(String(detQuick(M([[x, 1, 0], [1, x, 1], [0, 1, x]])))).toBe('x**3 - 2*x');
    expect(String(detQuick(Matrix.fromFunction(4, 4, (i, j) => (i === j ? x : 0))))).toBe('x**4');
    expect(String(detQuick(Matrix.fromFunction(5, 5, (i, j) => ((i + j) % 2 ? i + j + 1 : x))))).toBe('0');
    expect(String(detQuick(M([[x]])))).toBe('x');
  });
  it('invQuick', () => {
    expect(String(invQuick(M([[1, 2], [3, 4]])))).toBe('Matrix([[-2, 1], [3/2, -1/2]])');
    expect(String(invQuick(M([[x, 1, 0], [1, x, 1], [0, 1, x]])))).toBe('Matrix([[(x**2 - 1)/(x**3 - 2*x), -x/(x**3 - 2*x), 1/(x**3 - 2*x)], [-x/(x**3 - 2*x), x**2/(x**3 - 2*x), -x/(x**3 - 2*x)], [1/(x**3 - 2*x), -x/(x**3 - 2*x), (x**2 - 1)/(x**3 - 2*x)]])');
    // SymPy returns Matrix([[0, 0], [0, 0]]): its det_minor of a 1 x 1 minor is 0
    expect(String(invQuick(M([[x, 1], [0, x]])))).toBe('Matrix([[1/x, -1/x**2], [0, 1/x]])');
    expect(String(invQuick(M([[x, y], [z, a]])))).toBe('Matrix([[a/(a*x - y*z), -y/(a*x - y*z)], [-z/(a*x - y*z), x/(a*x - y*z)]])');
    expect(String(invQuick(M([[x]])))).toBe('Matrix([[1/x]])');
    expect(() => invQuick(M([[x, 2 as number], [x, 2]]))).toThrow('Matrix det == 0; not invertible');
  });
  it('solveLinearSystemLU', () => {
    const show = (m: Map<Expr, Expr>) => [...m].map(([k, v]) => `${String(k)}: ${String(v)}`).join(', ');
    expect(show(solveLinearSystemLU(M([[1, 2, 0, 1], [3, 2, 2, 1], [2, 0, 0, 1]]), [x, y, z]))).toBe('x: 1/2, y: 1/4, z: -1/2');
    expect(show(solveLinearSystemLU(M([[a, 1, 2], [1, b, 3]]), [x, y]))).toBe('x: -b*(2 - 3*a)/(-a*b + 1) + 3, y: (2 - 3*a)/(-a*b + 1)');
    expect(() => solveLinearSystemLU(M([[1, 2, 3]]), [x, y])).toThrow('Rows should be equal to columns - 1');
  });
});

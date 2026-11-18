// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/solvers/solve.ts: solve, solveLinear, invertEquation, nonlinsolve, nsolve and solveUndeterminedCoeffs; expected values from SymPy 1.14.


import { describe, expect, it } from 'vitest';
import type { Assumptions } from '../../src/core/nodes';
import { checksol, detQuick, diff, type Expr, invQuick, isLinearSolveSystem, isNoMatch, Matrix, nonlinsolve, solveLinearSystemLU, NotImplementedError, nsolve, parse, solve, solveComplexComponents, solveForSymbols, solveLinear, solveRelation, solveSystem, solveUndeterminedCoeffs, solveVariables, sstr, Sym, symbols, SymFunction, CRootOf, Poly, evalf, toComplex, unrad } from '../../src';
import { xreplace } from '../../src/core/traverse';
import { invertEquation, nonlinsolve as nonlinsolveCoordinates } from '../../src/solvers/solve';
import { at } from '../../src/core/guard';
import { Fn, Piecewise, Pow, Rel, S } from '../../src/core/nodes';

const [x, y] = symbols('x y');
const show = (r: readonly Expr[]): string => `[${r.map(String).join(', ')}]`;
const showMaps = (rows: readonly Map<Expr, Expr>[]) => rows.map((row) => Object.fromEntries([...row].map(([key, value]) => [String(key), String(value)])));

it('solves implicit targets, zero bases and coupled radicals', () => {
  expect(show(solve(parse('x**2+x-3'), x, { implicit: true }))).toBe('[3 - x**2]');
  expect(show(solve(parse('x*f(x)+f(x)+2'), x, { implicit: true }))).toBe('[-(f(x) + 2)/f(x)]');
  expect(show(solve(parse('x**x'), x))).toBe('[]');
  expect(show(solve(parse('0**(x-2)-1'), x))).toBe('[2]');
  expect(show(solve(parse('f(x+1)-f(2*x-1)'), x))).toBe('[2]');
  expect(show(solve(parse('sqrt(x+1)+sqrt(x+6)-5'), x))).toBe('[3]');
  expect(isNoMatch(unrad(parse('-8*x**2/(9*(x**2-1)**(4/3)) + 4/(3*(x**2-1)**(1/3))')))).toBe(true);
  expect(isNoMatch(unrad(parse('x**2-1')))).toBe(true);
});

it('reduces mixed trigonometric, hyperbolic and logarithmic generators', () => {
  expect(solve(parse('sin(x)+tan(x)'), x)).toHaveLength(4);
  expect(solve(parse('sin(x)+sec(x)'), x)).toHaveLength(4);
  expect(solve(parse('cos(x)**2+sin(x)'), x)).toHaveLength(4);
  expect(solve(parse('2*cos(x)**3-sin(x)**3'), x)).toHaveLength(3);
  expect(solve(parse('sin(300*x)+sin(600*x)'), x)).toHaveLength(3);
  expect(solve(parse('tanh(x-1)*tanh(x+1)+1'), x)).toHaveLength(4);
  expect(solve(parse('tanh(x-3)*tanh(x+3)-1'), x)).toHaveLength(0);
  expect(show(solve(parse('sinh(x)+tanh(x)'), x))).toBe('[0, I*pi]');
  for (const equation of ['coth(x)+sinh(x)-29/12', 'sech(x)+sinh(x)-31/20', 'csch(x)+cosh(x)-31/12']) {
    expect(solve(parse(equation), x).map(String)).toContain('log(2)');
  }
  expect(show(solve(parse('atan2(x,2)-pi/3'), x))).toBe('[2*sqrt(3)]');
  expect(show(solve(parse('(3*x + log(x))**2 - 6*x - 2*log(x) + 1'), x))).toBe('[LambertW(3*E)/3]');
  const index = new Sym('y', { integer: true });
  expect(solve(parse('2*x**y-4*(x+1)**y').subs(y, index), index)).toHaveLength(1);
});

it('solves for inferred variables and real and imaginary components', () => {
  const factors = showMaps(solveForSymbols(parse('z**2*(x**2-y**2)'), [...parse('x+y+z').freeSymbols()]));
  expect(factors).toHaveLength(3);
  expect(factors).toEqual(expect.arrayContaining([{ z: '0' }, { x: '-y' }, { x: 'y' }]));
  const real = new Sym('x', { real: true }), imaginary = new Sym('y', { imaginary: true });
  const split = parse('x+y+3+2*I').subs(new Map([[x, real], [y, imaginary]]));
  expect(showMaps(solveForSymbols(split, [real, imaginary]))).toEqual([{ x: '-3', y: '-2*I' }]);
  const independent = [parse('f(1)-2'), parse('x+2')];
  expect(solveVariables(independent).map(String)).toEqual(['x', 'f(1)']);
  expect(isLinearSolveSystem(independent, solveVariables(independent))).toBe(true);
  expect(isLinearSolveSystem([parse('x**2-2')], [x])).toBe(false);
  const components = solveComplexComponents([parse('re(x)-1'), parse('im(x)-2')], x);
  if (!Array.isArray(components)) throw new TypeError('expected complex components');
  expect(showMaps(components)).toEqual([{ x: '1 + 2*I', 're(x)': '1', 'im(x)': '2' }]);
  expect(solveComplexComponents([parse('sqrt(re(x)**2+im(x)**2)-3')], x)).toHaveLength(1);
  expect(isNoMatch(solveComplexComponents([parse('x-2')], x))).toBe(true);
});

it('checks a numerical Lambert W residual and finite real inequalities', () => {
  const expression = parse('exp(LambertW(log(x))*exp(LambertW(log(x)))) - x');
  expect(checksol(expression, x, 2)).toBe(true);
  expect(checksol(expression, x, 2, { numerical: false })).toBe('unknown');
  expect(checksol(parse('exp(x)+sin(x)-1'), new Map())).toBe('unknown');
  expect(checksol(parse('f(x)-1'), x, 2)).toBe('unknown');
  const above = new Rel('Gt', parse('exp(2*x+2)*(exp(x)+x**2+2)/(exp(x)+2)**2'), S.Zero);
  expect(String(solveRelation(above))).toBe('(-oo < x) & (x < oo)');
  expect(String(solveRelation(new Rel('Ne', S.One, x), x))).toContain('Ne(x, 1)');
  expect(isNoMatch(solveRelation(new Rel('Gt', x, y), x))).toBe(true);
  expect(isNoMatch(solveRelation(new Rel('Eq', x, S.Zero)))).toBe(true);
});

it('validates rationalized systems and preserves compact exact algebraic solutions', () => {
  expect(solveSystem([parse('0.5*x+y-1'), parse('y-0.25')], [x, y], { rational: true }).map(show)).toEqual(['[3/2, 1/4]']);
  const equations = [parse('327600995*x**2 - 37869137*x + 1809975124*y**2 - 9998905626'), parse('895613949*x**2 - 273830224*x*y + 530506983*y**2 - 10000000000')];
  const rows = solveSystem(equations, [y, x], { check: false });
  expect(rows).toHaveLength(4);
  expect(rows.every((row) => row[1] instanceof CRootOf)).toBe(true);
  expect(isNoMatch(solveUndeterminedCoeffs(parse('sin(y*x)-sin(2*x)'), [y], [x], { strict: true }))).toBe(true);
  expect(solveUndeterminedCoeffs(parse('(x-2)*sqrt(2)+y*(x-2)'), [x], [y]).map(show)).toEqual(['[2]']);
});

it('checks imaginary candidates and retains raw denominators only for unchecked radical elimination', () => {
  const a = new Sym('x', { imaginary: true }), b = new Sym('y', { imaginary: true });
  expect(show(solve(parse('abs(x)-3').subs(x, a), a))).toBe('[-3*I, 3*I]');
  expect(solve(parse('sqrt(x**2+y**2)-3').subs(new Map([[x, a], [y, b]])), a)).toEqual([]);
  const equation = parse('sqrt((1+1/x)**2+1)-sqrt(5)');
  expect(solve(equation, x, { check: false, simplify: false }).some((root) => root.equals(S.Zero))).toBe(true);
  expect(solve(equation, x).some((root) => root.equals(S.Zero))).toBe(false);
  expect(show(solve(parse('(x-1)**x-1'), x))).toBe('[0, 2]');
  expect(show(solve(parse('x**3 - 8*y**6 + 48*y**5 - 120*y**4 + 160*y**3 - 120*y**2 + 48*y - 8'), x))).toContain('2*(y - 1)**2');
  expect(() => solveForSymbols(parse('exp(x)+sin(x)+exp(y)+sin(y)'), [x, y])).toThrow(NotImplementedError);
  expect(solveForSymbols(parse('1/(x**2-y**2)'), [x, y])).toEqual([]);
  expect(solveForSymbols(parse('1/(1/x-y+exp(y))'), [x, y])).toEqual([]);
});

it('separates factors and leaves shared coordinates available in a system', () => {
  const z = new Sym('z');
  const rows = solveSystem([parse('x**2+z-4'), parse('y-z-2')], [z, y, x]);
  expect(rows).toHaveLength(2);
  expect(rows.every((row) => at(row, 0).equals(z) && String(at(row, 1)) === 'z + 2')).toBe(true);
  const real = new Sym('x', { real: true });
  const absolute = [parse('abs(4*x-7)-5'), parse('abs(8*x-3)-1')].map((e) => e.subs(x, real));
  expect(solveSystem(absolute, [real], { manual: true, check: false }).map(show)).toEqual(['[1/2]', '[3]']);
  const product = [parse('x*(x**2+y**2-z)'), parse('y*(x**2+y**2-z)')];
  expect(solveSystem(product, [x, y, z])).toHaveLength(2);
  expect(solveSystem([parse('sin(x)*sin(y)')], [x, y]).map(show)).toEqual(['[0, y]', '[pi, y]', '[x, 0]', '[x, pi]']);
  expect(isLinearSolveSystem([parse('exp(x)-exp(-x)-tanh(x)*(exp(x)+exp(-x))+x-5')], [x])).toBe(true);
});

it('retains unchecked branches from singular elimination and inconsistent linear constraints', () => {
  const rational = [parse('y*(x+y-1)'), parse('1/y+(y-1)/(x*y)')];
  expect(solveSystem(rational, [x, y], { check: false }).map(show)).toEqual(['[x, 0]', '[1 - y, y]']);
  const inconsistent = [parse('x+y-1'), parse('x+y-2')];
  expect(solveSystem(inconsistent, [x, y], { manual: true, check: false }).map(show)).toEqual(['[1 - y, y]']);
  expect(solveSystem(inconsistent, [x, y], { manual: true })).toEqual([]);
});

it('checks that a parametric branch satisfies every equation identically', () => {
  const unknowns = symbols('a b c d f g k');
  const equations = [
    '-k*a+b+5*f/6+2*c/9+5*d/6+4*a/3', '-k*f+4*f/3+d/2', '-k*d+f/6+d',
    '13*b/18+13*c/18+13*a/18', '-k*c+b/2+20*c/9+a', '-k*b+b+c/18+a/6',
    '5*b/3+c/3+a', '2*b/3+2*c+4*a/3', '-g',
  ].map((source) => parse(source));
  const solutions = solveSystem(equations, unknowns);
  expect(solutions).toHaveLength(3);
  expect(solutions.map(show)).toEqual(expect.arrayContaining([
    '[0, 0, 0, 0, 0, 0, k]',
    '[0, 0, 0, d, -d, 0, 5/6]',
    '[-2*c, c, c, 0, 0, 0, 13/18]',
  ]));
  const sample = new Map<Expr, number>([[parse('c'), 1], [parse('d'), 1], [parse('f'), -1], [parse('k'), 1]]);
  const manual = solveSystem(equations, unknowns, { manual: true }).map((row) => show(row.map((value) => value.subs(sample))));
  expect(manual).toHaveLength(3);
  expect(manual).toEqual(expect.arrayContaining([
    '[0, 0, 0, 0, 0, 0, 1]',
    '[0, 0, 0, 1, -1, 0, 5/6]',
    '[-2, 1, 1, 0, 0, 0, 13/18]',
  ]));
});

it('leaves unsupported relations and complex decompositions for the general solver', () => {
  const real = new Sym('x', { real: true });
  expect(isNoMatch(solveRelation(new Rel('Lt', real, S.One), real))).toBe(true);
  expect(isNoMatch(solveRelation(new Rel('Gt', S.One, S.Zero)))).toBe(true);
  expect(isNoMatch(solveComplexComponents([parse('x+re(x)+im(x)-3')], x))).toBe(true);
  expect(solveVariables([parse('x+y-1')]).map(String)).toEqual(['x', 'y']);
  const value = parse('f(x)');
  expect(showMaps(solveForSymbols(value.add(x).sub(2), [value]))).toEqual([{ 'f(x)': '2 - x' }]);
  expect(solve(parse('x**5+x**3+1').subs(x, real), real)).toHaveLength(1);
  expect(() => solve(parse('x**7+x+y'), x)).toThrow(NotImplementedError);
});

it('uses ordinary exact roots when the coefficients do not require indexed back-substitution', () => {
  const rows = solveSystem([parse('x**2+y**2-5'), parse('x**2-y**2-1')], [x, y], { check: false });
  expect(rows).toHaveLength(4);
  expect(rows.every((row) => row.every((root) => !(root instanceof CRootOf)))).toBe(true);
  expect(solve(parse('1/(1/x-y+exp(y))'))).toEqual([]);
  expect(solveUndeterminedCoeffs(parse('sin(x*y)-sin(2*x)'), [y], [x])).toEqual([]);
});

it('inverts positive symbolic bases, factored powers, and nested exponentials', () => {
  const a = new Sym('a', { positive: true });
  expect(show(solve(parse('a**x-2').subs(new Sym('a'), a), x))).toBe('[log(2)/log(a)]');
  expect(show(solve(parse('3**x-2'), x))).toBe('[log(2)/log(3)]');
  expect(show(solve(parse('x**y-x'), x))).toBe('[1]');
  expect(show(solve(parse('a*(x+1)**y-(x+1)**y-2'), x))).toBe('[(2/(a - 1))**(1/y) - 1]');
  expect(show(solve(parse('(7**x)**x+pi'), x))).toBe('[-sqrt(log(pi) + I*pi)/sqrt(log(7)), sqrt(log(pi) + I*pi)/sqrt(log(7))]');
  expect(solve(parse('(2**x)**y'), x)).toEqual([]);
  expect(() => solve(parse('((x+1)**x)**x-2'), x)).toThrow(NotImplementedError);
  expect(() => solve(parse('((-2)**x)**x-2'), x)).toThrow(NotImplementedError);
  const roots = solve(parse('x**3+y+z'), x);
  expect(roots).toHaveLength(3);
  expect(roots.some((root) => root.equals(parse('(-y-z)**(1/3)')))).toBe(true);
  const trigonometric = solve(parse('a*sin(x)**2-sin(x)**2-2'), x).map((root) => root.subs(parse('a'), 5).toComplex().re);
  expect(trigonometric.some((root) => Math.abs(root - Math.PI / 4) < 1e-12)).toBe(true);
});

it('takes logarithms of exponential ratios and reduces powers using Lambert W', () => {
  const k = new Sym('y', { integer: true });
  const ratio = solve(parse('2**y-4*x**y').subs(y, k), k);
  expect(at(ratio, 0).subs(x, 4).toComplex().re).toBeCloseTo(-2, 12);
  const roots = solve(parse('x**3-3**x'), x).map((root) => root.toComplex().re).sort((a, b) => a - b);
  expect(at(roots, 0)).toBeCloseTo(2.478052680288, 10);
  expect(at(roots, 1)).toBeCloseTo(3, 10);
  expect(show(solve(parse('exp(x**2)-exp(x)'), x))).toBe('[0, 1]');
  expect(() => solve(parse('exp(x**x)+exp(x**(x+1))'), x)).toThrow(NotImplementedError);
  expect(() => solve(parse('x**2-2**(x**3+x)'), x)).toThrow(NotImplementedError);
});

it('rejects unsupported atan2 inversions and coupled radical forms', () => {
  expect(() => solve(parse('atan2(x,-1)-pi/2'), x)).toThrow(NotImplementedError);
  expect(() => solve(parse('atan2(x,x+1)-pi/4'), x)).toThrow(NotImplementedError);
  expect(() => solveForSymbols(new Fn('atan2', [x]), [x])).toThrow('index');
  expect(() => solve(parse('sqrt(x)+sqrt(x+1)+exp(x)'), x)).toThrow(NotImplementedError);
  expect(() => solve(parse('sqrt(x)*sqrt(x+1)+sqrt(x+1)+sqrt(x+2)-4'), x)).toThrow(NotImplementedError);
  expect(show(solve(parse('sqrt(x)+x-6'), x, { check: false, simplify: false }))).toBe('[4, 9]');
  expect(show(solve(parse('sqrt(x)-2'), x, { check: false, simplify: false }))).toBe('[4]');
  const result = solve(parse('sqrt(x)+sqrt(x+1/y)-3'), x, { check: false, simplify: false });
  expect(String(at(result, 0).subs(y, 1))).toBe('16/9');
  const nonpolynomial = solve(parse('sqrt((1+1/(exp(x)+1))**2+1)-sqrt(5)'), x, { check: false, simplify: false });
  expect(nonpolynomial.map(String)).toContain('log(4/3) + I*pi');
});

it('applies the tangent substitution to symbolic amplitudes and mixed degrees', () => {
  expect(show(solve(parse('sin(x)+cos(x)+1'), x))).toBe('[-pi/2]');
  const roots = solve(parse('a*sin(x)+y*cos(x)'), x);
  expect(roots).toHaveLength(2);
  expect(roots.map((root) => String(root.subs(parse('a'), 1).subs(y, 1)))).toEqual([
    '2*atan(1 - sqrt(2))', '2*atan(1 + sqrt(2))',
  ]);
  expect(solve(parse('sin(x)*(sin(x)+1)+cos(x)'), x).map(String)).toContain('-pi/2');
  expect(() => solve(parse('sin(x)**2+cos(x)**2-1'), x)).toThrow(NotImplementedError);
});

it('falls back from indexed elimination for incompatible bases and reducible eliminants', () => {
  const z = new Sym('z');
  const impossible = [parse('1000001*x**2+y**2-1'), parse('1000001*x**2+y**2-2')];
  expect(solveSystem(impossible, [x, y], { check: false })).toEqual([]);
  const reducible = [parse('1000001*x**2+x*y+y**2-1'), parse('1000001*x**2+x*y+y**2+x-1')];
  expect(solveSystem(reducible, [x, y], { check: false }).map(show)).toEqual(['[0, -1]', '[0, 1]']);
  const quadratic = [parse('1000001*x**2+y**2-2'), parse('x**2+y**2-1')];
  expect(solveSystem(quadratic, [x, y], { check: false })).toHaveLength(4);
  const inconsistent = [parse('1000001*x**2+y**2-1'), parse('x**2+y**2-1'), parse('x**2*y**2+z'), z];
  expect(solveSystem(inconsistent, [x, y, z], { check: false }).map(show)).toEqual(['[0, -1, 0]', '[0, 1, 0]']);
  const indexed = [parse('1000001*x**2+y**4+y+1'), parse('1000001*x**2+y**4+y+x+1')];
  const rows = solveSystem(indexed, [x, y], { check: false });
  expect(rows).toHaveLength(4);
  expect(rows.every((row) => at(row, 0).equals(S.Zero) && at(row, 1) instanceof CRootOf)).toBe(true);
  const overdetermined = [parse('x**2+y**2-5'), parse('x**2-y**2-1'), parse('x**2+2*y**2-7')];
  expect(solveSystem(overdetermined, [x, y], { check: false }).map(show)).toEqual([
    '[-sqrt(3), -sqrt(2)]', '[-sqrt(3), sqrt(2)]', '[sqrt(3), -sqrt(2)]', '[sqrt(3), sqrt(2)]',
  ]);
});

it('validates and back-substitutes partial solutions of nonlinear systems', () => {
  const z = new Sym('z');
  expect(solveSystem([parse('z-x**2'), parse('x**2*y**2+1')], [x, y, z], { check: false }).map(show)).toEqual([
    '[-I/y, y, -1/y**2]', '[I/y, y, -1/y**2]',
  ]);
  expect(solveSystem([parse('x+y**2+z-1'), parse('y-z-2')], [x, y, z]).map(show)).toEqual(['[-z**2 - 5*z - 3, z + 2, z]']);
  expect(solveSystem([parse('sin(x)+y+z-1'), parse('y-z-2')], [x, y, z]).map(show)).toEqual(['[x, 3/2 - sin(x)/2, -sin(x)/2 - 1/2]']);
  expect(() => solveSystem([parse('2*(log(x)+log(y)+exp(x*y))')], [x, y])).toThrow(NotImplementedError);
  expect(solveSystem([parse('log(x)+y'), parse('x*y-y')], [x, y]).map(show)).toEqual(['[1, 0]']);
  expect(solveSystem([parse('x*y'), parse('log(x)+y')], [x, y]).map(show)).toEqual(['[1, 0]']);
  expect(solveSystem([parse('x+oo'), parse('x*y-1')], [x, y])).toEqual([]);
  expect(solveSystem([parse('x-y'), parse('y**7+y+1')], [x, y])).toHaveLength(7);
});

it('certifies positive powers and falls back for equations with a vanishing complex component', () => {
  const real = new Sym('x', { real: true });
  const positive = parse('exp(2*x+2)*(exp(x)+x**2+2)/(exp(x)+2)**2').subs(x, real);
  expect(solveRelation(new Rel('Gt', new Pow(positive, parse('1/3')), S.Zero), real)).toBe(S.true);
  expect(showMaps(solveForSymbols(parse('I*(x+1)').subs(x, real), [real]))).toEqual([{ x: '-1' }]);
  expect(solveForSymbols(parse('exp(x)'), [x])).toEqual([]);
});

it('checks bound limits and expression targets when isolating coefficients', () => {
  expect(solveLinear(parse('0**x-1')).map(String)).toEqual(['0**x - 1', '1']);
  expect(solveLinear(parse('x+Integral(x,(x,0,y))'), { symbols: [x] }).map(String)).toEqual(['x', '-Integral(x, (x, 0, y))']);
  const [numerator, denominator] = solveLinear(parse('Integral(y,(y,0,x))+1'), { symbols: [x] });
  expect(String(numerator.div(denominator).subs(x, 2))).toBe('3');
  const target = parse('f(y)');
  expect(isNoMatch(solveUndeterminedCoeffs(parse('sin(x*f(y))-sin(2*x)'), [target], [x], { strict: true }))).toBe(true);
});
it('solves Piecewise branches with their ordered domains', () => {
  expect(show(solve(parse('x-Piecewise((1, y > 0), (0, True))'), x))).toBe('[Piecewise((1, y > 0), (0, True))]');
  expect(show(solve(new Piecewise([x, S.false, x.add(-1), S.true, x, new Rel('Lt', x, S.Zero)]), x))).toBe('[1]');
  expect(show(solve(parse('Piecewise((2-x, x <= 2), (x-2, True))'), x))).toBe('[2]');
  expect(show(solve(parse('Piecewise((2-x, x <= 2), (x-2, True))-1'), x))).toBe('[1, 3]');
  expect(show(solve(parse('Piecewise(((x-5)**5, x >= 2), (Piecewise(((x-2)**2, x >= 0), (1, True)), True))'), x))).toBe('[5]');
  expect(show(solve(parse('Piecewise((x**2-4, x < y), (x-2, True))'), x))).toBe('[Piecewise((-2, y > -2), (nan, True)), Piecewise((2, y <= 2), (nan, True)), Piecewise((2, y > 2), (nan, True))]');
  expect(() => solve(parse('Piecewise((0, x < 0), (1, True))'), x)).toThrow(NotImplementedError);
});
it('returns radical quintic solutions and preserves the CRootOf fallback', () => {
  const p = Poly.from(parse('x**5-5*x+12'), [x]);
  const rs = solve(p.asExpr(), x, { check: false });
  expect(rs).toHaveLength(5);
  for (const r of rs) {
    expect(r instanceof CRootOf).toBe(false);
    const residual = p.eval(evalf(r, 30));
    if (residual instanceof Poly) throw new TypeError('expected scalar residual');
    const value = toComplex(residual);
    expect(Math.hypot(value.re, value.im)).toBeLessThan(1e-20);
  }
  expect(solve(parse('x**5-x+1'), x).every(r => r instanceof CRootOf)).toBe(true);
});
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
  ['x + exp(2*x) | exp(x)', '[-sqrt(-x), sqrt(-x)]'],
  ['exp(x) - 1 | exp(y)', '[]'],
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
    expect(sol('x**5 + y*x + 1')).toBe('[]');
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
    // SymPy raises NotImplementedError; exp(y) = 2 - 2*exp(-2*C1)/(2*x + 1) solves it (printed with the denominator expanded)
    expect(show(solve(parse('C1 + y/2 + log(exp(-y) - 1/2)/2 + log(2*x + 1)/2'), y))).toBe('[log(2 - 2/(2*x*exp(2*C1) + exp(2*C1)))]');
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

it('keeps indexed roots of the numerator when the denominator is nonzero', () => {
  const equations = [parse('x-y'), parse('(y**7+y+1)/(y+2)')];
  // (SymPy names the variable of the indexed roots x, whatever the unknown)
  const roots = Array.from({ length: 7 }, (_, index) => new CRootOf(parse('x**7+x+1'), index));
  expect(solveSystem(equations, [x, y]).map(show)).toEqual(roots.map((root) => show([root, root])));
});

it('keeps requested free parameters after polynomial elimination', () => {
  // SymPy 1.14: test_issue_21022.
  const equations = ['k-16', 'p-8', 'y**2+z**2-x**2', 'd-x+p', 'd**2+k**2-y**2', 'z**2-p**2-k**2', 'abc-efg'].map((equation) => parse(equation));
  const variables = symbols('abc d efg k p x y z');
  expect(solveSystem(equations, variables).map(show).sort()).toEqual([
    '[efg, 32, efg, 16, 8, 40, -16*sqrt(5), -8*sqrt(5)]',
    '[efg, 32, efg, 16, 8, 40, -16*sqrt(5), 8*sqrt(5)]',
    '[efg, 32, efg, 16, 8, 40, 16*sqrt(5), -8*sqrt(5)]',
    '[efg, 32, efg, 16, 8, 40, 16*sqrt(5), 8*sqrt(5)]',
  ]);
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

it('denoms collects denominator bases and filters symbols', () => {
  const names = (e: string, ...symbols: sj.Sym[]) => [...sj.denoms(sj.parseExpr(e), ...symbols)].map(String).sort();
  const y = new sj.Sym('y'), z = new sj.Sym('z');
  expect(names('x/y')).toEqual(['y']);
  expect(names('x/(y*z)')).toEqual(['y', 'z']);
  expect(names('3/x + y/z')).toEqual(['x', 'z']);
  expect(names('x/2 + y/z')).toEqual(['2', 'z']);
  expect(names('1/x + 1/y + 1/z', y, z)).toEqual(['y', 'z']);
  expect(names('1/x**2 + 1/x')).toEqual(['x']);
  expect(names('x + 1')).toEqual([]);
});
import * as sj from '../../src';

it('solves numeric systems with a Jacobian and arbitrary precision', () => {
  const equations = [parse('3*x**2 - 2*y**2 - 1'), parse('x**2 - 2*x + y**2 + 2*y - 8')];
  const root = nsolve(equations, [x, y], [-1, 1]);
  expect(root.get(0, 0).toNumber()).toBeCloseTo(-1.19287309935246, 13);
  expect(root.get(1, 0).toNumber()).toBeCloseTo(1.27844411169911, 13);
  for (const eq of equations) expect(Math.abs(sj.subs(eq, [[x, root.get(0, 0)], [y, root.get(1, 0)]]).toNumber())).toBeLessThan(1e-12);
  expect(String(nsolve([parse('x**2 - 2')], [x], [1], { prec: 40 }).get(0, 0))).toContain('1.414213562373095048801688724209698078570');
  const complex = nsolve([parse('x**2 + 1')], [x], [sj.add(1, sj.S.I)]).get(0, 0).toComplex();
  expect(complex.im).toBeCloseTo(1, 13);
  expect(() => nsolve([], [], [])).toThrow(RangeError);
  expect(() => nsolve([x], [x], [])).toThrow(RangeError);
  expect(() => nsolve([x, y], [x], [1])).toThrow(RangeError);
  expect(() => nsolve([x], x as never, [1])).toThrow(RangeError);
  expect(() => nsolve([x], [x], 1 as never)).toThrow(RangeError);
  expect(() => nsolve([x], [x], [1], { solver: 'bisect' })).toThrow(TypeError);
  expect(() => nsolve(x, [x] as never, 1)).toThrow(TypeError);
  expect(() => nsolve(x, x, [1] as never)).toThrow(TypeError);
  expect(() => nsolve([parse('x**3 - 2*x + 2')], [x], [0])).toThrow('did not converge');
});

describe('unrad', () => {
  it('clears radicals while retaining their polynomial supersets', () => {
    for (const [input, output] of [
      ['x**(5/6) + 2', 'x**5 - 64'],
      ['sqrt(x) + (x + 1)**(1/3)', '-x**3 + x**2 + 2*x + 1'],
      ['sqrt(x) - 2', 'x - 4'],
      ['-sqrt(x) + 2', 'x - 4'],
    ] as const) {
      const result = sj.unrad(parse(input));
      if (sj.isNoMatch(result)) throw new TypeError('expected radical elimination');
      expect(String(result[0])).toBe(output);
      expect(result[1]).toEqual([]);
    }
    expect(sj.unrad(x.add(1))).toBe(sj.NoMatch);
    expect(sj.unrad(parse('sqrt(x)'), sj.symbol('y'))).toBe(sj.NoMatch);
    expect(() => sj.unrad(parse('sqrt(x) + (x+1)**(1/3) + 1'))).toThrow(sj.NotImplementedError);
    expect(() => sj.unrad(parse('sin(sqrt(x)) + sqrt(x+1)'))).toThrow(sj.NotImplementedError);
    expect(() => sj.unrad(parse('(x + 1)**(1/7)'))).toThrow(sj.NotImplementedError);
  });
  it('returns the change of variable for common-base radicals', () => {
    const result = sj.unrad(parse('sqrt(x) + x**(1/3) - 2'));
    if (sj.isNoMatch(result)) throw new TypeError('expected change of variable');
    const [e, cov] = result;
    expect(String(e)).toBe('_p**3 + _p**2 - 2');
    expect(cov.map(String)).toEqual(['_p', '_p**6 - x']);
    expect(String(e.subs([[cov[0]!, sj.S.One]]))).toBe('0');
  });
});

it('checks every equation and preserves inconclusive checks', async () => {
  const { checksol, S, Float, Relational } = await import('../../src');
  const assignments = new Map([[x, S.One]]);
  expect(checksol([parse('x - 1'), parse('x**2 - 1')], assignments)).toBe(true);
  expect(checksol([parse('x - 1'), parse('x**2 - 2')], x, 1)).toBe(false);
  expect(checksol([SymFunction('f')(x), parse('x - 1')], assignments)).toBe('unknown');
  expect(() => checksol([], assignments)).toThrow(RangeError);
  expect(checksol(S.true, assignments)).toBe(true);
  expect(checksol(S.false, assignments)).toBe(false);
  expect(checksol(new Float(0), assignments)).toBe(true);
  expect(checksol(new Float(0.5), assignments)).toBe(false);
  expect(checksol(parse('x + 1e-10'), x, 0)).toBe(true);
  expect(checksol(parse('x + 0.5'), x, 0)).toBe(false);
  expect(checksol(Relational(x, 2, '<', { evaluate: false }), new Map())).toBe('unknown');
  expect(checksol(Relational(x, S.false, '!=', { evaluate: false }), new Map([[x, S.true]]))).toBe(true);
  expect(checksol(Relational(x, S.true, '==', { evaluate: false }), new Map([[x, S.false]]))).toBe(false);
  expect(checksol(y, assignments)).toBe(false);
});
it('inverts elementary and error functions and expands binomials', () => {
  for (const [source, expected] of [
    ['asin(x)-y', '[sin(y)]'], ['acos(x)-y', '[cos(y)]'], ['atan(x)-y', '[tan(y)]'],
    ['erf(x)-y', '[erfinv(y)]'], ['erfinv(x)-y', '[erf(y)]'],
    ['erfc(x)-y', '[erfcinv(y)]'], ['erfcinv(x)-y', '[erfc(y)]'],
    ['conjugate(x)-3+I', '[3 + I]'], ['LambertW(2*x)-y', '[y*exp(y)/2]'],
    ['Abs(x)', '[0]'], ['binomial(x,2)-3', '[-2, 3]'],
  ] as const) expect(show(solve(parse(source), x))).toBe(expected);
  expect(() => solve(parse('Abs(x)-y'), x)).toThrow(NotImplementedError);
  expect(() => Reflect.apply(nsolve, undefined, [x, x, 0, 2])).toThrow(TypeError);
  expect(() => Reflect.apply(nsolve, undefined, [x, x, 0, null])).toThrow(TypeError);
});
it('solves nested and nonlinear absolute values over the reals', () => {
  const real = new Sym('x', { real: true });
  for (const [source, expected] of [
    ['Abs(x+3)-2*Abs(x-3)', '[1, 9]'],
    ['2*Abs(x)-Abs(x-1)', '[-1, 1/3]'],
    ['Abs(x**2-2*x)-4', '[1 - sqrt(5), 1 + sqrt(5)]'],
    ['Abs(Abs(x**2-1)-x)-x', '[1, -1 + sqrt(2), 1 + sqrt(2)]'],
  ] as const) expect(show(solve(xreplace(parse(source), [[x, real]]), real))).toBe(expected);
});
it('checks evaluated inequalities and retains symbolic coordinates in finite systems', async () => {
  const { checksol, Relational, S, solveSystem } = await import('../../src');
  expect(checksol(Relational(x, 2, '<', { evaluate: false }), x, 1)).toBe(true);
  expect(checksol(Relational(x, 2, '<', { evaluate: false }), x, 3)).toBe(false);
  expect(checksol(Relational(x, S.false, '!=', { evaluate: false }), new Map([[x, S.false]]))).toBe(false);
  expect(solveSystem([parse('x-y-z'),parse('y**2-2')], [x,y]).map((r) => r.map(String))).toEqual([
    ['z - sqrt(2)', '-sqrt(2)'], ['z + sqrt(2)', 'sqrt(2)'],
  ]);
  expect(String(nsolve(parse('Integral(x*y, (x,0,5))'), y, 2))).toBe('0');
  expect(solveLinear(parse('x+Derivative(2*x,x)')).map(String)).toEqual(['x','-2']);
  expect(solveLinear(parse('x+Integral(x,y)-2'), { symbols: [x] }).map(String)).toEqual(['x','2/(y + 1)']);
  expect(solveLinear(parse('Integral(2, (x, 0, x)) - 6'), { symbols: [x] }).map(String)).toEqual(['x', '3']);
  expect(solveLinear(parse('Integral(2, x) + x - 6'), { symbols: [x] }).map(String)).toEqual(['x', '2']);
});
it('supports coefficient inference, expression targets, and numeric checking flags', async () => {
  const { checksol, S, solveSystem, detPerm, detMinor } = await import('../../src');
  const [a,b,c,u,v] = symbols('a b c u v');
  expect(checksol(parse('x+1e-10'), x, 0, { numerical: false })).toBe(false);
  expect(checksol(parse('x+1e-10'), new Map([[x,S.Zero]]), { numerical: false })).toBe(false);
  expect(checksol(parse('x*0.0'), x, 1, { numerical: false })).toBe(true);
  expect(checksol([parse('x+1e-10')], x, 0, { numerical: false })).toBe(false);
  const f = SymFunction('f')(x), g = SymFunction('g')(x);
  expect(show(solve(parse('f(x)+Derivative(f(x),x)'), f))).toBe('[-Derivative(f(x), x)]');
  expect(solveSystem([parse('f(x)-3*Derivative(f(x),x)'),parse('f(x)**2-y+4')], [f,y]).map((r) => r.map(String))).toEqual([['3*Derivative(f(x), x)','9*Derivative(f(x), x)**2 + 4']]);
  expect(solveUndeterminedCoeffs(parse('(a+b)*x+b-c'),[a,b]).map((r) => r.map(String))).toEqual([['-c','c']]);
  expect(solveUndeterminedCoeffs(parse('a*x+a-2'),[a])).toEqual([]);
  expect(solveUndeterminedCoeffs(S.Zero,[a])).toEqual([]);
  expect(solveUndeterminedCoeffs(parse('f(x)+g(x)*x-2'),[f,g], [x]).map((r) => r.map(String))).toEqual([['2','0']]);
  expect(solveUndeterminedCoeffs(parse('a*u**v+b*u**v/v+c-3-2*u**v/v-u**v'),[a,b,c],[u,v]).map((r) => r.map(String))).toEqual([['1','2','3']]);
  const matrix=Matrix.of([[x,1],[2,y]]);
  expect(String(detPerm(matrix))).toBe('x*y - 2');
  expect(String(detMinor(matrix))).toBe('x*y - 2');
});
it('keeps denominator and assumption restrictions in finite solutions', async () => {
  const { checksol, S, Eq, add, pow, solveSystem } = await import('../../src');
  const [a,b] = symbols('a b');
  expect(solveUndeterminedCoeffs(parse('a*x+b-x-2'),[a,b]).map((r) => r.map(String))).toEqual([['1','2']]);
  expect(() => Reflect.apply(checksol, undefined, [x,x,{}])).toThrow();
  const reciprocal = pow(x, -1);
  expect(solve(Eq(add(x,reciprocal),reciprocal),x)).toEqual([]);
  const positive = new Sym('p',{ positive: true });
  expect(solveSystem([add(positive,1)], [positive])).toEqual([]);
  expect(solveSystem([add(positive,1)], [positive],{check:false}).map((r) => r.map(String))).toEqual([['-1']]);
  expect(solveSystem([add(pow(positive,2),-1)], [positive]).map((r) => r.map(String))).toEqual([['1']]);
  expect(solveSystem([add(pow(positive,2),-1)], [positive],{check:false}).map((r) => r.map(String))).toEqual([['-1'],['1']]);
  expect(checksol(S.Zero, new Map())).toBe(true);
});

it('solves unevaluated-free equations without optional calculus evaluation', async () => {
  const { impl } = await import('../../src/core/nodes');
  const evaluate = Object.getOwnPropertyDescriptor(impl, 'doit');
  try {
    impl.doit = undefined;
    expect(String(nsolve(x, x, 2))).toBe('0');
    expect(solveLinear(parse('x + Integral(1,y)')).map(String)).toEqual(['x','-Integral(1, y)']);
  } finally {
    if (evaluate) Object.defineProperty(impl, 'doit', evaluate);
  }
});


it('inverts positive constant bases with nonlinear exponents', () => {
  expect(show(solve(parse('4**(2*x**2+2*x)-8'), x))).toBe('[-3/2, 1/2]');
  const equation = parse('4*3**(5*x+2)-7');
  const roots = solve(equation, x);
  expect(roots).toHaveLength(5);
  for (const root of roots) expect(Math.hypot(...Object.values(equation.subs(x, root).toComplex()))).toBeLessThan(1e-12);
  expect(solve(parse('2**x'), x)).toEqual([]);
});

it('takes logarithms of two positive exponential terms', () => {
  expect(show(solve(parse('4**(x/2)-2**(x/3)'), x))).toBe('[0, 3*I*pi/log(2)]');
  expect(show(solve(parse('5**(x/2)-2**(x/3)'), x))).toBe('[0]');
  const solutions = solve(parse('5**(x/2)-2**(3/x)'), x);
  expect(solutions).toHaveLength(2);
  for (const value of solutions) expect(Math.abs(value.toComplex().re)).toBeCloseTo(Math.sqrt(6 * Math.log(2) / Math.log(5)), 12);
  expect(show(solve(parse('2**x+x'), x))).toBe('[-LambertW(log(2))/log(2)]');
  expect(() => solve(parse('5**(x/2) + 2**(x/3)'), x)).toThrow(NotImplementedError);
});

it('keeps free coordinates in monic positive-dimensional systems', () => {
  const [x, y, z] = symbols('x y z');
  expect(nonlinsolve([parse('x**2-y**2')], [x, y]).map((row) => row.map(String))).toEqual([['-y', 'y'], ['y', 'y']]);
  const rows = nonlinsolve([parse('x**2+y**2-1'), parse('z-2')], [x, y, z]);
  expect(rows).toHaveLength(2);
  for (const row of rows) {
    expect(row[1]).toBe(y);
    expect(String(row[2])).toBe('2');
  }
});

it('solves parameter-dependent leading coefficients on the nonvanishing branch', () => {
  const equations = [parse('x**2*y**2+1')];
  expect(solveSystem(equations, [x, y]).map((row) => row.map(String))).toEqual([['-I/y', 'y'], ['I/y', 'y']]);
  expect(nonlinsolve(equations, [x, y]).map((row) => row.map(String))).toEqual([
    ['-I/y', 'Complement({y}, {0})'],
    ['I/y', 'Complement({y}, {0})'],
  ]);
});

it('inverts reciprocal trigonometric and hyperbolic functions', () => {
  for (const name of ['sec', 'csc', 'sech', 'csch']) {
    expect(solve(parse(`${name}(x)`), x)).toEqual([]);
    expect(solve(parse(`${name}(x)-2`), x).length).toBeGreaterThan(0);
  }
  expect(show(solve(parse('cot(x)'), x))).toBe('[pi/2]');
  expect(show(solve(parse('cot(x)-1'), x))).toBe('[pi/4]');
  for (const name of ['tanh', 'coth']) {
    expect(solve(parse(`${name}(x)-1`), x)).toEqual([]);
    expect(solve(parse(`${name}(x)+1`), x)).toEqual([]);
    expect(solve(parse(`${name}(x)-1/2`), x)).toHaveLength(1);
  }
});

it('rejects symbolic substitutions when the resulting expression depends on the unknown or is a nonzero polynomial', () => {
  expect(checksol(x, x, sj.SymFunction('f')(x))).toBe(false);
  expect(checksol(x, x, parse('Sum(x,(x,1,n))'))).toBe(false);
  expect(checksol(x, x, parse('Sum(f(x),(x,1,n))'))).toBe('unknown');
});

it('uses the symbolic residual if concrete evaluation is unavailable', async () => {
  const { impl } = await import('../../src/core/nodes');
  const previous = Object.getOwnPropertyDescriptor(impl, 'doit');
  try {
    delete impl.doit;
    expect(checksol(x, x, parse('Sum(f(x),(x,1,n))'))).toBe('unknown');
  } finally {
    if (previous !== undefined) Object.defineProperty(impl, 'doit', previous);
  }
});

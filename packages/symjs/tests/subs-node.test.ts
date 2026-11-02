// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

import { describe, expect, it } from 'vitest';
import { Derivative, Function, Subs, diff, doit, freeSymbols, latex, parse, sstr, symbols } from '../src';

const [x, y, z] = symbols('x y z');
const f = Function('f');

describe('Subs (SymPy Subs)', () => {
  it('derivative at a point', () => {
    const s = diff(f(x), x).subs(x, 0 as never);
    expect(s).toBeInstanceOf(Subs);
    expect(sstr(s)).toBe('Subs(Derivative(f(x), x), x, 0)');
    expect(latex(s)).toBe('\\left. \\frac{d}{d x} f{\\left(x \\right)} \\right|_{\\substack{ x=0 }}');
    expect(freeSymbols(s).size).toBe(0);
    expect(sstr(diff(s, x))).toBe('0');
    expect(sstr(doit(s))).toBe('Subs(Derivative(f(x), x), x, 0)');
    expect(sstr(diff(f(x), x).subs(x, y))).toBe('Derivative(f(y), y)');
    expect(sstr(Derivative(f(x, y), x).subs(x, parse('y + 1')))).toBe('Subs(Derivative(f(x, y), x), x, y + 1)');
  });

  it('several variables, substitution and evaluation', () => {
    const s = Subs(parse('f(x)*sin(y) + z'), [x, y], [0, 1]);
    expect(sstr(s)).toBe('Subs(z + f(x)*sin(y), (x, y), (0, 1))');
    expect(latex(s)).toBe('\\left. z + f{\\left(x \\right)} \\sin{\\left(y \\right)} \\right|_{\\substack{ x=0\\\\ y=1 }}');
    expect([...freeSymbols(s)].map(String)).toEqual(['z']);
    expect(sstr(s.subs(x, 3 as never))).toBe(sstr(s));
    expect(sstr(s.subs(z, 3 as never))).toBe('Subs(f(x)*sin(y) + 3, (x, y), (0, 1))');
    expect(sstr(doit(s))).toBe('z + f(0)*sin(1)');
    expect(sstr(diff(Subs(parse('x**2'), x, parse('y + 1')), y))).toBe('2*y + 2');
    expect(sstr(diff(Subs(f(x), x, y), y))).toBe('Derivative(f(y), y)');
  });
});

import { combsimp, gammasimp } from '../src';

describe('gammasimp and combsimp', () => {
  const n = symbols('n', { integer: true })[0];
  it('combine integer shifts', () => {
    expect(sstr(gammasimp(parse('gamma(x + 3)/gamma(x + 1)')))).toBe('(x + 1)*(x + 2)');
    expect(sstr(gammasimp(parse('gamma(x + 1)/gamma(x)/x')))).toBe('1');
    expect(sstr(combsimp(parse('factorial(n + 2)/factorial(n)', { symbols: { n } } as never)))).toBe('(n + 1)*(n + 2)');
    expect(sstr(combsimp(parse('binomial(n + 1, 2)/binomial(n, 2)', { symbols: { n } } as never)))).toBe('(n + 1)/(n - 1)');
    expect(sstr(combsimp(parse('factorial(n)/factorial(n - 3)', { symbols: { n } } as never)))).toBe('n*(n - 2)*(n - 1)');
    expect(sstr(combsimp(parse('factorial(n)*factorial(n + 1)', { symbols: { n } } as never)))).toBe('factorial(n)*factorial(n + 1)');
  });
});

describe('parser and assumptions', () => {
  it('repeating decimals', () => {
    expect(['.[3]', '1.2[3]', '0.[142857]', '-1.[3]'].map((s) => sstr(parse(s)))).toEqual(['1/3', '37/30', '1/7', '-4/3']);
  });
  it('zero=False splits powers', async () => {
    const { expandPowerExp, Symbol: Sym } = await import('../src');
    const xn = new Sym('x', { zero: false });
    expect(sstr(expandPowerExp(parse('x**(y + 2)', { symbols: { x: xn } } as never)))).toBe('x**2*x**y');
    expect(sstr(expandPowerExp(parse('x**(y + 2)')))).toBe('x**(y + 2)');
  });
});

describe('factor over GF(p)', () => {
  it('matches SymPy factor(f, modulus=p)', async () => {
    const { factor } = await import('../src');
    const cases: [string, number, string][] = [
      ['x**2 + 1', 2, '(x + 1)**2'],
      ['x**4 + 1', 3, '(x**2 - x - 1)*(x**2 + x - 1)'],
      ['x**6 - 1', 7, '(x - 3)*(x - 2)*(x - 1)*(x + 1)*(x + 2)*(x + 3)'],
      ['x**5 + x + 1', 2, '(x**2 + x + 1)*(x**3 + x**2 + 1)'],
      ['3*x**3 + 2*x + 1', 5, '-2*(x**3 - x + 2)'],
      ['x**8 + x**4', 2, 'x**4*(x + 1)**4'],
      ['x**9 - x', 3, 'x*(x - 1)*(x + 1)*(x**2 + 1)*(x**2 - x - 1)*(x**2 + x - 1)'],
    ];
    for (const [f, p, want] of cases) expect(sstr(factor(parse(f), { modulus: p }))).toBe(want);
  });
});

describe('solve with radicals', () => {
  it('isolates one radical and checks the candidates', async () => {
    const { solve } = await import('../src');
    const x = symbols('x')[0];
    const show = (s: string, opts = {}) => solve(parse(s), x, opts).map((e) => sstr(e));
    expect(show('sqrt(x + 1) - x + 1')).toEqual(['3']);
    expect(show('x**(2/3) - 4')).toEqual(['8']);
    expect(show('sqrt(x) + 1')).toEqual([]);
    expect(show('-x + (x**3 - 3*x**2)**(1/3) + 1')).toEqual([]);
    expect(show('-x + (x**3 - 3*x**2)**(1/3) + 1', { check: false })).toEqual(['1/3']);
  });
});

describe('roots of polynomials with algebraic coefficients', () => {
  it('uses the norm polynomial like SymPy', async () => {
    const { Poly } = await import('../src');
    const x = symbols('x')[0];
    expect(Poly.from(parse('x**2 + I*x - 1'), [x]).allRoots().map((e) => sstr(e))).toEqual(['CRootOf(x**4 - x**2 + 1, 0)', 'CRootOf(x**4 - x**2 + 1, 2)']);
    expect(Poly.from(parse('sqrt(2)*x**3 + x**2 - 1'), [x]).realRoots().map((e) => sstr(e))).toEqual(['sqrt(2)/2']);
  });
});

describe('Poly lift, eject and inject', () => {
  it('match SymPy', async () => {
    const { Poly, expand } = await import('../src');
    const [x, y] = symbols('x y');
    const show = (p: { asExpr(): unknown; gens: readonly unknown[]; domain: string }) => `${sstr(expand(p.asExpr() as never))} | ${p.gens.map((g) => sstr(g as never)).join(',')} | ${p.domain}`;
    expect(show(Poly.from(parse('x**2 + I*x - 1'), [x]).lift())).toBe('x**4 - x**2 + 1 | x | ZZ');
    const f = Poly.from(parse('x**2*y + x*y**3 + x*y + 1'), [x, y]);
    expect(show(f.eject(x))).toBe('x**2*y + x*y**3 + x*y + 1 | y | ZZ[x]');
    expect(show(f.eject(x).inject())).toBe('x**2*y + x*y**3 + x*y + 1 | y,x | ZZ');
    expect(show(f.eject(x).inject({ front: true }))).toBe('x**2*y + x*y**3 + x*y + 1 | x,y | ZZ');
  });
});

describe('multiple integrals', () => {
  it('print, differentiate and evaluate like SymPy', async () => {
    const { Integral, Rational, add, mul, pow, subs } = await import('../src');
    const [x, y] = symbols('x y');
    const i = new Integral([new Integral([add(x, y), y]), y, Rational.of(1), x]);
    expect(sstr(i)).toBe('Integral(x + y, y, (y, 1, x))');
    expect(latex(i)).toBe('\\int\\limits_{1}^{x}\\int \\left(x + y\\right)\\, dy\\, dy');
    expect(sstr(diff(i, x))).toBe('Integral(x + y, (y, x)) + Integral(1, y, (y, 1, x))');
    expect(sstr(diff(i, y))).toBe('0');
    expect(sstr(doit(i))).toBe('2*x**3/3 - x/2 - 1/6');
    expect(sstr(new Integral([new Integral([mul(x, y), x]), y]))).toBe('Integral(x*y, x, y)');
    expect(sstr(subs(new Integral([pow(x, 2), x]), [[x, Rational.of(1)]]))).toBe('Integral(x**2, (x, 1))');
  });
});

describe('powdenest and finite differences', () => {
  it('match SymPy', async () => {
    const { powdenest, asFiniteDifference, Derivative: D } = await import('../src');
    const [x, h] = symbols('x h');
    expect(sstr(powdenest(parse('(x**(2*i)*y**(4*i))**z'), { force: true }))).toBe('(x*y**2)**(2*i*z)');
    const f = Function('f');
    const dx = Function('dx');
    expect(sstr(asFiniteDifference(D(f(x), x) as never, dx(x), parse('x - h', { symbols: { x, h } } as never)))).toBe(
      '-f(-h + x - dx(-h + x)/2)/dx(-h + x) + f(-h + x + dx(-h + x)/2)/dx(-h + x)',
    );
  });
});

describe('nonlinsolve and undetermined coefficients', () => {
  it('handle radicals, polynomial systems and non-polynomial terms', async () => {
    const { nonlinsolve, solveUndeterminedCoeffs } = await import('../src');
    const [x, y] = symbols('x y', { real: true });
    const P = (s: string) => parse(s, { symbols: { x, y } } as never);
    const show = (r: unknown[][]) => r.map((t) => '(' + t.map((e) => sstr(e as never)).join(', ') + ')').join(' ');
    expect(show(nonlinsolve([P('sqrt(x**2+y**2)-10'), P('sqrt(y**2+(10-x)**2)-3')], [x, y]))).toBe('(191/20, -3*sqrt(391)/20) (191/20, 3*sqrt(391)/20)');
    const [a, b, c, u, v] = symbols('a b c u v');
    const eq = parse('-v - 2*u**v + a*v + b*u**v - 3*v*u**v + c*v*u**v', { symbols: { a, b, c, u, v } } as never);
    expect(show(solveUndeterminedCoeffs(eq, [a, b, c], [u, v]))).toBe('(1, 2, 3)');
  });
});

describe('matrix symbols', () => {
  it('transpose and adjoint like SymPy', async () => {
    const { MatrixSymbol, transpose, adjoint, mul, add } = await import('../src');
    const A = new MatrixSymbol('A', 3, 3);
    const B = new MatrixSymbol('B', 3, 3);
    expect(sstr(transpose(A))).toBe('A.T');
    expect(sstr(adjoint(A))).toBe('Adjoint(A)');
    expect(sstr(transpose(mul(A, B)))).toBe('B.T*A.T');
    expect(sstr(adjoint(mul(A, B)))).toBe('Adjoint(B)*Adjoint(A)');
    expect(sstr(transpose(transpose(A)))).toBe('A');
    expect(sstr(transpose(add(A, B)))).toBe('A.T + B.T');
    expect(latex(transpose(A))).toBe('A^{T}');
  });
});

describe('matrix solving and constructions', () => {
  it('match SymPy', async () => {
    const { Matrix, matrixSolve, gaussJordanSolve, solveLeastSquares, GramSchmidt, hessian, wronskian, casoratian, normalized } = await import('../src');
    const [x, y, n] = symbols('x y n');
    const A = Matrix.of([[2, 1], [1, 3]]);
    expect(String(matrixSolve(A, Matrix.col(1, 2)))).toBe('Matrix([[1/5], [3/5]])');
    const [sol, params] = gaussJordanSolve(Matrix.of([[1, 2], [2, 4]]), Matrix.col(3, 6));
    expect([String(sol), String(params)]).toEqual(['Matrix([[3 - 2*tau0], [tau0]])', 'Matrix([[tau0]])']);
    expect(String(solveLeastSquares(Matrix.of([[1, 2], [3, 4], [5, 6]]), Matrix.col(1, 2, 4)))).toBe('Matrix([[2/3], [1/12]])');
    expect(GramSchmidt([Matrix.col(3, 1), Matrix.col(2, 2)]).map(String)).toEqual(['Matrix([[3], [1]])', 'Matrix([[-2/5], [6/5]])']);
    expect(String(hessian(parse('x**2*y'), [x, y]))).toBe('Matrix([[2*y, 2*x], [2*x, 0]])');
    expect(sstr(wronskian([parse('sin(x)'), parse('cos(x)')], x))).toBe('-sin(x)**2 - cos(x)**2');
    expect(sstr(casoratian([1, parse('2**n')], n))).toBe('1');
    expect(String(normalized(Matrix.col(3, 4)))).toBe('Matrix([[3/5], [4/5]])');
  });
});

describe('small core functions', () => {
  it('match SymPy', async () => {
    const { count, asCoeffExponent, asPowersDict, Rem } = await import('../src');
    const [x, y] = symbols('x y');
    expect(count(parse('x*sin(x) + x'), x)).toBe(3);
    expect(asCoeffExponent(parse('x**3*y'), x).map((e) => sstr(e))).toEqual(['y', '3']);
    expect([...asPowersDict(parse('x**2*y'))].map(([b, e]) => `${sstr(b)}:${sstr(e)}`).sort()).toEqual(['x:2', 'y:1']);
    expect(sstr(Rem(-7, 3))).toBe('-1');
    expect(sstr(Rem(parse('x**3'), y))).toBe('Rem(x**3, y)');
    expect(sstr(Rem(parse('x**3'), y).subs([[x, -5], [y, 3]] as never))).toBe('-2');
  });
});

describe('Lambda, hypersimp and taylor terms', () => {
  it('match SymPy', async () => {
    const { Lambda, hypersimp, isHypergeometric, taylorTerm, freeSymbols: fs } = await import('../src');
    const [x, n] = symbols('x n');
    const L = Lambda(x, parse('x**2'));
    expect(sstr(L)).toBe('Lambda(x, x**2)');
    expect(sstr(L.call(3))).toBe('9');
    expect(latex(L)).toBe('\\left( x \\mapsto x^{2} \\right)');
    expect(fs(Lambda(x, parse('x + n'))).size).toBe(1);
    expect(sstr(Lambda([x, n], parse('x + n')))).toBe('Lambda((x, n), n + x)');
    const k = symbols('k', { integer: true })[0];
    const P = (s: string) => parse(s, { symbols: { k } } as never);
    expect(sstr(hypersimp(P('factorial(k)'), k)!)).toBe('k + 1');
    expect(sstr(hypersimp(P('2**k'), k)!)).toBe('2');
    expect(hypersimp(P('log(k)'), k)).toBeUndefined();
    expect(sstr(hypersimp(P('factorial(2*k)/factorial(k)**2'), k)!)).toBe('2*(2*k + 1)/(k + 1)');
    expect(isHypergeometric(P('binomial(n, k)'), k)).toBe(true);
    expect(sstr(taylorTerm(parse('exp(x)'), 3, x))).toBe('x**3/6');
    expect(sstr(taylorTerm(parse('sin(x)'), 3, x))).toBe('-x**3/6');
  });
});

describe('rcollect, hypersimilar, number theory and matrix helpers', () => {
  it('match SymPy', async () => {
    const { rcollect, hypersimilar, legendreSymbol, motzkin, andre, Matrix, rrefRhs, rankDecomposition, invMod, permuteRows } = await import('../src');
    const [x, y] = symbols('x y');
    expect(sstr(rcollect(parse('(x**2*y + x*y + x + y)/(x + y)'), y))).toBe('(x + y*(x**2 + x + 1))/(x + y)');
    const k = symbols('k')[0];
    expect(hypersimilar(parse('factorial(k)', { symbols: { k } } as never), parse('factorial(k + 1)', { symbols: { k } } as never), k)).toBe(true);
    expect([legendreSymbol(3, 7), legendreSymbol(2, 7)]).toEqual([-1, 1]);
    expect([2, 3, 6].map((n) => motzkin(n))).toEqual([1n, 2n, 21n]);
    expect([0, 1, 2, 3, 4, 5, 6, 7].map((n) => andre(n))).toEqual([1n, 1n, 1n, 2n, 5n, 16n, 61n, 272n]);
    const M = Matrix.of([[1, 2], [3, 4]]);
    expect(rrefRhs(M, Matrix.col(5, 6)).map(String)).toEqual(['Matrix([[1, 0], [0, 1]])', 'Matrix([[-4], [9/2]])']);
    expect(rankDecomposition(M).map(String)).toEqual(['Matrix([[1, 2], [3, 4]])', 'Matrix([[1, 0], [0, 1]])']);
    expect(String(invMod(M, 5))).toBe('Matrix([[3, 1], [4, 2]])');
    expect(String(permuteRows(M, [1, 0]))).toBe('Matrix([[3, 4], [1, 2]])');
    void x;
  });
});

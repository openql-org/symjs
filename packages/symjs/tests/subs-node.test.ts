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

describe('jordan_form', () => {
  it('gives A = P*J*P**-1 with Jordan blocks', async () => {
    const { Matrix, jordanForm, simplify: simp } = await import('../src');
    const cases = [
      [[5, 4, 2, 1], [0, 1, -1, -1], [-1, -1, 3, 0], [1, 1, -1, 2]],
      [[2, 1], [0, 2]],
      [[1, 2], [3, 4]],
      [[2, 0, 0], [0, 2, 0], [0, 0, 3]],
      [[0, 1, 0], [0, 0, 1], [0, 0, 0]],
    ];
    const Js: string[] = [];
    for (const rows of cases) {
      const A = Matrix.of(rows);
      const [P, J] = jordanForm(A);
      const back = P.mul(J).mul(P.inv()).map((e) => simp(e));
      expect(String(back)).toBe(String(A));
      Js.push(String(J));
    }
    expect(Js[0]).toBe('Matrix([[1, 0, 0, 0], [0, 2, 0, 0], [0, 0, 4, 1], [0, 0, 0, 4]])');
    expect(Js[4]).toBe('Matrix([[0, 1, 0], [0, 0, 1], [0, 0, 0]])');
  });
});

describe('systems of linear ODEs', () => {
  it('match SymPy dsolve', async () => {
    const { dsolve } = await import('../src');
    const t = symbols('t')[0];
    const P = (s: string) => parse(s, { symbols: { t } } as never);
    const show = (eqs: string[]) => (dsolve(eqs.map(P)) as unknown[]).map((e) => sstr(e as never));
    expect(show(['Eq(Derivative(x(t), t), 2*x(t) + y(t))', 'Eq(Derivative(y(t), t), x(t) + 2*y(t))'])).toEqual(['Eq(x(t), -C1*exp(t) + C2*exp(3*t))', 'Eq(y(t), C1*exp(t) + C2*exp(3*t))']);
    expect(show(['Eq(Derivative(x(t), t), y(t))', 'Eq(Derivative(y(t), t), -x(t))'])).toEqual(['Eq(x(t), C1*sin(t) + C2*cos(t))', 'Eq(y(t), C1*cos(t) - C2*sin(t))']);
    expect(show(['Eq(Derivative(x(t), t), x(t) - 2*y(t))', 'Eq(Derivative(y(t), t), 2*x(t) + y(t))'])).toEqual(['Eq(x(t), -C1*exp(t)*sin(2*t) - C2*exp(t)*cos(2*t))', 'Eq(y(t), C1*exp(t)*cos(2*t) - C2*exp(t)*sin(2*t))']);
    expect(show(['Eq(Derivative(x(t), t), 2*x(t) + y(t))', 'Eq(Derivative(y(t), t), 2*y(t))'])).toEqual(['Eq(x(t), C1*exp(2*t) + C2*t*exp(2*t))', 'Eq(y(t), C2*exp(2*t))']);
    // inhomogeneous (variation of parameters); the solution satisfies the system
    const [ex, ey] = dsolve([P('Eq(Derivative(x(t), t), y(t) + exp(t))'), P('Eq(Derivative(y(t), t), x(t))')]) as never as { rhs: never }[];
    const { diff: d, simplify: simp, sub } = await import('../src');
    expect(sstr(simp(sub(d(ex!.rhs, t), sub(ey!.rhs, P('-exp(t)')))))).toBe('0');
  });
});

describe('parser options', () => {
  it('logical operators, Xor, evaluate=False and implicit multiplication', () => {
    expect(sstr(parse('x^y', { convertXor: false }))).toBe('x ^ y');
    expect(sstr(parse('~x | y & x'))).toBe('~x | (x & y)');
    expect(sstr(parse('2**2 / 3 + 5', { evaluate: false }))).toBe('2**2/3 + 5');
    expect(sstr(parse('4/2+7', { evaluate: false }))).toBe('4/2 + 7');
    expect(sstr(parse('2x y + sin x', { transformations: 'all' }))).toBe('2*x*y + sin(x)');
    expect(sstr(parse('x(y+1)', { transformations: 'all' }))).toBe('x*(y + 1)');
  });
});

describe('RootSum and full partial fractions', () => {
  it('match SymPy apart(full=True)', async () => {
    const { apart } = await import('../src');
    const x = symbols('x')[0];
    const full = (s: string) => sstr(apart(parse(s), x, { full: true }));
    expect(full('y/(x**2 + x + 1)')).toBe('RootSum(_w**2 + _w + 1, Lambda(_a, (-2*_a*y/3 - y/3)/(-_a + x)))');
    expect(full('1/(x**2-2)')).toBe('RootSum(_w**2 - 2, Lambda(_a, _a/(-_a + x)))/4');
    expect(full('1/(x**3+1)')).toBe('-RootSum(_w**2 - _w + 1, Lambda(_a, _a/(-_a + x)))/3 + 1/(3*(x + 1))');
    expect(full('t/(x**2+x+t)')).toBe('RootSum(_w**2 + _w + t, Lambda(_a, (-2*_a*t/(4*t - 1) - t/(4*t - 1))/(-_a + x)))');
    expect(full('36/(x**5 - 2*x**4 - 2*x**3 + 4*x**2 + x - 2)')).toBe('-4/(x + 1) - 3/(x + 1)**2 - 9/(x - 1)**2 + 4/(x - 2)');
    expect(sstr(doit(apart(parse('2/(x**2-2)'), x, { full: true })))).toBe('-sqrt(2)/(2*(x + sqrt(2))) + sqrt(2)/(2*(x - sqrt(2)))');
  });
});

describe('nsimplify of exact numbers', () => {
  it('identifies closed forms like SymPy', async () => {
    const { nsimplify, pi } = await import('../src');
    const ns = (s: string) => sstr(nsimplify(parse(s)));
    expect(['pi', 'sqrt(2)', 'cos(pi/5)', '1/(exp(3*pi*I/5)+1)', 'sin(pi/12)', '2**(1/3)', 'log(2)'].map(ns)).toEqual([
      'pi', 'sqrt(2)', '1/4 + sqrt(5)/4', '1/2 - I*sqrt(sqrt(5)/10 + 1/4)', 'sqrt(1/2 - sqrt(3)/4)', '2**(1/3)', 'log(2)',
    ]);
    expect(sstr(nsimplify(parse('4/(1+sqrt(5))'), { constants: [parse('GoldenRatio')] }))).toBe('-2 + 2*GoldenRatio');
    expect(sstr(nsimplify(parse('I**I'), { constants: [pi] }))).toBe('exp(-pi/2)');
  });
});

describe('sqrtdenest and radsimp (SymPy ports)', () => {
  it('denest and rationalize like SymPy', async () => {
    const { sqrtdenest, radsimp, sqrt: rt, expand: ex } = await import('../src');
    const sd = (s: string) => sstr(sqrtdenest(parse(s)));
    expect(sd('sqrt(1+sqrt(3)) + sqrt(3+3*sqrt(3)) - sqrt(10+6*sqrt(3))')).toBe('0');
    expect(sstr(sqrtdenest(rt(ex(parse('(1 + sqrt(2) + sqrt(1+sqrt(1+sqrt(3))))**2')))))).toBe('1 + sqrt(2) + sqrt(1 + sqrt(1 + sqrt(3)))');
    expect(['sqrt(5 + 2*sqrt(6))', 'sqrt(3 + 2*sqrt(2))', 'sqrt(x + 2*sqrt(x - 1))', 'sqrt(4 + 2*sqrt(3)) / 2'].map(sd)).toEqual(['sqrt(2) + sqrt(3)', '1 + sqrt(2)', 'sqrt(x + 2*sqrt(x - 1))', '1/2 + sqrt(3)/2']);
    const rs = (s: string, o = {}) => sstr(radsimp(parse(s), o));
    expect(['1/(sqrt(2) + sqrt(3))', '1/(1 + sqrt(2) + sqrt(3))', '1/(a + b*sqrt(c))', '1/(2 + sqrt(2))'].map((s) => rs(s))).toEqual([
      '-sqrt(2) + sqrt(3)', '(-sqrt(6) + sqrt(2) + 2)/4', '(a - b*sqrt(c))/(a**2 - b**2*c)', '(2 - sqrt(2))/2',
    ]);
    expect(rs('1/(a + b*sqrt(c))', { symbolic: false })).toBe('1/(a + b*sqrt(c))');
  });
});

describe('as_sum, euler_maclaurin and nsolve bisection', () => {
  it('match SymPy', async () => {
    const { asSum, eulerMaclaurin, Integral, Sum, nsolve, Rational } = await import('../src');
    const [x, n, k, b] = symbols('x n k b');
    const I2 = new Integral([parse('x**2'), x, Rational.of(0), Rational.of(2)]);
    expect(sstr(asSum(I2, n, 'midpoint', { evaluate: false }))).toBe('2*Sum((2*_k/n - 1/n)**2, (_k, 1, n))/n');
    expect(sstr(asSum(I2, 4, 'midpoint'))).toBe('21/8');
    expect(eulerMaclaurin(Sum(k, [k, 2, b]) as never).map((e) => sstr(e))).toEqual(['b**2/2 + b/2 - 1', '0']);
    expect(sstr(nsolve(parse('cos(x)*cosh(x) - 1'), x, [313, 317]))).toBe('315.730061685774');
  });
});

describe('polynomial helpers and systems with irrational solutions', () => {
  it('match SymPy', async () => {
    const { Poly, sqfNorm, solvePolySystem, sqrt: rt } = await import('../src');
    const [x, y, z] = symbols('x y z');
    expect(String(Poly.from(parse('x**2 + 2*x + sqrt(3)'), [], { domain: 'R' }))).toBe("Poly(1.0*x**2 + 2.0*x + 1.73205080756888, x, domain='RR')");
    expect(sqfNorm(parse('x**2+1'), x, [rt(3)]).map(String)).toEqual(['1', 'x**2 - 2*sqrt(3)*x + 4', 'x**4 - 4*x**2 + 16']);
    expect(String(Poly.from(parse('x - sqrt(2)'), [x], { domain: 'QQ<sqrt(2) + sqrt(3)>' }).norm())).toBe("Poly(x**4 - 4*x**2 + 4, x, domain='QQ')");
    const [g, s] = Poly.from(parse('x**2/2 + x/4 + 1/8'), [x]).makeMonicOverIntegersByScalingRoots();
    expect([String(g), sstr(s)]).toEqual(["Poly(x**2 + 2*x + 4, x, domain='ZZ')", '4']);
    const sols = solvePolySystem(['x**2+y+z-1', 'x+y**2+z-1', 'x+y+z**2-1'].map((e) => parse(e)), [x, y, z]).map((t) => t.map((e) => sstr(e)).join(','));
    expect(sols).toEqual(['0,0,1', '0,1,0', '1,0,0', '-1 + sqrt(2),-1 + sqrt(2),-1 + sqrt(2)', '-sqrt(2) - 1,-sqrt(2) - 1,-sqrt(2) - 1']);
  });
});

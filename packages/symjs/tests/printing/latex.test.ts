// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/printing/latex.ts.

import { describe, expect, it } from 'vitest';
import * as sj from '../../src';
import { adjoint, exp, I, mul, pow, rational, sin, sqrt, Sym, symbol, symbols, SymFunction } from '../../src';
import { Add, Float, Fn, Integral, Limit, Mul, Order, Pow, Rational, S } from '../../src/core/nodes';
import type { FnName } from '../../src/core/nodes';
import { CosineTransform, FourierTransform, InverseLaplaceTransform, InverseSineTransform, LaplaceTransform, MellinTransform } from '../../src/integrals/transforms';
import { DotProduct, MatrixSymbol } from '../../src/matrices/expressions';
import { latex, splitSuperSub } from '../../src/printing/latex';
import * as Sets from '../../src/sets/sets';

const A = new Sym('A', { commutative: false });
const B = new Sym('B', { commutative: false });
const [j, k, m, x, y, z] = symbols('j k m x y z');
const [, , theta] = symbols('a b theta', { real: true });
const n = sj.symbol('n', { positive: true });
const f = sj.SymFunction('f');
const R = (p: number, q = 1): Rational => Rational.of(BigInt(p), BigInt(q));

describe('adjoint and transpose (SymPy semantics)', () => {
  it('latex', () => {
    expect(latex(adjoint(mul(A, B)))).toBe('B^{\\dagger} A^{\\dagger}');
    expect(latex(adjoint(pow(A, 2)))).toBe('\\left(A^{\\dagger}\\right)^{2}');
  });
});

describe('latex', () => {
  it('prints LaTeX', () => {
    expect(latex(mul(rational(1, 2), sqrt(2)))).toBe('\\frac{\\sqrt{2}}{2}');
    expect(latex(exp(mul(I, theta)))).toBe('e^{i \\theta}');
    expect(latex(pow(sin(x), 2))).toBe('\\sin^{2}{\\left(x \\right)}');
    expect(latex(symbol('phi_1'))).toBe('\\phi_{1}');
  });
});

describe('unevaluated transforms', () => {
  const [t, s, x, k] = symbols('t s x k nu');
  const f = SymFunction('f');

  it('LaTeX like SymPy', () => {
    expect(latex(new LaplaceTransform(f(t), t, s))).toBe('\\mathcal{L}_{t}\\left[f{\\left(t \\right)}\\right]\\left(s\\right)');
    expect(latex(new InverseLaplaceTransform(f(s), s, t))).toBe('\\mathcal{L}^{-1}_{s}\\left[f{\\left(s \\right)}\\right]\\left(t\\right)');
    expect(latex(new MellinTransform(f(x), x, s))).toBe('\\mathcal{M}_{x}\\left[f{\\left(x \\right)}\\right]\\left(s\\right)');
    expect(latex(new FourierTransform(f(x), x, k))).toBe('\\mathcal{F}_{x}\\left[f{\\left(x \\right)}\\right]\\left(k\\right)');
    expect(latex(new InverseSineTransform(f(k), k, x))).toBe('\\mathcal{SIN}^{-1}_{k}\\left[f{\\left(k \\right)}\\right]\\left(x\\right)');
    expect(latex(new CosineTransform(f(x), x, k))).toBe('\\mathcal{COS}_{x}\\left[f{\\left(x \\right)}\\right]\\left(k\\right)');
  });

});

/**
 * Coverage of the LaTeX printer: every expected string was produced by
 * `sympy.latex(expr)` with SymPy 1.14.
 */

describe('latex: symbol names', () => {
  const cases: [string, string][] = [
    ['xmathring', '\\mathring{x}'],
    ['xddddot', '\\ddddot{x}'],
    ['xdddot', '\\dddot{x}'],
    ['xddot', '\\ddot{x}'],
    ['xdot', '\\dot{x}'],
    ['xcheck', '\\check{x}'],
    ['xbreve', '\\breve{x}'],
    ['xacute', '\\acute{x}'],
    ['xgrave', '\\grave{x}'],
    ['xtilde', '\\tilde{x}'],
    ['xhat', '\\hat{x}'],
    ['xbar', '\\bar{x}'],
    ['xvec', '\\vec{x}'],
    ['xprime', "{x}'"],
    ['xprm', "{x}'"],
    ['xbold', '\\boldsymbol{x}'],
    ['xbm', '\\boldsymbol{x}'],
    ['xcal', '\\mathcal{x}'],
    ['xscr', '\\mathscr{x}'],
    ['xfrak', '\\mathfrak{x}'],
    ['xnorm', '\\left\\|{x}\\right\\|'],
    ['xavg', '\\left\\langle{x}\\right\\rangle'],
    ['xabs', '\\left|{x}\\right|'],
    ['xmag', '\\left|{x}\\right|'],
    ['Alpha', '\\mathrm{A}'],
    ['lamda', '\\lambda'],
    ['varphi', '\\varphi'],
    ['aleph', '\\aleph'],
    ['hbar', '\\hbar'],
    ['alphahatdot', '\\dot{\\hat{\\alpha}}'],
    ['x__a', 'x^{a}'],
    ['x__a_b', 'x^{a}_{b}'],
    ['x_a_b', 'x_{a b}'],
    ['x^a', 'x^{a}'],
    ['x_{ab}', 'x_{ab}'],
    ['x1', 'x_{1}'],
    ['Gamma', '\\Gamma'],
    ['Lambda_2', '\\Lambda_{2}'],
    ['dot', 'dot'],
    ['x_2__3', 'x^{3}_{2}'],
    ['x__2__3', 'x^{2 3}'],
  ];
  for (const [name, tex] of cases) it(name, () => expect(latex(sj.symbol(name))).toBe(tex));
  it('splitSuperSub of the empty string', () => expect(splitSuperSub('')).toEqual(['', [], []]));
});

describe('latex: expressions', () => {
  const cases: [string, () => sj.Expr, string][] = [
    ['re(x)**2', () => sj.pow(sj.re(x), 2), '\\left(\\operatorname{re}{\\left(x\\right)}\\right)^{2}'],
    ['im(x)', () => sj.im(x), '\\operatorname{im}{\\left(x\\right)}'],
    ['im(x)**3', () => sj.pow(sj.im(x), 3), '\\left(\\operatorname{im}{\\left(x\\right)}\\right)^{3}'],
    ['airyai(x)**2', () => sj.pow(sj.airyai(x), 2), 'Ai^{2}\\left(x\\right)'],
    ['airybiprime(x)', () => sj.airybiprime(x), 'Bi^\\prime\\left(x\\right)'],
    ['airyaiprime(x)**2', () => sj.pow(sj.airyaiprime(x), 2), '{Ai^\\prime}^{2}\\left(x\\right)'],
    ['airybi(x)', () => sj.airybi(x), 'Bi\\left(x\\right)'],
    ['besselj(n,x)**2', () => sj.pow(sj.besselj(n, x), 2), 'J^{2}_{n}\\left(x\\right)'],
    ['bessely(1,x)', () => sj.bessely(1, x), 'Y_{1}\\left(x\\right)'],
    ['Abs(x)**2', () => sj.pow(sj.Abs(x), 2), '\\left|{x}\\right|^{2}'],
    ['conjugate(x)**2', () => sj.pow(sj.conjugate(x), 2), '\\overline{x}^{2}'],
    ['adjoint(x)', () => sj.adjoint(x), '\\overline{x}'],
    ['adjoint(x)**2', () => sj.pow(sj.adjoint(x), 2), '\\overline{x}^{2}'],
    ['Float(1.0e20)', () => sj.float('1.0e20'), '1.0 \\cdot 10^{20}'],
    ['Float(1.5e-10)', () => sj.float('1.5e-10'), '1.5 \\cdot 10^{-10}'],
    ['Float(2.5)', () => sj.float('2.5'), '2.5'],
    ['Ne(x,y)', () => sj.Ne(x, y), 'x \\neq y'],
    ['Lt(x,y)', () => sj.Lt(x, y), 'x < y'],
    ['Le(x,y)', () => sj.Le(x, y), 'x \\leq y'],
    ['Gt(x,y)', () => sj.Gt(x, y), 'x > y'],
    ['Ge(x,y)', () => sj.Ge(x, y), 'x \\geq y'],
    ['Eq(x,y)', () => sj.Eq(x, y), 'x = y'],
    ['Piecewise otherwise', () => sj.Piecewise([x, sj.Lt(x, 0)], [y, true]), '\\begin{cases} x & \\text{for}\\: x < 0 \\\\y & \\text{otherwise} \\end{cases}'],
    ['Piecewise conditions', () => sj.Piecewise([x, sj.Lt(x, 0)], [y, sj.Gt(x, 1)]), '\\begin{cases} x & \\text{for}\\: x < 0 \\\\y & \\text{for}\\: x > 1 \\end{cases}'],
    ['Limit(1/x,x,0,-)', () => new Limit([sj.pow(x, -1), x, R(0)], '-'), '\\lim_{x \\to 0^-} \\frac{1}{x}'],
    ['Limit(x,x,0)', () => new Limit([x, x, R(0)]), '\\lim_{x \\to 0^+} x'],
    ['Limit(sin(x)/x,x,0)', () => new Limit([sj.mul(sj.sin(x), sj.pow(x, -1)), x, R(0)]), '\\lim_{x \\to 0^+}\\left(\\frac{\\sin{\\left(x \\right)}}{x}\\right)'],
    ['Limit(x+1,x,0,+-)', () => new Limit([sj.add(x, 1), x, R(0)], '+-'), '\\lim_{x \\to 0}\\left(x + 1\\right)'],
    ['Limit(x,x,0,+-)', () => new Limit([x, x, R(0)], '+-'), '\\lim_{x \\to 0} x'],
    ['Limit(1/x,x,oo)', () => new Limit([sj.pow(x, -1), x, S.Infinity], '-'), '\\lim_{x \\to \\infty} \\frac{1}{x}'],
    ['Limit(x**2,x,-oo)', () => new Limit([sj.pow(x, 2), x, S.NegativeInfinity]), '\\lim_{x \\to -\\infty} x^{2}'],
    ['O(x - 1, (x, 1))', () => sj.O(sj.add(x, -1), x, 1), 'O\\left(x - 1; x\\rightarrow 1\\right)'],
    ['O((x - 1)**2, (x, 1))', () => sj.O(sj.pow(sj.add(x, -1), 2), x, 1), 'O\\left(\\left(x - 1\\right)^{2}; x\\rightarrow 1\\right)'],
    ['O(1)', () => sj.O(1), 'O\\left(1\\right)'],
    ['O(x**2)', () => sj.O(sj.pow(x, 2)), 'O\\left(x^{2}\\right)'],
    ['O(x,(x,oo))', () => new Order([x, x, S.Infinity]), 'O\\left(x; x\\rightarrow \\infty\\right)'],
    ['Derivative(f(x),x)', () => sj.Derivative(f(x), x), '\\frac{d}{d x} f{\\left(x \\right)}'],
    ['Derivative(f(x),x,2)', () => sj.Derivative(f(x), [x, 2]), '\\frac{d^{2}}{d x^{2}} f{\\left(x \\right)}'],
    ['Derivative(f(x,y),x,y)', () => sj.Derivative(f(x, y), x, y), '\\frac{\\partial^{2}}{\\partial y\\partial x} f{\\left(x,y \\right)}'],
    ['Derivative(f(x,y),x,2,y)', () => sj.Derivative(f(x, y), [x, 2], y), '\\frac{\\partial^{3}}{\\partial y\\partial x^{2}} f{\\left(x,y \\right)}'],
    ['Derivative(x*y**2+f(x),x)', () => sj.Derivative(sj.add(sj.mul(x, sj.pow(y, 2)), f(x)), x), '\\frac{\\partial}{\\partial x} \\left(x y^{2} + f{\\left(x \\right)}\\right)'],
    ['Integral(x,(x,0,1))', () => new Integral([x, x, R(0), R(1)]), '\\int\\limits_{0}^{1} x\\, dx'],
    ['Integral(x+1,x)', () => new Integral([sj.add(x, 1), x]), '\\int \\left(x + 1\\right)\\, dx'],
    ['nested Integral', () => new Integral([new Integral([sj.mul(x, y), x, R(0), R(1)]), y, R(0), R(2)]), '\\int\\limits_{0}^{2}\\int\\limits_{0}^{1} x y\\, dx\\, dy'],
    ['f(x)**2', () => sj.pow(f(x), 2), 'f^{2}{\\left(x \\right)}'],
    ['f(x,y)', () => f(x, y), 'f{\\left(x,y \\right)}'],
    ['Float(1.5)**x', () => sj.pow(new Float(1.5), x), '{1.5}^{x}'],
    ['x**(-pi)', () => sj.pow(x, sj.neg(S.Pi)), 'x^{- \\pi}'],
    ['x**(-n)', () => sj.pow(x, sj.neg(n)), 'x^{- n}'],
    ['x**(-1/2)', () => sj.pow(x, R(-1, 2)), '\\frac{1}{\\sqrt{x}}'],
    ['x**(-1/3)', () => sj.pow(x, R(-1, 3)), '\\frac{1}{\\sqrt[3]{x}}'],
    ['x**(1/3)', () => sj.pow(x, R(1, 3)), '\\sqrt[3]{x}'],
    ['-2*x', () => sj.mul(-2, x), '- 2 x'],
    ['-x/y', () => sj.mul(sj.neg(x), sj.pow(y, -1)), '- \\frac{x}{y}'],
    ['-2*x/3', () => sj.mul(R(-2, 3), x), '- \\frac{2 x}{3}'],
    ['2*x/3', () => sj.mul(R(2, 3), x), '\\frac{2 x}{3}'],
    ['y/x**2', () => sj.mul(sj.pow(x, -2), y), '\\frac{y}{x^{2}}'],
    ['sin(x)**2', () => sj.pow(sj.sin(x), 2), '\\sin^{2}{\\left(x \\right)}'],
    ['x**y**z', () => sj.pow(x, sj.pow(y, z)), 'x^{y^{z}}'],
    ['(x+1)**2', () => sj.pow(sj.add(x, 1), 2), '\\left(x + 1\\right)^{2}'],
    ['true', () => S.true, '\\text{True}'],
    ['false', () => S.false, '\\text{False}'],
    ['Catalan', () => S.Catalan, 'G'],
    ['GoldenRatio', () => S.GoldenRatio, '\\phi'],
    ['EulerGamma', () => S.EulerGamma, '\\gamma'],
    ['TribonacciConstant', () => S.TribonacciConstant, '\\text{TribonacciConstant}'],
    ['zoo', () => S.ComplexInfinity, '\\tilde{\\infty}'],
    ['nan', () => S.NaN, '\\text{NaN}'],
    ['-oo', () => S.NegativeInfinity, '-\\infty'],
    ['exp(x)', () => sj.exp(x), 'e^{x}'],
    ['sqrt(x)/y', () => sj.mul(sj.sqrt(x), sj.pow(y, -1)), '\\frac{\\sqrt{x}}{y}'],
    ['x**(-3/2)', () => sj.pow(x, R(-3, 2)), '\\frac{1}{x^{\\frac{3}{2}}}'],
    ['Mul(-1,x+1,evaluate=False)', () => new Mul([R(-1), sj.add(x, 1)]), '- (x + 1)'],
    ['Mul(2,3,evaluate=False)', () => new Mul([R(2), R(3)]), '2 \\cdot 3'],
    ['Add(x,Add(y,z),evaluate=False)', () => new Add([x, new Add([y, z])]), 'x + \\left(y + z\\right)'],
    ['(x+1)*(y+2)', () => sj.mul(sj.add(x, 1), sj.add(y, 2)), '\\left(x + 1\\right) \\left(y + 2\\right)'],
    ['x*(-y)', () => sj.mul(x, sj.neg(y)), '- x y'],
    ['Mul(x,Mul(-1,y),evaluate=False)', () => new Mul([x, new Mul([R(-1), y])]), 'x \\left(- y\\right)'],
    ['Integral(x**2+1,(x,0,1))', () => new Integral([sj.add(sj.pow(x, 2), 1), x, R(0), R(1)]), '\\int\\limits_{0}^{1} \\left(x^{2} + 1\\right)\\, dx'],
    ['Derivative(x**2+f(x),x)', () => sj.Derivative(sj.add(sj.pow(x, 2), f(x)), x), '\\frac{d}{d x} \\left(x^{2} + f{\\left(x \\right)}\\right)'],
    ['Mul(1/2,x,evaluate=False)', () => new Mul([R(1, 2), x]), '\\frac{x}{2}'],
    ['x**(1/y)', () => sj.pow(x, sj.pow(y, -1)), 'x^{\\frac{1}{y}}'],
    ['Pow(x,-y)', () => new Pow(x, sj.neg(y)), 'x^{- y}'],
    ['Mul(2,sqrt(3),evaluate=False)', () => new Mul([R(2), sj.sqrt(3)]), '2 \\sqrt{3}'],
  ];
  for (const [label, build, tex] of cases) it(label, () => expect(latex(build())).toBe(tex));
});

describe('latex: functions with their own SymPy printer', () => {
  const x1 = sj.add(x, 1);
  const y2 = sj.mul(2, y);
  // [name, args, latex(f(args, evaluate=False)), latex(Pow(f(args), 2, evaluate=False))]
  const cases: [FnName, sj.Expr[], string, string][] = [
  ["gamma", [x], "\\Gamma\\left(x\\right)", "\\Gamma^{2}\\left(x\\right)"],
  ["gamma", [x1], "\\Gamma\\left(x + 1\\right)", "\\Gamma^{2}\\left(x + 1\\right)"],
  ["zeta", [x], "\\zeta\\left(x\\right)", "\\zeta^{2}\\left(x\\right)"],
  ["zeta", [x1], "\\zeta\\left(x + 1\\right)", "\\zeta^{2}\\left(x + 1\\right)"],
  ["zeta", [x, y], "\\zeta\\left(x, y\\right)", "\\zeta^{2}\\left(x, y\\right)"],
  ["zeta", [x1, y2], "\\zeta\\left(x + 1, 2 y\\right)", "\\zeta^{2}\\left(x + 1, 2 y\\right)"],
  ["Chi", [x], "\\operatorname{Chi}\\left(x\\right)", "\\operatorname{Chi}^{2}\\left(x\\right)"],
  ["Chi", [x1], "\\operatorname{Chi}\\left(x + 1\\right)", "\\operatorname{Chi}^{2}\\left(x + 1\\right)"],
  ["fresnels", [x], "S\\left(x\\right)", "S^{2}\\left(x\\right)"],
  ["fresnels", [x1], "S\\left(x + 1\\right)", "S^{2}\\left(x + 1\\right)"],
  ["fresnelc", [x], "C\\left(x\\right)", "C^{2}\\left(x\\right)"],
  ["fresnelc", [x1], "C\\left(x + 1\\right)", "C^{2}\\left(x + 1\\right)"],
  ["lowergamma", [x, y], "\\gamma\\left(x, y\\right)", "\\gamma^{2}\\left(x, y\\right)"],
  ["lowergamma", [x1, y2], "\\gamma\\left(x + 1, 2 y\\right)", "\\gamma^{2}\\left(x + 1, 2 y\\right)"],
  ["uppergamma", [x, y], "\\Gamma\\left(x, y\\right)", "\\Gamma^{2}\\left(x, y\\right)"],
  ["uppergamma", [x1, y2], "\\Gamma\\left(x + 1, 2 y\\right)", "\\Gamma^{2}\\left(x + 1, 2 y\\right)"],
  ["mobius", [x], "\\mu\\left(x\\right)", "\\mu^{2}\\left(x\\right)"],
  ["mobius", [x1], "\\mu\\left(x + 1\\right)", "\\mu^{2}\\left(x + 1\\right)"],
  ["bernoulli", [x], "B_{x}", "B_{x}^{2}"],
  ["bernoulli", [x1], "B_{x + 1}", "B_{x + 1}^{2}"],
  ["bernoulli", [x, y], "B_{x}\\left(y\\right)", "B_{x}^{2}\\left(y\\right)"],
  ["bernoulli", [x1, y2], "B_{x + 1}\\left(2 y\\right)", "B_{x + 1}^{2}\\left(2 y\\right)"],
  ["genocchi", [x], "G_{x}", "G_{x}^{2}"],
  ["genocchi", [x1], "G_{x + 1}", "G_{x + 1}^{2}"],
  ["genocchi", [x, y], "G_{x}\\left(y\\right)", "G_{x}^{2}\\left(y\\right)"],
  ["genocchi", [x1, y2], "G_{x + 1}\\left(2 y\\right)", "G_{x + 1}^{2}\\left(2 y\\right)"],
  ["bell", [x], "B_{x}", "B_{x}^{2}"],
  ["bell", [x1], "B_{x + 1}", "B_{x + 1}^{2}"],
  ["bell", [x, y], "B_{x}\\left(y\\right)", "B_{x}^{2}\\left(y\\right)"],
  ["bell", [x1, y2], "B_{x + 1}\\left(2 y\\right)", "B_{x + 1}^{2}\\left(2 y\\right)"],
  ["fibonacci", [x], "F_{x}", "F_{x}^{2}"],
  ["fibonacci", [x1], "F_{x + 1}", "F_{x + 1}^{2}"],
  ["fibonacci", [x, y], "F_{x}\\left(y\\right)", "F_{x}^{2}\\left(y\\right)"],
  ["fibonacci", [x1, y2], "F_{x + 1}\\left(2 y\\right)", "F_{x + 1}^{2}\\left(2 y\\right)"],
  ["tribonacci", [x], "T_{x}", "T_{x}^{2}"],
  ["tribonacci", [x1], "T_{x + 1}", "T_{x + 1}^{2}"],
  ["tribonacci", [x, y], "T_{x}\\left(y\\right)", "T_{x}^{2}\\left(y\\right)"],
  ["tribonacci", [x1, y2], "T_{x + 1}\\left(2 y\\right)", "T_{x + 1}^{2}\\left(2 y\\right)"],
  ["totient", [x], "\\phi\\left(x\\right)", "\\left(\\phi\\left(x\\right)\\right)^{2}"],
  ["totient", [x1], "\\phi\\left(x + 1\\right)", "\\left(\\phi\\left(x + 1\\right)\\right)^{2}"],
  ["reduced_totient", [x], "\\lambda\\left(x\\right)", "\\left(\\lambda\\left(x\\right)\\right)^{2}"],
  ["reduced_totient", [x1], "\\lambda\\left(x + 1\\right)", "\\left(\\lambda\\left(x + 1\\right)\\right)^{2}"],
  ["primenu", [x], "\\nu\\left(x\\right)", "\\left(\\nu\\left(x\\right)\\right)^{2}"],
  ["primenu", [x1], "\\nu\\left(x + 1\\right)", "\\left(\\nu\\left(x + 1\\right)\\right)^{2}"],
  ["primeomega", [x], "\\Omega\\left(x\\right)", "\\left(\\Omega\\left(x\\right)\\right)^{2}"],
  ["primeomega", [x1], "\\Omega\\left(x + 1\\right)", "\\left(\\Omega\\left(x + 1\\right)\\right)^{2}"],
  ["besselj", [x, y], "J_{x}\\left(y\\right)", "J^{2}_{x}\\left(y\\right)"],
  ["besselj", [x1, y2], "J_{x + 1}\\left(2 y\\right)", "J^{2}_{x + 1}\\left(2 y\\right)"],
  ["jn", [x, y], "j_{x}\\left(y\\right)", "j^{2}_{x}\\left(y\\right)"],
  ["jn", [x1, y2], "j_{x + 1}\\left(2 y\\right)", "j^{2}_{x + 1}\\left(2 y\\right)"],
  ["yn", [x, y], "y_{x}\\left(y\\right)", "y^{2}_{x}\\left(y\\right)"],
  ["yn", [x1, y2], "y_{x + 1}\\left(2 y\\right)", "y^{2}_{x + 1}\\left(2 y\\right)"],
  ["log", [x], "\\log{\\left(x \\right)}", "\\log{\\left(x \\right)}^{2}"],
  ["log", [x1], "\\log{\\left(x + 1 \\right)}", "\\log{\\left(x + 1 \\right)}^{2}"],
  ["floor", [x], "\\left\\lfloor{x}\\right\\rfloor", "\\left\\lfloor{x}\\right\\rfloor^{2}"],
  ["floor", [x1], "\\left\\lfloor{x + 1}\\right\\rfloor", "\\left\\lfloor{x + 1}\\right\\rfloor^{2}"],
  ["ceiling", [x], "\\left\\lceil{x}\\right\\rceil", "\\left\\lceil{x}\\right\\rceil^{2}"],
  ["ceiling", [x1], "\\left\\lceil{x + 1}\\right\\rceil", "\\left\\lceil{x + 1}\\right\\rceil^{2}"],
  ["frac", [x], "\\operatorname{frac}{\\left(x\\right)}", "\\operatorname{frac}{\\left(x\\right)}^{2}"],
  ["frac", [x1], "\\operatorname{frac}{\\left(x + 1\\right)}", "\\operatorname{frac}{\\left(x + 1\\right)}^{2}"],
  ["factorial", [x], "x!", "x!^{2}"],
  ["factorial", [x1], "\\left(x + 1\\right)!", "\\left(x + 1\\right)!^{2}"],
  ["factorial2", [x], "x!!", "x!!^{2}"],
  ["factorial2", [x1], "\\left(x + 1\\right)!!", "\\left(x + 1\\right)!!^{2}"],
  ["subfactorial", [x], "!x", "\\left(!x\\right)^{2}"],
  ["subfactorial", [x1], "!\\left(x + 1\\right)", "\\left(!\\left(x + 1\\right)\\right)^{2}"],
  ["catalan", [x], "C_{x}", "C_{x}^{2}"],
  ["catalan", [x1], "C_{x + 1}", "C_{x + 1}^{2}"],
  ["lucas", [x], "L_{x}", "L_{x}^{2}"],
  ["lucas", [x1], "L_{x + 1}", "L_{x + 1}^{2}"],
  ["binomial", [x, y], "{\\binom{x}{y}}", "{\\binom{x}{y}}^{2}"],
  ["binomial", [x1, y2], "{\\binom{x + 1}{2 y}}", "{\\binom{x + 1}{2 y}}^{2}"],
  ["expint", [x, y], "\\operatorname{E}_{x}\\left(y\\right)", "\\operatorname{E}_{x}^{2}\\left(y\\right)"],
  ["expint", [x1, y2], "\\operatorname{E}_{x + 1}\\left(2 y\\right)", "\\operatorname{E}_{x + 1}^{2}\\left(2 y\\right)"],
  ["ff", [x, y], "{\\left(x\\right)}_{y}", "\\left({\\left(x\\right)}_{y}\\right)^{2}"],
  ["ff", [x1, y2], "{\\left(x + 1\\right)}_{\\left(2 y\\right)}", "\\left({\\left(x + 1\\right)}_{\\left(2 y\\right)}\\right)^{2}"],
  ["rf", [x, y], "{x}^{\\left(y\\right)}", "\\left({x}^{\\left(y\\right)}\\right)^{2}"],
  ["rf", [x1, y2], "{\\left(x + 1\\right)}^{\\left(2 y\\right)}", "\\left({\\left(x + 1\\right)}^{\\left(2 y\\right)}\\right)^{2}"],
  ["LambertW", [x], "W\\left(x\\right)", "W^{2}\\left(x\\right)"],
  ["LambertW", [x1], "W\\left(x + 1\\right)", "W^{2}\\left(x + 1\\right)"],
  ["LambertW", [x, y], "W_{y}\\left(x\\right)", "W^{2}_{y}\\left(x\\right)"],
  ["LambertW", [x1, y2], "W_{2 y}\\left(x + 1\\right)", "W^{2}_{2 y}\\left(x + 1\\right)"],
  ["euler", [x], "E_{x}", "E_{x}^{2}"],
  ["euler", [x1], "E_{x + 1}", "E_{x + 1}^{2}"],
  ["euler", [x, y], "E_{x}\\left(y\\right)", "E_{x}^{2}\\left(y\\right)"],
  ["euler", [x1, y2], "E_{x + 1}\\left(2 y\\right)", "E_{x + 1}^{2}\\left(2 y\\right)"],
  ["divisor_sigma", [x, y], "\\sigma_y\\left(x\\right)", "\\sigma^{2}_y\\left(x\\right)"],
  ["divisor_sigma", [x1, y2], "\\sigma_2 y\\left(x + 1\\right)", "\\sigma^{2}_2 y\\left(x + 1\\right)"],
  ["KroneckerDelta", [x, y], "\\delta_{x y}", "\\left(\\delta_{x y}\\right)^{2}"],
  ["Max", [x, y], "\\max\\left(x, y\\right)", "\\max\\left(x, y\\right)^{2}"],
  ["Max", [x1, y2], "\\max\\left(2 y, x + 1\\right)", "\\max\\left(2 y, x + 1\\right)^{2}"],
  ["Min", [x, y], "\\min\\left(x, y\\right)", "\\min\\left(x, y\\right)^{2}"],
  ["Min", [x1, y2], "\\min\\left(2 y, x + 1\\right)", "\\min\\left(2 y, x + 1\\right)^{2}"],
  ["polar_lift", [x], "\\operatorname{polar\\_lift}{\\left(x \\right)}", "\\operatorname{polar\\_lift}^{2}{\\left(x \\right)}"],
  ["polar_lift", [x1], "\\operatorname{polar\\_lift}{\\left(x + 1 \\right)}", "\\operatorname{polar\\_lift}^{2}{\\left(x + 1 \\right)}"],
  ["exp_polar", [x], "e^{x}", "\\left(e^{x}\\right)^{2}"],
  ["exp_polar", [x1], "e^{x + 1}", "\\left(e^{x + 1}\\right)^{2}"],
  ["atan2", [x, y], "\\operatorname{atan}_{2}{\\left(x,y \\right)}", "\\operatorname{atan}_{2}^{2}{\\left(x,y \\right)}"],
  ["atan2", [x1, y2], "\\operatorname{atan}_{2}{\\left(x + 1,2 y \\right)}", "\\operatorname{atan}_{2}^{2}{\\left(x + 1,2 y \\right)}"],
  ["erf2", [x, y], "\\operatorname{erf}_{2}{\\left(x,y \\right)}", "\\operatorname{erf}_{2}^{2}{\\left(x,y \\right)}"],
  ["erf2", [x1, y2], "\\operatorname{erf}_{2}{\\left(x + 1,2 y \\right)}", "\\operatorname{erf}_{2}^{2}{\\left(x + 1,2 y \\right)}"],
  ["polygamma", [x, y], "\\operatorname{polygamma}{\\left(x,y \\right)}", "\\operatorname{polygamma}^{2}{\\left(x,y \\right)}"],
  ["polygamma", [x1, y2], "\\operatorname{polygamma}{\\left(x + 1,2 y \\right)}", "\\operatorname{polygamma}^{2}{\\left(x + 1,2 y \\right)}"],
  ["Si", [x], "\\operatorname{Si}{\\left(x \\right)}", "\\operatorname{Si}^{2}{\\left(x \\right)}"],
  ["Si", [x1], "\\operatorname{Si}{\\left(x + 1 \\right)}", "\\operatorname{Si}^{2}{\\left(x + 1 \\right)}"],
  ["sign", [x], "\\operatorname{sign}{\\left(x \\right)}", "\\operatorname{sign}^{2}{\\left(x \\right)}"],
  ["sign", [x1], "\\operatorname{sign}{\\left(x + 1 \\right)}", "\\operatorname{sign}^{2}{\\left(x + 1 \\right)}"],
  ["harmonic", [x], "\\operatorname{harmonic}{\\left(x \\right)}", "\\operatorname{harmonic}^{2}{\\left(x \\right)}"],
  ["harmonic", [x1], "\\operatorname{harmonic}{\\left(x + 1 \\right)}", "\\operatorname{harmonic}^{2}{\\left(x + 1 \\right)}"],
    ['beta', [x, y], '\\operatorname{B}\\left(x, y\\right)', '\\operatorname{B}^{2}\\left(x, y\\right)'],
    ['beta', [x], '\\operatorname{B}\\left(x, x\\right)', '\\operatorname{B}^{2}\\left(x, x\\right)'],
    // SymPy evaluates divisor_sigma(x) to divisor_sigma(x, 1); its printer's one-argument form
    ['divisor_sigma', [x], '\\sigma\\left(x\\right)', '\\sigma^{2}\\left(x\\right)'],
    ['KroneckerDelta', [x1, y2], '\\delta_{x + 1, 2 y}', '\\left(\\delta_{x + 1, 2 y}\\right)^{2}'],
  ];
  for (const [name, args, tex, tex2] of cases) {
    it(`${name}(${args.map(sj.str).join(', ')})`, () => {
      const e = new Fn(name, args);
      expect(latex(e)).toBe(tex);
      expect(latex(new Pow(e, R(2)))).toBe(tex2);
    });
  }
  // SymPy _print_beta formats the arguments with str (B(x + 1, 2*y))\\; the LaTeX form of the arguments is kept here
  it('beta with compound arguments prints them in LaTeX', () => {
    expect(latex(new Fn('beta', [x1, y2]))).toBe('\\operatorname{B}\\left(x + 1, 2 y\\right)');
  });
});

describe('latex: undefined function names and other forms', () => {
  const cases: [string, () => sj.Expr, string][] = [
    ['f_a(x)', () => sj.SymFunction('f_a')(x), 'f_{a}{\\left(x \\right)}'],
    ['f_a(x)**2', () => sj.pow(sj.SymFunction('f_a')(x), 2), 'f_{a}^{2}{\\left(x \\right)}'],
    ['f__b(x)', () => sj.SymFunction('f__b')(x), 'f^{b}{\\left(x \\right)}'],
    ['f__b(x)**2', () => sj.pow(sj.SymFunction('f__b')(x), 2), '\\left(f^{b}\\right)^{2}{\\left(x \\right)}'],
    ['my_func(x)', () => sj.SymFunction('my_func')(x), '\\operatorname{my}_{func}{\\left(x \\right)}'],
    ['my_func(x)**2', () => sj.pow(sj.SymFunction('my_func')(x), 2), '\\operatorname{my}_{func}^{2}{\\left(x \\right)}'],
    ['Gamma1(x)', () => sj.SymFunction('Gamma1')(x), '\\Gamma_{1}{\\left(x \\right)}'],
    ['alpha(x)', () => sj.SymFunction('alpha')(x), '\\alpha{\\left(x \\right)}'],
    ['f_a__b(x)', () => sj.SymFunction('f_a__b')(x), 'f^{b}_{a}{\\left(x \\right)}'],
    ['xi_1(x, y)', () => sj.SymFunction('xi_1')(x, y), '\\xi_{1}{\\left(x,y \\right)}'],
    ['x__a**2', () => sj.pow(sj.symbol('x__a'), 2), '\\left(x^{a}\\right)^{2}'],
    ['Derivative(f(x__a), (x__a, 2))', () => sj.Derivative(sj.SymFunction('f')(sj.symbol('x__a')), [sj.symbol('x__a'), 2]), '\\frac{d^{2}}{d \\left(x^{a}\\right)^{2}} f{\\left(x^{a} \\right)}'],
    ['y*x**(-n)', () => sj.mul(y, sj.pow(x, sj.neg(n))), 'x^{- n} y'],
    ['y*x**(-pi)', () => sj.mul(y, sj.pow(x, sj.neg(S.Pi))), '\\frac{y}{x^{\\pi}}'],
    ['-2*x*y', () => sj.mul(-2, x, y), '- 2 x y'],
    ['-1/2', () => R(-1, 2), '- \\frac{1}{2}'],
    ['Sum(k, (k, 1, n))', () => sj.Sum(k, [k, 1, m]), '\\sum_{k=1}^{m} k'],
    ['Sum(k + 1, (k, 1, n))', () => sj.Sum(sj.add(k, 1), [k, 1, m]), '\\sum_{k=1}^{m} \\left(k + 1\\right)'],
    ['Sum(k*j, (k, 1, m), (j, 0, 2))', () => sj.Sum(sj.mul(k, j), [k, 1, m], [j, 0, 2]), '\\sum_{\\substack{1 \\leq k \\leq m\\\\0 \\leq j \\leq 2}} j k'],
    ['Product(k, (k, 1, m))', () => sj.Product(k, [k, 1, m]), '\\prod_{k=1}^{m} k'],
    ['Product(k + 1, (k, 1, m), (j, 1, 3))', () => sj.Product(sj.add(k, 1), [k, 1, m], [j, 1, 3]), '\\prod_{\\substack{1 \\leq k \\leq m\\\\1 \\leq j \\leq 3}} \\left(k + 1\\right)'],
  ];
  for (const [label, build, tex] of cases) it(label, () => expect(latex(build())).toBe(tex));
});

describe('latex: sets', () => {
  const I01 = Sets.interval(0, 1);
  const I23 = Sets.interval(2, 3);
  const cases: [string, () => sj.Expr, string][] = [
    ['Interval(0, 1)', () => I01, '\\left[0, 1\\right]'],
    ['Interval.open(0, 1)', () => Sets.openInterval(0, 1), '\\left(0, 1\\right)'],
    ['Interval.Lopen(0, x)', () => Sets.Lopen(0, x), '\\left(0, x\\right]'],
    ['Interval.Ropen(-oo, 1)', () => Sets.Ropen(S.NegativeInfinity, 1), '\\left(-\\infty, 1\\right)'],
    ['Interval(x, x) node', () => new Sets.Interval(x, x, false, false), '\\left\\{x\\right\\}'],
    ['FiniteSet(y, 1, x)', () => Sets.finiteSet(y, 1, x), '\\left\\{1, x, y\\right\\}'],
    ['EmptySet', () => Sets.EmptySet, '\\emptyset'],
    ['UniversalSet', () => Sets.UniversalSet, '\\mathbb{U}'],
    ['Reals', () => Sets.Reals, '\\mathbb{R}'],
    ['Integers', () => Sets.Integers, '\\mathbb{Z}'],
    ['Naturals', () => Sets.Naturals, '\\mathbb{N}'],
    ['Naturals0', () => Sets.Naturals0, '\\mathbb{N}_0'],
    ['Complexes', () => Sets.Complexes, '\\mathbb{C}'],
    ['Union(Interval(2, 3), Interval(0, 1))', () => Sets.union(I23, I01), '\\left[0, 1\\right] \\cup \\left[2, 3\\right]'],
    ['Intersection(Interval(0, x), FiniteSet(y), evaluate=False)', () => new Sets.SetOp('Intersection', [Sets.interval(0, x), Sets.finiteSet(y)]), '\\left[0, x\\right] \\cap \\left\\{y\\right\\}'],
    ['Complement(Interval(0, 1), FiniteSet(x), evaluate=False)', () => new Sets.SetOp('Complement', [I01, Sets.finiteSet(x)]), '\\left[0, 1\\right] \\setminus \\left\\{x\\right\\}'],
    [
      'Intersection(Union(Interval(0, 1), Interval(2, 3)), Interval(x, y), evaluate=False)',
      () => new Sets.SetOp('Intersection', [new Sets.SetOp('Union', [I01, I23]), Sets.interval(x, y)]),
      '\\left(\\left[0, 1\\right] \\cup \\left[2, 3\\right]\\right) \\cap \\left[x, y\\right]',
    ],
    [
      'Complement(S.Reals, Union(FiniteSet(x), Interval(0, 1)), evaluate=False)',
      () => new Sets.SetOp('Complement', [Sets.Reals, new Sets.SetOp('Union', [Sets.finiteSet(x), I01])]),
      '\\mathbb{R} \\setminus \\left(\\left[0, 1\\right] \\cup \\left\\{x\\right\\}\\right)',
    ],
    ['Union(Interval(0, 1), FiniteSet(0, 5), evaluate=False)', () => new Sets.SetOp('Union', [I01, Sets.finiteSet(0, 5)]), '\\left\\{0, 5\\right\\} \\cup \\left[0, 1\\right]'],
    ['ImageSet(Lambda(x, x**2), S.Naturals)', () => new Sets.ImageSet(x, sj.pow(x, 2), Sets.Naturals), '\\left\\{x^{2}\\; \\middle|\\; x \\in \\mathbb{N}\\right\\}'],
    [
      'ConditionSet(x, Eq(sin(x), 0), S.Reals)',
      () => new Sets.ConditionSet(x, sj.Eq(sj.sin(x), 0), Sets.Reals),
      '\\left\\{x\\; \\middle|\\; x \\in \\mathbb{R} \\wedge \\sin{\\left(x \\right)} = 0 \\right\\}',
    ],
    ['ConditionSet(x, x > 0, S.UniversalSet)', () => new Sets.ConditionSet(x, sj.Gt(x, 0), Sets.UniversalSet), '\\left\\{x\\; \\middle|\\; x > 0 \\right\\}'],
  ];
  for (const [label, build, tex] of cases) it(label, () => expect(latex(build())).toBe(tex));

  it('a set or expression class the printer does not know prints as its key', () => {
    class MySet extends Sets.SetExpr {
      readonly args: readonly sj.Expr[] = [];
      get className(): string {
        return 'MySet';
      }
      protected computeKey(): string {
        return 'MySet()';
      }
    }
    // an Expr subclass outside the library's node classes
    class MyExpr extends sj.Expr {
      readonly kind = 'Extension' as const;
      readonly args: readonly sj.Expr[] = [];
      protected computeKey(): string {
        return 'MyExpr()';
      }
    }
    expect(latex(new MySet())).toBe('MySet()');
    expect(latex(new MyExpr())).toBe('MyExpr()');
  });
});

describe('latex and str: factors whose node precedence is below Mul', () => {
  // A, B = MatrixSymbol('A', 3, 1), MatrixSymbol('B', 3, 1)
  const A = MatrixSymbol('A', 3, 1);
  const B = MatrixSymbol('B', 3, 1);
  const cases: [string, () => sj.Expr, string, string][] = [
    ['2*DotProduct(A, A)', () => sj.mul(2, DotProduct(A, A)), '2*DotProduct(A, A)', '2 \\left(A \\cdot A\\right)'],
    ['x*DotProduct(A, B)', () => sj.mul(x, DotProduct(A, B)), 'x*DotProduct(A, B)', 'x \\left(A \\cdot B\\right)'],
    ['-DotProduct(A, B)', () => sj.neg(DotProduct(A, B)), '-DotProduct(A, B)', '- A \\cdot B'],
    ['DotProduct(A, B)**2', () => sj.pow(DotProduct(A, B), 2), 'DotProduct(A, B)**2', '\\left(A \\cdot B\\right)^{2}'],
    ['DotProduct(A, B) + x', () => sj.add(DotProduct(A, B), x), 'x + DotProduct(A, B)', 'x + A \\cdot B'],
    ['2*x*DotProduct(A, B)/3', () => sj.mul(R(2, 3), x, DotProduct(A, B)), '2*x*DotProduct(A, B)/3', '\\frac{2 x \\left(A \\cdot B\\right)}{3}'],
  ];
  for (const [label, build, s, tex] of cases) {
    it(label, () => {
      const e = build();
      expect(sj.str(e)).toBe(s);
      expect(latex(e)).toBe(tex);
    });
  }
});

/**
 * Coverage of the str printer and the printing sort keys: expected
 * values are SymPy 1.14 `str(expr)`, `latex(expr)` and
 * `expr.as_ordered_terms()` / `sorted(..., key=default_sort_key)`.
 */

describe('latex of negative infinity terms', () => {
  it('x - oo', () => expect(latex(sj.add(x, S.NegativeInfinity))).toBe('x - \\infty'));
  it('Add(x, -oo, evaluate=False)', () => expect(latex(new Add([x, S.NegativeInfinity]))).toBe('x - \\infty'));
  it('Pow(-oo, x, evaluate=False)', () => expect(latex(new Pow(S.NegativeInfinity, x))).toBe('\\left(-\\infty\\right)^{x}'));
  it('-oo*x/y', () => expect(latex(sj.mul(S.NegativeInfinity, x, sj.pow(y, -1)))).toBe('- \\frac{\\infty x}{y}'));
  it('Pow(-oo*x, 2, evaluate=False)', () => expect(latex(new Pow(sj.mul(S.NegativeInfinity, x), R(2)))).toBe('\\left(- \\infty x\\right)^{2}'));
  it('-oo*x + y', () => expect(latex(sj.add(sj.mul(S.NegativeInfinity, x), y))).toBe('- \\infty x + y'));
  it('Mul(-oo, x, evaluate=False)', () => expect(latex(new Mul([S.NegativeInfinity, x]))).toBe('- \\infty x'));
});

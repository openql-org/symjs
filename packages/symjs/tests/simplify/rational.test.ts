// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/simplify/rational.ts.

// Expected values are the str() forms printed by SymPy 1.14 unless a comment says otherwise.

import { describe, expect, it } from 'vitest';
import { DiracDelta, Dummy, Float, Heaviside, Sym, add, cancel, fraction, mul, parse, pow, ratsimp, symbol, together } from '../../src';
import type { Expr } from '../../src';

const P = (s: string) => parse(s, { locals: { Heaviside, DiracDelta } });
const Qs = (s: string, syms: Sym[]) => parse(s, { symbols: syms, locals: { Heaviside, DiracDelta } });
const show = (v: unknown): string => (Array.isArray(v) ? `[${v.map(String).join(', ')}]` : String(v));
type Assume = NonNullable<Parameters<typeof symbol>[1]>;
const PA = (s: string, a: Record<string, Assume> = {}): Expr =>
  parse(s, { symbols: Object.entries(a).map(([k, v]) => symbol(k, v)) });
const showMap = (v: unknown): string => {
  if (Array.isArray(v)) return `[${v.map(showMap).join(', ')}]`;
  if (v instanceof Map) return `{${[...v].map(([k, w]) => `${showMap(k)}: ${showMap(w)}`).sort().join(', ')}}`;
  return String(v);
};
const [x] = [symbol('x'), symbol('y')];

describe("simplify functions: SymPy 1.14 test cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["ratsimp(P(\"1/y + 1/x\"))", () => ratsimp(P("1/y + 1/x")), "(x + y)/(x*y)"],
    ["ratsimp(P(\"1/(1 + 1/x)\"))", () => ratsimp(P("1/(1 + 1/x)")), "1 - 1/(x + 1)"],
    ["ratsimp(P(\"x/(x + y) + y/(x + y)\"))", () => ratsimp(P("x/(x + y) + y/(x + y)")), "1"],
    ["ratsimp(P(\"x**2/(x + y) - x - y**2/(x + y) - y\"))", () => ratsimp(P("x**2/(x + y) - x - y**2/(x + y) - y")), "-2*y"],
    ["ratsimp(P(\"(a*c*x*y + a*c*z - b*d*x*y - b*d*z - b*t*x*y - b*t*x - b*t*z + e*x)/(x*y + z)\"))", () => ratsimp(P("(a*c*x*y + a*c*z - b*d*x*y - b*d*z - b*t*x*y - b*t*x - b*t*z + e*x)/(x*y + z)")), "a*c - b*d - b*t + (-b*t*x + e*x)/(x*y + z)"],
    ["together(0)", () => together(0), "0"],
    ["together(1)", () => together(1), "1"],
    ["together(P(\"x*y*z\"))", () => together(P("x*y*z")), "x*y*z"],
    ["together(P(\"x + y\"))", () => together(P("x + y")), "x + y"],
    ["together(P(\"1/x\"))", () => together(P("1/x")), "1/x"],
    ["together(P(\"1 + 1/x\"))", () => together(P("1 + 1/x")), "(x + 1)/x"],
    ["together(P(\"3 + 1/x\"))", () => together(P("3 + 1/x")), "(3*x + 1)/x"],
    ["together(P(\"x + 1/x\"))", () => together(P("x + 1/x")), "(x**2 + 1)/x"],
    ["together(P(\"1/2 + 1/x\"))", () => together(P("1/2 + 1/x")), "(x + 2)/(2*x)"],
    ["together(P(\"x/2 + 1/2\"))", () => together(P("x/2 + 1/2")), "(x + 1)/2"],
    ["together(P(\"2/y + 1/x\"))", () => together(P("2/y + 1/x")), "(2*x + y)/(x*y)"],
    ["together(P(\"1/(1 + 1/x)\"))", () => together(P("1/(1 + 1/x)")), "x/(x + 1)"],
    ["together(P(\"x/(1 + 1/x)\"))", () => together(P("x/(1 + 1/x)")), "x**2/(x + 1)"],
    ["together(P(\"1/z + 1/y + 1/x\"))", () => together(P("1/z + 1/y + 1/x")), "(x*y + x*z + y*z)/(x*y*z)"],
    ["together(P(\"1/(x + 1 + 1/z + 1/y)\"))", () => together(P("1/(x + 1 + 1/z + 1/y)")), "y*z/(x*y*z + y*z + y + z)"],
    ["together(P(\"1/(x*y) + 1/(x**2*y**2)\"))", () => together(P("1/(x*y) + 1/(x**2*y**2)")), "(x*y + 1)/(x**2*y**2)"],
    ["together(P(\"1/(x*y) + 1/(x**4*y**4)\"))", () => together(P("1/(x*y) + 1/(x**4*y**4)")), "(x**3*y**3 + 1)/(x**4*y**4)"],
    ["together(P(\"1/(x**4*y**4) + 1/(x**7*y)\"))", () => together(P("1/(x**4*y**4) + 1/(x**7*y)")), "(x**3 + y**3)/(x**7*y**4)"],
    ["together(P(\"5/(2 + 6/(3 + 7/(4 + 8/(5 + 9/x))))\"))", () => together(P("5/(2 + 6/(3 + 7/(4 + 8/(5 + 9/x))))")), "5*(119*x + 171)/(2*(203*x + 279))"],
    ["together(P(\"1 + (x + 1)**(-2)\"))", () => together(P("1 + (x + 1)**(-2)")), "((x + 1)**2 + 1)/(x + 1)**2"],
    ["together(P(\"1 + 1/(x*(x + 1))\"))", () => together(P("1 + 1/(x*(x + 1))")), "(x*(x + 1) + 1)/(x*(x + 1))"],
    ["together(P(\"1/(x*(x + 2)) + 1/(x*(x + 1))\"))", () => together(P("1/(x*(x + 2)) + 1/(x*(x + 1))")), "(2*x + 3)/(x*(x + 1)*(x + 2))"],
    ["together(P(\"1 + (2*x + 2)**(-2)\"))", () => together(P("1 + (2*x + 2)**(-2)")), "(4*(x + 1)**2 + 1)/(4*(x + 1)**2)"],
    ["together(P(\"sin(1/y + 1/x)\"))", () => together(P("sin(1/y + 1/x)")), "sin(1/y + 1/x)"],
    ["together(P(\"exp(-x) + exp(-x)/x\"))", () => together(P("exp(-x) + exp(-x)/x")), "(x + 1)*exp(-x)/x"],
    ["together(P(\"exp(-2*x) + exp(-3*x)/x\"))", () => together(P("exp(-2*x) + exp(-3*x)/x")), "(x*exp(x) + 1)*exp(-3*x)/x"],
    ["together(P(\"Eq(1/y + 1/x, 1 + 1/z)\"))", () => together(P("Eq(1/y + 1/x, 1 + 1/z)")), "Eq((x + y)/(x*y), (z + 1)/z)"],
    ["together(Qs(\"(A*B)**(-1) + (B*A)**(-1)\", [symbol(\"A\", { commutative: false }), symbol(\"B\", { commutative: false })]))", () => together(Qs("(A*B)**(-1) + (B*A)**(-1)", [symbol("A", { commutative: false }), symbol("B", { commutative: false })])), "(A*B)**(-1) + (B*A)**(-1)"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(show(run())).toBe(want);
  });
});

describe("simplify (cov2): SymPy 1.14 cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["fraction(P('2*x**-2*y/3', {y: {positive: true}}), { exact: true })", () => fraction(PA('2*x**-2*y/3', {y: {positive: true}}), { exact: true }), "[2*y, 3*x**2]"],
    ["fraction(P('x**-y', {y: {positive: true}}), { exact: true })", () => fraction(PA('x**-y', {y: {positive: true}}), { exact: true }), "[x**(-y), 1]"],
    ["fraction(P('x**-y', {y: {positive: true}}))", () => fraction(PA('x**-y', {y: {positive: true}})), "[1, x**y]"],
    ["fraction(P('x**(-sqrt(2))*y'), { exact: true })", () => fraction(PA('x**(-sqrt(2))*y'), { exact: true }), "[y, x**(sqrt(2))]"],
    ["fraction(P('x'), { exact: true })", () => fraction(PA('x'), { exact: true }), "[x, 1]"],
    ["fraction(P('1/x'), { exact: true })", () => fraction(PA('1/x'), { exact: true }), "[1, x]"],
    ["fraction(P('x/3'), { exact: true })", () => fraction(PA('x/3'), { exact: true }), "[x, 3]"],
    ["fraction(P('exp(-x)*x'), { exact: true })", () => fraction(PA('exp(-x)*x'), { exact: true }), "[x*exp(-x), 1]"],
    ["fraction(P('3/(x*y)'), { exact: true })", () => fraction(PA('3/(x*y)'), { exact: true }), "[3, x*y]"],
    ["fraction(P('x**(-1/2)'), { exact: true })", () => fraction(PA('x**(-1/2)'), { exact: true }), "[1, sqrt(x)]"],
    ["together(P('(1/x + 1/y)**(1/z + 1)'), { deep: true })", () => together(PA('(1/x + 1/y)**(1/z + 1)'), { deep: true }), "((x + y)/(x*y))**((z + 1)/z)"],
    ["together(P('exp(1/x + 1/y)'), { deep: true })", () => together(PA('exp(1/x + 1/y)'), { deep: true }), "exp((x + y)/(x*y))"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(showMap(run())).toBe(want);
  });
});

describe("ratsimpmodprime, gammasimp, signsimp, cancel, ratsimp (cov2): SymPy 1.14 cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["cancel(P('(sqrt(2) + sqrt(3)*x)/(x + 1)'))", () => cancel(PA('(sqrt(2) + sqrt(3)*x)/(x + 1)')), "(sqrt(3)*x + sqrt(2))/(x + 1)"],
    ["cancel(P('(sqrt(3) + sqrt(15)*x)/(sqrt(2) + sqrt(10)*x)'))", () => cancel(PA('(sqrt(3) + sqrt(15)*x)/(sqrt(2) + sqrt(10)*x)')), "sqrt(6)/2"],
    ["cancel(P('(sqrt(2)*x + sqrt(6))/(sqrt(3)*x + 3)'))", () => cancel(PA('(sqrt(2)*x + sqrt(6))/(sqrt(3)*x + 3)')), "(sqrt(2)*x + sqrt(6))/(sqrt(3)*x + 3)"],
    ["ratsimp(P('(x**2 + y)/(x + y)'))", () => ratsimp(PA('(x**2 + y)/(x + y)')), "x - y + (y**2 + y)/(x + y)"],
    ["ratsimp(P('(x**3 + 2*x*y + y**2)/(x - y)'))", () => ratsimp(PA('(x**3 + 2*x*y + y**2)/(x - y)')), "x**2 + x*y + y**2 + 2*y + (y**3 + 3*y**2)/(x - y)"],
    ["ratsimp(P('(x**2 + 1)/2'))", () => ratsimp(PA('(x**2 + 1)/2')), "x**2/2 + 1/2"],
    ["ratsimp(P('x/(x*y + y)'))", () => ratsimp(PA('x/(x*y + y)')), "x/(x*y + y)"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(showMap(run())).toBe(want);
  });
});

describe('ratsimp and cancel (cov2): a Dummy and a Symbol with the same name', () => {
  it('orders the generators by name and divides', () => {
    const d = new Dummy('x');
    // the value is that of (x**2 + d)/(x + d) for two different symbols named x
    const e = mul(add(pow(x, 2), d), pow(add(x, d), -1));
    const r = ratsimp(e);
    const at = (v: Expr) => v.subs([[x, 2], [d, 5]]).toNumber();
    expect(at(r)).toBeCloseTo(9 / 7, 12);
    expect(at(cancel(e))).toBeCloseTo(9 / 7, 12);
  });
});

describe('cancel and ratsimp over all the generators (SymPy 1.14)', () => {
  it('cancel makes the leading coefficient of the denominator positive', () => {
    const cases: [string, string][] = [
      ['1/(x2 - x1*x10)', '-1/(x1*x10 - x2)'],
      ['(x + y)/(2 - x*y)', '(-x - y)/(x*y - 2)'],
      ['1/(I - x*sin(y))', '-1/(x*sin(y) - I)'],
      ['x/(1 - sin(x)*x)', '-x/(x*sin(x) - 1)'],
      ['1/(2 - sin(x))', '-1/(sin(x) - 2)'],
      ['2/(8 - 8*erf(x))', '-1/(4*erf(x) - 4)'],
      // a Gaussian leading coefficient is moved into the first quadrant
      ['1/(-I*x*y - 1)', 'I/(x*y - I)'],
      ['1/(I*x*y - 1)', '-I/(x*y + I)'],
      ['1/(-I*sin(x) + 2)', 'I/(sin(x) + 2*I)'],
      // the Gaussian coefficient is kept collected, as SymPy's as_expr prints it
      ['1/((1 - I)*x*y + 1)', 'I/(x*y*(1 + I) + I)'],
      ['1/((-1 + I)*x*y + 1)', '-I/(x*y*(1 + I) - I)'],
    ];
    for (const [e, r] of cases) expect(String(cancel(parse(e)))).toBe(r);
  });
  it('ratsimp divides in functions and radicals as generators', () => {
    const cases: [string, string][] = [
      ['-sqrt(pi)*log(erf(x) - 1)*erf(x)/(8 - 8*erf(x)) + sqrt(pi)*log(erf(x) - 1)/(8 - 8*erf(x)) + sqrt(pi)*log(erf(x) + 1)*erf(x)/(8 - 8*erf(x)) - sqrt(pi)*log(erf(x) + 1)/(8 - 8*erf(x)) + 2*sqrt(pi)/(8 - 8*erf(x))',
        'sqrt(pi)*log(erf(x) - 1)/8 - sqrt(pi)*log(erf(x) + 1)/8 - sqrt(pi)/(4*erf(x) - 4)'],
      ['(x*exp(x) + exp(2*x))/(exp(x) + 1)', 'x + (1 - x)/(exp(x) + 1) + exp(x) - 1'],
      ['sin(x)/(sin(x)*cos(x) + sin(x))', '1/(cos(x) + 1)'],
      ['(a*x + a**2)/(x - a)', '2*a**2/(-a + x) + a'],
    ];
    for (const [e, r] of cases) expect(String(ratsimp(parse(e)))).toBe(r);
  });
});

describe('cancel: SymPy PolyElement.cancel normalisation', () => {
  // integer (Gaussian) coefficients with the denominators cleared, the gcd of the contents
  // cancelled, and the lex-leading coefficient of the denominator canonical (positive, or in the
  // first quadrant); generators that are not symbols (sin(x), exp(x), sqrt(2), pi) are polynomial variables
  const cases: [string, string][] = [
    ['(-63*x + 15)/(5*x**2 - 6*x + 1)', '(15 - 63*x)/(5*x**2 - 6*x + 1)'],
    ['(x/2 + 1)/(x/3 - 1)', '(3*x + 6)/(2*x - 6)'],
    ['(2*x + 4)/(6*x**2)', '(x + 2)/(3*x**2)'],
    ['(x + I/2)/(3*x + I)', '(2*x + I)/(6*x + 2*I)'],
    ['(sin(x)**2 - 1)/(2*sin(x) - 2)', 'sin(x)/2 + 1/2'],
    ['(exp(x)**2 - 1)/(exp(x) + 1)', 'exp(x) - 1'],
    ['(x**2 + 1)/(x - I)', 'x + I'],
    ['(x**2 + 2*x + 1)/(2*I*x + 2*I)', '-I*x/2 - I/2'],
    ['(x**2 + y**2)/((1 + I)*x + (1 - I)*y)', '(1 - I)*(x + I*y)/2'],
    ['(x + 1)/(1 - I*x)', '(I*x + I)/(x + I)'],
    ['(x**2 - 1)/(x**2/2 + x + 1/2)', '(2*x - 2)/(x + 1)'],
    ['(6*x**2*y + 4*x*y**2)/(9*x*y/2)', '4*x/3 + 8*y/9'],
    ['(x + y)/(-2*x - 2*y + 4)', '(-x - y)/(2*x + 2*y - 4)'],
    ['(x**2 - 2)/(x - sqrt(2))', '(x**2 - 2)/(x - sqrt(2))'],
    ['(pi*x + pi)/(x + 1)', 'pi'],
  ];
  it.each(cases)('cancel(%s)', (src, want) => {
    expect(String(cancel(P(src)))).toBe(want);
  });
  it('the generating function of 3*5**n + 12', () => {
    // SymPy: cancel(3*(5 - 21*x)/((x - 1)*(5*x - 1)))
    expect(String(cancel(P('3*(5 - 21*x)/((x - 1)*(5*x - 1))')))).toBe('(15 - 63*x)/(5*x**2 - 6*x + 1)');
  });
  it('a unit I for a leading coefficient in the fourth quadrant', () => {
    expect(String(cancel(P('(x + 1)/((1 - I)*x + 1)')))).toBe('(I*x + I)/(x*(1 + I) + I)');
  });
  // SymPy's domain RR: the Floats as rationals (mpmath to_rational with limit), the cofactors of
  // the monic gcd over QQ, and every coefficient a Float again
  it.each([
    ['(2.0*x + 1)/(4*x + 2.0)', '0.500000000000000'],
    ['(0.5*x+1)/(x+2)', '0.500000000000000'],
    ['(0.1*x+0.2)/(x+2)', '0.100000000000000'],
    ['(-0.1*x - 0.2)/(x + 2)', '-0.100000000000000'],
    ['(x**2-1.0)/(x-1)', '1.0*x + 1.0'],
    ['(1.5*x*y+3*y)/(x+2)', '1.5*y'],
    ['x/(2.5*x+1)', '1.0*x/(2.5*x + 1.0)'],
    ['(-x+0.5)/(-2*x+1)', '0.500000000000000'],
    ['(x+0.3)/(x**2 + 0.6*x + 0.09)', '1.0/(1.0*x + 0.3)'],
    ['(x-0.1)/(x**2-0.2*x+0.01)', '1.0/(1.0*x - 0.1)'],
    ['(x**2+0.5)/(2*x)', '0.5*(1.0*x**2 + 0.5)/x'],
    ['(0.1*x+0.3)/(0.2*x)', '1.0*(0.5*x + 1.5)/x'],
    ['(0.8474337369372327*x+0.8474337369372327)/(x+1)', '0.8474337369372327'],
  ])('cancel(%s) over RR', (src, want) => {
    expect(String(cancel(P(src)))).toBe(want);
  });
  it('a 53-bit Float whose nearer continued-fraction bound is the larger-denominator one', () => {
    // SymPy: v = Float(0.8474337369372327); cancel((v*x + v)/(x + 1)) = 0.847433736937233
    const v = new Float(0.8474337369372327);
    expect(String(cancel(mul(add(mul(v, x), v), pow(add(x, 1), -1))))).toBe('0.847433736937233');
  });
  // SymPy as_numer_denom of a sum: exp(-x) = 1/exp(x) goes to the denominator
  it.each([
    ['x + exp(-x)', '(x*exp(x) + 1)*exp(-x)'],
    ['(1 + exp(-x))/(x + 1)', '(exp(x) + 1)/(x*exp(x) + exp(x))'],
    ['exp(-x)*y + x*exp(-x)', '(x + y)*exp(-x)'],
    ['-sqrt(2)*I*sqrt(pi)*exp(-x**2/2)*erf(sqrt(2)*I*x/2)/2 + exp(-x**2/2)', '(-sqrt(2)*I*sqrt(pi)*erf(sqrt(2)*I*x/2) + 2)*exp(-x**2/2)/2'],
  ])('cancel(%s) with exponentials of negative arguments', (src, want) => {
    expect(String(cancel(P(src)))).toBe(want);
  });
  // Floats over a numeric denominator and without one are converted too; zoo and oo stay as they are
  it.each([
    ['(1.0*x+1)/3', '0.333333333333333*x + 0.333333333333333'],
    ['(1.0*x**2 + x)/x', '1.0*x + 1.0'],
    ['(1.0*pi*x+1)/(x+2)', '(1.0*pi*x + 1.0)/(1.0*x + 2.0)'],
    ['(1.0*x+zoo)/(x+1)', '(1.0*x + zoo)/(1.0*x + 1.0)'],
    ['(1.0*x+oo)/(x+1)', '(1.0*x + oo)/(1.0*x + 1.0)'],
  ])('cancel(%s) over RR (constant denominators, generators that are not symbols)', (src, want) => {
    expect(String(cancel(P(src)))).toBe(want);
  });
  // SymPy's domain CC: the Floats and I as Gaussian rationals (CC.get_exact = QQ_I), the cofactors
  // of the monic gcd over QQ_I, every coefficient a Float (re + im*I) again; CC has no canonical
  // unit, the signs come from SymPy's signsimp (q could extract a minus sign)
  it.each([
    ['(1.0*I*x + 1)/(x + 2)', '(1.0*I*x + 1.0)/(1.0*x + 2.0)'],
    ['(2.0*I*x + 2)/(4*x + 4.0*I)', '(2.0*I*x + 2.0)/(4.0*x + 4.0*I)'],
    ['(x**2+1.0)/(x+I)', '1.0*x - 1.0*I'],
    ['(I*x-2.0)/(-x+1)', '(-1.0*I*x + 2.0)/(1.0*x - 1.0)'],
    ['(-2.0*I*x + 1)/(-I*x+3)', '(2.0*I*x - 1.0)/(1.0*I*x - 3.0)'],
    ['(1.5*I*x**2 + 3.0*x)/(x*y+0.5*I)', '(1.5*I*x**2 + 3.0*x)/(1.0*x*y + 0.5*I)'],
    ['(x**2-1.0*I)/(2*x)', '0.5*(1.0*x**2 - 1.0*I)/x'],
    ['(1.0*I*x+1)/(2*I*x+2)', '0.500000000000000'],
    ['(1.0*I*x+1)/(2*I)', '0.5*x - 0.5*I'],
    ['((1+2.0*I)*x + 1)/(x+3)', '(x*(1.0 + 2.0*I) + 1.0)/(1.0*x + 3.0)'],
    ['(x**2+1)/(1.0*I*x**2+1.0*I)', '-1.0*I'],
    ['(I*x/3+1.0)/(x+1)', '(1.0*I*x + 3.0)/(3.0*x + 3.0)'],
    ['((1.0+I)*x**2 - (1.0+I))/(x-1)', '1.0*x*(1.0 + 1.0*I) + 1.0 + 1.0*I'],
    ['x/(1.0*I*x+x**2)', '1.0/(1.0*x + 1.0*I)'],
    ['(1.0*I*x**2 + x)/x', '1.0*I*x + 1.0'],
  ])('cancel(%s) over CC', (src, want) => {
    expect(String(cancel(P(src)))).toBe(want);
  });
});

describe('cancel with many generators (the heuristic GCD)', () => {
  it('cancels h_y/h_yy of h = y**2/(sin(y - x) - x**2 + 2*x*y) quickly', async () => {
    const sj = await import('../../src');
    const [, y] = sj.symbols('x y');
    const h = sj.parse('y**2/(sin(y - x) - x**2 + 2*x*y)');
    const q = sj.mul(sj.diff(h, y), sj.pow(sj.diff(h, y, 2), -1));
    const t = Date.now();
    // SymPy 1.14 (0.1 s)
    expect(String(sj.cancel(q))).toBe(
      '(2*x**4*y - 6*x**3*y**2 + 4*x**2*y**3 + x**2*y**2*cos(x - y) + 4*x**2*y*sin(x - y) - 2*x*y**3*cos(x - y) - 6*x*y**2*sin(x - y) + y**2*sin(x - y)*cos(x - y) + 2*y*sin(x - y)**2)/(2*x**4 + x**2*y**2*sin(x - y) + 4*x**2*y*cos(x - y) + 4*x**2*sin(x - y) - 2*x*y**3*sin(x - y) + y**2*sin(x - y)**2 + 2*y**2*cos(x - y)**2 + 4*y*sin(x - y)*cos(x - y) + 2*sin(x - y)**2)',
    );
    expect(Date.now() - t).toBeLessThan(1000);
  });
});

// SPDX-License-Identifier: MIT
// SPDX-FileCopyrightText: Copyright 2026 OpenQL Project

// Tests of src/simplify/simplify.ts.

import { describe, expect, it, vi } from 'vitest';
import { UndefFn, SymFunction, piecewise, Eq, Ne, Ge, Gt, Le, Lt, and, I, KroneckerDelta, add, cancel, cos, countOps, exp, exptotrig, hyper, mul, parse, pow, rational, simplify, sin, symbol, symbols, together, trigsimp } from '../../src';
import type { Expr } from '../../src';
import { clearCoefficients, factorSum, inversecombine, ncSimplify, nthroot, fn, S, Sum, Mul, Pow } from '../../src';
import { Add, And, Or, Piecewise, Rel, Tuple, pi, sstr } from '../../src';

it('cancels reciprocal principal square roots on the negative real axis', () => {
  const z = symbol('z', { negative: true });
  expect(simplify(parse('sqrt(1/z) + 1/sqrt(z)', { symbols: [z] })).equals(0)).toBe(true);
});

it('retains a short logarithmic change-of-base ratio', () => {
  const y = symbol('y', { positive: true });
  const expr = parse('log(y/10)/log(y/5)', { symbols: [y] });
  expect(simplify(expr).equals(expr)).toBe(true);
});

describe('simplifying Piecewise intervals and equalities', () => {
  const [x, y] = symbols('x y', { real: true });
  it.each([
    [Piecewise([x, Gt(x, 2)]), 'Piecewise((x, x > 2), (nan, True))'],
    [Piecewise([1, Gt(x, 3)], [2, Lt(x, 2)], [3, Gt(x, 1)]), 'Piecewise((1, x > 3), (2, x < 2), (3, True))'],
    [Piecewise([1, Lt(x, 2)], [2, Lt(x, 1)], [3, true]), 'Piecewise((1, x < 2), (3, True))'],
    [Piecewise([1, And(Gt(x, 1), Lt(x, 3))], [2, And(Gt(x, 2), Lt(x, 4))]), 'Piecewise((1, (x > 1) & (x < 3)), (2, (x >= 3) & (x < 4)), (nan, True))'],
    [Piecewise([1, And(Ge(x, 1), Le(x, 3))], [2, Gt(x, 2)]), 'Piecewise((1, (x >= 1) & (x <= 3)), (2, x > 3), (nan, True))'],
    [Piecewise([1, Lt(x, 1)], [2, Le(x, 3)], [3, true]), 'Piecewise((1, x < 1), (2, x <= 3), (3, True))'],
    [Piecewise([x, and(Eq(x, y), Eq(pow(x, 2), 2))], [2, true]), 'Piecewise((y, Eq(x, y) & Eq(y**2, 2)), (2, True))'],
    [Piecewise([x, and(Eq(x, y), Gt(x, 2))], [2, true]), 'Piecewise((y, Eq(x, y) & (y > 2)), (2, True))'],
    [Piecewise([x, Eq(mul(x, y), 2)], [2, true]), 'Piecewise((x, Eq(x*y, 2)), (2, True))'],
    [add(x, Piecewise([x, Gt(x, 1)], [2, true])), 'Piecewise((2*x, x > 1), (x + 2, True))'],
    [Piecewise([x, Eq(x, pi)], [pi, true]), 'pi'],
    [Piecewise([9, Lt(x, 0)], [8, Eq(x, 3)], [7, true]), 'Piecewise((9, x < 0), (8, Eq(x, 3)), (7, True))'],
    [Piecewise([x, Or(Gt(x, y), Lt(x, 1))], [1, true]), 'Piecewise((x, (x > y) | (x < 1)), (1, True))'],
  ])('simplifies %s', (value, expected) => {
    expect(sstr(simplify(value))).toBe(expected);
  });

  it('substitutes equalities through conjunctions and tuple values', () => {
    const value = Piecewise([Tuple(x, y), And(Eq(x, 2), Eq(y, 1))], [Tuple(0, 0), true]);
    expect(sstr(simplify(value))).toBe('Piecewise(((2, 1), Eq(x, 2) & Eq(y, 1)), ((0, 0), True))');
  });

  it('simplifies Boolean bounds in raw Piecewise nodes and collapses a folded sum', () => {
    const never = new Piecewise([x, S.false, S.One, Gt(x, 0), S.Two, S.true]);
    expect(sstr(simplify(never))).toBe('Piecewise((1, x > 0), (2, True))');
    const reversed = Piecewise([x, new Rel('Lt', S.Zero, x)], [0, true], { evaluate: false });
    expect(sstr(simplify(reversed))).toBe('Piecewise((x, x > 0), (0, True))');
    const nonlinear = Piecewise([1, And(Gt(x, 0), Gt(pow(x, 2), 3))], [0, true]);
    const simplified = simplify(nonlinear);
    expect(simplified.subs(x, 2).equals(S.One)).toBe(true);
    expect(simplified.subs(x, -2).equals(S.Zero)).toBe(true);
    expect(simplify(new Add([reversed, mul(-1, reversed)])).equals(S.Zero)).toBe(true);
  });

  it('removes positive rational content from the complex sign', () => {
    expect(sstr(simplify(fn('sign', [add(2, mul(2, I))])))).toBe('sign(1 + I)');
    expect(sstr(simplify(fn('sign', [add(1, I)])))).toBe('sign(1 + I)');
  });
});

it('strips coefficients while preserving the transformed equation', () => {
  expect(clearCoefficients(parse('4*y*(6*x + 3) - 2'))).toEqual([parse('y*(2*x + 1)'), parse('1/6')]);
  expect(clearCoefficients(parse('4*y*(6*x + 3)'), parse('rhs'))).toEqual([parse('y*(2*x + 1)'), parse('rhs/12')]);
  expect(clearCoefficients(3, 5)).toEqual([S.Zero, parse('2')]);
  expect(clearCoefficients(parse('-2*x + 4'), 6).map(String)).toEqual(['x', '-1']);
  expect(String(factorSum(Sum(parse('x*y'), [symbol('x'), 1, 3])))).toBe('y*Sum(x, (x, 1, 3))');
  expect(String(factorSum(parse('x*y'), [[symbol('x'), 1, 3]]))).toBe('y*Sum(x, (x, 1, 3))');
});

it('formally combines inverse functions under their documented branch assumption', () => {
  for (const source of ['asin(sin(x))', 'acosh(cosh(x))', 'log(exp(x))', 'exp(log(x))']) expect(String(inversecombine(parse(source)))).toBe('x');
  expect(String(inversecombine(parse('2*log(exp(3*x))')))).toBe('6*x');
  expect(String(inversecombine(fn('sin', [fn('asin', [symbol('x')], { evaluate: false })], { evaluate: false })))).toBe('x');
  expect(String(inversecombine(parse('sin(cos(x)) + atan2(x, y)')))).toBe('sin(cos(x)) + atan2(x, y)');
  expect(String(inversecombine(new Pow(S.E, fn('log', [symbol('x')]))))).toBe('x');
  expect(String(inversecombine(parse('exp(sin(x)) + 2**x')))).toBe('2**x + exp(sin(x))');
});

it('verifies proposed real surd roots exactly', () => {
  expect(String(nthroot(parse('90 + 34*sqrt(7)'), 3))).toBe('sqrt(7) + 3');
  expect(String(nthroot(parse('-90 - 34*sqrt(7)'), 3))).toBe('-3 - sqrt(7)');
  expect(String(nthroot(parse('3 + 2*sqrt(2)'), 2, { maxLen: 2 }))).toBe('1 + sqrt(2)');
  expect(String(nthroot(symbol('x'), 3))).toBe('x**(1/3)');
  expect(String(nthroot(2, S.Half))).toBe('4');
  expect(String(nthroot(2, 0))).toBe('nan');
  expect(String(nthroot(parse('1 + sqrt(2)'), 3, { maxLen: 0 }))).toBe('(1 + sqrt(2))**(1/3)');
});

it('compresses noncommutative words without changing factor order', () => {
  const syms = ['a', 'b', 'c'].map((n) => symbol(n, { commutative: false }));
  const P = (s: string): Expr => parse(s, { symbols: syms });
  for (const [source, expected] of [
    ['a*b*a*b*c*a*b*c', 'a*b*(a*b*c)**2'],
    ['a**2*b*a**4*b*a**4', 'a**2*(b*a**4)**2'],
    ['a*b*a*b*c**2*(a*b)**2*c**2', '((a*b)**2*c**2)**2'],
    ['a*b*a*b + 2*a*c*a**2*c*a**2*c*a', '(a*b)**2 + 2*(a*c*a)**3'],
    ['b**-1*a**-1*(a*b)**2', 'a*b'],
    ['a**-1*b**-1*c*a', '(b*a)**(-1)*c*a'],
    ['(a*b*a*b)**2*a*c*a*c', '(a*b)**4*(a*c)**2'],
    ['a*b*c', 'a*b*c'],
    ['a**(-1/2)*b**(-1/2)', '(sqrt(b)*sqrt(a))**(-1)'],
  ]) expect(String(ncSimplify(P(source!)))).toBe(expected);
  expect(String(ncSimplify(P('(a*b*a*b)**2*a*c*a*c'), { deep: false }))).toBe('(a*b*a*b)**2*(a*c)**2');
  expect(String(ncSimplify(P('(a*b*a*b)**2')))).toBe('(a*b)**4');
  expect(String(ncSimplify(P('(a*b*a*b)**2'), { deep: false }))).toBe('(a*b*a*b)**2');
  expect(String(ncSimplify(P('a')))).toBe('a');
  expect(String(ncSimplify(P('x*y')))).toBe('x*y');
  expect(String(ncSimplify(new Mul([P('a'), P('a**-1')])))).toBe('1');
  const large = P('(a*b)**64*c*(a*b)**64');
  expect(ncSimplify(large)).toBe(large);
});

const [x, y] = symbols('x y');
it('simplifies signs, unevaluated objects and rationalized Floats (SymPy 1.14)', () => {
  for (const [src, expected] of [
    ['sign(x)*Abs(x)', 'x'], ['sign(x)*Abs(x)*sin(y)', 'x*sin(y)'],
    ['sign(x)*Abs(y)', 'Abs(y)*sign(x)'],
    ['Integral(sin(x)**2 + cos(x)**2, x)', 'Integral(1, x)'],
    ['Sum(k, (k, 1, n))', 'Sum(k, (k, 1, n))'],
    ['Product(k, (k, 1, n))', 'factorial(n)'],
    ['Derivative(sin(x), x)', 'cos(x)'],
  ] as const) expect(String(simplify(parse(src)))).toBe(expected);
  expect(String(simplify(parse('Derivative(sin(x), x)'), { doit: false }))).toBe('Derivative(sin(x), x)');
  expect(String(simplify(parse('Product(k, (k, 1, n))'), { doit: false }))).toBe('Product(k, (k, 1, n))');
  expect(String(simplify(parse('0.1*x + 0.2*y'), { rational: true }))).toBe('x/10 + y/5');
  expect(String(simplify(parse('(0.1*x + 0.2)/(x + 2)'), { rational: true }))).toBe('1/10');
  expect(String(simplify(parse('(0.1*x + 0.2)/(x + 2)'), { rational: null }))).toBe('0.100000000000000');
  expect(String(simplify(parse('1.25'), { rational: true }))).toBe('5/4');
});
it('combines sums and products with equal or adjacent bounds (SymPy 1.14)', () => {
  for (const [source, expected] of [
    ['Sum(f(k), (k, 1, n)) + Sum(g(k), (k, 1, n))', 'Sum(f(k) + g(k), (k, 1, n))'],
    ['Product(f(k), (k, 1, n))*Product(g(k), (k, 1, n))', 'Product(f(k)*g(k), (k, 1, n))'],
    ['Sum(f(k), (k, 1, n)) + Sum(f(k), (k, n+1, m))', 'Sum(f(k), (k, 1, m))'],
    ['Product(f(k), (k, 1, n))*Product(f(k), (k, n+1, m))', 'Product(f(k), (k, 1, m))'],
    ['2*Sum(f(k), (k, 1, n)) + Sum(g(k), (k, 1, n))', 'Sum(2*f(k) + g(k), (k, 1, n))'],
    ['Integral(a*sin(x)**2 + a*cos(x)**2, x)', 'a*x'],
    ['Integral(a*f(x), x)', 'a*Integral(f(x), x)'],
  ] as const) expect(String(simplify(parse(source)))).toBe(expected);
  expect(String(simplify(parse('Integral(a*sin(x)**2 + a*cos(x)**2, x)'), { doit: false }))).toBe('a*Integral(1, x)');
  // SymPy 1.14 incorrectly captures the free k inside the sum. For f=1, g=0,
  // n=2, k=10 the original value is 20, whereas its simplified result is 3.
  const e = parse('k*Sum(f(k), (k, 1, n)) + Sum(g(k), (k, 1, n))');
  expect(String(simplify(e))).toBe(String(e));
});
it('keeps distinct summation domains and joins adjacent constant summands', () => {
  const untouched = [
    'Sum(f(k),(k,1,n))+g(x)',
    'Sum(f(k),(k,1,n))+Sum(g(k),(k,2,n))',
    'Sum(f(k),(k,1,n))+Sum(f(k),(k,n+2,m))',
    'Sum(f(k,j),(k,1,n),(j,1,m))+Sum(g(k,j),(k,2,n),(j,1,m))',
  ];
  for (const source of untouched) {
    const e = parse(source);
    expect(String(simplify(e, { doit: false }))).toBe(String(e));
  }
  // SymPy factors out the summand independent of the bound indices.
  expect(String(simplify(parse('Sum(f(x),(k,1,n))+Sum(f(x),(j,1,m))'), { doit: false }))).toBe('(Sum(1, (j, 1, m)) + Sum(1, (k, 1, n)))*f(x)');
  expect(String(simplify(parse('Sum(f(x),(k,1,n))+Sum(f(x),(k,n+1,m))'), { doit: false }))).toBe('f(x)*Sum(1, (k, 1, m))');
});
const [a, b, theta] = symbols('a b theta', { real: true });
type Assume = NonNullable<Parameters<typeof symbol>[1]>;
const PA = (s: string, a: Record<string, Assume> = {}): Expr =>
  parse(s, { symbols: Object.entries(a).map(([k, v]) => symbol(k, v)) });
const showMap = (v: unknown): string => {
  if (Array.isArray(v)) return `[${v.map(showMap).join(', ')}]`;
  if (v instanceof Map) return `{${[...v].map(([k, w]) => `${showMap(k)}: ${showMap(w)}`).sort().join(', ')}}`;
  return String(v);
};

describe('simplify', () => {
  it('proves sin^2 + cos^2 = 1', () => {
    expect(simplify(add(pow(sin(x), 2), pow(cos(x), 2))).toString()).toBe('1');
    expect(simplify(add(pow(sin(mul(rational(1, 2), theta)), 2), pow(cos(mul(rational(1, 2), theta)), 2))).toString()).toBe('1');
  });

  it('collapses angle addition', () => {
    const e = add(mul(cos(a), cos(b)), mul(-1, sin(a), sin(b)));
    expect(simplify(e).toString()).toBe('cos(a + b)');
    const f = add(mul(sin(a), cos(b)), mul(cos(a), sin(b)));
    expect(simplify(f).toString()).toBe('sin(a + b)');
  });

  it('rewrites Euler form', () => {
    expect(simplify(add(cos(theta), mul(I, sin(theta)))).toString()).toBe('exp(I*theta)');
    expect(trigsimp(exp(mul(I, theta))).toString()).toBe('exp(I*theta)');
    expect(exptotrig(exp(mul(I, theta))).toString()).toBe('I*sin(theta) + cos(theta)');
  });

  it('keeps already simple expressions', () => {
    expect(simplify(pow(cos(x), 2)).toString()).toBe('cos(x)**2');
    expect(simplify(add(x, 1)).toString()).toBe('x + 1');
  });

  it('cancels rational functions', () => {
    const e = mul(add(pow(x, 2), -1), pow(add(x, -1), -1));
    expect(cancel(e).toString()).toBe('x + 1');
    expect(simplify(e).toString()).toBe('x + 1');
    expect(together(add(pow(x, -1), pow(y, -1))).toString()).toBe('(x + y)/(x*y)');
    // regression: denominators with non-rational exponents (found by fuzzing)
    const e2 = add(rational(1, 2), mul(2, exp(mul(-3, I))));
    expect(together(e2).toComplex().re).toBeCloseTo(e2.toComplex().re);
  });
});

describe("simplify (cov2): SymPy 1.14 cases", () => {
  const cases: [string, () => unknown, string][] = [
    ["simplify(P('log(x) + log(y)', {x: {positive: true}, y: {positive: true}}), { measure: countOps })", () => simplify(PA('log(x) + log(y)', {x: {positive: true}, y: {positive: true}}), { measure: countOps }), "log(x*y)"],
    ["simplify(P('2*log(x) + 3*log(y)', {x: {positive: true}, y: {positive: true}}), { measure: (e) => countOps(e) })", () => simplify(PA('2*log(x) + 3*log(y)', {x: {positive: true}, y: {positive: true}}), { measure: (e) => countOps(e) }), "log(x**2*y**3)"],
    ["simplify(P('log(x*y)', {x: {positive: true}, y: {positive: true}}), { measure: countOps })", () => simplify(PA('log(x*y)', {x: {positive: true}, y: {positive: true}}), { measure: countOps }), "log(x*y)"],
    ["simplify(P('log(x**2*y)'), { measure: countOps })", () => simplify(PA('log(x**2*y)'), { measure: countOps }), "log(x**2*y)"],
  ];
  it.each(cases)('%s', (_name, run, want) => {
    expect(showMap(run())).toBe(want);
  });
});

describe('simplify ends with exptrigsimp (SymPy)', () => {
  // SymPy 1.14: simplify(Znm(1, 1, theta, phi).expand(func=True)), simplify(Znm(2, 1, theta, phi).expand(func=True))
  it('exp(I*phi) + exp(-I*phi) inside a product becomes 2*cos(phi)', () => {
    const [ph, th] = symbols('phi theta');
    const c1 = parse('-sqrt(3)/(4*sqrt(pi))');
    const e1 = add(mul(c1, exp(mul(I, ph)), sin(th)), mul(c1, exp(mul(-1, I, ph)), sin(th)));
    expect(String(simplify(e1))).toBe('-sqrt(3)*sin(theta)*cos(phi)/(2*sqrt(pi))');
    const c2 = parse('-sqrt(15)/(4*sqrt(pi))');
    const e2 = add(mul(c2, exp(mul(I, ph)), sin(th), cos(th)), mul(c2, exp(mul(-1, I, ph)), sin(th), cos(th)));
    expect(String(simplify(e2))).toBe('-sqrt(15)*sin(2*theta)*cos(phi)/(4*sqrt(pi))');
    // an exponential that exptrigsimp does not shorten is kept: simplify(exp(I*x)*y) = y*exp(I*x)
    expect(String(simplify(mul(exp(mul(I, ph)), th)))).toBe('theta*exp(I*phi)');
  });
});

describe('simplify keeps the numeric content of a quotient in front (SymPy factor_terms(expr, sign=False))', () => {
  it.each([
    ['(15 - 63*x)/((x - 1)*(5*x - 1))', '3*(5 - 21*x)/((x - 1)*(5*x - 1))'],
    ['(2*x + 2)/y', '2*(x + 1)/y'],
    ['2*x/(4*y + 6)', 'x/(2*y + 3)'],
    ['(x/2 + 1/2)/y', '(x + 1)/(2*y)'],
    // sums are not factored
    ['2*x + 2', '2*x + 2'],
    ['6*x + 4*y', '6*x + 4*y'],
  ])('simplify(%s)', (src, want) => {
    expect(String(simplify(parse(src)))).toBe(want);
  });
  it('the generating function of sequence(3*5**n + 12)', () => {
    // SymPy: sequence(3*5**n + 12).find_linear_recurrence(20, gfvar=x)[1]
    const e = mul(parse('-3*(21*x - 5)'), pow(parse('(x - 1)*(5*x - 1)'), -1));
    expect(String(simplify(e))).toBe('3*(5 - 21*x)/((x - 1)*(5*x - 1))');
  });
});

describe('simplify of holonomic to_expr results (SymPy holonomic tests)', () => {
  it('exp(-x**2/2) goes to the denominator of together and cancel', () => {
    const e = parse('-x**2*(2/x**2 - 2*exp(-x**2/2)/x**2)/2 + 1 - sqrt(2)*I*sqrt(pi)*exp(-x**2/2)*erf(sqrt(2)*I*x/2)/2');
    expect(String(together(e, { deep: true }))).toBe('(-sqrt(2)*I*sqrt(pi)*erf(sqrt(2)*I*x/2) + 2)*exp(-x**2/2)/2');
    expect(String(simplify(e))).toBe('(-sqrt(2)*I*sqrt(pi)*erf(sqrt(2)*I*x/2) + 2)*exp(-x**2/2)/2');
  });
  it('the product after trigsimp is expanded when that is shorter (SymPy expand_power_exp(expand_mul(short)))', () => {
    expect(String(simplify(parse('(-x**2*(Si(2*x)/x + cos(2*x)/(2*x**2) - 1/(2*x**2)) - 1)/x')))).toBe('-Si(2*x) - cos(x)**2/x');
  });
});

describe('fractions in sums, opposite bases of even powers and rationalized denominators (SymPy simplify)', () => {
  it('match SymPy', () => {
    // SymPy: (-x**2 - y**2)/y**3
    expect(String(simplify(parse('-(x**2/y**2 + 1)/y')))).toBe('(-x**2 - y**2)/y**3');
    expect(String(simplify(parse('sqrt((-u + v)**2) - sqrt((u - v)**2)')))).toBe('0');
    expect(String(simplify(parse('sqrt((-2*u/3 + 2*v/3)**2 + (-2*w/3 + 2*z/3)**2) + sqrt((u/3 - v/3)**2 + (w/3 - z/3)**2) - sqrt((u - v)**2 + (w - z)**2)')))).toBe('0');
    expect(String(simplify(parse('1/(1 + sqrt(2))')))).toBe('-1 + sqrt(2)');
    expect(String(simplify(parse('1/(2 + sqrt(2))')))).toBe('1 - sqrt(2)/2');
    expect(String(simplify(parse('1/(x + 1)')))).toBe('1/(x + 1)');
  });
});

describe('simplify of the moments of sympy.stats distributions (SymPy 1.14)', () => {
  const l = symbol('lambda', { positive: true });
  const k = symbol('k', { positive: true });
  const [mu, om] = [symbol('mu', { positive: true }), symbol('omega', { positive: true })];
  const S2 = (e: string): string => String(simplify(parse(e, { symbols: [l, k, mu, om] })));
  it('powers of the same base combine after their exponents are simplified (Weibull)', () => {
    expect(S2('lambda**k*lambda**(k*(-1 + (k + 1)/k))*lambda**(1 - k)*gamma(1 + 1/k)/lambda')).toBe('lambda*gamma(1 + 1/k)');
    expect(S2('2**x*2**(1-x)*y')).toBe('2*y');
  });
  it('the minus sign of a product goes into its sum when that is shorter', () => {
    expect(S2('-lambda**2*(gamma(1+1/k)**2-gamma(1+2/k))')).toBe('lambda**2*(-gamma(1 + 1/k)**2 + gamma(1 + 2/k))');
    expect(S2('-x*(x+1)')).toBe('-x*(x + 1)');
    expect(S2('-(x+1)*(y-1)')).toBe('-(x + 1)*(y - 1)');
  });
  it('gamma functions with powers of quotients of positive bases (Nakagami)', () => {
    expect(S2('mu**mu*omega*(mu/omega)**(1/2 - mu)*gamma(mu + 1/2)/(mu*omega**mu*gamma(mu))')).toBe('sqrt(mu)*sqrt(omega)*gamma(mu + 1/2)/gamma(mu + 1)');
  });
});

describe('logarithms expanded or combined, whichever is shorter by count_ops (SymPy simplify)', () => {
  it('SymPy 1.14', () => {
    const [x, y] = symbols('x y', { positive: true });
    const cases: [Expr, string][] = [
      [parse('log(8)/log(2)'), '3'],
      [parse('log(6) - log(2) - log(3)'), '0'],
      [add(parse('log(x)'), parse('log(y)')).subs(parse('x'), x).subs(parse('y'), y), 'log(x*y)'],
      [parse('2*log(x) - log(y)').subs(parse('x'), x).subs(parse('y'), y), 'log(x**2/y)'],
      [parse('log(x**2)').subs(parse('x'), x), '2*log(x)'],
      [parse('log(x)/2 + log(2)').subs(parse('x'), x), 'log(x)/2 + log(2)'],
    ];
    expect(cases.map(([e]) => String(simplify(e)))).toEqual(cases.map(([, r]) => r));
  });
});

describe('the SymPy simplify pipeline (sympy/simplify/simplify.py)', () => {
  it('_eval_simplify of hyper, Bessel and combinatorial functions at the top level', () => {
    // SymPy 1.14
    expect(String(simplify(hyper([], [], x)))).toBe('exp(x)');
    expect(String(simplify(parse('besselj(1/2, x)')))).toBe('sqrt(2)*sin(x)/(sqrt(pi)*sqrt(x))');
    expect(String(simplify(parse('binomial(x, 2)')))).toBe('binomial(x, 2)');
    expect(String(simplify(parse('factorial(x + 1)/factorial(x)')))).toBe('x + 1');
    // log(exp(x)) is not x for complex x (expand_log without force)
    expect(String(simplify(parse('log(exp(x))')))).toBe('log(exp(x))');
  });
  it('ratio = oo', () => {
    // SymPy: simplify(r, ratio=oo) keeps the together form even when it is longer
    expect(String(simplify(parse('1/x + 1/y'), { ratio: Infinity }))).toBe('(x + y)/(x*y)');
  });
  it('kroneckersimp', () => {
    const i = symbol('i');
    // SymPy 1.14: x
    expect(String(simplify(add(x, mul(KroneckerDelta(0, i), KroneckerDelta(1, i)))))).toBe('x');
  });
  it('collects Abs factors (SymPy collect_abs)', () => {
    // SymPy 1.14
    expect(String(simplify(parse('5*Abs((x**2 - 1)/(x - 1))')))).toBe('5*Abs(x + 1)');
    expect(String(simplify(parse('Abs(x)/Abs(x**2)')))).toBe('1/Abs(x)');
  });
  it('simplifies the lie group coordinate of sqrt(y - 1)/sqrt(y + 1) quickly', () => {
    const t = Date.now();
    // SymPy 1.14: 0
    expect(String(simplify(parse('sqrt(y + 1)/sqrt(y - 1) + (y**2 - 1)*(x/(2*sqrt(y - 1)*sqrt(y + 1)) - x*sqrt(y + 1)/(2*(y - 1)**(3/2)))/x')))).toBe('0');
    expect(Date.now() - t).toBeLessThan(1000);
  });
});

it('respects relational measures and recognizes algebraic zero identities', async () => {
  const sj = await import('../../src');
  const { impl } = await import('../../src/core/nodes');
  const x = new sj.Sym('x');
  const relation = new sj.Rel('Lt', sj.S.One, x);
  expect(sj.simplify(relation, { ratio: 0 })).toBe(relation);
  expect(String(sj.simplify(relation, { measure: (e) => sj.Rational.of(sj.countOps(e) + 1) }))).toBe('x > 1');
  expect(impl.equalsZero?.(sj.S.Zero)).toBe(true);
  expect(impl.equalsZero?.(sj.S.One)).toBeUndefined();
  expect(impl.equalsZero?.(x)).toBeUndefined();
  expect(impl.equalsZero?.(sj.I)).toBeUndefined();
  expect(impl.equalsZero?.(sj.add(sj.sqrt(2), 1))).toBeUndefined();
  expect(impl.equalsZero?.(sj.mul(sj.sqrt(2), sj.sqrt(3)))).toBeUndefined();
});

it('simplifies nested special functions and extension expressions', async () => {
  const sj = await import('../../src');
  expect(sj.simplify(sj.Quaternion(sj.add(sj.pow(sj.sin(x), 2), sj.pow(sj.cos(x), 2)), 0, 0, 0)).key).toBe(sj.Quaternion(1, 0, 0, 0).key);
  expect(String(sj.simplify(sj.add(x, sj.hyper([], [], x))))).toBe('x + hyper((), (), x)');
  expect(sj.simplify(sj.add(x, sj.fn('besselj', [sj.S.Half, x])))).toBeDefined();
  expect(sj.simplify(sj.fn('binomial', [x, sj.S.Two]), { ratio: 0 }).key).toBe(sj.fn('binomial', [x, sj.S.Two]).key);
});

it('uses expression-valued measures and the algebraic zero certificate', async () => {
  const sj = await import('../../src');
  const { impl } = await import('../../src/core/nodes');
  expect(sj.simplify(sj.add(x, sj.symbol('y')), { measure: (e) => sj.Rational.of(sj.countOps(e) + 1) }).key).toBe(sj.add(x, sj.symbol('y')).key);
  const factorial = new sj.Fn('factorial', [x]);
  expect(sj.simplify(factorial, { ratio: 0 }).key).toBe(factorial.key);
  expect(sj.simplify(factorial, { ratio: Infinity }).key).toBe(sj.combsimp(factorial).key);
  const zero = sj.parse('sqrt(2) + sqrt(3) - sqrt(5 + 2*sqrt(6))');
  expect(impl.equalsZero?.(zero)).toBe(true);
});

it('cancels shifted powers of the roots of a characteristic polynomial', () => {
  const n = symbol('n', {integer:true});
  for (const base of [parse('(1+sqrt(5))/2'),parse('(1-sqrt(5))/2')]) {
    const residual = add(pow(base,add(n,2)),mul(-1,pow(base,add(n,1))),mul(-1,pow(base,n)));
    expect(simplify(residual)).toBe(S.Zero);
  }
});

it('decides mathematical equality independently of structural equality', async () => {
  const sj = await import('../../src');
  const f = (s: string) => sj.parse(s);
  expect(sj.exprEquals(f('x'), f('x'))).toBe(true);
  expect(sj.exprEquals(f('sqrt(x)'), 0)).toBe(false);
  expect(sj.exprEquals(f('sqrt(3)+sqrt(5)'), 0)).toBe(false);
  expect(sj.exprEquals(f('sqrt(1+sqrt(3))+sqrt(3+3*sqrt(3))'), f('sqrt(10+6*sqrt(3))'))).toBe(true);
  expect(sj.exprEquals(f('(9*3**(2/3)+30+27*3**(1/3))**(1/3)'), f('3+3**(1/3)'))).toBe(true);
  expect(sj.exprEquals(f('x/(1+y)'), 0)).toBe(false);
  expect(sj.exprEquals(f('sin(x)+y'), 0)).toBe('unknown');
});

it('chooses an exactly equivalent simpler primitive element for an algebraic number', async () => {
  const sj = await import('../../src');
  const root = sj.parse('(41+29*sqrt(2))**(1/5)');
  const a = new sj.AlgebraicNumber(root);
  expect(sj.simplify(a).root.equals(sj.parse('1+sqrt(2)'))).toBe(true);
  expect(sj.simplify(a, { ratio: 0 })).toBe(a);
  const t = new sj.AlgebraicNumber(sj.sqrt(2));
  expect(sj.simplify(t, { measure: (e) => sj.Rational.of(sj.countOps(e)) })).toBe(t);
  const alias = sj.symbol('theta');
  expect(sj.simplify(new sj.AlgebraicNumber(root, [1, 0], { alias })).alias).toBe(alias);
  expect(sj.exprEquals(sj.parse('sin(x)+2'), 0)).toBe('unknown');
  expect(sj.exprEquals(sj.Mod(x, 3), 0)).toBe('unknown');
  expect(sj.exprEquals(sj.parse('x*sin(x)/(1+y)'), 0)).toBe(false);
  const zero = sj.parse('(9*3**(2/3)+30+27*3**(1/3))**(1/3)-3-3**(1/3)');
  expect(sj.exprEquals(sj.mul(zero, x), 0)).toBe(true);
});

it('leaves symbolic products undecided when a factor may be zero', async () => {
  const sj = await import('../../src');
  const { impl } = await import('../../src/core/nodes');
  expect(sj.exprEquals(sj.parse('(sin(x)+y)*(1+z)'), 0)).toBe('unknown');
  expect(impl.equalsZero?.(new sj.Pow(sj.S.Zero, sj.S.NegOne))).toBeUndefined();
});

it('folds the absolute-value rewrite of sign before simplifying products', async () => {
  const sj = await import('../../src');
  const r = sj.symbol('r', { real: true });
  const lhs = sj.parse('2*sign(r+3)/(5*Abs(r+3)**(3/5))', { symbols: { r } });
  const relation = sj.simplify(sj.Eq(lhs, 0));
  expect(String(relation)).toContain('Piecewise((0, Eq(r, -3))');
  expect(sj.subs(relation, [[r, -3]])).toBe(sj.S.true);
});

it('simplifies an unevaluated integral without extracting a unit coefficient', async () => {
  const sj = await import('../../src');
  const v = sj.symbol('v');
  const integral = new sj.Integral([sj.sin(v), v]);
  expect(sj.simplify(integral, { doit: false }).equals(integral)).toBe(true);
});

it('keeps sign intact when no rewrite applies', async () => {
  const sj = await import('../../src');
  const { impl } = await import('../../src/core/nodes');
  const rewrite = Object.getOwnPropertyDescriptor(impl, 'rewrite');
  const e = sj.parse('sign(x)/Abs(x)**(3/5)');
  try {
    impl.rewrite = (input) => input;
    expect(String(sj.simplify(e))).toContain('sign(x)');
  } finally {
    if (rewrite !== undefined) Object.defineProperty(impl, 'rewrite', rewrite);
  }
});

it('handles an indeterminate minimal polynomial for an algebraic difference', async () => {
  const sj = await import('../../src');
  const numberfields = await import('../../src/polys/numberfields');
  const mock = vi.spyOn(numberfields, 'minimalPolynomial').mockImplementationOnce(() => {
    throw new sj.NotImplementedError('minimal polynomial is indeterminate');
  });
  try {
    expect(sj.exprEquals(sj.sqrt(2), 0)).toBe(false);
  } finally {
    mock.mockRestore();
  }
});

it('honors explicitly requested inverse cancellation for user functions', () => {
  const x = symbol('x'), g = SymFunction('g');
  class F extends UndefFn { inverse() { return g; } }
  expect(simplify(new F('f', [g(x)]), { inverse: true })).toEqual(x);
  for (const args of [[x], [sin(x)], [g(x), x]]) {
    const f = new F('f', args);
    expect(inversecombine(f)).toEqual(f);
  }
});

it('cancels an unevaluated logarithm of an exponential in explicit inverse mode', () => {
  const x = symbol('x');
  const raw = { evaluate: false };
  expect(simplify(fn('log', [exp(x)], raw), { inverse: true })).toEqual(x);
  const based = fn('log', [exp(x), 2], raw);
  expect(simplify(based, { inverse: true })).toEqual(x.div(fn('log', [2])));
  const unmatched = fn('log', [exp(x), 2, 3], raw);
  expect(inversecombine(unmatched)).toEqual(unmatched);
});

it('preserves an unevaluated logarithm of a symbolic sum', () => {
  const [n, x] = symbols('n x');
  const log = fn('log', [Sum(n, [n, 1, x])], { evaluate: false });
  expect(simplify(log)).toEqual(log);
});

it('retains the strongest comparable conjunct and preserves independent conditions', () => {
  const [x, y, z] = symbols('x y z');
  for (const op of [Ge, Gt, Le, Lt]) {
    const bound = op === Ge || op === Gt ? 2 : 1;
    expect(simplify(and(op(x, 1), op(x, 2))).equals(op(x, bound))).toBe(true);
  }
  for (const condition of [and(Ge(x, 1), Lt(x, 2)), and(Ne(x, y), Ne(x, z))]) {
    expect(simplify(condition).equals(condition)).toBe(true);
  }
});

it('preserves piecewise values that do not define a Kronecker delta', () => {
  const [x, y] = symbols('x y');
  const delta = KroneckerDelta(x, y);
  for (const condition of [
    piecewise([1, Ge(x, y)], [0, true]), piecewise([2, Eq(x, y)], [0, true]),
    piecewise([1, Eq(x, y)], [2, true]), piecewise([0, Ne(x, y)], [2, true]),
    piecewise([1, Eq(x, y)], [0, Ge(x, y)]),
  ]) {
    const result = simplify(add(delta, condition));
    expect(result.has(delta)).toBe(true);
  }
});
